import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_353

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

/-!
## Part 1: Parity-octagon summaries (`Sum8`) and exact query / peeling theory
-/

private structure Sum8 where
  fr : ℕ
  fb : ℕ
  cr : ℕ
  cb : ℕ
  d00 : ℕ
  d11 : ℕ
  d01 : ℕ
  d10 : ℕ
  deriving DecidableEq

private def Sum8.zero : Sum8 := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

private def Sum8.comb (a b : Sum8) : Sum8 :=
  ⟨a.fr + b.fr, a.fb + b.fb, a.cr + b.cr, a.cb + b.cb,
   a.d00 + b.d00, a.d11 + b.d11, a.d01 + b.d01, a.d10 + b.d10⟩

private def Sum8.ofSeg (R B : ℕ) (p : Bool) : Sum8 :=
  if R + B = 0 then Sum8.zero
  else if R + B = 1 then
    if R = 1 then ⟨p.toNat, 0, 0, 0, 0, 0, 0, 0⟩
    else ⟨0, p.toNat, 0, 0, 0, 0, 0, 0⟩
  else
    ⟨0, 0, R, B, p.toNat, (R + B + p.toNat) % 2, (B + p.toNat) % 2, (R + p.toNat) % 2⟩

private def Sum8.Mem (s : Sum8) (r b : ℕ) : Prop :=
  s.fr ≤ r ∧ r ≤ s.fr + s.cr ∧
  s.fb ≤ b ∧ b ≤ s.fb + s.cb ∧
  (r - s.fr + (b - s.fb)) % 2 = s.d00 % 2 ∧
  s.d00 ≤ r - s.fr + (b - s.fb) ∧
  r - s.fr + (b - s.fb) + s.d11 ≤ s.cr + s.cb ∧
  s.d01 + (b - s.fb) ≤ (r - s.fr) + s.cb ∧
  s.d10 + (r - s.fr) ≤ s.cr + (b - s.fb)

private instance (s : Sum8) (r b : ℕ) : Decidable (s.Mem r b) := by
  unfold Sum8.Mem; infer_instance

private structure Sum8.Good (s : Sum8) : Prop where
  zero_iff : s.cr = 0 ↔ s.cb = 0
  d00_d01 : s.d00 + s.d01 ≤ s.cb
  d11_d10 : s.d11 + s.d10 ≤ s.cb
  d00_d10 : s.d00 + s.d10 ≤ s.cr
  d11_d01 : s.d11 + s.d01 ≤ s.cr
  par_d11 : s.d11 % 2 = (s.cr + s.cb + s.d00) % 2
  par_d01 : s.d01 % 2 = (s.cb + s.d00) % 2
  par_d10 : s.d10 % 2 = (s.cr + s.d00) % 2

private lemma Sum8.comb_zero_left (s : Sum8) : Sum8.zero.comb s = s := by
  cases s; simp [Sum8.zero, Sum8.comb]

private lemma Sum8.comb_zero_right (s : Sum8) : s.comb Sum8.zero = s := by
  cases s; simp [Sum8.zero, Sum8.comb]

private lemma Sum8.comb_assoc (a b c : Sum8) : (a.comb b).comb c = a.comb (b.comb c) := by
  cases a; cases b; cases c; simp [Sum8.comb, Nat.add_assoc]

private lemma Sum8.comb_comm (a b : Sum8) : a.comb b = b.comb a := by
  cases a; cases b; simp [Sum8.comb, Nat.add_comm]

private lemma Sum8.comb_4_swap (a b c d : Sum8) :
    a.comb (b.comb (c.comb d)) = (c.comb a).comb (b.comb d) := by
  cases a; cases b; cases c; cases d; simp only [Sum8.comb, Sum8.mk.injEq]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

private lemma Sum8.comb_3_swap (a b c : Sum8) :
    (a.comb b).comb c = b.comb (a.comb c) := by
  cases a; cases b; cases c; simp only [Sum8.comb, Sum8.mk.injEq]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

private lemma Sum8.good_zero : Sum8.zero.Good := by
  refine ⟨by simp [Sum8.zero], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Sum8.zero]

private lemma Sum8.good_comb {a b : Sum8} (ha : a.Good) (hb : b.Good) : (a.comb b).Good := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Sum8.comb]
    have h1 := ha.zero_iff; have h2 := hb.zero_iff; omega
  · simp only [Sum8.comb]; have := ha.d00_d01; have := hb.d00_d01; omega
  · simp only [Sum8.comb]; have := ha.d11_d10; have := hb.d11_d10; omega
  · simp only [Sum8.comb]; have := ha.d00_d10; have := hb.d00_d10; omega
  · simp only [Sum8.comb]; have := ha.d11_d01; have := hb.d11_d01; omega
  · simp only [Sum8.comb]; have := ha.par_d11; have := hb.par_d11; omega
  · simp only [Sum8.comb]; have := ha.par_d01; have := hb.par_d01; omega
  · simp only [Sum8.comb]; have := ha.par_d10; have := hb.par_d10; omega

private lemma Sum8.good_ofSeg (R B : ℕ) (p : Bool) (h : R + B ≤ 1 ∨ (1 ≤ R ∧ 1 ≤ B)) :
    (Sum8.ofSeg R B p).Good := by
  unfold Sum8.ofSeg
  split_ifs with h0 h1 hR
  · exact Sum8.good_zero
  · refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  · refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  · have hRB : 1 ≤ R ∧ 1 ≤ B := by omega
    cases p <;> refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

private lemma Sum8.mem_zero_iff (r b : ℕ) : Sum8.zero.Mem r b ↔ r = 0 ∧ b = 0 := by
  unfold Sum8.Mem Sum8.zero; dsimp only; omega

private lemma Sum8.mem_comb_of_mem {s1 s2 : Sum8} {r1 b1 r2 b2 : ℕ}
    (h1 : s1.Mem r1 b1) (h2 : s2.Mem r2 b2) : (s1.comb s2).Mem (r1 + r2) (b1 + b2) := by
  rcases h1 with ⟨_, _, _, _, _, _, _, _, _⟩
  rcases h2 with ⟨_, _, _, _, _, _, _, _, _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Sum8.comb] <;> omega

private lemma Sum8.mem_ofSeg_of_bounds {R B : ℕ} {p : Bool} {r b : ℕ}
    (hRB : R + B ≤ 1 ∨ (1 ≤ R ∧ 1 ≤ B))
    (hr : r ≤ R) (hb : b ≤ B) (hpar : (r + b) % 2 = p.toNat)
    (h0 : R + B = 0 → p = false) :
    (Sum8.ofSeg R B p).Mem r b := by
  unfold Sum8.ofSeg Sum8.Mem
  split_ifs with hL0 hL1 hR1
  · have hp := h0 hL0; subst hp; dsimp only [Sum8.zero]; omega
  · cases p <;> dsimp only <;> omega
  · cases p <;> dsimp only <;> omega
  · cases p <;> dsimp only <;> omega

private lemma sub_one_sub_cancel (a b : ℕ) (hb : 1 ≤ b) : a + b - 1 - a = b - 1 := by omega
private lemma add_sub_succ_cancel (a b : ℕ) (hb : 1 ≤ b) : a + b - (1 + a) = b - 1 := by omega
private lemma par_sub_two (x y d : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) (h : (x + y) % 2 = d % 2) :
    (x - 1 + (y - 1)) % 2 = d % 2 := by omega
private lemma par_sub_one (x y d : ℕ) (hx : 1 ≤ x) (h : (x + y) % 2 = (1 + d) % 2) :
    (x - 1 + y) % 2 = d % 2 := by omega
private lemma par_add_sub_one (x y d : ℕ) (hy : 1 ≤ y) (h : (x + y) % 2 = (1 + d) % 2) :
    (x + (y - 1)) % 2 = d % 2 := by omega
private lemma par_flip_sub (x y c d : ℕ) (hx : 1 ≤ x) (hc : c ≤ 1) (h : (x + y) % 2 = (c + d) % 2) :
    (x - 1 + y) % 2 = (1 - c + d) % 2 := by omega
private lemma par_flip_sub_b (x y c d : ℕ) (hy : 1 ≤ y) (hc : c ≤ 1) (h : (x + y) % 2 = (c + d) % 2) :
    (x + (y - 1)) % 2 = (1 - c + d) % 2 := by omega
private lemma par_sub_d00 (d00 rp : ℕ) (t : Bool) (hle : rp ≤ d00) (hrp : rp % 2 = t.toNat) :
    (d00 - rp) % 2 = (xor t (decide (d00 % 2 = 1))).toNat := by
  cases t <;> by_cases hd : d00 % 2 = 1 <;> simp [hd] at hrp ⊢ <;> omega
private lemma par_d10_rp (d10 d00 cr rp : ℕ) (t : Bool) (hle : cr ≤ d10 + rp)
    (hp10 : d10 % 2 = (cr + d00) % 2) (hrp : rp % 2 = t.toNat) :
    (d10 + rp - cr) % 2 = (xor t (decide (d00 % 2 = 1))).toNat := by
  cases t <;> by_cases hd : d00 % 2 = 1 <;> simp [hd] at hp10 hrp ⊢ <;> omega
private lemma par_b_from_r (rp bp d00 : ℕ) (t : Bool)
    (hmp : (rp + bp) % 2 = d00 % 2) (hpar : rp % 2 = t.toNat) :
    bp % 2 = (xor t (decide (d00 % 2 = 1))).toNat := by
  cases t <;> by_cases hd : d00 % 2 = 1 <;> simp [hd] at hmp hpar ⊢ <;> omega

private lemma par_eq_add_two (rp bp cr cb d00 d11 : ℕ)
    (h5 : (rp + bp) % 2 = d00 % 2) (hp11 : d11 % 2 = (cr + cb + d00) % 2)
    (h7 : rp + bp + d11 ≤ 1 + cr + (1 + cb)) (hC : cr + cb < rp + bp + d11) :
    rp + bp + d11 = cr + cb + 2 := by omega
private lemma par_eq_d10_top (rp bp cr d00 d10 : ℕ)
    (hb : 1 ≤ bp) (h5 : (rp + bp) % 2 = (1 + d00) % 2) (hp10 : d10 % 2 = (cr + d00) % 2)
    (h9 : d10 + rp ≤ 1 + cr + bp) (hC : cr + (bp - 1) < d10 + rp) :
    d10 + rp = cr + 1 + bp := by omega
private lemma par_eq_d01_top (rp bp cb d00 d01 : ℕ)
    (hr : 1 ≤ rp) (h5 : (rp + bp) % 2 = (1 + d00) % 2) (hp01 : d01 % 2 = (cb + d00) % 2)
    (h8 : d01 + bp ≤ rp + (1 + cb)) (hC : (rp - 1) + cb < d01 + bp) :
    d01 + bp = rp + 1 + cb := by omega
private lemma mod2_le_one (x : ℕ) : x % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt x (by decide))
private lemma bool_toNat_le_one (p : Bool) : p.toNat ≤ 1 := by cases p <;> decide
private lemma bool_not_toNat (p : Bool) : (!p).toNat = 1 - p.toNat := by cases p <;> decide
private lemma mod2_add1_mid3 (a b c : ℕ) : (a + 1 + b + c) % 2 = 1 - (a + b + c) % 2 := by omega
private lemma mod2_add1_mid2 (a c : ℕ) : (a + 1 + c) % 2 = 1 - (a + c) % 2 := by omega
private lemma mod2_add1_r3 (a b c : ℕ) : (a + (b + 1) + c) % 2 = 1 - (a + b + c) % 2 := by omega
private lemma mod2_add_not (x : ℕ) (p : Bool) : (x + (!p).toNat) % 2 = 1 - (x + p.toNat) % 2 := by
  cases p <;> simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true] <;> omega
private lemma par_same_ge2 (a b : ℕ) (hpar : a % 2 = b % 2) (hlt : b < a) : b + 2 ≤ a := by omega
private lemma par_sum_c11 (rp bp R' B cr cb c00 d00 d11 : ℕ)
    (h5 : (rp + bp) % 2 = (c00 + d00) % 2) (hp11 : d11 % 2 = (cr + cb + d00) % 2) :
    (rp + bp + ((R' + B + c00) % 2 + d11)) % 2 = (R' + cr + (B + cb)) % 2 := by omega
private lemma par_sum_c10 (rp bp R' cr c00 d00 d10 : ℕ)
    (h5 : (rp + bp) % 2 = (c00 + d00) % 2) (hp10 : d10 % 2 = (cr + d00) % 2) :
    ((R' + c00) % 2 + d10 + rp) % 2 = (R' + cr + bp) % 2 := by omega
private lemma par_sum_c01 (rp bp B' cb c00 d00 d01 : ℕ)
    (h5 : (rp + bp) % 2 = (c00 + d00) % 2) (hp01 : d01 % 2 = (cb + d00) % 2) :
    ((B' + c00) % 2 + d01 + bp) % 2 = (rp + (B' + cb)) % 2 := by omega

private lemma Sum8.mem_peel_red {R B : ℕ} {p : Bool} {s : Sum8} (hs : s.Good)
    (hR : 1 ≤ R) (hB : 1 ≤ B) (hR1B : R = 1 → B = 1) {r b : ℕ}
    (hmem : ((Sum8.ofSeg R B p).comb s).Mem r b) :
    ((Sum8.ofSeg (R - 1) B p).comb s).Mem r b ∨
    (1 ≤ r ∧ ((Sum8.ofSeg (R - 1) B (!p)).comb s).Mem (r - 1) b) := by
  have hd01 := hs.d00_d01; have hd10 := hs.d11_d10
  have hd0010 := hs.d00_d10; have hd1101 := hs.d11_d01
  have hp11 := hs.par_d11; have hp01 := hs.par_d01; have hp10 := hs.par_d10
  have hof : Sum8.ofSeg R B p =
      ⟨0, 0, R, B, p.toNat, (R + B + p.toNat) % 2, (B + p.toNat) % 2, (R + p.toNat) % 2⟩ := by
    unfold Sum8.ofSeg; rw [if_neg (by omega), if_neg (by omega)]
  rw [hof] at hmem
  rcases hmem with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  simp only [Sum8.comb, Nat.zero_add] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨rp, rfl⟩ : ∃ rp, r = s.fr + rp := ⟨r - s.fr, by omega⟩
  obtain ⟨bp, rfl⟩ : ∃ bp, b = s.fb + bp := ⟨b - s.fb, by omega⟩
  simp only [Nat.add_sub_cancel_left] at h2 h4 h5 h6 h7 h8 h9
  by_cases hR1 : R = 1
  · have hB1 : B = 1 := hR1B hR1
    subst hR1; subst hB1
    have hof0 : Sum8.ofSeg 0 1 p = ⟨0, p.toNat, 0, 0, 0, 0, 0, 0⟩ := by
      unfold Sum8.ofSeg; rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    have hof1 : Sum8.ofSeg 0 1 (!p) = ⟨0, (!p).toNat, 0, 0, 0, 0, 0, 0⟩ := by
      unfold Sum8.ofSeg; rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    rw [hof0, hof1]
    cases p
    · simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true] at *
      have h5' : (rp + bp) % 2 = s.d00 % 2 := by simpa using h5
      have h7' : rp + bp + s.d11 ≤ 1 + s.cr + (1 + s.cb) := by simpa using h7
      have h8' : 1 + s.d01 + bp ≤ rp + (1 + s.cb) := by simpa using h8
      have h9' : 1 + s.d10 + rp ≤ 1 + s.cr + bp := by simpa using h9
      by_cases hc : rp ≤ s.cr ∧ bp ≤ s.cb ∧ rp + bp + s.d11 ≤ s.cr + s.cb
      · left; clear hp11 hp01 hp10 h5; unfold Sum8.Mem; simp only [Sum8.comb, Nat.zero_add, Nat.add_sub_cancel_left]
        exact ⟨Nat.le_add_right _ _, by omega, Nat.le_add_right _ _, by omega, h5', by omega, by omega, by omega, by omega⟩
      · right
        have hgeq : 1 ≤ rp ∧ 1 ≤ bp ∧ s.d00 ≤ (rp - 1) + (bp - 1) := by
          by_cases hA : rp ≤ s.cr
          · by_cases hB' : bp ≤ s.cb
            · have hC : s.cr + s.cb < rp + bp + s.d11 := lt_of_not_ge (fun hle => hc ⟨hA, hB', hle⟩)
              have heq : rp + bp + s.d11 = s.cr + s.cb + 2 :=
                par_eq_add_two rp bp s.cr s.cb s.d00 s.d11 h5' hp11 h7' hC
              clear hp11 hp01 hp10 h5 h5'; omega
            · clear hp11 hp01 hp10 h5 h5'; omega
          · clear hp11 hp01 hp10 h5 h5'; omega
        have hsubR : s.fr + rp - 1 - s.fr = rp - 1 := sub_one_sub_cancel s.fr rp (by first | exact hgeq.1 | exact hok.1)
        have hsubB : s.fb + bp - (1 + s.fb) = bp - 1 := add_sub_succ_cancel s.fb bp (by first | exact hgeq.2.1 | exact hc.1)
        have hpar' : (rp - 1 + (bp - 1)) % 2 = s.d00 % 2 := par_sub_two rp bp s.d00 hgeq.1 hgeq.2.1 h5'
        clear hp11 hp01 hp10 h5 h5'
        refine ⟨by omega, ?_⟩; unfold Sum8.Mem; simp only [Sum8.comb, Nat.zero_add, hsubR, hsubB]
        exact ⟨by omega, by omega, by omega, by omega, hpar', by omega, by omega, by omega, by omega⟩
    · simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true] at *
      have h5' : (rp + bp) % 2 = (1 + s.d00) % 2 := by simpa using h5
      have h6' : 1 + s.d00 ≤ rp + bp := by simpa using h6
      have h7' : rp + bp + (1 + s.d11) ≤ 1 + s.cr + (1 + s.cb) := by simpa using h7
      have h8' : s.d01 + bp ≤ rp + (1 + s.cb) := by simpa using h8
      have h9' : s.d10 + rp ≤ 1 + s.cr + bp := by simpa using h9
      by_cases hc : 1 ≤ bp ∧ rp ≤ s.cr ∧ s.d10 + rp ≤ s.cr + (bp - 1)
      · left
        have hsubB : s.fb + bp - (1 + s.fb) = bp - 1 := add_sub_succ_cancel s.fb bp (by first | exact hgeq.2.1 | exact hc.1)
        have hpar' : (rp + (bp - 1)) % 2 = s.d00 % 2 := par_add_sub_one rp bp s.d00 (by first | exact hc.1 | exact hok.1) h5'
        clear hp11 hp01 hp10 h5 h5'; unfold Sum8.Mem; simp only [Sum8.comb, Nat.zero_add, Nat.add_sub_cancel_left, hsubB]
        exact ⟨Nat.le_add_right _ _, by omega, by omega, by omega, hpar', by omega, by omega, by omega, by omega⟩
      · right
        have hok : 1 ≤ rp ∧ bp ≤ s.cb ∧ s.d01 + bp ≤ (rp - 1) + s.cb := by
          by_cases hA : 1 ≤ bp
          · by_cases hB' : rp ≤ s.cr
            · have hC : s.cr + (bp - 1) < s.d10 + rp := lt_of_not_ge (fun hle => hc ⟨hA, hB', hle⟩)
              have heq : s.d10 + rp = s.cr + 1 + bp :=
                par_eq_d10_top rp bp s.cr s.d00 s.d10 hA h5' hp10 h9' hC
              clear hp11 hp01 hp10 h5 h5'; omega
            · clear hp11 hp01 hp10 h5 h5'; omega
          · clear hp11 hp01 hp10 h5 h5'; omega
        have hsubR : s.fr + rp - 1 - s.fr = rp - 1 := sub_one_sub_cancel s.fr rp (by first | exact hgeq.1 | exact hok.1)
        have hpar' : (rp - 1 + bp) % 2 = s.d00 % 2 := par_sub_one rp bp s.d00 (by first | exact hc.1 | exact hok.1) h5'
        clear hp11 hp01 hp10 h5 h5'
        refine ⟨by omega, ?_⟩; unfold Sum8.Mem; simp only [Sum8.comb, Nat.zero_add, Nat.add_sub_cancel_left, hsubR]
        exact ⟨by omega, by omega, Nat.le_add_right _ _, by omega, hpar', by omega, by omega, by omega, by omega⟩
  · have hR2 : 2 ≤ R := by omega
    obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
    have hR'1 : 1 ≤ R' := by omega
    have hsubR' : R' + 1 - 1 = R' := Nat.add_sub_cancel R' 1
    rw [hsubR']
    have hof0 : Sum8.ofSeg R' B p =
        ⟨0, 0, R', B, p.toNat, (R' + B + p.toNat) % 2,
         (B + p.toNat) % 2, (R' + p.toNat) % 2⟩ := by
      unfold Sum8.ofSeg; rw [if_neg (by omega), if_neg (by omega)]
    have hof1 : Sum8.ofSeg R' B (!p) =
        ⟨0, 0, R', B, (!p).toNat, (R' + B + (!p).toNat) % 2,
         (B + (!p).toNat) % 2, (R' + (!p).toNat) % 2⟩ := by
      unfold Sum8.ofSeg; rw [if_neg (by omega), if_neg (by omega)]
    rw [hof0, hof1]
    rw [mod2_add1_mid3 R' B p.toNat] at h7
    rw [mod2_add1_mid2 R' p.toNat] at h9
    rw [mod2_add_not (R' + B) p, mod2_add_not B p, mod2_add_not R' p, bool_not_toNat p]
    have hc00 : p.toNat ≤ 1 := bool_toNat_le_one p
    have hc11 : (R' + B + p.toNat) % 2 ≤ 1 := mod2_le_one _
    have hc01 : (B + p.toNat) % 2 ≤ 1 := mod2_le_one _
    have hc10 : (R' + p.toNat) % 2 ≤ 1 := mod2_le_one _
    have hparB : (rp + bp + ((R' + B + p.toNat) % 2 + s.d11)) % 2 = (R' + s.cr + (B + s.cb)) % 2 :=
      par_sum_c11 rp bp R' B s.cr s.cb p.toNat s.d00 s.d11 h5 hp11
    have hparC : ((R' + p.toNat) % 2 + s.d10 + rp) % 2 = (R' + s.cr + bp) % 2 :=
      par_sum_c10 rp bp R' s.cr p.toNat s.d00 s.d10 h5 hp10
    generalize p.toNat = c00 at hc00 hc11 hc01 hc10 h5 h6 h7 h8 h9 hparB hparC ⊢
    generalize (R' + B + c00) % 2 = c11 at hc11 h7 hparB ⊢
    generalize (B + c00) % 2 = c01 at hc01 h8 ⊢
    generalize (R' + c00) % 2 = c10 at hc10 h9 hparC ⊢
    by_cases hc : rp ≤ R' + s.cr ∧ rp + bp + (c11 + s.d11) ≤ R' + s.cr + (B + s.cb) ∧
        c10 + s.d10 + rp ≤ R' + s.cr + bp
    · left; clear hp11 hp01 hp10 hparB hparC; unfold Sum8.Mem; simp only [Sum8.comb, Nat.zero_add, Nat.add_sub_cancel_left]
      exact ⟨Nat.le_add_right _ _, by omega, Nat.le_add_right _ _, by omega, h5, h6, by omega, h8, by omega⟩
    · right
      have hok : 1 ≤ rp ∧ 1 - c00 + s.d00 ≤ rp - 1 + bp ∧ 1 - c01 + s.d01 + bp ≤ rp - 1 + (B + s.cb) := by
        by_cases hA : rp ≤ R' + s.cr
        · by_cases hB' : rp + bp + (c11 + s.d11) ≤ R' + s.cr + (B + s.cb)
          · have hC : R' + s.cr + bp < c10 + s.d10 + rp := lt_of_not_ge (fun hle => hc ⟨hA, hB', hle⟩)
            have hC2 : R' + s.cr + bp + 2 ≤ c10 + s.d10 + rp := par_same_ge2 _ _ hparC hC
            clear h5 hp11 hp01 hp10 hparB hparC; omega
          · have hB2 : R' + s.cr + (B + s.cb) + 2 ≤ rp + bp + (c11 + s.d11) :=
              par_same_ge2 _ _ hparB (lt_of_not_ge hB')
            clear h5 hp11 hp01 hp10 hparB hparC; omega
        · clear h5 hp11 hp01 hp10 hparB hparC; omega
      have hsubR : s.fr + rp - 1 - s.fr = rp - 1 := sub_one_sub_cancel s.fr rp hok.1
      have hpar' : (rp - 1 + bp) % 2 = (1 - c00 + s.d00) % 2 := par_flip_sub rp bp c00 s.d00 hok.1 hc00 h5
      clear h5 hp11 hp01 hp10 hparB hparC
      refine ⟨by omega, ?_⟩
      unfold Sum8.Mem
      simp only [Sum8.comb, Nat.zero_add, Nat.add_sub_cancel_left, hsubR]
      exact ⟨by omega, by omega, Nat.le_add_right _ _, by omega, hpar', hok.2.1, by omega, hok.2.2, by omega⟩

private lemma Sum8.mem_peel_blue {R B : ℕ} {p : Bool} {s : Sum8} (hs : s.Good)
    (hR : 1 ≤ R) (hB : 1 ≤ B) (hB1R : B = 1 → R = 1) {r b : ℕ}
    (hmem : ((Sum8.ofSeg R B p).comb s).Mem r b) :
    ((Sum8.ofSeg R (B - 1) p).comb s).Mem r b ∨
    (1 ≤ b ∧ ((Sum8.ofSeg R (B - 1) (!p)).comb s).Mem r (b - 1)) := by
  have hd01 := hs.d00_d01; have hd10 := hs.d11_d10
  have hd0010 := hs.d00_d10; have hd1101 := hs.d11_d01
  have hp11 := hs.par_d11; have hp01 := hs.par_d01; have hp10 := hs.par_d10
  have hof : Sum8.ofSeg R B p =
      ⟨0, 0, R, B, p.toNat, (R + B + p.toNat) % 2, (B + p.toNat) % 2, (R + p.toNat) % 2⟩ := by
    unfold Sum8.ofSeg; rw [if_neg (by omega), if_neg (by omega)]
  rw [hof] at hmem
  rcases hmem with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  simp only [Sum8.comb, Nat.zero_add] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨rp, rfl⟩ : ∃ rp, r = s.fr + rp := ⟨r - s.fr, by omega⟩
  obtain ⟨bp, rfl⟩ : ∃ bp, b = s.fb + bp := ⟨b - s.fb, by omega⟩
  simp only [Nat.add_sub_cancel_left] at h2 h4 h5 h6 h7 h8 h9
  by_cases hB1 : B = 1
  · have hR1 : R = 1 := hB1R hB1
    subst hR1; subst hB1
    have hof0 : Sum8.ofSeg 1 0 p = ⟨p.toNat, 0, 0, 0, 0, 0, 0, 0⟩ := by
      unfold Sum8.ofSeg; rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    have hof1 : Sum8.ofSeg 1 0 (!p) = ⟨(!p).toNat, 0, 0, 0, 0, 0, 0, 0⟩ := by
      unfold Sum8.ofSeg; rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
    rw [hof0, hof1]
    cases p
    · simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true] at *
      have h5' : (rp + bp) % 2 = s.d00 % 2 := by simpa using h5
      have h7' : rp + bp + s.d11 ≤ 1 + s.cr + (1 + s.cb) := by simpa using h7
      have h8' : 1 + s.d01 + bp ≤ rp + (1 + s.cb) := by simpa using h8
      have h9' : 1 + s.d10 + rp ≤ 1 + s.cr + bp := by simpa using h9
      by_cases hc : rp ≤ s.cr ∧ bp ≤ s.cb ∧ rp + bp + s.d11 ≤ s.cr + s.cb
      · left; clear hp11 hp01 hp10 h5; unfold Sum8.Mem; simp only [Sum8.comb, Nat.zero_add, Nat.add_sub_cancel_left]
        exact ⟨Nat.le_add_right _ _, by omega, Nat.le_add_right _ _, by omega, h5', by omega, by omega, by omega, by omega⟩
      · right
        have hgeq : 1 ≤ rp ∧ 1 ≤ bp ∧ s.d00 ≤ (rp - 1) + (bp - 1) := by
          by_cases hA : rp ≤ s.cr
          · by_cases hB' : bp ≤ s.cb
            · have hC : s.cr + s.cb < rp + bp + s.d11 := lt_of_not_ge (fun hle => hc ⟨hA, hB', hle⟩)
              have heq : rp + bp + s.d11 = s.cr + s.cb + 2 :=
                par_eq_add_two rp bp s.cr s.cb s.d00 s.d11 h5' hp11 h7' hC
              clear hp11 hp01 hp10 h5 h5'; omega
            · clear hp11 hp01 hp10 h5 h5'; omega
          · clear hp11 hp01 hp10 h5 h5'; omega
        have hsubR : s.fr + rp - (1 + s.fr) = rp - 1 := add_sub_succ_cancel s.fr rp (by first | exact hgeq.1 | exact hc.1)
        have hsubB : s.fb + bp - 1 - s.fb = bp - 1 := sub_one_sub_cancel s.fb bp (by first | exact hgeq.2.1 | exact hok.1)
        have hpar' : (rp - 1 + (bp - 1)) % 2 = s.d00 % 2 := par_sub_two rp bp s.d00 hgeq.1 hgeq.2.1 h5'
        clear hp11 hp01 hp10 h5 h5'
        refine ⟨by omega, ?_⟩; unfold Sum8.Mem; simp only [Sum8.comb, Nat.zero_add, hsubR, hsubB]
        exact ⟨by omega, by omega, by omega, by omega, hpar', by omega, by omega, by omega, by omega⟩
    · simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false, Bool.not_true] at *
      have h5' : (rp + bp) % 2 = (1 + s.d00) % 2 := by simpa using h5
      have h6' : 1 + s.d00 ≤ rp + bp := by simpa using h6
      have h7' : rp + bp + (1 + s.d11) ≤ 1 + s.cr + (1 + s.cb) := by simpa using h7
      have h8' : s.d01 + bp ≤ rp + (1 + s.cb) := by simpa using h8
      have h9' : s.d10 + rp ≤ 1 + s.cr + bp := by simpa using h9
      by_cases hc : 1 ≤ rp ∧ bp ≤ s.cb ∧ s.d01 + bp ≤ (rp - 1) + s.cb
      · left
        have hsubR : s.fr + rp - (1 + s.fr) = rp - 1 := add_sub_succ_cancel s.fr rp (by first | exact hgeq.1 | exact hc.1)
        have hpar' : (rp - 1 + bp) % 2 = s.d00 % 2 := par_sub_one rp bp s.d00 (by first | exact hc.1 | exact hok.1) h5'
        clear hp11 hp01 hp10 h5 h5'; unfold Sum8.Mem; simp only [Sum8.comb, Nat.zero_add, Nat.add_sub_cancel_left, hsubR]
        exact ⟨by omega, by omega, Nat.le_add_right _ _, by omega, hpar', by omega, by omega, by omega, by omega⟩
      · right
        have hok : 1 ≤ bp ∧ rp ≤ s.cr ∧ s.d10 + rp ≤ s.cr + (bp - 1) := by
          by_cases hA : 1 ≤ rp
          · by_cases hB' : bp ≤ s.cb
            · have hC : (rp - 1) + s.cb < s.d01 + bp := lt_of_not_ge (fun hle => hc ⟨hA, hB', hle⟩)
              have heq : s.d01 + bp = rp + 1 + s.cb :=
                par_eq_d01_top rp bp s.cb s.d00 s.d01 hA h5' hp01 h8' hC
              clear hp11 hp01 hp10 h5 h5'; omega
            · clear hp11 hp01 hp10 h5 h5'; omega
          · clear hp11 hp01 hp10 h5 h5'; omega
        have hsubB : s.fb + bp - 1 - s.fb = bp - 1 := sub_one_sub_cancel s.fb bp (by first | exact hgeq.2.1 | exact hok.1)
        have hpar' : (rp + (bp - 1)) % 2 = s.d00 % 2 := par_add_sub_one rp bp s.d00 (by first | exact hc.1 | exact hok.1) h5'
        clear hp11 hp01 hp10 h5 h5'
        refine ⟨by omega, ?_⟩; unfold Sum8.Mem; simp only [Sum8.comb, Nat.zero_add, Nat.add_sub_cancel_left, hsubB]
        exact ⟨Nat.le_add_right _ _, by omega, by omega, by omega, hpar', by omega, by omega, by omega, by omega⟩
  · have hB2 : 2 ≤ B := by omega
    obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    have hB'1 : 1 ≤ B' := by omega
    have hsubB' : B' + 1 - 1 = B' := Nat.add_sub_cancel B' 1
    rw [hsubB']
    have hof0 : Sum8.ofSeg R B' p =
        ⟨0, 0, R, B', p.toNat, (R + B' + p.toNat) % 2,
         (B' + p.toNat) % 2, (R + p.toNat) % 2⟩ := by
      unfold Sum8.ofSeg; rw [if_neg (by omega), if_neg (by omega)]
    have hof1 : Sum8.ofSeg R B' (!p) =
        ⟨0, 0, R, B', (!p).toNat, (R + B' + (!p).toNat) % 2,
         (B' + (!p).toNat) % 2, (R + (!p).toNat) % 2⟩ := by
      unfold Sum8.ofSeg; rw [if_neg (by omega), if_neg (by omega)]
    rw [hof0, hof1]
    rw [mod2_add1_r3 R B' p.toNat] at h7
    rw [mod2_add1_mid2 B' p.toNat] at h8
    rw [mod2_add_not (R + B') p, mod2_add_not B' p, mod2_add_not R p, bool_not_toNat p]
    have hc00 : p.toNat ≤ 1 := bool_toNat_le_one p
    have hc11 : (R + B' + p.toNat) % 2 ≤ 1 := mod2_le_one _
    have hc01 : (B' + p.toNat) % 2 ≤ 1 := mod2_le_one _
    have hc10 : (R + p.toNat) % 2 ≤ 1 := mod2_le_one _
    have hparB : (rp + bp + ((R + B' + p.toNat) % 2 + s.d11)) % 2 = (R + s.cr + (B' + s.cb)) % 2 :=
      par_sum_c11 rp bp R B' s.cr s.cb p.toNat s.d00 s.d11 h5 hp11
    have hparC : ((B' + p.toNat) % 2 + s.d01 + bp) % 2 = (rp + (B' + s.cb)) % 2 :=
      par_sum_c01 rp bp B' s.cb p.toNat s.d00 s.d01 h5 hp01
    generalize p.toNat = c00 at hc00 hc11 hc01 hc10 h5 h6 h7 h8 h9 hparB hparC ⊢
    generalize (R + B' + c00) % 2 = c11 at hc11 h7 hparB ⊢
    generalize (B' + c00) % 2 = c01 at hc01 h8 hparC ⊢
    generalize (R + c00) % 2 = c10 at hc10 h9 ⊢
    by_cases hc : bp ≤ B' + s.cb ∧ rp + bp + (c11 + s.d11) ≤ R + s.cr + (B' + s.cb) ∧
        c01 + s.d01 + bp ≤ rp + (B' + s.cb)
    · left; clear hp11 hp01 hp10 hparB hparC; unfold Sum8.Mem; simp only [Sum8.comb, Nat.zero_add, Nat.add_sub_cancel_left]
      exact ⟨Nat.le_add_right _ _, by omega, Nat.le_add_right _ _, by omega, h5, h6, by omega, by omega, h9⟩
    · right
      have hok : 1 ≤ bp ∧ 1 - c00 + s.d00 ≤ rp + (bp - 1) ∧ 1 - c10 + s.d10 + rp ≤ R + s.cr + (bp - 1) := by
        by_cases hA : bp ≤ B' + s.cb
        · by_cases hB' : rp + bp + (c11 + s.d11) ≤ R + s.cr + (B' + s.cb)
          · have hC : rp + (B' + s.cb) < c01 + s.d01 + bp := lt_of_not_ge (fun hle => hc ⟨hA, hB', hle⟩)
            have hC2 : rp + (B' + s.cb) + 2 ≤ c01 + s.d01 + bp := par_same_ge2 _ _ hparC hC
            clear h5 hp11 hp01 hp10 hparB hparC; omega
          · have hB2 : R + s.cr + (B' + s.cb) + 2 ≤ rp + bp + (c11 + s.d11) :=
              par_same_ge2 _ _ hparB (lt_of_not_ge hB')
            clear h5 hp11 hp01 hp10 hparB hparC; omega
        · clear h5 hp11 hp01 hp10 hparB hparC; omega
      have hsubB : s.fb + bp - 1 - s.fb = bp - 1 := sub_one_sub_cancel s.fb bp hok.1
      have hpar' : (rp + (bp - 1)) % 2 = (1 - c00 + s.d00) % 2 := par_flip_sub_b rp bp c00 s.d00 hok.1 hc00 h5
      clear h5 hp11 hp01 hp10 hparB hparC
      refine ⟨by omega, ?_⟩
      unfold Sum8.Mem
      simp only [Sum8.comb, Nat.zero_add, Nat.add_sub_cancel_left, hsubB]
      exact ⟨Nat.le_add_right _ _, by omega, by omega, by omega, hpar', hok.2.1, by omega, by omega, hok.2.2⟩

private lemma Sum8.mem_peel_chain {s : Sum8} (hs : s.Good) :
    ∀ (R1 B1 R2 B2 : ℕ) (p : Bool) (r b : ℕ),
      (R1 = 0 ∨ 1 ≤ B1 + B2) → 1 ≤ R2 → B2 ≤ R2 → R2 ≤ B2 + 1 →
      ((Sum8.ofSeg (R1 + R2) (B1 + B2) p).comb s).Mem r b →
      ∃ r1 b1, r1 ≤ R1 ∧ b1 ≤ B1 ∧ r1 ≤ r ∧ b1 ≤ b ∧
        ((Sum8.ofSeg R2 B2 (xor p (decide ((r1 + b1) % 2 = 1)))).comb s).Mem (r - r1) (b - b1) := by
  intro R1
  induction R1 with
  | zero =>
    intro B1
    induction B1 with
    | zero =>
      intro R2 B2 p r b _ _ _ _ hmem
      refine ⟨0, 0, le_rfl, le_rfl, Nat.zero_le _, Nat.zero_le _, ?_⟩
      simpa using hmem
    | succ B1 ihB =>
      intro R2 B2 p r b _ hR2 hB2R hRB2 hmem
      have hB1R : B1 + 1 + B2 = 1 → R2 = 1 := by omega
      have hpeel := Sum8.mem_peel_blue hs (R := R2) (B := B1 + 1 + B2) (p := p)
        (by omega) (by omega) hB1R (by simpa [Nat.zero_add] using hmem)
      have hsub : B1 + 1 + B2 - 1 = B1 + B2 := by omega
      rw [hsub] at hpeel
      rcases hpeel with h0 | ⟨hb1, h1⟩
      · rcases ihB R2 B2 p r b (Or.inl rfl) hR2 hB2R hRB2 (by simpa [Nat.zero_add] using h0) with
          ⟨r1, b1, hr1, hb1', hrr, hbb, hrest⟩
        exact ⟨r1, b1, hr1, by omega, hrr, hbb, hrest⟩
      · rcases ihB R2 B2 (!p) r (b - 1) (Or.inl rfl) hR2 hB2R hRB2 (by simpa [Nat.zero_add] using h1) with
          ⟨r1, b1, hr1, hb1', hrr, hbb, hrest⟩
        refine ⟨r1, b1 + 1, hr1, by omega, hrr, by omega, ?_⟩
        have hpar : xor p (decide ((r1 + (b1 + 1)) % 2 = 1)) =
            xor (!p) (decide ((r1 + b1) % 2 = 1)) := by
          cases p <;> by_cases h : (r1 + b1) % 2 = 1 <;>
            simp [h, show ((r1 + (b1 + 1)) % 2 = 1) ↔ ¬((r1 + b1) % 2 = 1) by omega]
        rw [hpar, show b - (b1 + 1) = b - 1 - b1 by omega]
        exact hrest
  | succ R1 ihR =>
    intro B1 R2 B2 p r b hB12 hR2 hB2R hRB2 hmem
    have hBpos : 1 ≤ B1 + B2 := hB12.resolve_left (Nat.succ_ne_zero R1)
    have hpeel := Sum8.mem_peel_red hs (R := R1 + 1 + R2) (B := B1 + B2) (p := p)
      (by omega) hBpos (by omega) hmem
    have hsub : R1 + 1 + R2 - 1 = R1 + R2 := by omega
    rw [hsub] at hpeel
    rcases hpeel with h0 | ⟨hr1, h1⟩
    · rcases ihR B1 R2 B2 p r b (Or.inr hBpos) hR2 hB2R hRB2 h0 with
        ⟨r1, b1, hr1', hb1, hrr, hbb, hrest⟩
      exact ⟨r1, b1, by omega, hb1, hrr, hbb, hrest⟩
    · rcases ihR B1 R2 B2 (!p) (r - 1) b (Or.inr hBpos) hR2 hB2R hRB2 h1 with
        ⟨r1, b1, hr1', hb1, hrr, hbb, hrest⟩
      refine ⟨r1 + 1, b1, by omega, hb1, by omega, hbb, ?_⟩
      have hpar : xor p (decide ((r1 + 1 + b1) % 2 = 1)) =
          xor (!p) (decide ((r1 + b1) % 2 = 1)) := by
        cases p <;> by_cases h : (r1 + b1) % 2 = 1 <;>
          simp [h, show ((r1 + 1 + b1) % 2 = 1) ↔ ¬((r1 + b1) % 2 = 1) by omega]
      rw [hpar, show r - (r1 + 1) = r - 1 - r1 by omega]
      exact hrest

private lemma Sum8.mem_split_seg {R1 B1 R2 B2 : ℕ} {b1 b2 : Bool} {s : Sum8} (hs : s.Good)
    (h1B : 1 ≤ B1) (h1alt : R1 ≤ B1 ∧ B1 ≤ R1 + 1)
    (h2R : 1 ≤ R2) (h2alt : B2 ≤ R2 ∧ R2 ≤ B2 + 1)
    {r b : ℕ} (hmem : ((Sum8.ofSeg (R1 + R2) (B1 + B2) (xor b1 b2)).comb s).Mem r b) :
    (((Sum8.ofSeg R1 B1 (xor b1 false)).comb (Sum8.ofSeg R2 B2 (xor false b2))).comb s).Mem r b ∨
    (((Sum8.ofSeg R1 B1 (xor b1 true)).comb (Sum8.ofSeg R2 B2 (xor true b2))).comb s).Mem r b := by
  rcases Sum8.mem_peel_chain hs R1 B1 R2 B2 (xor b1 b2) r b (Or.inr (by omega)) h2R h2alt.1 h2alt.2 hmem with
    ⟨r1, b1', hr1, hb1', hrr, hbb, hrest⟩
  let a : Bool := xor b1 (decide ((r1 + b1') % 2 = 1))
  have hmem1 : (Sum8.ofSeg R1 B1 (xor b1 a)).Mem r1 b1' := by
    refine Sum8.mem_ofSeg_of_bounds (by omega) hr1 hb1' ?_ (by omega)
    dsimp only [a]
    cases b1 <;> by_cases h : (r1 + b1') % 2 = 1 <;> simp [h] <;> omega
  have hpar2 : xor (xor b1 b2) (decide ((r1 + b1') % 2 = 1)) = xor a b2 := by
    dsimp only [a]; cases b1 <;> cases b2 <;> cases decide ((r1 + b1') % 2 = 1) <;> rfl
  rw [hpar2] at hrest
  have hcomb := Sum8.mem_comb_of_mem hmem1 hrest
  rw [← Sum8.comb_assoc, show r1 + (r - r1) = r by omega, show b1' + (b - b1') = b by omega] at hcomb
  cases ha : a
  · left; rw [ha] at hcomb; exact hcomb
  · right; rw [ha] at hcomb; exact hcomb

private def Sum8.queryParity (s : Sum8) (r0 r1 b0 b1 : ℕ) (t : Bool) : Bool × ℕ × ℕ :=
  let pB : Bool := xor t (decide (s.d00 % 2 = 1))
  let b0p : ℕ := b0 + if decide (b0 % 2 = 1) == pB then 0 else 1
  let b1_under : Bool := decide (b1 = 0) && pB
  let b1p : ℕ := b1 - if decide (b1 % 2 = 1) == pB then 0 else 1
  let ok_b : Bool := (!b1_under) && decide (b0p ≤ b1p)
  let rp_lo : ℕ := max r0 (max (b0p + s.d01 - s.cb) (s.d00 - b1p))
  let rp_hi : ℕ := min r1 (min (s.cr + s.cb - (s.d11 + b0p)) (b1p + s.cr - s.d10))
  let rp_lo_t : ℕ := rp_lo + if decide (rp_lo % 2 = 1) == t then 0 else 1
  let rp_hi_under : Bool := decide (rp_hi = 0) && t
  let rp_hi_t : ℕ := rp_hi - if decide (rp_hi % 2 = 1) == t then 0 else 1
  let ok : Bool := ok_b && (!rp_hi_under) && decide (rp_lo_t ≤ rp_hi_t)
  let rp : ℕ := rp_lo_t
  let bp : ℕ := max b0p (max (s.d00 - rp) (s.d10 + rp - s.cr))
  (ok, s.fr + rp, s.fb + bp)

private def Sum8.query (s : Sum8) (loR hiR loB hiB : ℕ) : Bool × ℕ × ℕ :=
  let R0 := max s.fr loR
  let R1 := min (s.fr + s.cr) hiR
  let B0 := max s.fb loB
  let B1 := min (s.fb + s.cb) hiB
  let box_ok := decide (loR ≤ hiR) && decide (loB ≤ hiB) && decide (R0 ≤ R1) && decide (B0 ≤ B1)
  let r0 := R0 - s.fr
  let r1 := R1 - s.fr
  let b0 := B0 - s.fb
  let b1 := B1 - s.fb
  let q0 := s.queryParity r0 r1 b0 b1 false
  let q1 := s.queryParity r0 r1 b0 b1 true
  let f0 := box_ok && q0.1
  let f1 := box_ok && q1.1
  let flag := f0 || f1
  let pick0 := f0 && ((!f1) || decide (q0.2.1 < q1.2.1) ||
    (decide (q0.2.1 = q1.2.1) && decide (q0.2.2 ≤ q1.2.2)))
  (flag, if pick0 then q0.2.1 else q1.2.1, if pick0 then q0.2.2 else q1.2.2)

private lemma roundUpPar_par (x : ℕ) (t : Bool) :
    (x + if decide (x % 2 = 1) == t then 0 else 1) % 2 = t.toNat := by
  cases t <;> by_cases h : x % 2 = 1 <;> simp [h] <;> omega

private lemma roundUpPar_le_of_par {x y : ℕ} {t : Bool} (hle : x ≤ y) (hy : y % 2 = t.toNat) :
    x + (if decide (x % 2 = 1) == t then 0 else 1) ≤ y := by
  cases t <;> by_cases h : x % 2 = 1 <;> simp [h] at hy ⊢ <;> omega

private lemma le_roundDnPar_of_par {x y : ℕ} {t : Bool} (hle : y ≤ x) (hy : y % 2 = t.toNat) :
    y ≤ x - (if decide (x % 2 = 1) == t then 0 else 1) := by
  cases t <;> by_cases h : x % 2 = 1 <;> simp [h] at hy ⊢ <;> omega

private lemma not_under_of_par {x y : ℕ} {t : Bool} (hle : y ≤ x) (hy : y % 2 = t.toNat) :
    (decide (x = 0) && t) = false := by
  cases t <;> simp at hy ⊢ <;> omega

private lemma par_add_from_pB (rp bp d00 : ℕ) (t : Bool)
    (hrp : rp % 2 = t.toNat) (hbp : bp % 2 = (xor t (decide (d00 % 2 = 1))).toNat) :
    (rp + bp) % 2 = d00 % 2 := by
  cases t <;> by_cases hd : d00 % 2 = 1 <;> simp [hd] at hrp hbp ⊢ <;> omega

private lemma max3_choice (a b c : ℕ) :
    max a (max b c) = a ∨ max a (max b c) = b ∨ max a (max b c) = c := by
  rcases max_choice a (max b c) with h | h
  · exact Or.inl h
  · rcases max_choice b c with h' | h'
    · exact Or.inr (Or.inl (h.trans h'))
    · exact Or.inr (Or.inr (h.trans h'))

private lemma Sum8.queryParity_sound {s : Sum8} (hs : s.Good)
    {r0 r1 b0 b1 : ℕ} (hr1 : r1 ≤ s.cr) (hb1 : b1 ≤ s.cb) (t : Bool)
    (hok : (s.queryParity r0 r1 b0 b1 t).1 = true) :
    let res := s.queryParity r0 r1 b0 b1 t
    s.Mem res.2.1 res.2.2 ∧
    s.fr + r0 ≤ res.2.1 ∧ res.2.1 ≤ s.fr + r1 ∧
    s.fb + b0 ≤ res.2.2 ∧ res.2.2 ≤ s.fb + b1 ∧
    (res.2.1 - s.fr) % 2 = t.toNat := by
  have hd01 := hs.d00_d01; have hd10 := hs.d11_d10
  have hd0010 := hs.d00_d10; have hd1101 := hs.d11_d01
  have hp11 := hs.par_d11; have hp01 := hs.par_d01; have hp10 := hs.par_d10
  dsimp only [Sum8.queryParity] at hok ⊢
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨hb1u, hb01⟩, hrpu⟩, hrp01⟩
  generalize hb0p_def : b0 + (if decide (b0 % 2 = 1) == xor t (decide (s.d00 % 2 = 1)) then 0 else 1) = b0p at hb01 hrpu hrp01 ⊢
  have hb0p_par : b0p % 2 = (xor t (decide (s.d00 % 2 = 1))).toNat := hb0p_def ▸ roundUpPar_par b0 _
  have hb0_le : b0 ≤ b0p := hb0p_def ▸ Nat.le_add_right _ _
  clear hb0p_def
  generalize hb1p_def : b1 - (if decide (b1 % 2 = 1) == xor t (decide (s.d00 % 2 = 1)) then 0 else 1) = b1p at hb01 hrpu hrp01 ⊢
  have hb1p_le : b1p ≤ b1 := hb1p_def ▸ Nat.sub_le _ _
  clear hb1p_def
  generalize hrp_lo_def : max r0 (max (b0p + s.d01 - s.cb) (s.d00 - b1p)) = rp_lo at hrp01 ⊢
  have hlo_r0 : r0 ≤ rp_lo := hrp_lo_def ▸ le_max_left _ _
  have hlo_d01 : b0p + s.d01 - s.cb ≤ rp_lo := hrp_lo_def ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have hlo_d00 : s.d00 - b1p ≤ rp_lo := hrp_lo_def ▸ le_trans (le_max_right _ _) (le_max_right _ _)
  clear hrp_lo_def
  generalize hrp_hi_def : min r1 (min (s.cr + s.cb - (s.d11 + b0p)) (b1p + s.cr - s.d10)) = rp_hi at hrpu hrp01
  have hhi_r1 : rp_hi ≤ r1 := hrp_hi_def ▸ min_le_left _ _
  have hhi_d11 : rp_hi ≤ s.cr + s.cb - (s.d11 + b0p) := hrp_hi_def ▸ le_trans (min_le_right _ _) (min_le_left _ _)
  have hhi_d10 : rp_hi ≤ b1p + s.cr - s.d10 := hrp_hi_def ▸ le_trans (min_le_right _ _) (min_le_right _ _)
  clear hrp_hi_def
  generalize hrp_def : rp_lo + (if decide (rp_lo % 2 = 1) == t then 0 else 1) = rp at hrp01 ⊢
  have hrp_par : rp % 2 = t.toNat := hrp_def ▸ roundUpPar_par rp_lo t
  have hrp_lo_le : rp_lo ≤ rp := hrp_def ▸ Nat.le_add_right _ _
  clear hrp_def
  have hrp_le_hi : rp ≤ rp_hi := le_trans hrp01 (Nat.sub_le _ _)
  have hrp_r0 : r0 ≤ rp := le_trans hlo_r0 hrp_lo_le
  have hrp_d01 : b0p + s.d01 - s.cb ≤ rp := le_trans hlo_d01 hrp_lo_le
  have hrp_d00 : s.d00 - b1p ≤ rp := le_trans hlo_d00 hrp_lo_le
  have hrp_r1 : rp ≤ r1 := le_trans hrp_le_hi hhi_r1
  have hrp_d11 : rp ≤ s.cr + s.cb - (s.d11 + b0p) := le_trans hrp_le_hi hhi_d11
  have hrp_d10 : rp ≤ b1p + s.cr - s.d10 := le_trans hrp_le_hi hhi_d10
  clear hrpu hrp01 hb1u rp_lo hlo_r0 hlo_d01 hlo_d00 hrp_lo_le rp_hi hhi_r1 hhi_d11 hhi_d10 hrp_le_hi
  generalize hbp_def : max b0p (max (s.d00 - rp) (s.d10 + rp - s.cr)) = bp at ⊢
  have hbp_ge_b0p : b0p ≤ bp := hbp_def ▸ le_max_left _ _
  have hbp_ge_d00 : s.d00 - rp ≤ bp := hbp_def ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have hbp_ge_d10 : s.d10 + rp - s.cr ≤ bp := hbp_def ▸ le_trans (le_max_right _ _) (le_max_right _ _)
  have hbp_cases : bp = b0p ∨ bp = s.d00 - rp ∨ bp = s.d10 + rp - s.cr := hbp_def ▸ max3_choice _ _ _
  clear hbp_def
  have hbp_par : bp % 2 = (xor t (decide (s.d00 % 2 = 1))).toNat := by
    rcases hbp_cases with rfl | h | h
    · exact hb0p_par
    · by_cases hle : rp ≤ s.d00
      · rw [h]; exact par_sub_d00 s.d00 rp t hle hrp_par
      · have : bp = b0p := le_antisymm (by rw [h]; clear hp11 hp01 hp10 hb0p_par hrp_par; omega) hbp_ge_b0p
        rw [this]; exact hb0p_par
    · by_cases hle : s.cr ≤ s.d10 + rp
      · rw [h]; exact par_d10_rp s.d10 s.d00 s.cr rp t hle hp10 hrp_par
      · have : bp = b0p := le_antisymm (by rw [h]; clear hp11 hp01 hp10 hb0p_par hrp_par; omega) hbp_ge_b0p
        rw [this]; exact hb0p_par
  have hmem_par : (rp + bp) % 2 = s.d00 % 2 := par_add_from_pB rp bp s.d00 t hrp_par hbp_par
  clear hp11 hp01 hp10 hb0p_par hbp_par
  have hbp_le_b1p : bp ≤ b1p := by rcases hbp_cases with rfl | h | h <;> clear hmem_par hrp_par <;> omega
  have hbp_d11 : rp + bp + s.d11 ≤ s.cr + s.cb := by rcases hbp_cases with rfl | h | h <;> clear hmem_par hrp_par <;> omega
  have hbp_d01 : s.d01 + bp ≤ rp + s.cb := by rcases hbp_cases with rfl | h | h <;> clear hmem_par hrp_par <;> omega
  clear hbp_cases
  refine ⟨⟨Nat.le_add_right _ _, ?_, Nat.le_add_right _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · clear hmem_par hrp_par; omega
  · clear hmem_par hrp_par; omega
  · simp only [Nat.add_sub_cancel_left]; exact hmem_par
  · simp only [Nat.add_sub_cancel_left]; clear hmem_par hrp_par; omega
  · simp only [Nat.add_sub_cancel_left]; exact hbp_d11
  · simp only [Nat.add_sub_cancel_left]; exact hbp_d01
  · simp only [Nat.add_sub_cancel_left]; clear hmem_par hrp_par; omega
  · clear hmem_par hrp_par; omega
  · clear hmem_par hrp_par; omega
  · clear hmem_par hrp_par; omega
  · clear hmem_par hrp_par; omega
  · simp only [Nat.add_sub_cancel_left]; exact hrp_par

private lemma Sum8.queryParity_complete {s : Sum8} (hs : s.Good)
    {r0 r1 b0 b1 r b : ℕ} (t : Bool)
    (hmem : s.Mem r b)
    (hr0 : s.fr + r0 ≤ r) (hr1 : r ≤ s.fr + r1)
    (hb0 : s.fb + b0 ≤ b) (hb1 : b ≤ s.fb + b1)
    (hpar : (r - s.fr) % 2 = t.toNat) :
    let res := s.queryParity r0 r1 b0 b1 t
    res.1 = true ∧ (res.2.1 < r ∨ (res.2.1 = r ∧ res.2.2 ≤ b)) := by
  rcases hmem with ⟨hfr, hcr, hfb, hcb, hmp, hd00, hd11, hd01, hd10⟩
  have hb_par : (b - s.fb) % 2 = (xor t (decide (s.d00 % 2 = 1))).toNat :=
    par_b_from_r (r - s.fr) (b - s.fb) s.d00 t hmp hpar
  dsimp only [Sum8.queryParity]
  generalize hb0p_def : b0 + (if decide (b0 % 2 = 1) == xor t (decide (s.d00 % 2 = 1)) then 0 else 1) = b0p at ⊢
  have hb0p_le : b0p ≤ b - s.fb := hb0p_def ▸ roundUpPar_le_of_par (by clear hmp hpar hb_par; omega) hb_par
  clear hb0p_def
  have hb1_nu : (decide (b1 = 0) && xor t (decide (s.d00 % 2 = 1))) = false :=
    not_under_of_par (by clear hmp hpar hb_par; omega) hb_par
  generalize hb1p_def : b1 - (if decide (b1 % 2 = 1) == xor t (decide (s.d00 % 2 = 1)) then 0 else 1) = b1p at ⊢
  have hb_le_b1p : b - s.fb ≤ b1p := hb1p_def ▸ le_roundDnPar_of_par (by clear hmp hpar hb_par; omega) hb_par
  clear hb1p_def
  generalize hrp_lo_def : max r0 (max (b0p + s.d01 - s.cb) (s.d00 - b1p)) = rp_lo at ⊢
  have hrp_lo_le : rp_lo ≤ r - s.fr := hrp_lo_def ▸ by
    clear hmp hpar hb_par
    refine max_le (by omega) (max_le (by omega) (by omega))
  clear hrp_lo_def
  generalize hrp_hi_def : min r1 (min (s.cr + s.cb - (s.d11 + b0p)) (b1p + s.cr - s.d10)) = rp_hi at ⊢
  have hr_le_rp_hi : r - s.fr ≤ rp_hi := hrp_hi_def ▸ by
    clear hmp hpar hb_par
    refine le_min (by omega) (le_min (by omega) (by omega))
  clear hrp_hi_def
  have hrp_hi_nu : (decide (rp_hi = 0) && t) = false := not_under_of_par hr_le_rp_hi hpar
  generalize hrp_lo_t_def : rp_lo + (if decide (rp_lo % 2 = 1) == t then 0 else 1) = rp_lo_t at ⊢
  have hrp_lo_t_le : rp_lo_t ≤ r - s.fr := hrp_lo_t_def ▸ roundUpPar_le_of_par hrp_lo_le hpar
  clear hrp_lo_t_def
  generalize hrp_hi_t_def : rp_hi - (if decide (rp_hi % 2 = 1) == t then 0 else 1) = rp_hi_t at ⊢
  have hr_le_rp_hi_t : r - s.fr ≤ rp_hi_t := hrp_hi_t_def ▸ le_roundDnPar_of_par hr_le_rp_hi hpar
  clear hrp_hi_t_def hmp hpar hb_par
  constructor
  · simp [hb1_nu, hrp_hi_nu, le_trans hb0p_le hb_le_b1p, le_trans hrp_lo_t_le hr_le_rp_hi_t]
  · by_cases heq : s.fr + rp_lo_t = r
    · right
      refine ⟨heq, ?_⟩
      have hrp_eq : rp_lo_t = r - s.fr := by rw [← heq, Nat.add_sub_cancel_left]
      have hbp_le : max b0p (max (s.d00 - rp_lo_t) (s.d10 + rp_lo_t - s.cr)) ≤ b - s.fb := by
        rw [hrp_eq]; refine max_le hb0p_le (max_le (by omega) (by omega))
      omega
    · left; omega

private lemma Sum8.query_spec {s : Sum8} (hs : s.Good) (loR hiR loB hiB : ℕ) :
    let q := s.query loR hiR loB hiB
    (q.1 = true ↔ ∃ r b, s.Mem r b ∧ loR ≤ r ∧ r ≤ hiR ∧ loB ≤ b ∧ b ≤ hiB) ∧
    (q.1 = true → s.Mem q.2.1 q.2.2 ∧
      loR ≤ q.2.1 ∧ q.2.1 ≤ hiR ∧ loB ≤ q.2.2 ∧ q.2.2 ≤ hiB ∧
      ∀ r b, s.Mem r b → loR ≤ r → r ≤ hiR → loB ≤ b → b ≤ hiB →
        q.2.1 < r ∨ (q.2.1 = r ∧ q.2.2 ≤ b)) := by
  dsimp only [Sum8.query]
  set R0 := max s.fr loR
  set R1 := min (s.fr + s.cr) hiR
  set B0 := max s.fb loB
  set B1 := min (s.fb + s.cb) hiB
  set box_ok := decide (loR ≤ hiR) && decide (loB ≤ hiB) && decide (R0 ≤ R1) && decide (B0 ≤ B1)
  set r0 := R0 - s.fr
  set r1 := R1 - s.fr
  set b0 := B0 - s.fb
  set b1 := B1 - s.fb
  have hr1_le : r1 ≤ s.cr := by dsimp only [r1, R1]; omega
  have hb1_le : b1 ≤ s.cb := by dsimp only [b1, B1]; omega
  have hsound0 := fun h => Sum8.queryParity_sound hs (r0 := r0) (b0 := b0) hr1_le hb1_le false h
  have hsound1 := fun h => Sum8.queryParity_sound hs (r0 := r0) (b0 := b0) hr1_le hb1_le true h
  have hcomp0 := fun {r b} hm h1 h2 h3 h4 hp => Sum8.queryParity_complete hs (r0 := r0) (r1 := r1) (b0 := b0) (b1 := b1) (r := r) (b := b) false hm h1 h2 h3 h4 hp
  have hcomp1 := fun {r b} hm h1 h2 h3 h4 hp => Sum8.queryParity_complete hs (r0 := r0) (r1 := r1) (b0 := b0) (b1 := b1) (r := r) (b := b) true hm h1 h2 h3 h4 hp
  generalize s.queryParity r0 r1 b0 b1 false = q0 at hsound0 hcomp0 ⊢
  generalize s.queryParity r0 r1 b0 b1 true = q1 at hsound1 hcomp1 ⊢
  set f0 := box_ok && q0.1
  set f1 := box_ok && q1.1
  set flag := f0 || f1
  set pick0 := f0 && ((!f1) || decide (q0.2.1 < q1.2.1) ||
    (decide (q0.2.1 = q1.2.1) && decide (q0.2.2 ≤ q1.2.2)))
  have hsound_part : ∀ hfl : flag = true,
      s.Mem (if pick0 then q0.2.1 else q1.2.1) (if pick0 then q0.2.2 else q1.2.2) ∧
      loR ≤ (if pick0 then q0.2.1 else q1.2.1) ∧ (if pick0 then q0.2.1 else q1.2.1) ≤ hiR ∧
      loB ≤ (if pick0 then q0.2.2 else q1.2.2) ∧ (if pick0 then q0.2.2 else q1.2.2) ≤ hiB ∧
      ∀ r b, s.Mem r b → loR ≤ r → r ≤ hiR → loB ≤ b → b ≤ hiB →
        (if pick0 then q0.2.1 else q1.2.1) < r ∨
        ((if pick0 then q0.2.1 else q1.2.1) = r ∧ (if pick0 then q0.2.2 else q1.2.2) ≤ b) := by
    intro hfl
    have hbox : box_ok = true := by
      dsimp only [flag, f0, f1] at hfl; cases hbx : box_ok <;> simp [hbx] at hfl ⊢
    have hbox' : loR ≤ hiR ∧ loB ≤ hiB ∧ R0 ≤ R1 ∧ B0 ≤ B1 := by
      dsimp only [box_ok] at hbox; simp only [Bool.and_eq_true, decide_eq_true_eq] at hbox
      exact ⟨hbox.1.1.1, hbox.1.1.2, hbox.1.2, hbox.2⟩
    have hR0_ge : s.fr ≤ R0 := le_max_left _ _
    have hB0_ge : s.fb ≤ B0 := le_max_left _ _
    have hR1_ge : s.fr ≤ R1 := le_trans hR0_ge hbox'.2.2.1
    have hB1_ge : s.fb ≤ B1 := le_trans hB0_ge hbox'.2.2.2
    have hmin_any : ∀ (r b : ℕ), s.Mem r b → loR ≤ r → r ≤ hiR → loB ≤ b → b ≤ hiB →
        (f0 = true ∧ (q0.2.1 < r ∨ (q0.2.1 = r ∧ q0.2.2 ≤ b))) ∨
        (f1 = true ∧ (q1.2.1 < r ∨ (q1.2.1 = r ∧ q1.2.2 ≤ b))) := by
      intro r b hmem hlr hhr hlb hhb
      have hfr := hmem.1; have hcr := hmem.2.1
      have hfb := hmem.2.2.1; have hcb := hmem.2.2.2.1
      have hr0' : s.fr + r0 ≤ r := by dsimp only [r0, R0]; omega
      have hr1' : r ≤ s.fr + r1 := by dsimp only [r1, R1]; omega
      have hb0' : s.fb + b0 ≤ b := by dsimp only [b0, B0]; omega
      have hb1' : b ≤ s.fb + b1 := by dsimp only [b1, B1]; omega
      by_cases hp : (r - s.fr) % 2 = 0
      · left
        have hc := hcomp0 hmem hr0' hr1' hb0' hb1' (by simpa using hp)
        exact ⟨by simp only [f0, hbox, hc.1, Bool.and_self], hc.2⟩
      · right
        have hc := hcomp1 hmem hr0' hr1' hb0' hb1' (by dsimp; omega)
        exact ⟨by simp only [f1, hbox, hc.1, Bool.and_self], hc.2⟩
    by_cases hpk : pick0 = true
    · rw [if_pos hpk, if_pos hpk]
      have hf0 : f0 = true := by
        dsimp only [pick0] at hpk; cases hf : f0 <;> simp [hf] at hpk ⊢
      have hq0 : q0.1 = true := by dsimp only [f0] at hf0; simp [hbox] at hf0; exact hf0
      have hs0 := hsound0 hq0
      refine ⟨hs0.1,
        by have h := hs0.2.1; dsimp only [r0, R0] at h; omega,
        by have h := hs0.2.2.1; dsimp only [r1, R1] at h; omega,
        by have h := hs0.2.2.2.1; dsimp only [b0, B0] at h; omega,
        by have h := hs0.2.2.2.2.1; dsimp only [b1, B1] at h; omega, ?_⟩
      intro r b hmem hlr hhr hlb hhb
      rcases hmin_any r b hmem hlr hhr hlb hhb with ⟨_, hle0⟩ | ⟨hf1, hle1⟩
      · exact hle0
      · dsimp only [pick0] at hpk
        simp [hf0, hf1] at hpk
        rcases hpk with hlt | ⟨heq, hle⟩ <;> rcases hle1 with hlt1 | ⟨heq1, hle1'⟩ <;> omega
    · rw [if_neg hpk, if_neg hpk]
      have hf1 : f1 = true := by
        dsimp only [flag, pick0] at hfl hpk
        cases h0 : f0 <;> cases h1 : f1 <;> simp [h0, h1] at hfl hpk ⊢
      have hq1 : q1.1 = true := by dsimp only [f1] at hf1; simp [hbox] at hf1; exact hf1
      have hs1 := hsound1 hq1
      refine ⟨hs1.1,
        by have h := hs1.2.1; dsimp only [r0, R0] at h; omega,
        by have h := hs1.2.2.1; dsimp only [r1, R1] at h; omega,
        by have h := hs1.2.2.2.1; dsimp only [b0, B0] at h; omega,
        by have h := hs1.2.2.2.2.1; dsimp only [b1, B1] at h; omega, ?_⟩
      intro r b hmem hlr hhr hlb hhb
      rcases hmin_any r b hmem hlr hhr hlb hhb with ⟨hf0, hle0⟩ | ⟨_, hle1⟩
      · dsimp only [pick0] at hpk
        simp [hf0, hf1] at hpk
        rcases hle0 with hlt0 | ⟨heq0, hle0'⟩ <;> omega
      · exact hle1
  refine ⟨⟨fun hfl => ?_, fun ⟨r, b, hmem, hlr, hhr, hlb, hhb⟩ => ?_⟩, hsound_part⟩
  · have h := hsound_part hfl
    exact ⟨_, _, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  · have hfr := hmem.1; have hcr := hmem.2.1
    have hfb := hmem.2.2.1; have hcb := hmem.2.2.2.1
    have hbox : box_ok = true := by
      dsimp only [box_ok, R0, R1, B0, B1]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    have hr0' : s.fr + r0 ≤ r := by dsimp only [r0, R0]; omega
    have hr1' : r ≤ s.fr + r1 := by dsimp only [r1, R1]; omega
    have hb0' : s.fb + b0 ≤ b := by dsimp only [b0, B0]; omega
    have hb1' : b ≤ s.fb + b1 := by dsimp only [b1, B1]; omega
    by_cases hp : (r - s.fr) % 2 = 0
    · have hc := hcomp0 hmem hr0' hr1' hb0' hb1' (by simpa using hp)
      simp only [flag, f0, hbox, hc.1, Bool.and_self, Bool.true_or]
    · have hc := hcomp1 hmem hr0' hr1' hb0' hb1' (by dsimp; omega)
      simp only [flag, f1, hbox, hc.1, Bool.and_self, Bool.or_true]

/-!
## Part 2: Cycle decomposition of `(M false, M true)`, pure `prep`, and pure `build`
-/

private lemma exists_perm_period {n : ℕ} (step : Equiv.Perm (Fin n)) (i0 : Fin n) :
    ∃ t : ℕ, 1 ≤ t ∧ (step^[t]) i0 = i0 := by
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
  rcases Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (n + 1) => (step^[k.val]) i0) hcard with
    ⟨a, b, hne, heq⟩
  have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · refine ⟨b.val - a.val, by omega, ?_⟩
    have h1 : (step^[a.val]) ((step^[b.val - a.val]) i0) = (step^[a.val]) i0 := by
      rw [← Function.iterate_add_apply, show a.val + (b.val - a.val) = b.val by omega, heq]
    exact (step.injective.iterate a.val) h1
  · refine ⟨a.val - b.val, by omega, ?_⟩
    have h1 : (step^[b.val]) ((step^[a.val - b.val]) i0) = (step^[b.val]) i0 := by
      rw [← Function.iterate_add_apply, show b.val + (a.val - b.val) = a.val by omega, heq.symm]
    exact (step.injective.iterate b.val) h1

private noncomputable def permPeriod {n : ℕ} (step : Equiv.Perm (Fin n)) (i0 : Fin n) : ℕ :=
  Nat.find (exists_perm_period step i0)

private noncomputable def permOrbit {n : ℕ} (step : Equiv.Perm (Fin n)) (i0 : Fin n) :
    List (Fin n) :=
  List.ofFn (fun j : Fin (permPeriod step i0) => (step^[j.val]) i0)

private lemma permOrbit_props {n : ℕ} (step : Equiv.Perm (Fin n)) (i0 : Fin n) :
    let orb := permOrbit step i0
    1 ≤ orb.length ∧
    i0 ∈ orb ∧
    orb.Nodup ∧
    (∀ j (hj : j < orb.length), step (orb.get ⟨j, hj⟩) = (orb.get ⟨(j + 1) % orb.length, Nat.mod_lt _ (by omega)⟩)) ∧
    (∀ x ∈ orb, step x ∈ orb) ∧
    (∀ x ∈ orb, step.symm x ∈ orb) := by
  have hspec := Nat.find_spec (exists_perm_period step i0)
  set p := permPeriod step i0
  have hp1 : 1 ≤ p := hspec.1
  have hp_eq : (step^[p]) i0 = i0 := hspec.2
  have hlen : (permOrbit step i0).length = p := by simp [permOrbit, p]
  have hget : ∀ (j : ℕ) (hj : j < (permOrbit step i0).length),
      (permOrbit step i0).get ⟨j, hj⟩ = (step^[j]) i0 := by
    intro j hj; simp [permOrbit]
  have hi0 : i0 ∈ permOrbit step i0 := by
    have h0 : (permOrbit step i0).get ⟨0, by omega⟩ = i0 := by simp [permOrbit]
    have hm : (permOrbit step i0).get ⟨0, by omega⟩ ∈ permOrbit step i0 := List.get_mem _ _
    rw [h0] at hm; exact hm
  have hnodup : (permOrbit step i0).Nodup := by
    rw [List.nodup_iff_injective_get]
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    rw [hget a ha, hget b hb] at hab
    have ha' : a < Nat.find (exists_perm_period step i0) := by simpa [hlen, p, permPeriod] using ha
    have hb' : b < Nat.find (exists_perm_period step i0) := by simpa [hlen, p, permPeriod] using hb
    apply Fin.ext; dsimp only
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (step^[b - a]) i0 = i0 := by
        apply step.injective.iterate a
        rw [← Function.iterate_add_apply, show a + (b - a) = b by omega, hab.symm]
      have hmin := Nat.find_min (exists_perm_period step i0) (m := b - a) (by omega)
      exact hmin ⟨by omega, h1⟩
    · have h1 : (step^[a - b]) i0 = i0 := by
        apply step.injective.iterate b
        rw [← Function.iterate_add_apply, show b + (a - b) = a by omega, hab]
      have hmin := Nat.find_min (exists_perm_period step i0) (m := a - b) (by omega)
      exact hmin ⟨by omega, h1⟩
  have hstep : ∀ j (hj : j < (permOrbit step i0).length),
      step ((permOrbit step i0).get ⟨j, hj⟩) =
      ((permOrbit step i0).get ⟨(j + 1) % (permOrbit step i0).length, Nat.mod_lt _ (by omega)⟩) := by
    intro j hj
    rw [hget j hj, hget _ (Nat.mod_lt _ (by omega))]
    by_cases hlast : j + 1 = p
    · rw [hlen, hlast, Nat.mod_self]
      calc step ((step^[j]) i0) = (step^[j + 1]) i0 := (Function.iterate_succ_apply' step j i0).symm
        _ = (step^[p]) i0 := by rw [hlast]
        _ = i0 := hp_eq
    · have hlt : j + 1 < p := by omega
      rw [hlen, Nat.mod_eq_of_lt hlt]
      exact (Function.iterate_succ_apply' step j i0).symm
  have hcl : ∀ x ∈ permOrbit step i0, step x ∈ permOrbit step i0 := by
    intro x hx
    rcases List.mem_iff_get.mp hx with ⟨⟨j, hj⟩, rfl⟩
    rw [hstep j hj]; exact List.get_mem _ _
  have hcl_symm : ∀ x ∈ permOrbit step i0, step.symm x ∈ permOrbit step i0 := by
    intro x hx
    rcases List.mem_iff_get.mp hx with ⟨⟨j, hj⟩, rfl⟩
    have hj' : (j + p - 1) % p < (permOrbit step i0).length := by rw [hlen]; exact Nat.mod_lt _ (by omega)
    have heq : step ((permOrbit step i0).get ⟨(j + p - 1) % p, hj'⟩) = (permOrbit step i0).get ⟨j, hj⟩ := by
      rw [hstep ((j + p - 1) % p) hj']; congr 1; ext; dsimp only
      rw [hlen]
      by_cases hj0 : j = 0
      · subst hj0
        have hpm : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
        rw [Nat.zero_add, hpm, show p - 1 + 1 = p by omega, Nat.mod_self]
      · have h1 : (j + p - 1) % p = j - 1 := by
          rw [show j + p - 1 = (j - 1) + p by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h1, show j - 1 + 1 = j by omega, Nat.mod_eq_of_lt (by omega)]
    rw [← heq, Equiv.symm_apply_apply]
    exact List.get_mem _ _
  exact ⟨by omega, hi0, hnodup, hstep, hcl, hcl_symm⟩

private noncomputable def decompAux {n : ℕ} (step : Equiv.Perm (Fin n)) (rem : Finset (Fin n)) :
    List (List (Fin n)) :=
  if h : rem.Nonempty then
    let i0 := rem.min' h
    let orb := permOrbit step i0
    orb :: decompAux step (rem \ orb.toFinset)
  else []
termination_by rem.card
decreasing_by
  have hmem : rem.min' h ∈ rem := Finset.min'_mem rem h
  have horb : rem.min' h ∈ (permOrbit step (rem.min' h)).toFinset :=
    List.mem_toFinset.mpr (permOrbit_props step (rem.min' h)).2.1
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun heq => by
    have h1 : rem.min' h ∈ rem \ (permOrbit step (rem.min' h)).toFinset := heq.symm ▸ hmem
    exact (Finset.mem_sdiff.mp h1).2 horb⟩)

private lemma decompAux_props {n : ℕ} (step : Equiv.Perm (Fin n)) :
    ∀ (k : ℕ) (rem : Finset (Fin n)), rem.card = k →
      (∀ x ∈ rem, step x ∈ rem) →
      let cs := decompAux step rem
      (∀ c ∈ cs, 1 ≤ c.length ∧ c.Nodup ∧
        ∀ j (hj : j < c.length), step (c.get ⟨j, hj⟩) = (c.get ⟨(j + 1) % c.length, Nat.mod_lt _ (by omega)⟩)) ∧
      cs.flatten.Nodup ∧
      (∀ x : Fin n, x ∈ cs.flatten ↔ x ∈ rem) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro rem hcard hclosed
    unfold decompAux
    split_ifs with hne
    · set i0 := rem.min' hne
      set orb := permOrbit step i0
      have hop := permOrbit_props step i0
      have horb_sub : ∀ x ∈ orb, x ∈ rem := by
        intro x hx
        rcases List.getElem_of_mem hx with ⟨j, hj, rfl⟩
        have : orb[j] = (step^[j]) i0 := by simp [orb, permOrbit]
        rw [this]
        have hi0_mem : i0 ∈ rem := Finset.min'_mem rem hne
        clear hx hj this
        induction j with
        | zero => exact hi0_mem
        | succ m ihm =>
          rw [Function.iterate_succ_apply']
          exact hclosed _ ihm
      have hrem'_closed : ∀ x ∈ rem \ orb.toFinset, step x ∈ rem \ orb.toFinset := by
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        refine ⟨hclosed x hx.1, fun hsx => hx.2 ?_⟩
        rw [List.mem_toFinset] at hsx ⊢
        have := hop.2.2.2.2.2 (step x) hsx
        simpa using this
      have hlt : (rem \ orb.toFinset).card < k := by
        rw [← hcard]
        exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, fun heq => by
          have h1 : i0 ∈ rem \ orb.toFinset := heq.symm ▸ Finset.min'_mem rem hne
          exact (Finset.mem_sdiff.mp h1).2 (List.mem_toFinset.mpr hop.2.1)⟩)
      have hrec := ih _ hlt (rem \ orb.toFinset) rfl hrem'_closed
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact ⟨hop.1, hop.2.2.1, hop.2.2.2.1⟩
        · exact hrec.1 c hc'
      · rw [List.flatten_cons, List.nodup_append]
        refine ⟨hop.2.2.1, hrec.2.1, fun x hx1 y hy2 heq => ?_⟩
        subst heq
        have hy := (hrec.2.2 x).mp hy2
        rw [Finset.mem_sdiff, List.mem_toFinset] at hy
        exact hy.2 hx1
      · intro x
        rw [List.flatten_cons, List.mem_append, hrec.2.2 x, Finset.mem_sdiff, List.mem_toFinset]
        constructor
        · rintro (hx | ⟨hx, _⟩)
          · exact horb_sub x hx
          · exact hx
        · intro hx
          by_cases ho : x ∈ orb
          · exact Or.inl ho
          · exact Or.inr ⟨hx, ho⟩
    · have hemp : rem = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst hemp
      simp

private noncomputable def permCycles {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) :
    List (List (Fin n)) :=
  decompAux ((M false).trans (M true).symm) Finset.univ

private lemma list_map_sum_eq_toFinset_sum {α : Type} [DecidableEq α] (l : List α)
    (hnd : l.Nodup) (f : α → ℕ) : (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons, List.toFinset_cons, Finset.sum_insert (by simp [hnd.1]), ih hnd.2]

private lemma permCycles_props {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) :
    let step := (M false).trans (M true).symm
    let cs := permCycles M
    (∀ c ∈ cs, 1 ≤ c.length ∧ c.Nodup ∧
      ∀ j (hj : j < c.length), step (c.get ⟨j, hj⟩) = (c.get ⟨(j + 1) % c.length, Nat.mod_lt _ (by omega)⟩)) ∧
    cs.flatten.Nodup ∧
    (∀ i : Fin n, i ∈ cs.flatten) ∧
    (cs.map List.length).sum = n := by
  have h := decompAux_props ((M false).trans (M true).symm)
    (Finset.univ : Finset (Fin n)).card Finset.univ rfl (fun x _ => Finset.mem_univ _)
  refine ⟨h.1, h.2.1, fun i => (h.2.2 i).mpr (Finset.mem_univ i), ?_⟩
  have hlen : (permCycles M).flatten.length = ((permCycles M).map List.length).sum :=
    List.length_flatten
  rw [← hlen]
  have hto : (permCycles M).flatten.toFinset = Finset.univ := by
    ext i; simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact (h.2.2 i).mpr (Finset.mem_univ i)
  have hcard : (permCycles M).flatten.toFinset.card = (permCycles M).flatten.length :=
    List.toFinset_card_of_nodup h.2.1
  rw [← hcard, hto, Finset.card_univ, Fintype.card_fin]

private lemma sum_over_cycles {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (f : Fin n → ℕ) :
    ((permCycles M).map fun c => (c.map f).sum).sum = ∑ i : Fin n, f i := by
  have hp := permCycles_props M
  have h1 : ((permCycles M).map fun c => (c.map f).sum).sum =
      ((permCycles M).flatten.map f).sum := by
    rw [List.map_flatten, List.sum_flatten, List.map_map]; rfl
  rw [h1]
  have hto : (permCycles M).flatten.toFinset = Finset.univ := by
    ext i; simp only [List.mem_toFinset, Finset.mem_univ, iff_true]; exact hp.2.2.1 i
  rw [← hto, list_map_sum_eq_toFinset_sum _ hp.2.1]

/-- Vertex `j < 2 * c.length` along alternating cycle `c`. -/
private def cycVert {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (c : List (Fin n))
    (j : ℕ) (hj : j < 2 * c.length) : Bool × Fin n :=
  if j % 2 = 0 then (false, (c.get ⟨j / 2, by omega⟩))
  else (true, M false (c.get ⟨j / 2, by omega⟩))

/-- Red mismatch count on a single cycle `c` for assignment `x`. -/
private def cycRedCount {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (c : List (Fin n))
    (x : Bool × Fin n → Bool) : ℕ :=
  (c.map fun i => (decide (x (false, i) ≠ x (true, M false i))).toNat).sum

/-- Blue mismatch count on a single cycle `c` for assignment `x`. -/
private def cycBlueCount {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (c : List (Fin n))
    (x : Bool × Fin n → Bool) : ℕ :=
  let step := (M false).trans (M true).symm
  (c.map fun i => (decide (x (false, step i) ≠ x (true, M false i))).toNat).sum

private lemma count_eq_sum_cyc {n : ℕ} (M : Bool → Equiv.Perm (Fin n))
    (x : Bool × Fin n → Bool) :
    (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M false i))).card =
      ((permCycles M).map (fun c => cycRedCount M c x)).sum ∧
    (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M true i))).card =
      ((permCycles M).map (fun c => cycBlueCount M c x)).sum := by
  constructor
  · rw [Finset.card_filter, ← sum_over_cycles M]
    congr 1; refine List.map_congr_left fun c _ => ?_; unfold cycRedCount
    congr 1; refine List.map_congr_left fun i _ => ?_; split_ifs <;> simp [*]
  · set step := (M false).trans (M true).symm
    have hstep_eq : ∀ i : Fin n, M true (step i) = M false i := fun i => by
      simp [step]
    rw [Finset.card_filter]
    have hcomp : (∑ i : Fin n, if x (false, i) ≠ x (true, M true i) then 1 else 0) =
        ∑ i : Fin n, if x (false, step i) ≠ x (true, M false i) then 1 else 0 := by
      rw [← Equiv.sum_comp step (fun i => if x (false, i) ≠ x (true, M true i) then 1 else 0)]
      refine Finset.sum_congr rfl fun i _ => by rw [hstep_eq i]
    rw [hcomp, ← sum_over_cycles M]
    congr 1; refine List.map_congr_left fun c _ => ?_; unfold cycBlueCount
    congr 1; refine List.map_congr_left fun i _ => ?_; split_ifs with h <;> simp [step] at h ⊢ <;> simp [h]

/-- Pure cycle summary computed by a single forward pass with wrap-around merged at the close. -/
private structure PrepState where
  hasPin : Bool
  firstBit : Bool
  preR : ℕ
  preB : ℕ
  curBit : Bool
  curR : ℕ
  curB : ℕ
  acc : Sum8

private def prepStep (e : ℕ) (p b : Bool) (st : PrepState) : PrepState :=
  let er := if e % 2 = 0 then 1 else 0
  let eb := if e % 2 = 0 then 0 else 1
  if p then
    if !st.hasPin then
      ⟨true, b, st.curR, st.curB, b, er, eb, st.acc⟩
    else
      ⟨true, st.firstBit, st.preR, st.preB, b, er, eb,
        st.acc.comb (Sum8.ofSeg st.curR st.curB (xor st.curBit b))⟩
  else
    ⟨st.hasPin, st.firstBit, st.preR, st.preB, st.curBit, st.curR + er, st.curB + eb, st.acc⟩

private def prepLoop (k : ℕ) (pins bits : ℕ → Bool) : ℕ → PrepState
  | 0 => ⟨false, false, 0, 0, false, 0, 0, Sum8.zero⟩
  | j + 1 => prepStep j (pins j) (bits j) (prepLoop k pins bits j)

private def pureCycleSum (k : ℕ) (pins bits : ℕ → Bool) : Sum8 :=
  let st := prepLoop k pins bits (2 * k)
  if st.hasPin then
    st.acc.comb (Sum8.ofSeg (st.curR + st.preR) (st.curB + st.preB) (xor st.curBit st.firstBit))
  else
    st.acc.comb (Sum8.ofSeg st.curR st.curB false)

/-- Pure backward scan on an open path `0 .. 2*k` with vertex `2*k` pinned to `a0`. -/
private structure BackState where
  nxtBit : Bool
  remR : ℕ
  remB : ℕ
  later : Sum8

private def backStep (j : ℕ) (pNext bNext : Bool) (stNext : BackState) : BackState :=
  let er := if j % 2 = 0 then 1 else 0
  let eb := if j % 2 = 0 then 0 else 1
  if pNext then
    ⟨bNext, er, eb,
      (Sum8.ofSeg stNext.remR stNext.remB (xor bNext stNext.nxtBit)).comb stNext.later⟩
  else
    ⟨stNext.nxtBit, stNext.remR + er, stNext.remB + eb, stNext.later⟩

private def backScanList (k : ℕ) (pins bits : ℕ → Bool) (a0 : Bool) (laterCyc : Sum8) :
    ℕ → BackState
  | 0 => ⟨a0, 0, 0, laterCyc⟩
  | d + 1 =>
    let j := 2 * k - 1 - d
    let stNext := backScanList k pins bits a0 laterCyc d
    if d = 0 then
      -- j = 2*k - 1, next vertex is 2*k pinned to a0, later is laterCyc directly
      ⟨a0, if j % 2 = 0 then 1 else 0, if j % 2 = 0 then 0 else 1, laterCyc⟩
    else
      backStep j (pins (j + 1)) (bits (j + 1)) stNext

/-- `backAt k pins bits a0 laterCyc j` is the `BackState` at vertex `j ≤ 2*k`. -/
private def backAt (k : ℕ) (pins bits : ℕ → Bool) (a0 : Bool) (laterCyc : Sum8) (j : ℕ) :
    BackState :=
  backScanList k pins bits a0 laterCyc (2 * k - j)

private def tailSum (k : ℕ) (pins bits : ℕ → Bool) (a0 : Bool) (laterCyc : Sum8)
    (j : ℕ) (curX : Bool) : Sum8 :=
  let st := backAt k pins bits a0 laterCyc j
  (Sum8.ofSeg st.remR st.remB (xor curX st.nxtBit)).comb st.later

private lemma backAt_eq_step {k : ℕ} (pins bits : ℕ → Bool) (a0 : Bool) (laterCyc : Sum8)
    {j : ℕ} (hj : j + 1 < 2 * k) :
    backAt k pins bits a0 laterCyc j =
      backStep j (pins (j + 1)) (bits (j + 1)) (backAt k pins bits a0 laterCyc (j + 1)) := by
  unfold backAt
  have h1 : 2 * k - j = (2 * k - (j + 1)) + 1 := by omega
  have h2 : 2 * k - (j + 1) ≠ 0 := by omega
  have h3 : 2 * k - 1 - (2 * k - (j + 1)) = j := by omega
  rw [h1]
  conv_lhs => unfold backScanList
  simp only [h2, ↓reduceIte, h3]

private lemma backAt_last {k : ℕ} (hk : 1 ≤ k) (pins bits : ℕ → Bool) (a0 : Bool)
    (laterCyc : Sum8) :
    backAt k pins bits a0 laterCyc (2 * k - 1) = ⟨a0, 0, 1, laterCyc⟩ := by
  unfold backAt
  have h1 : 2 * k - (2 * k - 1) = 1 := by omega
  rw [h1]
  unfold backScanList
  have hpar : (2 * k - 1) % 2 ≠ 0 := by omega
  simp [hpar]

private lemma backAt_rem_alt {k : ℕ} (hk : 1 ≤ k) (pins bits : ℕ → Bool) (a0 : Bool)
    (laterCyc : Sum8) (hlat : laterCyc.Good) :
    ∀ (d : ℕ) (hd : 1 ≤ d) (hdk : d ≤ 2 * k),
      let j := 2 * k - d
      let st := backAt k pins bits a0 laterCyc j
      st.later.Good ∧
      1 ≤ st.remR + st.remB ∧
      (j % 2 = 0 → st.remB ≤ st.remR ∧ st.remR ≤ st.remB + 1 ∧ 1 ≤ st.remR) ∧
      (j % 2 = 1 → st.remR ≤ st.remB ∧ st.remB ≤ st.remR + 1 ∧ 1 ≤ st.remB) ∧
      st.remR + st.remB ≤ d := by
  intro d
  induction d with
  | zero => intro hd; omega
  | succ d ih =>
    intro _ hdk
    by_cases hd0 : d = 0
    · subst hd0
      have hlast := backAt_last hk pins bits a0 laterCyc
      dsimp only
      rw [hlast]
      simp only
      refine ⟨hlat, by omega, fun h => by omega, fun _ => by omega, by omega⟩
    · have hj : (2 * k - (d + 1)) + 1 < 2 * k := by omega
      have hrec := ih (by omega) (by omega)
      have heq : (2 * k - (d + 1)) + 1 = 2 * k - d := by omega
      dsimp only
      rw [backAt_eq_step pins bits a0 laterCyc hj, heq]
      dsimp only [backStep]
      set j := 2 * k - (d + 1)
      set stN := backAt k pins bits a0 laterCyc (2 * k - d)
      rcases hrec with ⟨hgN, hposN, hevN, hodN, hleN⟩
      change stN.later.Good at hgN
      change 1 ≤ stN.remR + stN.remB at hposN
      change (2 * k - d) % 2 = 0 → stN.remB ≤ stN.remR ∧ stN.remR ≤ stN.remB + 1 ∧ 1 ≤ stN.remR at hevN
      change (2 * k - d) % 2 = 1 → stN.remR ≤ stN.remB ∧ stN.remB ≤ stN.remR + 1 ∧ 1 ≤ stN.remB at hodN
      change stN.remR + stN.remB ≤ d at hleN
      by_cases hp : pins (2 * k - d) = true
      · rw [if_pos hp]
        have hsegG : (Sum8.ofSeg stN.remR stN.remB (xor (bits (2 * k - d)) stN.nxtBit)).Good := by
          apply Sum8.good_ofSeg
          by_cases hpar : (2 * k - d) % 2 = 0
          · have := hevN hpar; omega
          · have := hodN (by omega); omega
        refine ⟨Sum8.good_comb hsegG hgN, by simp only; split_ifs <;> omega,
          fun h => by simp only [h, ↓reduceIte]; decide,
          fun h => by
            have h0 : j % 2 ≠ 0 := by omega
            simp only [h0, ↓reduceIte]; decide,
          by simp only; split_ifs <;> omega⟩
      · rw [if_neg hp]
        by_cases hpar : j % 2 = 0
        · have hparN : (2 * k - d) % 2 = 1 := by omega
          have := hodN hparN
          simp only [hpar, ↓reduceIte]
          exact ⟨hgN, by omega, fun _ => by omega, fun h => by omega, by omega⟩
        · have hparN : (2 * k - d) % 2 = 0 := by omega
          have := hevN hparN
          simp only [hpar, ↓reduceIte]
          exact ⟨hgN, by omega, fun h => False.elim h, fun _ => by omega, by omega⟩

private lemma tailSum_good {k : ℕ} (hk : 1 ≤ k) (pins bits : ℕ → Bool) (a0 : Bool)
    (laterCyc : Sum8) (hlat : laterCyc.Good) {j : ℕ} (hj : j < 2 * k) (curX : Bool) :
    (tailSum k pins bits a0 laterCyc j curX).Good := by
  have h := backAt_rem_alt hk pins bits a0 laterCyc hlat (2 * k - j) (by omega) (by omega)
  rw [show 2 * k - (2 * k - j) = j by omega] at h
  rcases h with ⟨hg, _, hev, hod, _⟩
  apply Sum8.good_comb _ hg
  apply Sum8.good_ofSeg
  by_cases hpar : j % 2 = 0
  · have := hev hpar; omega
  · have := hod (by omega); omega

/-- Key relation between `prepLoop` (forward pass) and `backAt` (backward scan) on `[0..2*k]`. -/
private lemma prepLoop_inv (k : ℕ) (pins bits : ℕ → Bool) :
    ∀ j ≤ 2 * k,
      let st := prepLoop k pins bits j
      st.acc.Good ∧
      (st.hasPin = false →
        st.acc = Sum8.zero ∧
        st.curR = (j + 1) / 2 ∧ st.curB = j / 2 ∧
        ∀ t < j, pins t = false) ∧
      (st.hasPin = true →
        ∃ e0 el, e0 ≤ el ∧ el < j ∧
          pins e0 = true ∧ pins el = true ∧
          (∀ t < e0, pins t = false) ∧
          (∀ t, el < t → t < j → pins t = false) ∧
          st.firstBit = bits e0 ∧ st.curBit = bits el ∧
          st.preR = (e0 + 1) / 2 ∧ st.preB = e0 / 2 ∧
          st.curR = (j + 1) / 2 - (el + 1) / 2 ∧ st.curB = j / 2 - el / 2 ∧
          (∀ a0 laterCyc,
            (tailSum k pins bits a0 laterCyc e0 (bits e0)) =
            st.acc.comb (tailSum k pins bits a0 laterCyc el (bits el)))) := by
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨Sum8.good_zero, fun _ => ⟨rfl, rfl, rfl, fun _ h => by omega⟩, fun h => by simp [prepLoop] at h⟩
  | succ j ih =>
    intro hj
    rcases ih (by omega) with ⟨hG, hF, hT⟩
    dsimp only [prepLoop, prepStep]
    set st := prepLoop k pins bits j
    by_cases hp : pins j = true
    · simp only [hp, ↓reduceIte]
      cases hhp : st.hasPin
      · simp only [Bool.not_false, ↓reduceIte]
        rcases hF hhp with ⟨hacc0, hcr, hcb, hno⟩
        refine ⟨hG, fun h => by simp at h, fun _ => ⟨j, j, le_rfl, by omega, hp, hp, hno,
          fun t ht1 ht2 => by omega, rfl, rfl, hcr, hcb, by split_ifs <;> omega,
          by split_ifs <;> omega,
          fun a0 lat => by rw [hacc0, Sum8.comb_zero_left]⟩⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rcases hT hhp with ⟨e0, el, he0l, helj, hpe0, hpel, hbef, haft, hfb, hcb, hpr, hpb, hcr, hcb', htail⟩
        have hsegG : (Sum8.ofSeg st.curR st.curB (xor st.curBit (bits j))).Good := by
          apply Sum8.good_ofSeg; omega
        refine ⟨Sum8.good_comb hG hsegG, fun h => by simp at h,
          fun _ => ⟨e0, j, by omega, by omega, hpe0, hp, hbef,
            fun t ht1 ht2 => by omega, hfb, rfl, hpr, hpb, by split_ifs <;> omega,
            by split_ifs <;> omega,
            fun a0 lat => ?_⟩⟩
        rw [htail a0 lat, Sum8.comb_assoc]
        congr 1
        -- Show tailSum at el equals ofSeg (curR, curB, bits el ^^ bits j) + tailSum at j!
        have hbridge : ∀ (t : ℕ), el ≤ t → t < j →
            backAt k pins bits a0 lat t =
              ⟨bits j, (j + 1) / 2 - (t + 1) / 2, j / 2 - t / 2,
                tailSum k pins bits a0 lat j (bits j)⟩ := by
          intro t hlt htj
          induction hdist : j - 1 - t generalizing t with
          | zero =>
            have hteq : t = j - 1 := by omega
            subst hteq
            rw [backAt_eq_step pins bits a0 lat (by omega)]
            rw [show j - 1 + 1 = j by omega]
            dsimp only [backStep]
            rw [if_pos hp]
            dsimp only [tailSum]; congr 1 <;> (split_ifs <;> omega)
          | succ m ihm =>
            have htj1 : t + 1 < j := by omega
            have hrec := ihm (t + 1) (by omega) htj1 (by omega)
            rw [backAt_eq_step pins bits a0 lat (by omega)]
            dsimp only [backStep]
            rw [if_neg (by rw [haft (t + 1) (by omega) htj1]; decide), hrec]
            simp only; congr 1 <;> (split_ifs <;> omega)
        conv_lhs => unfold tailSum
        rw [hbridge el le_rfl helj]
        simp [hcb, hcr, hcb']
    · rw [if_neg hp]
      cases hhp : st.hasPin
      · rcases hF hhp with ⟨hacc0, hcr, hcb, hno⟩
        refine ⟨hG, fun _ => ⟨hacc0, by simp only; rw [hcr]; split_ifs <;> omega,
          by simp only; rw [hcb]; split_ifs <;> omega,
          fun t ht => if htj : t = j then htj ▸ Bool.eq_false_iff.mpr hp else hno t (by omega)⟩,
          fun h => by simp [hhp] at h⟩
      · rcases hT hhp with ⟨e0, el, he0l, helj, hpe0, hpel, hbef, haft, hfb, hcb, hpr, hpb, hcr, hcb', htail⟩
        refine ⟨hG, fun h => by simp [hhp] at h, fun _ => ⟨e0, el, he0l, by omega, hpe0, hpel, hbef,
          fun t ht1 ht2 =>
            if htj : t = j then htj ▸ Bool.eq_false_iff.mpr hp else haft t ht1 (by omega),
          hfb, hcb, hpr, hpb, by simp only; rw [hcr]; split_ifs <;> omega,
          by simp only; rw [hcb']; split_ifs <;> omega, htail⟩⟩

private lemma pureCycleSum_good {k : ℕ} (hk : 1 ≤ k) (pins bits : ℕ → Bool) :
    (pureCycleSum k pins bits).Good := by
  rcases prepLoop_inv k pins bits (2 * k) le_rfl with ⟨hG, hF, hT⟩
  dsimp only [pureCycleSum]
  cases hhp : (prepLoop k pins bits (2 * k)).hasPin
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases hF hhp with ⟨_, hcr, hcb, _⟩
    exact Sum8.good_comb hG (Sum8.good_ofSeg _ _ _ (by omega))
  · simp only [↓reduceIte]
    rcases hT hhp with ⟨e0, el, he0l, helk, _, _, _, _, _, _, hpr, hpb, hcr, hcb, _⟩
    exact Sum8.good_comb hG (Sum8.good_ofSeg _ _ _ (by omega))

/-- Splitting a cycle at vertex 0: any `(r, b)` in `pureCycleSum + laterCyc` lies in
    `tailSum ... false` (if `0` may be false) or `tailSum ... true` (if `0` may be true). -/
private lemma pureCycleSum_split_a0 {k : ℕ} (hk : 1 ≤ k) (pins bits : ℕ → Bool)
    {laterCyc : Sum8} (hlat : laterCyc.Good) {r b : ℕ}
    (hmem : ((pureCycleSum k pins bits).comb laterCyc).Mem r b) :
    ((pins 0 = false ∨ bits 0 = false) ∧ (tailSum k pins bits false laterCyc 0 false).Mem r b) ∨
    ((pins 0 = false ∨ bits 0 = true) ∧ (tailSum k pins bits true laterCyc 0 true).Mem r b) := by
  rcases prepLoop_inv k pins bits (2 * k) le_rfl with ⟨hG, hF, hT⟩
  set st := prepLoop k pins bits (2 * k)
  -- Helper: compute tailSum from a pinned vertex `el < 2*k` to `2*k` when no pins lie in `(el, 2*k)`.
  have htail_end : ∀ (el : ℕ) (hel : el < 2 * k) (haft : ∀ t, el < t → t < 2 * k → pins t = false)
      (a0 : Bool),
      tailSum k pins bits a0 laterCyc el (bits el) =
      (Sum8.ofSeg (k - (el + 1) / 2) (k - el / 2) (xor (bits el) a0)).comb laterCyc := by
    intro el hel haft a0
    have hbr : ∀ (t : ℕ), el ≤ t → t < 2 * k →
        backAt k pins bits a0 laterCyc t =
        ⟨a0, k - (t + 1) / 2, k - t / 2, laterCyc⟩ := by
      intro t hlt htk
      induction hd : 2 * k - 1 - t generalizing t with
      | zero =>
        have hteq : t = 2 * k - 1 := by omega
        subst hteq
        rw [backAt_last hk]
        congr 1 <;> omega
      | succ m ihm =>
        have ht1 : t + 1 < 2 * k := by omega
        have hrec := ihm (t + 1) (by omega) ht1 (by omega)
        rw [backAt_eq_step pins bits a0 laterCyc ht1]
        dsimp only [backStep]
        rw [if_neg (by rw [haft (t + 1) (by omega) ht1]; decide), hrec]
        simp only; congr 1 <;> (split_ifs <;> omega)
    unfold tailSum; rw [hbr el le_rfl hel]
  -- Helper: compute tailSum at 0 when no pins lie in `(0, e0)` and `e0 < 2*k` is pinned.
  have htail_start : ∀ (e0 : ℕ) (he0 : 1 ≤ e0) (he0k : e0 < 2 * k)
      (hpe0 : pins e0 = true) (hbef : ∀ t < e0, pins t = false) (a0 : Bool),
      tailSum k pins bits a0 laterCyc 0 a0 =
      (Sum8.ofSeg ((e0 + 1) / 2) (e0 / 2) (xor a0 (bits e0))).comb
        (tailSum k pins bits a0 laterCyc e0 (bits e0)) := by
    intro e0 he0 he0k hpe0 hbef a0
    have hbr : ∀ (t : ℕ), t < e0 →
        backAt k pins bits a0 laterCyc t =
        ⟨bits e0, (e0 + 1) / 2 - (t + 1) / 2, e0 / 2 - t / 2,
          tailSum k pins bits a0 laterCyc e0 (bits e0)⟩ := by
      intro t hte
      induction hd : e0 - 1 - t generalizing t with
      | zero =>
        have hteq : t = e0 - 1 := by omega
        subst hteq
        rw [backAt_eq_step pins bits a0 laterCyc (by omega)]
        rw [show e0 - 1 + 1 = e0 by omega]
        dsimp only [backStep]
        rw [if_pos hpe0]
        dsimp only [tailSum]; congr 1 <;> (split_ifs <;> omega)
      | succ m ihm =>
        have ht1 : t + 1 < e0 := by omega
        have hrec := ihm (t + 1) ht1 (by omega)
        rw [backAt_eq_step pins bits a0 laterCyc (by omega)]
        dsimp only [backStep]
        rw [if_neg (by rw [hbef (t + 1) ht1]; decide), hrec]
        simp only; congr 1 <;> (split_ifs <;> omega)
    conv_lhs => unfold tailSum
    rw [hbr 0 (by omega)]; simp
  cases hhp : st.hasPin
  · -- No pins anywhere on the cycle: root at 0 = false!
    rcases hF hhp with ⟨hacc0, hcr, hcb, hno⟩
    have hcyc : pureCycleSum k pins bits = Sum8.ofSeg k k false := by
      dsimp only [pureCycleSum]; change (if st.hasPin = true then _ else _) = _
      rw [hhp, if_neg Bool.false_ne_true, hacc0, Sum8.comb_zero_left]
      rw [hcr, hcb]; congr 1 <;> omega
    have ht0 : tailSum k pins bits false laterCyc 0 false =
        (Sum8.ofSeg k k false).comb laterCyc := by
      have hbr : ∀ (t : ℕ), t < 2 * k →
          backAt k pins bits false laterCyc t =
          ⟨false, k - (t + 1) / 2, k - t / 2, laterCyc⟩ := by
        intro t htk
        induction hd : 2 * k - 1 - t generalizing t with
        | zero =>
          have hteq : t = 2 * k - 1 := by omega
          subst hteq; rw [backAt_last hk]; congr 1 <;> omega
        | succ m ihm =>
          have ht1 : t + 1 < 2 * k := by omega
          have hrec := ihm (t + 1) ht1 (by omega)
          rw [backAt_eq_step pins bits false laterCyc ht1]
          dsimp only [backStep]
          rw [if_neg (by rw [hno (t + 1) ht1]; decide), hrec]
          simp only; congr 1 <;> (split_ifs <;> omega)
      conv_lhs => unfold tailSum
      rw [hbr 0 (by omega)]; simp
    left
    refine ⟨Or.inl (hno 0 (by omega)), ?_⟩
    rw [ht0, ← hcyc]; exact hmem
  · rcases hT hhp with ⟨e0, el, he0l, helk, hpe0, hpel, hbef, haft, hfb, hcb, hpr, hpb, hcr, hcb', htail⟩
    have hcyc : pureCycleSum k pins bits =
        st.acc.comb (Sum8.ofSeg (k - (el + 1) / 2 + (e0 + 1) / 2)
          (k - el / 2 + e0 / 2) (xor (bits el) (bits e0))) := by
      dsimp only [pureCycleSum]; change (if st.hasPin = true then _ else _) = _
      rw [hhp, if_pos rfl, hfb, hcb, hpr, hpb, hcr, hcb']
      congr 2 <;> omega
    by_cases he00 : e0 = 0
    · -- Vertex 0 IS pinned!
      subst he00
      have hts : tailSum k pins bits (bits 0) laterCyc 0 (bits 0) =
          (pureCycleSum k pins bits).comb laterCyc := by
        rw [htail (bits 0) laterCyc, htail_end el helk haft (bits 0), hcyc, Sum8.comb_assoc]
        simp
      cases hb0 : bits 0
      · left; rw [hb0] at hts; exact ⟨Or.inr rfl, hts.symm ▸ hmem⟩
      · right; rw [hb0] at hts; exact ⟨Or.inr rfl, hts.symm ▸ hmem⟩
    · -- Vertex 0 is unpinned (`e0 >= 1`): split the wrap-around segment at vertex 0!
      have hp0 : pins 0 = false := hbef 0 (by omega)
      have hts_eq : ∀ a0 : Bool,
          tailSum k pins bits a0 laterCyc 0 a0 =
          ((Sum8.ofSeg (k - (el + 1) / 2) (k - el / 2) (xor (bits el) a0)).comb
            (Sum8.ofSeg ((e0 + 1) / 2) (e0 / 2) (xor a0 (bits e0)))).comb
            (st.acc.comb laterCyc) := by
        intro a0
        rw [htail_start e0 (by omega) (by omega) hpe0 hbef a0, htail a0 laterCyc,
          htail_end el helk haft a0]
        exact Sum8.comb_4_swap _ _ _ _
      rw [hcyc, Sum8.comb_3_swap] at hmem
      have hsplit := Sum8.mem_split_seg (Sum8.good_comb hG hlat)
        (R1 := k - (el + 1) / 2) (B1 := k - el / 2)
        (R2 := (e0 + 1) / 2) (B2 := e0 / 2)
        (b1 := bits el) (b2 := bits e0)
        (by omega) (by omega) (by omega) (by omega) hmem
      rcases hsplit with h0 | h1
      · left; exact ⟨Or.inl hp0, (hts_eq false).symm ▸ h0⟩
      · right; exact ⟨Or.inl hp0, (hts_eq true).symm ▸ h1⟩

/-- Soundness of `pureCycleSum`: any valid bit assignment `x` on a cycle lands in `pureCycleSum`. -/
private lemma pureCycleSum_sound {k : ℕ} (hk : 1 ≤ k) (pins bits xs : ℕ → Bool)
    (hpin : ∀ j < 2 * k, pins j = true → xs j = bits j) :
    let rC := ((List.range (2 * k)).filter (fun e => decide (e % 2 = 0 ∧ xs e ≠ xs ((e + 1) % (2 * k))))).length
    let bC := ((List.range (2 * k)).filter (fun e => decide (e % 2 = 1 ∧ xs e ≠ xs ((e + 1) % (2 * k))))).length
    (pureCycleSum k pins bits).Mem rC bC := by
  -- Helper: mismatch counts on a subrange `[a, b)` of edges satisfy `(r + b) % 2 = (xs a != xs b)`.
  let edgeM (e : ℕ) : Bool := xs e != xs ((e + 1) % (2 * k))
  let rCnt (a b : ℕ) : ℕ :=
    ((List.range b).filter (fun e => decide (a ≤ e ∧ e % 2 = 0 ∧ edgeM e = true))).length
  let bCnt (a b : ℕ) : ℕ :=
    ((List.range b).filter (fun e => decide (a ≤ e ∧ e % 2 = 1 ∧ edgeM e = true))).length
  have hstep_cnt : ∀ a b, a ≤ b → b < 2 * k →
      rCnt a (b + 1) = rCnt a b + (if b % 2 = 0 ∧ edgeM b = true then 1 else 0) ∧
      bCnt a (b + 1) = bCnt a b + (if b % 2 = 1 ∧ edgeM b = true then 1 else 0) := by
    intro a b hab hbk
    constructor <;> {
      dsimp only [rCnt, bCnt]
      rw [List.range_succ, List.filter_append, List.length_append]
      simp [hab, List.filter_cons]
      split_ifs <;> rfl
    }
  have hseg_par : ∀ a b, a ≤ b → b ≤ 2 * k →
      rCnt a b ≤ (b + 1) / 2 - (a + 1) / 2 ∧
      bCnt a b ≤ b / 2 - a / 2 ∧
      (rCnt a b + bCnt a b) % 2 = (xor (xs (a % (2 * k))) (xs (b % (2 * k)))).toNat := by
    intro a b hab hbk
    induction b with
    | zero =>
      have ha0 : a = 0 := by omega
      subst ha0; simp [rCnt, bCnt]
    | succ b ih =>
      by_cases hab' : a = b + 1
      · subst hab'
        have hr0 : rCnt (b + 1) (b + 1) = 0 := by
          dsimp only [rCnt]; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro e he; rw [List.mem_range] at he; simp; omega
        have hb0 : bCnt (b + 1) (b + 1) = 0 := by
          dsimp only [bCnt]; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro e he; rw [List.mem_range] at he; simp; omega
        rw [hr0, hb0]; simp
      · rcases ih (by omega) (by omega) with ⟨hr, hb, hp⟩
        rcases hstep_cnt a b (by omega) (by omega) with ⟨hrs, hbs⟩
        rw [hrs, hbs]
        have hbm : b % (2 * k) = b := Nat.mod_eq_of_lt (by omega)
        rw [hbm] at hp
        refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
        dsimp only [edgeM]
        have hstep_par : ∀ (rc bc : ℕ) (x1 x2 x3 : Bool) (m : ℕ),
            (rc + bc) % 2 = (xor x1 x2).toNat →
            ((rc + if m % 2 = 0 ∧ (x2 != x3) = true then 1 else 0) +
             (bc + if m % 2 = 1 ∧ (x2 != x3) = true then 1 else 0)) % 2 = (xor x1 x3).toNat := by
          intro rc bc x1 x2 x3 m hpp
          have hpar1 : m % 2 = 1 ↔ ¬ (m % 2 = 0) := by omega
          cases x1 <;> cases x2 <;> cases x3 <;> by_cases hpar : m % 2 = 0 <;>
            simp [hpar, hpar1] at hpp ⊢ <;> omega
        exact hstep_par (rCnt a b) (bCnt a b) (xs (a % (2 * k))) (xs b) (xs ((b + 1) % (2 * k))) b hp
  have hrc_add : ∀ a b c, a ≤ b → b ≤ c → rCnt a c = rCnt a b + rCnt b c := by
    intro a b c hab hbc
    induction c with
    | zero =>
      have : a = 0 := by omega
      have : b = 0 := by omega
      subst a; subst b; rfl
    | succ c ih =>
      by_cases hbc' : b = c + 1
      · subst hbc'
        have : rCnt (c + 1) (c + 1) = 0 := by
          dsimp only [rCnt]; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro e he; rw [List.mem_range] at he; simp; omega
        omega
      · dsimp only [rCnt]
        rw [List.range_succ, List.filter_append, List.filter_append, List.length_append, List.length_append]
        have hrec := ih (by omega)
        dsimp only [rCnt] at hrec
        rw [hrec]
        have h1 : a ≤ c := by omega
        have h2 : b ≤ c := by omega
        simp [List.filter_cons, h1, h2]; split_ifs <;> omega
  have hbc_add : ∀ a b c, a ≤ b → b ≤ c → bCnt a c = bCnt a b + bCnt b c := by
    intro a b c hab hbc
    induction c with
    | zero =>
      have : a = 0 := by omega
      have : b = 0 := by omega
      subst a; subst b; rfl
    | succ c ih =>
      by_cases hbc' : b = c + 1
      · subst hbc'
        have : bCnt (c + 1) (c + 1) = 0 := by
          dsimp only [bCnt]; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
          intro e he; rw [List.mem_range] at he; simp; omega
        omega
      · dsimp only [bCnt]
        rw [List.range_succ, List.filter_append, List.filter_append, List.length_append, List.length_append]
        have hrec := ih (by omega)
        dsimp only [bCnt] at hrec
        rw [hrec]
        have h1 : a ≤ c := by omega
        have h2 : b ≤ c := by omega
        simp [List.filter_cons, h1, h2]; split_ifs <;> omega
  -- Induct on `j ≤ 2*k` to prove `st.acc` covers all edges in `[e0, el)`!
  have hloop : ∀ j ≤ 2 * k,
      let st := prepLoop k pins bits j
      (st.hasPin = true → ∃ e0 el, e0 ≤ el ∧ el < j ∧
        pins e0 = true ∧ pins el = true ∧
        st.firstBit = bits e0 ∧ st.curBit = bits el ∧
        st.preR = (e0 + 1) / 2 ∧ st.preB = e0 / 2 ∧
        st.curR = (j + 1) / 2 - (el + 1) / 2 ∧ st.curB = j / 2 - el / 2 ∧
        st.acc.Mem (rCnt e0 el) (bCnt e0 el)) := by
    intro j
    induction j with
    | zero => intro _; dsimp only [prepLoop]; intro h; exact False.elim (Bool.false_ne_true h)
    | succ j ih =>
      intro hj
      dsimp only [prepLoop, prepStep]
      set st := prepLoop k pins bits j
      rcases prepLoop_inv k pins bits j (by omega) with ⟨_, hF, _⟩
      by_cases hp : pins j = true
      · simp only [hp, ↓reduceIte]
        cases hhp : st.hasPin
        · simp only [Bool.not_false, ↓reduceIte]
          rcases hF hhp with ⟨hacc0, hcr, hcb, _⟩
          intro _
          have hr0 : rCnt j j = 0 := by
            dsimp only [rCnt]; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
            intro e he; rw [List.mem_range] at he; simp; omega
          have hb0 : bCnt j j = 0 := by
            dsimp only [bCnt]; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
            intro e he; rw [List.mem_range] at he; simp; omega
          refine ⟨j, j, le_rfl, by omega, hp, hp, rfl, rfl, hcr, hcb, by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
          rw [hacc0, hr0, hb0, Sum8.mem_zero_iff]; exact ⟨rfl, rfl⟩
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          intro _
          rcases ih (by omega) hhp with ⟨e0, el, he0l, helj, hpe0, hpel, hfb, hcb, hpr, hpb, hcr, hcb', hmem_acc⟩
          refine ⟨e0, j, by omega, by omega, hpe0, hp, hfb, rfl, hpr, hpb, by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
          rw [hrc_add e0 el j he0l (by omega), hbc_add e0 el j he0l (by omega)]
          apply Sum8.mem_comb_of_mem hmem_acc
          rcases hseg_par el j (by omega) (by omega) with ⟨hr, hb, hpar⟩
          rw [Nat.mod_eq_of_lt (a := el) (by omega), Nat.mod_eq_of_lt (a := j) (by omega),
            hpin el (by omega) hpel, hpin j (by omega) hp] at hpar
          exact Sum8.mem_ofSeg_of_bounds (by omega) (by omega) (by omega) (by rw [hcb]; exact hpar) (by omega)
      · rw [if_neg hp]
        intro hhp
        rcases ih (by omega) hhp with ⟨e0, el, he0l, helj, hpe0, hpel, hfb, hcb, hpr, hpb, hcr, hcb', hmem_acc⟩
        exact ⟨e0, el, he0l, by omega, hpe0, hpel, hfb, hcb, hpr, hpb,
          by simp only; rw [hcr]; split_ifs <;> omega, by simp only; rw [hcb']; split_ifs <;> omega, hmem_acc⟩
  -- Finish at j = 2*k!
  have hrc_eq : ((List.range (2 * k)).filter (fun e => decide (e % 2 = 0 ∧ xs e ≠ xs ((e + 1) % (2 * k))))).length =
      rCnt 0 (2 * k) := by
    dsimp only [rCnt, edgeM]; exact congrArg List.length (List.filter_congr fun e _ => by simp [bne_iff_ne])
  have hbc_eq : ((List.range (2 * k)).filter (fun e => decide (e % 2 = 1 ∧ xs e ≠ xs ((e + 1) % (2 * k))))).length =
      bCnt 0 (2 * k) := by
    dsimp only [bCnt, edgeM]; exact congrArg List.length (List.filter_congr fun e _ => by simp [bne_iff_ne])
  dsimp only
  rw [hrc_eq, hbc_eq]
  dsimp only [pureCycleSum]
  cases hhp : (prepLoop k pins bits (2 * k)).hasPin
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rcases (prepLoop_inv k pins bits (2 * k) le_rfl).2.1 hhp with ⟨hacc0, hcr, hcb, _⟩
    rw [hacc0, Sum8.comb_zero_left]
    rcases hseg_par 0 (2 * k) (Nat.zero_le _) le_rfl with ⟨hr, hb, hpar⟩
    rw [Nat.zero_mod, Nat.mod_self, Bool.xor_self] at hpar
    exact Sum8.mem_ofSeg_of_bounds (by omega) (by omega) (by omega) hpar (by omega)
  · simp only [↓reduceIte]
    rcases hloop (2 * k) le_rfl hhp with ⟨e0, el, he0l, helk, hpe0, hpel, hfb, hcb, hpr, hpb, hcr, hcb', hmem_acc⟩
    have hr_tot : rCnt 0 (2 * k) = rCnt e0 el + (rCnt el (2 * k) + rCnt 0 e0) := by
      have h1 := hrc_add 0 e0 (2 * k) (Nat.zero_le _) (by omega)
      have h2 := hrc_add e0 el (2 * k) he0l (by omega)
      omega
    have hb_tot : bCnt 0 (2 * k) = bCnt e0 el + (bCnt el (2 * k) + bCnt 0 e0) := by
      have h1 := hbc_add 0 e0 (2 * k) (Nat.zero_le _) (by omega)
      have h2 := hbc_add e0 el (2 * k) he0l (by omega)
      omega
    rw [hr_tot, hb_tot]
    apply Sum8.mem_comb_of_mem hmem_acc
    rcases hseg_par el (2 * k) (by omega) le_rfl with ⟨hr1, hb1, hp1⟩
    rcases hseg_par 0 e0 (Nat.zero_le _) (by omega) with ⟨hr2, hb2, hp2⟩
    rw [Nat.mod_eq_of_lt (a := el) helk, Nat.mod_self, hpin el helk hpel] at hp1
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (a := e0) (by omega), hpin e0 (by omega) hpe0] at hp2
    have hpar_wrap : (rCnt el (2 * k) + rCnt 0 e0 + (bCnt el (2 * k) + bCnt 0 e0)) % 2 =
        (xor (bits el) (bits e0)).toNat := by
      cases h0 : xs 0 <;> cases h1 : bits el <;> cases h2 : bits e0 <;>
        simp [h0, h1, h2] at hp1 hp2 ⊢ <;> omega
    refine Sum8.mem_ofSeg_of_bounds (by omega) (by omega) (by omega) ?_ (by omega)
    rw [hcb, hfb]; exact hpar_wrap

/-- Pure forward greedy walk on a cycle of length `2 * k` with `v_0` fixed to `a0`. -/
private structure WalkState where
  curX : Bool
  remR : ℕ
  remB : ℕ

private def walkStep (k : ℕ) (pins bits : ℕ → Bool) (a0 : Bool) (laterCyc : Sum8)
    (e : ℕ) (st : WalkState) : WalkState :=
  let er := if e % 2 = 0 then 1 else 0
  let eb := if e % 2 = 0 then 0 else 1
  let isLast := decide (e + 1 = 2 * k)
  let pNext := isLast || pins (e + 1)
  let bNext := if isLast then a0 else bits (e + 1)
  let take0 : Bool :=
    if pNext then st.curX == bNext
    else decide ((tailSum k pins bits a0 laterCyc (e + 1) st.curX).Mem st.remR st.remB)
  if take0 then ⟨st.curX, st.remR, st.remB⟩
  else ⟨!st.curX, st.remR - er, st.remB - eb⟩

private def walkLoop (k : ℕ) (pins bits : ℕ → Bool) (a0 : Bool) (laterCyc : Sum8)
    (remR0 remB0 : ℕ) : ℕ → WalkState
  | 0 => ⟨a0, remR0, remB0⟩
  | j + 1 => walkStep k pins bits a0 laterCyc j (walkLoop k pins bits a0 laterCyc remR0 remB0 j)

private lemma Sum8.mem_comb_one_red {s : Sum8} {r b : ℕ}
    (h : (Sum8.comb ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ s).Mem r b) :
    1 ≤ r ∧ s.Mem (r - 1) b := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  simp only [Sum8.comb, Nat.zero_add] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hsub : r - 1 - s.fr = r - (1 + s.fr) := by omega
  refine ⟨by omega, by omega, by omega, h3, h4, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hsub] <;> assumption

private lemma Sum8.mem_comb_one_blue {s : Sum8} {r b : ℕ}
    (h : (Sum8.comb ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ s).Mem r b) :
    1 ≤ b ∧ s.Mem r (b - 1) := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  simp only [Sum8.comb, Nat.zero_add] at h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hsub : b - 1 - s.fb = b - (1 + s.fb) := by omega
  refine ⟨by omega, h1, h2, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hsub] <;> assumption

private lemma walkLoop_spec {k : ℕ} (hk : 1 ≤ k) (pins bits : ℕ → Bool) (a0 : Bool)
    {laterCyc : Sum8} (hlat : laterCyc.Good) (remR0 remB0 : ℕ)
    (hpin0 : pins 0 = true → a0 = bits 0)
    (hinit : (tailSum k pins bits a0 laterCyc 0 a0).Mem remR0 remB0) :
    let xs := fun j => (walkLoop k pins bits a0 laterCyc remR0 remB0 j).curX
    let stEnd := walkLoop k pins bits a0 laterCyc remR0 remB0 (2 * k)
    (∀ j < 2 * k, pins j = true → xs j = bits j) ∧
    stEnd.curX = a0 ∧
    laterCyc.Mem stEnd.remR stEnd.remB ∧
    stEnd.remR ≤ remR0 ∧ stEnd.remB ≤ remB0 ∧
    remR0 - stEnd.remR =
      ((List.range (2 * k)).filter (fun e => decide (e % 2 = 0 ∧ xs e ≠ xs ((e + 1) % (2 * k))))).length ∧
    remB0 - stEnd.remB =
      ((List.range (2 * k)).filter (fun e => decide (e % 2 = 1 ∧ xs e ≠ xs ((e + 1) % (2 * k))))).length := by
  let xs := fun j => (walkLoop k pins bits a0 laterCyc remR0 remB0 j).curX
  have hinv : ∀ j ≤ 2 * k,
      let st := walkLoop k pins bits a0 laterCyc remR0 remB0 j
      (∀ t ≤ j, t < 2 * k → pins t = true → xs t = bits t) ∧
      (j < 2 * k → (tailSum k pins bits a0 laterCyc j st.curX).Mem st.remR st.remB) ∧
      (j = 2 * k → st.curX = a0 ∧ laterCyc.Mem st.remR st.remB) ∧
      st.remR ≤ remR0 ∧ st.remB ≤ remB0 ∧
      remR0 - st.remR = ((List.range j).filter (fun e => decide (e % 2 = 0 ∧ xs e ≠ xs (e + 1)))).length ∧
      remB0 - st.remB = ((List.range j).filter (fun e => decide (e % 2 = 1 ∧ xs e ≠ xs (e + 1)))).length := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun t ht _ hp => by rw [Nat.eq_zero_of_le_zero ht] at hp ⊢; exact hpin0 hp,
        fun _ => hinit, fun h => by omega, le_rfl, le_rfl, by simp [walkLoop], by simp [walkLoop]⟩
    | succ j ih =>
      intro hj
      rcases ih (by omega) with ⟨hp_prev, hmem_prev, _, hrle, hble, hrc, hbc⟩
      have hmem_j := hmem_prev (by omega)
      set st := walkLoop k pins bits a0 laterCyc remR0 remB0 j
      have hst_next : walkLoop k pins bits a0 laterCyc remR0 remB0 (j + 1) =
          walkStep k pins bits a0 laterCyc j st := rfl
      -- Compute the step invariant by cases on j + 1 = 2*k, pins (j + 1) = true, or unpinned!
      have hstep :
          (j + 1 < 2 * k → (pins (j + 1) = true → (walkStep k pins bits a0 laterCyc j st).curX = bits (j + 1)) ∧
            (tailSum k pins bits a0 laterCyc (j + 1) (walkStep k pins bits a0 laterCyc j st).curX).Mem
              (walkStep k pins bits a0 laterCyc j st).remR (walkStep k pins bits a0 laterCyc j st).remB) ∧
          (j + 1 = 2 * k → (walkStep k pins bits a0 laterCyc j st).curX = a0 ∧
            laterCyc.Mem (walkStep k pins bits a0 laterCyc j st).remR (walkStep k pins bits a0 laterCyc j st).remB) ∧
          (walkStep k pins bits a0 laterCyc j st).remR ≤ st.remR ∧
          (walkStep k pins bits a0 laterCyc j st).remB ≤ st.remB ∧
          st.remR - (walkStep k pins bits a0 laterCyc j st).remR =
            (if j % 2 = 0 ∧ st.curX ≠ (walkStep k pins bits a0 laterCyc j st).curX then 1 else 0) ∧
          st.remB - (walkStep k pins bits a0 laterCyc j st).remB =
            (if j % 2 = 1 ∧ st.curX ≠ (walkStep k pins bits a0 laterCyc j st).curX then 1 else 0) := by
        dsimp only [walkStep]
        by_cases hlast : j + 1 = 2 * k
        · have hj_eq : j = 2 * k - 1 := by omega
          have hj_odd : j % 2 = 1 := by omega
          have hj_ne0 : j % 2 ≠ 0 := by omega
          simp only [hlast, decide_true, Bool.true_or, ↓reduceIte, hj_ne0]
          dsimp only [tailSum] at hmem_j
          rw [hj_eq, backAt_last hk] at hmem_j
          dsimp only at hmem_j
          by_cases heq : st.curX = a0
          · have hbeq : (st.curX == a0) = true := by simp [heq]
            rw [if_pos hbeq]
            rw [heq, Bool.xor_self] at hmem_j
            have hof0 : Sum8.ofSeg 0 1 false = Sum8.zero := by unfold Sum8.ofSeg; rfl
            rw [hof0, Sum8.comb_zero_left] at hmem_j
            exact ⟨fun h => by omega, fun _ => ⟨heq, hmem_j⟩, le_rfl, le_rfl, by simp, by simp⟩
          · have hbeq : (st.curX == a0) = false := by cases hx : st.curX <;> cases ha : a0 <;> simp [hx, ha] at heq ⊢
            rw [if_neg (by simp [hbeq])]
            have hxor : xor st.curX a0 = true := by cases hx : st.curX <;> cases ha : a0 <;> simp [hx, ha] at heq ⊢
            have hnot : (!st.curX) = a0 := by cases hx : st.curX <;> cases ha : a0 <;> simp [hx, ha] at heq ⊢
            rw [hxor] at hmem_j
            have hof1 : Sum8.ofSeg 0 1 true = ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ := by unfold Sum8.ofSeg; rfl
            rw [hof1] at hmem_j
            have hmem' : 1 ≤ st.remB ∧ laterCyc.Mem st.remR (st.remB - 1) := Sum8.mem_comb_one_blue hmem_j
            have hne_not : st.curX ≠ !st.curX := by cases st.curX <;> decide
            exact ⟨fun h => by omega, fun _ => ⟨hnot, hmem'.2⟩, le_rfl, Nat.sub_le _ _,
              by simp [hj_ne0], by simp [hj_odd, hne_not]; omega⟩
        · have hjlt : j + 1 < 2 * k := by omega
          simp only [hlast, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
          dsimp only [tailSum] at hmem_j
          rw [backAt_eq_step pins bits a0 laterCyc hjlt] at hmem_j
          dsimp only [backStep] at hmem_j
          by_cases hpn : pins (j + 1) = true
          · simp only [hpn, ↓reduceIte] at hmem_j ⊢
            by_cases heq : st.curX = bits (j + 1)
            · have hbeq : (st.curX == bits (j + 1)) = true := by simp [heq]
              rw [if_pos hbeq]
              rw [heq, Bool.xor_self] at hmem_j
              have hof0 : Sum8.ofSeg (if j % 2 = 0 then 1 else 0) (if j % 2 = 0 then 0 else 1) false = Sum8.zero := by
                split_ifs <;> unfold Sum8.ofSeg <;> rfl
              rw [hof0, Sum8.comb_zero_left] at hmem_j
              exact ⟨fun _ => ⟨fun _ => heq, by dsimp only [tailSum]; rw [heq]; exact hmem_j⟩,
                fun h => False.elim h, le_rfl, le_rfl, by simp, by simp⟩
            · have hbeq : (st.curX == bits (j + 1)) = false := by
                cases hx : st.curX <;> cases hb : bits (j + 1) <;> simp [hx, hb] at heq ⊢
              rw [if_neg (by simp [hbeq])]
              have hxor : xor st.curX (bits (j + 1)) = true := by
                cases hx : st.curX <;> cases hb : bits (j + 1) <;> simp [hx, hb] at heq ⊢
              have hnot : (!st.curX) = bits (j + 1) := by
                cases hx : st.curX <;> cases hb : bits (j + 1) <;> simp [hx, hb] at heq ⊢
              rw [hxor] at hmem_j
              have hne_not : st.curX ≠ !st.curX := by cases st.curX <;> decide
              by_cases hpar : j % 2 = 0
              · simp only [hpar, ↓reduceIte] at hmem_j ⊢
                have hof1 : Sum8.ofSeg 1 0 true = ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ := by unfold Sum8.ofSeg; rfl
                rw [hof1] at hmem_j
                have hmem' : 1 ≤ st.remR ∧
                    (tailSum k pins bits a0 laterCyc (j + 1) (bits (j + 1))).Mem (st.remR - 1) st.remB :=
                  Sum8.mem_comb_one_red hmem_j
                exact ⟨fun _ => ⟨fun _ => hnot, by rw [hnot]; exact hmem'.2⟩,
                  fun h => False.elim h, Nat.sub_le _ _, le_rfl,
                  by simp [hpar, hne_not]; omega, by simp [show j % 2 ≠ 1 by omega]⟩
              · have hodd : j % 2 = 1 := by omega
                simp only [hpar, ↓reduceIte] at hmem_j ⊢
                have hof1 : Sum8.ofSeg 0 1 true = ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ := by unfold Sum8.ofSeg; rfl
                rw [hof1] at hmem_j
                have hmem' : 1 ≤ st.remB ∧
                    (tailSum k pins bits a0 laterCyc (j + 1) (bits (j + 1))).Mem st.remR (st.remB - 1) :=
                  Sum8.mem_comb_one_blue hmem_j
                exact ⟨fun _ => ⟨fun _ => hnot, by rw [hnot]; exact hmem'.2⟩,
                  fun h => False.elim h, le_rfl, Nat.sub_le _ _,
                  by simp [hpar], by simp [hodd, hne_not]; omega⟩
          · -- j + 1 is UNPINNED: use mem_peel_red / mem_peel_blue!
            have hpnf : pins (j + 1) = false := Bool.eq_false_iff.mpr hpn
            simp only [hpnf, Bool.false_eq_true, ↓reduceIte] at hmem_j ⊢
            by_cases htk0 : (tailSum k pins bits a0 laterCyc (j + 1) st.curX).Mem st.remR st.remB
            · simp only [htk0, decide_true, ↓reduceIte]
              exact ⟨fun _ => ⟨False.elim, trivial⟩, fun h => False.elim h,
                le_rfl, le_rfl, by simp, by simp⟩
            · simp only [htk0, decide_false, Bool.false_eq_true, ↓reduceIte]
              have halt := backAt_rem_alt hk pins bits a0 laterCyc hlat (2 * k - (j + 1)) (by omega) (by omega)
              rw [show 2 * k - (2 * k - (j + 1)) = j + 1 by omega] at halt
              rcases halt with ⟨hgN, _, hevN, hodN, _⟩
              have hne_not : st.curX ≠ !st.curX := by cases st.curX <;> decide
              by_cases hpar : j % 2 = 0
              · have hparN : (j + 1) % 2 = 1 := by omega
                have hN := hodN hparN
                simp only [hpar, ↓reduceIte] at hmem_j ⊢
                have hpeel := Sum8.mem_peel_red hgN (R := (backAt k pins bits a0 laterCyc (j + 1)).remR + 1)
                  (B := (backAt k pins bits a0 laterCyc (j + 1)).remB) (by omega) (by omega) (by omega) hmem_j
                rw [Nat.add_sub_cancel] at hpeel
                rcases hpeel with h0 | ⟨hr1, h1⟩
                · exact absurd h0 htk0
                · have hxor_not : (!(xor st.curX (backAt k pins bits a0 laterCyc (j + 1)).nxtBit)) =
                      xor (!st.curX) (backAt k pins bits a0 laterCyc (j + 1)).nxtBit := by
                    cases st.curX <;> cases (backAt k pins bits a0 laterCyc (j + 1)).nxtBit <;> rfl
                  rw [hxor_not] at h1
                  exact ⟨fun _ => ⟨False.elim, h1⟩, fun h => False.elim h,
                    Nat.sub_le _ _, le_rfl, by simp [hpar, hne_not]; omega, by simp [show j % 2 ≠ 1 by omega]⟩
              · have hodd : j % 2 = 1 := by omega
                have hparN : (j + 1) % 2 = 0 := by omega
                have hN := hevN hparN
                simp only [hpar, ↓reduceIte] at hmem_j ⊢
                have hpeel := Sum8.mem_peel_blue hgN (R := (backAt k pins bits a0 laterCyc (j + 1)).remR)
                  (B := (backAt k pins bits a0 laterCyc (j + 1)).remB + 1) (by omega) (by omega) (by omega) hmem_j
                rw [Nat.add_sub_cancel] at hpeel
                rcases hpeel with h0 | ⟨hb1, h1⟩
                · exact absurd h0 htk0
                · have hxor_not : (!(xor st.curX (backAt k pins bits a0 laterCyc (j + 1)).nxtBit)) =
                      xor (!st.curX) (backAt k pins bits a0 laterCyc (j + 1)).nxtBit := by
                    cases st.curX <;> cases (backAt k pins bits a0 laterCyc (j + 1)).nxtBit <;> rfl
                  rw [hxor_not] at h1
                  exact ⟨fun _ => ⟨False.elim, h1⟩, fun h => False.elim h,
                    le_rfl, Nat.sub_le _ _, by simp [hpar], by simp [hodd, hne_not]; omega⟩
      rcases hstep with ⟨hs1, hs2, hsr, hsb, hsdr, hsdb⟩
      refine ⟨?_, fun hlt => (hs1 hlt).2, hs2, le_trans hsr hrle, le_trans hsb hble, ?_, ?_⟩
      · intro t ht htk hp
        by_cases hteq : t = j + 1
        · subst hteq; exact (hs1 htk).1 hp
        · exact hp_prev t (by omega) htk hp
      · rw [List.range_succ, List.filter_append, List.length_append, ← hrc]
        rw [hst_next]
        have : ([j].filter (fun e => decide (e % 2 = 0 ∧ xs e ≠ xs (e + 1)))).length =
            if j % 2 = 0 ∧ st.curX ≠ (walkStep k pins bits a0 laterCyc j st).curX then 1 else 0 := by
          dsimp only [xs]
          by_cases h : j % 2 = 0 ∧ st.curX ≠ (walkStep k pins bits a0 laterCyc j st).curX <;>
            simp [h, walkLoop, st]
        rw [this]; omega
      · rw [List.range_succ, List.filter_append, List.length_append, ← hbc]
        rw [hst_next]
        have : ([j].filter (fun e => decide (e % 2 = 1 ∧ xs e ≠ xs (e + 1)))).length =
            if j % 2 = 1 ∧ st.curX ≠ (walkStep k pins bits a0 laterCyc j st).curX then 1 else 0 := by
          dsimp only [xs]
          by_cases h : j % 2 = 1 ∧ st.curX ≠ (walkStep k pins bits a0 laterCyc j st).curX <;>
            simp [h, walkLoop, st]
        rw [this]; omega
  rcases hinv (2 * k) le_rfl with ⟨hp, _, hfin, hrle, hble, hrc, hbc⟩
  rcases hfin rfl with ⟨hxa0, hlatm⟩
  have hxs_wrap : ∀ e ∈ List.range (2 * k), xs ((e + 1) % (2 * k)) = xs (e + 1) := by
    intro e he; rw [List.mem_range] at he
    by_cases hlast : e + 1 = 2 * k
    · rw [hlast, Nat.mod_self]; exact hxa0.symm
    · rw [Nat.mod_eq_of_lt (by omega)]
  dsimp only [xs] at hxs_wrap
  refine ⟨fun j hj => hp j (by omega) hj, hxa0, hlatm, hrle, hble, ?_, ?_⟩
  · rw [hrc]; congr 1
    refine List.filter_congr fun e he => by dsimp only [xs]; simp only [hxs_wrap e he]
  · rw [hbc]; congr 1
    refine List.filter_congr fun e he => by dsimp only [xs]; simp only [hxs_wrap e he]

/-!
## Part 3: Fan-in-2 Boolean circuit builder and `W`-bit unsigned arithmetic combinators
-/

private def GateOK (gate : Gate) : Prop :=
  ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
    (gate.op = .not ∧ gate.inputs.length = 1)

private def ValidG (nin : ℕ) (g : List Gate) : Prop :=
  ReadsBack nin ⟨g, 0⟩ ∧ ∀ gate ∈ g, GateOK gate

private def evalW (g : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk g 0).wires x

private def valAt (g : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (evalW g x).getD w false

private def GExt (g g' : List Gate) : Prop :=
  ∃ suf, g' = g ++ suf

private structure Ctx (nin : ℕ) (x : List Bool) : Prop where
  hlen : x.length = nin
  hnin : 2 ≤ nin
  h0 : x.getD 0 false = false
  h1 : x.getD 1 false = true

private lemma gExt_refl (g : List Gate) : GExt g g := ⟨[], (List.append_nil g).symm⟩

private lemma gExt_trans {g1 g2 g3 : List Gate} (h12 : GExt g1 g2) (h23 : GExt g2 g3) :
    GExt g1 g3 := by
  rcases h12 with ⟨s1, rfl⟩; rcases h23 with ⟨s2, rfl⟩
  exact ⟨s1 ++ s2, List.append_assoc _ _ _⟩

private lemma gExt_len_le {g g' : List Gate} (h : GExt g g') : g.length ≤ g'.length := by
  rcases h with ⟨s, rfl⟩; simp

private lemma evalW_append (g1 g2 : List Gate) (x : List Bool) :
    evalW (g1 ++ g2) x = evalW g2 (evalW g1 x) := by
  unfold evalW Circuit.wires; exact List.foldl_append

private lemma evalW_length (g : List Gate) (x : List Bool) :
    (evalW g x).length = x.length + g.length := by
  induction g generalizing x with
  | nil => simp [evalW, Circuit.wires]
  | cons hd tl ih =>
    unfold evalW Circuit.wires at ih ⊢
    simp only [List.foldl_cons]
    rw [ih]; simp; omega

private lemma evalW_prefix (g : List Gate) (x : List Bool) :
    ∃ suf, evalW g x = x ++ suf := by
  induction g generalizing x with
  | nil => exact ⟨[], by simp [evalW, Circuit.wires]⟩
  | cons hd tl ih =>
    unfold evalW Circuit.wires at ih ⊢
    simp only [List.foldl_cons]
    rcases ih (x ++ [hd.op.eval (hd.inputs.map fun i => x.getD i false)]) with ⟨s, hs⟩
    exact ⟨[hd.op.eval (hd.inputs.map fun i => x.getD i false)] ++ s, by rw [hs, List.append_assoc]⟩

private lemma valAt_ext {nin : ℕ} {g g' : List Gate} {x : List Bool}
    (hx : x.length = nin) (hext : GExt g g') {i : ℕ} (hi : i < nin + g.length) :
    valAt g' x i = valAt g x i := by
  rcases hext with ⟨suf, rfl⟩
  unfold valAt
  rw [evalW_append]
  rcases evalW_prefix suf (evalW g x) with ⟨s, hs⟩
  rw [hs]
  have hlen : (evalW g x).length = nin + g.length := by rw [evalW_length, hx]
  have hi' : i < (evalW g x).length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']

private lemma valAt_zero {nin : ℕ} {g : List Gate} {x : List Bool} (hx : Ctx nin x) :
    valAt g x 0 = false := by
  have h := valAt_ext hx.hlen ⟨g, (List.nil_append g).symm⟩ (i := 0) (by have := hx.hnin; omega)
  rw [h]; unfold valAt evalW Circuit.wires; exact hx.h0

private lemma valAt_one {nin : ℕ} {g : List Gate} {x : List Bool} (hx : Ctx nin x) :
    valAt g x 1 = true := by
  have h := valAt_ext hx.hlen ⟨g, (List.nil_append g).symm⟩ (i := 1) (by have := hx.hnin; omega)
  rw [h]; unfold valAt evalW Circuit.wires; exact hx.h1

private lemma validG_nil (nin : ℕ) : ValidG nin [] := by
  refine ⟨fun j hj => by simp at hj, fun _ h => by simp at h⟩

private lemma validG_snoc {nin : ℕ} {g : List Gate} (hv : ValidG nin g) (gate : Gate)
    (hgate : GateOK gate) (hins : ∀ i ∈ gate.inputs, i < nin + g.length) :
    ValidG nin (g ++ [gate]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    unfold gateAt at hi
    by_cases hlt : j < g.length
    · have hget : (g ++ [gate]).getD j ⟨.or, []⟩ = g.getD j ⟨.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hv.1 j hlt i hi
    · have hj_eq : j = g.length := by omega
      subst hj_eq
      have hget : (g ++ [gate]).getD g.length ⟨.or, []⟩ = gate := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hins i hi
  · intro gt hgt
    rw [List.mem_append, List.mem_singleton] at hgt
    rcases hgt with h | rfl
    · exact hv.2 gt h
    · exact hgate

private def emitNot (nin : ℕ) (g : List Gate) (a : ℕ) : List Gate × ℕ :=
  (g ++ [⟨.not, [min a (nin + g.length - 1)]⟩], nin + g.length)

private def emitAnd (nin : ℕ) (g : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (g ++ [⟨.and, [min a (nin + g.length - 1), min b (nin + g.length - 1)]⟩], nin + g.length)

private def emitOr (nin : ℕ) (g : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (g ++ [⟨.or, [min a (nin + g.length - 1), min b (nin + g.length - 1)]⟩], nin + g.length)

private lemma emitNot_spec {nin : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a : ℕ} (ha : a < nin + g.length) :
    let res := emitNot nin g a
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 1 ∧
    res.2 < nin + res.1.length ∧ valAt res.1 x res.2 = !(valAt g x a) := by
  have hnin := hx.hnin
  dsimp only [emitNot]
  refine ⟨⟨_, rfl⟩, validG_snoc hv _ (Or.inr ⟨rfl, rfl⟩) (by intro i hi; simp at hi; omega),
    by simp, by simp, ?_⟩
  have hlen : (evalW g x).length = nin + g.length := by rw [evalW_length, hx.hlen]
  have hmin : min a (nin + g.length - 1) = a := by omega
  have hev : evalW (g ++ [⟨.not, [min a (nin + g.length - 1)]⟩]) x = evalW g x ++ [!valAt g x a] := by
    rw [evalW_append]; unfold valAt
    change List.foldl _ (evalW g x) _ = _
    simp [hmin, GateOp.eval]
  unfold valAt; rw [hev, List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl

private lemma emitAnd_spec {nin : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : ℕ}
    (ha : a < nin + g.length) (hb : b < nin + g.length) :
    let res := emitAnd nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 1 ∧
    res.2 < nin + res.1.length ∧ valAt res.1 x res.2 = (valAt g x a && valAt g x b) := by
  have hnin := hx.hnin
  dsimp only [emitAnd]
  refine ⟨⟨_, rfl⟩, validG_snoc hv _ (Or.inl ⟨Or.inl rfl, rfl⟩)
    (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega),
    by simp, by simp, ?_⟩
  have hlen : (evalW g x).length = nin + g.length := by rw [evalW_length, hx.hlen]
  have hma : min a (nin + g.length - 1) = a := by omega
  have hmb : min b (nin + g.length - 1) = b := by omega
  have hev : evalW (g ++ [⟨.and, [min a (nin + g.length - 1), min b (nin + g.length - 1)]⟩]) x =
      evalW g x ++ [valAt g x a && valAt g x b] := by
    rw [evalW_append]; unfold valAt
    change List.foldl _ (evalW g x) _ = _
    simp [hma, hmb, GateOp.eval]
  unfold valAt; rw [hev, List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl

private lemma emitOr_spec {nin : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : ℕ}
    (ha : a < nin + g.length) (hb : b < nin + g.length) :
    let res := emitOr nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 1 ∧
    res.2 < nin + res.1.length ∧ valAt res.1 x res.2 = (valAt g x a || valAt g x b) := by
  have hnin := hx.hnin
  dsimp only [emitOr]
  refine ⟨⟨_, rfl⟩, validG_snoc hv _ (Or.inl ⟨Or.inr rfl, rfl⟩)
    (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega),
    by simp, by simp, ?_⟩
  have hlen : (evalW g x).length = nin + g.length := by rw [evalW_length, hx.hlen]
  have hma : min a (nin + g.length - 1) = a := by omega
  have hmb : min b (nin + g.length - 1) = b := by omega
  have hev : evalW (g ++ [⟨.or, [min a (nin + g.length - 1), min b (nin + g.length - 1)]⟩]) x =
      evalW g x ++ [valAt g x a || valAt g x b] := by
    rw [evalW_append]; unfold valAt
    change List.foldl _ (evalW g x) _ = _
    simp [hma, hmb, GateOp.eval]
  unfold valAt; rw [hev, List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right le_rfl, Nat.sub_self]; rfl

private def cXor (nin : ℕ) (g : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let (g1, o) := emitOr nin g a b
  let (g2, an) := emitAnd nin g1 a b
  let (g3, nan) := emitNot nin g2 an
  emitAnd nin g3 o nan

private lemma cXor_spec {nin : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : ℕ}
    (ha : a < nin + g.length) (hb : b < nin + g.length) :
    let res := cXor nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 4 ∧
    res.2 < nin + res.1.length ∧ valAt res.1 x res.2 = xor (valAt g x a) (valAt g x b) := by
  dsimp only [cXor]
  have h1 := emitOr_spec hx hv ha hb
  dsimp only at h1
  set g1 := (emitOr nin g a b).1; set o := (emitOr nin g a b).2
  have h2 := emitAnd_spec (a := a) (b := b) hx h1.2.1 (by omega) (by omega)
  dsimp only at h2
  set g2 := (emitAnd nin g1 a b).1; set an := (emitAnd nin g1 a b).2
  have h3 := emitNot_spec hx h2.2.1 h2.2.2.2.1
  dsimp only at h3
  set g3 := (emitNot nin g2 an).1; set nan := (emitNot nin g2 an).2
  have h4 := emitAnd_spec (a := o) hx h3.2.1 (by omega) h3.2.2.2.1
  dsimp only at h4
  refine ⟨gExt_trans h1.1 (gExt_trans h2.1 (gExt_trans h3.1 h4.1)), h4.2.1,
    by omega, h4.2.2.2.1, ?_⟩
  rw [h4.2.2.2.2, valAt_ext hx.hlen (gExt_trans h2.1 h3.1) h1.2.2.2.1, h1.2.2.2.2,
    h3.2.2.2.2, h2.2.2.2.2, valAt_ext hx.hlen h1.1 ha, valAt_ext hx.hlen h1.1 hb]
  cases valAt g x a <;> cases valAt g x b <;> rfl

private def cEqBit (nin : ℕ) (g : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let (g1, xr) := cXor nin g a b
  emitNot nin g1 xr

private lemma cEqBit_spec {nin : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : ℕ}
    (ha : a < nin + g.length) (hb : b < nin + g.length) :
    let res := cEqBit nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 5 ∧
    res.2 < nin + res.1.length ∧ valAt res.1 x res.2 = (valAt g x a == valAt g x b) := by
  dsimp only [cEqBit]
  have h1 := cXor_spec hx hv ha hb
  dsimp only at h1
  have h2 := emitNot_spec hx h1.2.1 h1.2.2.2.1
  dsimp only at h2
  refine ⟨gExt_trans h1.1 h2.1, h2.2.1, by omega, h2.2.2.2.1, ?_⟩
  rw [h2.2.2.2.2, h1.2.2.2.2]
  cases valAt g x a <;> cases valAt g x b <;> rfl

private def cMux (nin : ℕ) (g : List Gate) (sel t f : ℕ) : List Gate × ℕ :=
  let (g1, ns) := emitNot nin g sel
  let (g2, a1) := emitAnd nin g1 sel t
  let (g3, a2) := emitAnd nin g2 ns f
  emitOr nin g3 a1 a2

private lemma cMux_spec {nin : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {sel t f : ℕ}
    (hs : sel < nin + g.length) (ht : t < nin + g.length) (hf : f < nin + g.length) :
    let res := cMux nin g sel t f
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 4 ∧
    res.2 < nin + res.1.length ∧
    valAt res.1 x res.2 = (if valAt g x sel then valAt g x t else valAt g x f) := by
  dsimp only [cMux]
  have h1 := emitNot_spec hx hv hs
  dsimp only at h1
  set g1 := (emitNot nin g sel).1; set ns := (emitNot nin g sel).2
  have h2 := emitAnd_spec (a := sel) (b := t) hx h1.2.1 (by omega) (by omega)
  dsimp only at h2
  set g2 := (emitAnd nin g1 sel t).1; set a1 := (emitAnd nin g1 sel t).2
  have h3 := emitAnd_spec (a := ns) (b := f) hx h2.2.1 (by omega) (by omega)
  dsimp only at h3
  set g3 := (emitAnd nin g2 ns f).1; set a2 := (emitAnd nin g2 ns f).2
  have h4 := emitOr_spec (a := a1) hx h3.2.1 (by omega) h3.2.2.2.1
  dsimp only at h4
  refine ⟨gExt_trans h1.1 (gExt_trans h2.1 (gExt_trans h3.1 h4.1)), h4.2.1,
    by omega, h4.2.2.2.1, ?_⟩
  rw [h4.2.2.2.2, valAt_ext hx.hlen h3.1 h2.2.2.2.1, h2.2.2.2.2,
    valAt_ext hx.hlen h1.1 hs, valAt_ext hx.hlen h1.1 ht,
    h3.2.2.2.2, valAt_ext hx.hlen h2.1 h1.2.2.2.1, h1.2.2.2.2,
    valAt_ext hx.hlen (gExt_trans h1.1 h2.1) hf]
  cases valAt g x sel <;> cases valAt g x t <;> cases valAt g x f <;> rfl

private def cFullAdd (nin : ℕ) (g : List Gate) (a b cin : ℕ) : List Gate × ℕ × ℕ :=
  let (g1, s1) := cXor nin g a b
  let (g2, sum) := cXor nin g1 s1 cin
  let (g3, c1) := emitAnd nin g2 a b
  let (g4, c2) := emitAnd nin g3 s1 cin
  let (g5, cout) := emitOr nin g4 c1 c2
  (g5, sum, cout)

private lemma cFullAdd_spec {nin : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b cin : ℕ}
    (ha : a < nin + g.length) (hb : b < nin + g.length) (hc : cin < nin + g.length) :
    let res := cFullAdd nin g a b cin
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 11 ∧
    res.2.1 < nin + res.1.length ∧ res.2.2 < nin + res.1.length ∧
    (valAt res.1 x res.2.1).toNat + 2 * (valAt res.1 x res.2.2).toNat =
      (valAt g x a).toNat + (valAt g x b).toNat + (valAt g x cin).toNat := by
  dsimp only [cFullAdd]
  have h1 := cXor_spec hx hv ha hb
  dsimp only at h1
  set g1 := (cXor nin g a b).1; set s1 := (cXor nin g a b).2
  have h2 := cXor_spec (a := s1) (b := cin) hx h1.2.1 h1.2.2.2.1 (by omega)
  dsimp only at h2
  set g2 := (cXor nin g1 s1 cin).1; set sm := (cXor nin g1 s1 cin).2
  have h3 := emitAnd_spec (a := a) (b := b) hx h2.2.1 (by omega) (by omega)
  dsimp only at h3
  set g3 := (emitAnd nin g2 a b).1; set c1 := (emitAnd nin g2 a b).2
  have h4 := emitAnd_spec (a := s1) (b := cin) hx h3.2.1 (by omega) (by omega)
  dsimp only at h4
  set g4 := (emitAnd nin g3 s1 cin).1; set c2 := (emitAnd nin g3 s1 cin).2
  have h5 := emitOr_spec (a := c1) hx h4.2.1 (by omega) h4.2.2.2.1
  dsimp only at h5
  refine ⟨gExt_trans h1.1 (gExt_trans h2.1 (gExt_trans h3.1 (gExt_trans h4.1 h5.1))), h5.2.1,
    by omega, by omega, h5.2.2.2.1, ?_⟩
  rw [valAt_ext hx.hlen (gExt_trans h3.1 (gExt_trans h4.1 h5.1)) h2.2.2.2.1, h2.2.2.2.2,
    h1.2.2.2.2, valAt_ext hx.hlen h1.1 hc,
    h5.2.2.2.2, valAt_ext hx.hlen h4.1 h3.2.2.2.1, h3.2.2.2.2,
    valAt_ext hx.hlen (gExt_trans h1.1 h2.1) ha, valAt_ext hx.hlen (gExt_trans h1.1 h2.1) hb,
    h4.2.2.2.2, valAt_ext hx.hlen (gExt_trans h2.1 h3.1) h1.2.2.2.1, h1.2.2.2.2,
    valAt_ext hx.hlen (gExt_trans h1.1 (gExt_trans h2.1 h3.1)) hc]
  cases valAt g x a <;> cases valAt g x b <;> cases valAt g x cin <;> decide

/-! ### `W`-bit unsigned words -/

private abbrev Word (W : ℕ) := Fin W → ℕ

private def WordIn (bound : ℕ) {W : ℕ} (a : Word W) : Prop :=
  ∀ i : Fin W, a i < bound

private lemma wordIn_mono {b1 b2 : ℕ} {W : ℕ} {a : Word W} (hle : b1 ≤ b2) (ha : WordIn b1 a) :
    WordIn b2 a := fun i => lt_of_lt_of_le (ha i) hle

private def wordVal {W : ℕ} (g : List Gate) (x : List Bool) (a : Word W) : ℕ :=
  ∑ i : Fin W, (valAt g x (a i)).toNat * 2 ^ i.val

private lemma wordVal_ext {nin W : ℕ} {g g' : List Gate} {x : List Bool}
    (hx : x.length = nin) (hext : GExt g g') {a : Word W} (ha : WordIn (nin + g.length) a) :
    wordVal g' x a = wordVal g x a := by
  unfold wordVal
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [valAt_ext hx hext (ha i)]

private lemma wordVal_lt {W : ℕ} (g : List Gate) (x : List Bool) (a : Word W) :
    wordVal g x a < 2 ^ W := by
  unfold wordVal
  induction W with
  | zero => simp
  | succ W ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun i : Fin W => a i.castSucc)
    have h2 : (valAt g x (a (Fin.last W))).toNat ≤ 1 := by cases valAt g x (a (Fin.last W)) <;> decide
    have h3 : (valAt g x (a (Fin.last W))).toNat * 2 ^ W ≤ 2 ^ W := by
      simpa using Nat.mul_le_mul_right (2 ^ W) h2
    simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢
    rw [pow_succ]; omega

private lemma wordVal_mod_two {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (x : List Bool) (a : Word W) :
    wordVal g x a % 2 = (valAt g x (a ⟨0, hW⟩)).toNat := by
  unfold wordVal
  have hsplit : (∑ i : Fin W, (valAt g x (a i)).toNat * 2 ^ i.val) =
      (valAt g x (a ⟨0, hW⟩)).toNat +
      ∑ i ∈ Finset.univ.erase ⟨0, hW⟩, (valAt g x (a i)).toNat * 2 ^ i.val := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hW⟩)]
    simp
  rw [hsplit]
  have heven : 2 ∣ ∑ i ∈ Finset.univ.erase ⟨0, hW⟩, (valAt g x (a i)).toNat * 2 ^ i.val := by
    refine Finset.dvd_sum fun i hi => ?_
    have hne : i.val ≠ 0 := fun h => (Finset.ne_of_mem_erase hi) (Fin.ext h)
    have hpow : 2 ∣ 2 ^ i.val := by
      rw [show i.val = (i.val - 1) + 1 by omega, pow_succ]; exact dvd_mul_left 2 _
    exact dvd_mul_of_dvd_right hpow _
  rcases heven with ⟨k, hk⟩
  rw [hk]
  cases valAt g x (a ⟨0, hW⟩) <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

private def cConst0 (W : ℕ) : Word W := fun _ => 0

private def cConstBit (W : ℕ) (b : ℕ) : Word W := fun i => if i.val = 0 then b else 0

private lemma cConst0_spec {nin W : ℕ} {g : List Gate} {x : List Bool} (hx : Ctx nin x) :
    WordIn (nin + g.length) (cConst0 W) ∧ wordVal g x (cConst0 W) = 0 := by
  have hnin := hx.hnin
  refine ⟨fun _ => by dsimp [cConst0]; omega, ?_⟩
  unfold wordVal cConst0
  simp [valAt_zero hx]

private lemma cConstBit_spec {nin W : ℕ} (hW : 1 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) {b : ℕ} (hb : b < nin + g.length) :
    WordIn (nin + g.length) (cConstBit W b) ∧
    wordVal g x (cConstBit W b) = (valAt g x b).toNat := by
  have hnin := hx.hnin
  refine ⟨fun i => by dsimp [cConstBit]; split_ifs <;> omega, ?_⟩
  unfold wordVal cConstBit
  rw [Finset.sum_eq_single ⟨0, hW⟩]
  · simp
  · intro i _ hne
    have hne' : i.val ≠ 0 := fun h => hne (Fin.ext h)
    simp [hne', valAt_zero hx]
  · intro h; exact absurd (Finset.mem_univ _) h

private def cPadW {w W : ℕ} (a : Word w) : Word W :=
  fun i => if h : i.val < w then a ⟨i.val, h⟩ else 0

private def cTruncW {w W : ℕ} (hw : w ≤ W) (a : Word W) : Word w :=
  fun i => a ⟨i.val, by omega⟩

private lemma cPadW_spec {nin w W : ℕ} (hw : w ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) {a : Word w} (ha : WordIn (nin + g.length) a) :
    WordIn (nin + g.length) (cPadW (W := W) a) ∧
    wordVal g x (cPadW (W := W) a) = wordVal g x a := by
  have hnin := hx.hnin
  refine ⟨fun i => by
    dsimp [cPadW]
    split_ifs with h
    · exact ha _
    · omega, ?_⟩
  unfold wordVal cPadW
  rw [← Finset.sum_subset (s₁ := (Finset.univ : Finset (Fin w)).image (fun i : Fin w => (⟨i.val, by omega⟩ : Fin W)))
    (Finset.subset_univ _)]
  · rw [Finset.sum_image (fun i _ j _ h => Fin.ext (by simpa using congrArg Fin.val h))]
    refine Finset.sum_congr rfl fun i _ => by simp
  · intro i _ hni
    have hge : ¬ i.val < w := by
      intro hlt
      exact hni (Finset.mem_image.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    simp [hge, valAt_zero hx]

private lemma cTruncW_spec {w W : ℕ} (hw : w ≤ W) (g : List Gate) (x : List Bool)
    (a : Word W) (hlt : wordVal g x a < 2 ^ w) :
    wordVal g x (cTruncW hw a) = wordVal g x a := by
  unfold wordVal at hlt ⊢; unfold cTruncW
  have hzero : ∀ i : Fin W, w ≤ i.val → valAt g x (a i) = false := by
    intro i hi
    by_contra hne
    have htr : valAt g x (a i) = true := by cases hv : valAt g x (a i) <;> simp [hv] at hne ⊢
    have hge : 2 ^ i.val ≤ ∑ j : Fin W, (valAt g x (a j)).toNat * 2 ^ j.val := by
      calc 2 ^ i.val = (valAt g x (a i)).toNat * 2 ^ i.val := by simp [htr]
        _ ≤ _ := Finset.single_le_sum (f := fun j : Fin W => (valAt g x (a j)).toNat * 2 ^ j.val)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hpow : 2 ^ w ≤ 2 ^ i.val := Nat.pow_le_pow_right (by decide) hi
    omega
  rw [← Finset.sum_subset (s₁ := (Finset.univ : Finset (Fin w)).image (fun i : Fin w => (⟨i.val, by omega⟩ : Fin W)))
    (Finset.subset_univ _)]
  · rw [Finset.sum_image (fun i _ j _ h => Fin.ext (by simpa using congrArg Fin.val h))]
  · intro i _ hni
    have hge : w ≤ i.val := by
      by_contra hlt'
      exact hni (Finset.mem_image.mpr ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    simp [hzero i hge]

/-- `cNotW`: bitwise NOT of a `W`-bit word (`W` gates). -/
private def cNotWAux (nin : ℕ) : ∀ (k : ℕ), List Gate → (Fin k → ℕ) → List Gate × (Fin k → ℕ)
  | 0, g, _ => (g, Fin.elim0)
  | k + 1, g, a =>
    let (g1, lo) := cNotWAux nin k g (fun i => a i.castSucc)
    let (g2, hi) := emitNot nin g1 (a (Fin.last k))
    (g2, Fin.snoc lo hi)

private def cNotW (nin : ℕ) {W : ℕ} (g : List Gate) (a : Word W) : List Gate × Word W :=
  cNotWAux nin W g a

private lemma cNotW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a : Word W} (ha : WordIn (nin + g.length) a) :
    let res := cNotW nin g a
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + W ∧
    WordIn (nin + res.1.length) res.2 ∧
    wordVal res.1 x res.2 + wordVal g x a + 1 = 2 ^ W := by
  unfold cNotW
  induction W generalizing g with
  | zero =>
    dsimp only [cNotWAux]
    refine ⟨gExt_refl g, hv, by simp, fun i => i.elim0, by simp [wordVal]⟩
  | succ W ih =>
    dsimp only [cNotWAux]
    have h1 := ih hv (fun i : Fin W => ha i.castSucc)
    dsimp only at h1
    set g1 := (cNotWAux nin W g (fun i => a i.castSucc)).1
    set lo := (cNotWAux nin W g (fun i => a i.castSucc)).2
    have h2 := emitNot_spec (a := (a (Fin.last W))) hx h1.2.1 (by have := ha (Fin.last W); omega)
    dsimp only at h2
    set g2 := (emitNot nin g1 (a (Fin.last W))).1
    set hi := (emitNot nin g1 (a (Fin.last W))).2
    refine ⟨gExt_trans h1.1 h2.1, h2.2.1, by omega, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc_last, h2.2.2.2.1]
      · intro j; simp only [Fin.snoc_castSucc]; have := h1.2.2.2.1 j; omega
    · unfold wordVal at h1 ⊢
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
      have hlo_eq : (∑ i : Fin W, (valAt g2 x (lo i)).toNat * 2 ^ i.val) =
          ∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val :=
        Finset.sum_congr rfl fun i _ => by rw [valAt_ext hx.hlen h2.1 (h1.2.2.2.1 i)]
      rw [hlo_eq, h2.2.2.2.2, valAt_ext hx.hlen h1.1 (ha (Fin.last W))]
      have hbit : (!(valAt g x (a (Fin.last W)))).toNat + (valAt g x (a (Fin.last W))).toNat = 1 := by
        cases valAt g x (a (Fin.last W)) <;> decide
      have hsum_lo : (∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val) +
          (∑ i : Fin W, (valAt g x (a i.castSucc)).toNat * 2 ^ i.val) + 1 = 2 ^ W := h1.2.2.2.2
      calc (∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val) + (!(valAt g x (a (Fin.last W)))).toNat * 2 ^ W +
            ((∑ i : Fin W, (valAt g x (a i.castSucc)).toNat * 2 ^ i.val) + (valAt g x (a (Fin.last W))).toNat * 2 ^ W) + 1
          = ((∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val) + (∑ i : Fin W, (valAt g x (a i.castSucc)).toNat * 2 ^ i.val) + 1) +
            ((!(valAt g x (a (Fin.last W)))).toNat + (valAt g x (a (Fin.last W))).toNat) * 2 ^ W := by ring
        _ = 2 ^ W + 1 * 2 ^ W := by rw [hsum_lo, hbit]
        _ = 2 ^ (W + 1) := by rw [pow_succ]; ring

/-- `cMuxW`: `W`-bit multiplexer (`4 * W` gates). -/
private def cMuxWAux (nin : ℕ) : ∀ (k : ℕ), List Gate → ℕ → (Fin k → ℕ) → (Fin k → ℕ) →
    List Gate × (Fin k → ℕ)
  | 0, g, _, _, _ => (g, Fin.elim0)
  | k + 1, g, sel, t, f =>
    let (g1, lo) := cMuxWAux nin k g sel (fun i => t i.castSucc) (fun i => f i.castSucc)
    let (g2, hi) := cMux nin g1 sel (t (Fin.last k)) (f (Fin.last k))
    (g2, Fin.snoc lo hi)

private def cMuxW (nin : ℕ) {W : ℕ} (g : List Gate) (sel : ℕ) (t f : Word W) : List Gate × Word W :=
  cMuxWAux nin W g sel t f

private lemma cMuxW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {sel : ℕ} {t f : Word W}
    (hs : sel < nin + g.length) (ht : WordIn (nin + g.length) t) (hf : WordIn (nin + g.length) f) :
    let res := cMuxW nin g sel t f
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 4 * W ∧
    WordIn (nin + res.1.length) res.2 ∧
    wordVal res.1 x res.2 = (if valAt g x sel then wordVal g x t else wordVal g x f) := by
  unfold cMuxW
  induction W generalizing g with
  | zero =>
    dsimp only [cMuxWAux]
    refine ⟨gExt_refl g, hv, by simp, fun i => i.elim0, by simp [wordVal]⟩
  | succ W ih =>
    dsimp only [cMuxWAux]
    have h1 := ih hv hs (fun i : Fin W => ht i.castSucc) (fun i : Fin W => hf i.castSucc)
    dsimp only at h1
    set g1 := (cMuxWAux nin W g sel (fun i => t i.castSucc) (fun i => f i.castSucc)).1
    set lo := (cMuxWAux nin W g sel (fun i => t i.castSucc) (fun i => f i.castSucc)).2
    have h2 := cMux_spec (sel := sel) (t := (t (Fin.last W))) (f := (f (Fin.last W))) hx h1.2.1 (by omega) (by have := ht (Fin.last W); omega) (by have := hf (Fin.last W); omega)
    dsimp only at h2
    set g2 := (cMux nin g1 sel (t (Fin.last W)) (f (Fin.last W))).1
    set hi := (cMux nin g1 sel (t (Fin.last W)) (f (Fin.last W))).2
    refine ⟨gExt_trans h1.1 h2.1, h2.2.1, by omega, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc_last, h2.2.2.2.1]
      · intro j; simp only [Fin.snoc_castSucc]; have := h1.2.2.2.1 j; omega
    · unfold wordVal at h1 ⊢
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
      have hlo_eq : (∑ i : Fin W, (valAt g2 x (lo i)).toNat * 2 ^ i.val) =
          ∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val :=
        Finset.sum_congr rfl fun i _ => by rw [valAt_ext hx.hlen h2.1 (h1.2.2.2.1 i)]
      rw [hlo_eq, h1.2.2.2.2, h2.2.2.2.2, valAt_ext hx.hlen h1.1 hs,
        valAt_ext hx.hlen h1.1 (ht (Fin.last W)), valAt_ext hx.hlen h1.1 (hf (Fin.last W))]
      cases valAt g x sel <;> simp

/-- `cAddCin`: `W`-bit ripple-carry adder with carry-in (`11 * W` gates). -/
private def cAddCinAux (nin : ℕ) : ∀ (k : ℕ), List Gate → (Fin k → ℕ) → (Fin k → ℕ) → ℕ →
    List Gate × (Fin k → ℕ) × ℕ
  | 0, g, _, _, cin => (g, Fin.elim0, cin)
  | k + 1, g, a, b, cin =>
    let (g1, lo, c1) := cAddCinAux nin k g (fun i => a i.castSucc) (fun i => b i.castSucc) cin
    let (g2, hi, cout) := cFullAdd nin g1 (a (Fin.last k)) (b (Fin.last k)) c1
    (g2, Fin.snoc lo hi, cout)

private def cAddCin (nin : ℕ) {W : ℕ} (g : List Gate) (a b : Word W) (cin : ℕ) :
    List Gate × Word W × ℕ :=
  cAddCinAux nin W g a b cin

private lemma cAddCin_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Word W} {cin : ℕ}
    (ha : WordIn (nin + g.length) a) (hb : WordIn (nin + g.length) b)
    (hc : cin < nin + g.length) :
    let res := cAddCin nin g a b cin
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 11 * W ∧
    WordIn (nin + res.1.length) res.2.1 ∧ res.2.2 < nin + res.1.length ∧
    wordVal res.1 x res.2.1 + (valAt res.1 x res.2.2).toNat * 2 ^ W =
      wordVal g x a + wordVal g x b + (valAt g x cin).toNat := by
  unfold cAddCin
  induction W generalizing g with
  | zero =>
    dsimp only [cAddCinAux]
    refine ⟨gExt_refl g, hv, by simp, fun i => i.elim0, hc, by simp [wordVal]⟩
  | succ W ih =>
    dsimp only [cAddCinAux]
    have h1 := ih hv (fun i : Fin W => ha i.castSucc) (fun i : Fin W => hb i.castSucc) hc
    dsimp only at h1
    set g1 := (cAddCinAux nin W g (fun i => a i.castSucc) (fun i => b i.castSucc) cin).1
    set lo := (cAddCinAux nin W g (fun i => a i.castSucc) (fun i => b i.castSucc) cin).2.1
    set c1 := (cAddCinAux nin W g (fun i => a i.castSucc) (fun i => b i.castSucc) cin).2.2
    have h2 := cFullAdd_spec (a := (a (Fin.last W))) (b := (b (Fin.last W))) (cin := c1) hx h1.2.1 (by have := ha (Fin.last W); omega)
      (by have := hb (Fin.last W); omega) h1.2.2.2.2.1
    dsimp only at h2
    set g2 := (cFullAdd nin g1 (a (Fin.last W)) (b (Fin.last W)) c1).1
    set hi := (cFullAdd nin g1 (a (Fin.last W)) (b (Fin.last W)) c1).2.1
    set cout := (cFullAdd nin g1 (a (Fin.last W)) (b (Fin.last W)) c1).2.2
    refine ⟨gExt_trans h1.1 h2.1, h2.2.1, by omega, ?_, h2.2.2.2.2.1, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc_last, h2.2.2.2.1]
      · intro j; simp only [Fin.snoc_castSucc]; have := h1.2.2.2.1 j; omega
    · unfold wordVal at h1 ⊢
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
      have hlo_eq : (∑ i : Fin W, (valAt g2 x (lo i)).toNat * 2 ^ i.val) =
          ∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val :=
        Finset.sum_congr rfl fun i _ => by rw [valAt_ext hx.hlen h2.1 (h1.2.2.2.1 i)]
      rw [hlo_eq]
      have hfa : (valAt g2 x hi).toNat + 2 * (valAt g2 x cout).toNat =
          (valAt g x (a (Fin.last W))).toNat + (valAt g x (b (Fin.last W))).toNat + (valAt g1 x c1).toNat := by
        have := h2.2.2.2.2.2
        rw [valAt_ext hx.hlen h1.1 (ha (Fin.last W)), valAt_ext hx.hlen h1.1 (hb (Fin.last W))] at this
        exact this
      have hsum_lo : (∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val) + (valAt g1 x c1).toNat * 2 ^ W =
          (∑ i : Fin W, (valAt g x (a i.castSucc)).toNat * 2 ^ i.val) +
          (∑ i : Fin W, (valAt g x (b i.castSucc)).toNat * 2 ^ i.val) + (valAt g x cin).toNat := h1.2.2.2.2.2
      calc (∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val) + (valAt g2 x hi).toNat * 2 ^ W + (valAt g2 x cout).toNat * 2 ^ (W + 1)
          = (∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val) + ((valAt g2 x hi).toNat + 2 * (valAt g2 x cout).toNat) * 2 ^ W := by rw [pow_succ]; ring
        _ = (∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val) + ((valAt g x (a (Fin.last W))).toNat + (valAt g x (b (Fin.last W))).toNat + (valAt g1 x c1).toNat) * 2 ^ W := by rw [hfa]
        _ = ((∑ i : Fin W, (valAt g1 x (lo i)).toNat * 2 ^ i.val) + (valAt g1 x c1).toNat * 2 ^ W) +
            (valAt g x (a (Fin.last W))).toNat * 2 ^ W + (valAt g x (b (Fin.last W))).toNat * 2 ^ W := by ring
        _ = (∑ i : Fin W, (valAt g x (a i.castSucc)).toNat * 2 ^ i.val) + (valAt g x (a (Fin.last W))).toNat * 2 ^ W +
            ((∑ i : Fin W, (valAt g x (b i.castSucc)).toNat * 2 ^ i.val) + (valAt g x (b (Fin.last W))).toNat * 2 ^ W) + (valAt g x cin).toNat := by rw [hsum_lo]; ring

private def cAddW (nin : ℕ) {W : ℕ} (g : List Gate) (a b : Word W) : List Gate × Word W :=
  let (g1, sm, _) := cAddCin nin g a b 0
  (g1, sm)

private lemma cAddW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Word W}
    (ha : WordIn (nin + g.length) a) (hb : WordIn (nin + g.length) b)
    (hno : wordVal g x a + wordVal g x b < 2 ^ W) :
    let res := cAddW nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 11 * W ∧
    WordIn (nin + res.1.length) res.2 ∧
    wordVal res.1 x res.2 = wordVal g x a + wordVal g x b := by
  have hnin := hx.hnin
  dsimp only [cAddW]
  have h1 := cAddCin_spec (cin := 0) hx hv ha hb (by omega)
  dsimp only at h1
  refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, ?_⟩
  have hEq := h1.2.2.2.2.2
  rw [valAt_zero hx] at hEq
  have hlt := wordVal_lt (cAddCin nin g a b 0).1 x (cAddCin nin g a b 0).2.1
  cases hco : valAt (cAddCin nin g a b 0).1 x (cAddCin nin g a b 0).2.2 <;>
    simp [hco] at hEq <;> omega

private lemma cAddW_struct {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Word W}
    (ha : WordIn (nin + g.length) a) (hb : WordIn (nin + g.length) b) :
    let res := cAddW nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 11 * W ∧
    WordIn (nin + res.1.length) res.2 ∧
    (wordVal g x a + wordVal g x b < 2 ^ W → wordVal res.1 x res.2 = wordVal g x a + wordVal g x b) := by
  have hnin := hx.hnin
  dsimp only [cAddW]
  have h1 := cAddCin_spec (cin := 0) hx hv ha hb (by omega)
  dsimp only at h1
  refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, fun hno => ?_⟩
  have hEq := h1.2.2.2.2.2
  rw [valAt_zero hx] at hEq
  have hlt := wordVal_lt (cAddCin nin g a b 0).1 x (cAddCin nin g a b 0).2.1
  cases hco : valAt (cAddCin nin g a b 0).1 x (cAddCin nin g a b 0).2.2 <;>
    simp [hco] at hEq <;> omega

/-- `cSubLeW a b`: returns `(diff, ge)` where `ge = decide (b ≤ a)` and if `b ≤ a` then `diff = a - b`. (`12 * W` gates) -/
private def cSubLeW (nin : ℕ) {W : ℕ} (g : List Gate) (a b : Word W) : List Gate × Word W × ℕ :=
  let (g1, nb) := cNotW nin g b
  cAddCin nin g1 a nb 1

private lemma cSubLeW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Word W}
    (ha : WordIn (nin + g.length) a) (hb : WordIn (nin + g.length) b) :
    let res := cSubLeW nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 12 * W ∧
    WordIn (nin + res.1.length) res.2.1 ∧ res.2.2 < nin + res.1.length ∧
    valAt res.1 x res.2.2 = decide (wordVal g x b ≤ wordVal g x a) ∧
    (wordVal g x b ≤ wordVal g x a → wordVal res.1 x res.2.1 = wordVal g x a - wordVal g x b) := by
  have hnin := hx.hnin
  dsimp only [cSubLeW]
  have h1 := cNotW_spec hx hv hb
  dsimp only at h1
  set g1 := (cNotW nin g b).1; set nb := (cNotW nin g b).2
  have h2 := cAddCin_spec (cin := 1) hx h1.2.1 (wordIn_mono (by omega) ha) h1.2.2.2.1 (by omega)
  dsimp only at h2
  refine ⟨gExt_trans h1.1 h2.1, h2.2.1, by omega, h2.2.2.2.1, h2.2.2.2.2.1, ?_, ?_⟩
  · have hEq := h2.2.2.2.2.2
    rw [wordVal_ext hx.hlen h1.1 ha, valAt_one hx] at hEq
    have hnb := h1.2.2.2.2
    have hlt_s := wordVal_lt (cAddCin nin g1 a nb 1).1 x (cAddCin nin g1 a nb 1).2.1
    have hlt_a := wordVal_lt g x a
    have hlt_b := wordVal_lt g x b
    cases hco : valAt (cAddCin nin g1 a nb 1).1 x (cAddCin nin g1 a nb 1).2.2 <;>
      simp [hco] at hEq ⊢ <;> omega
  · intro hle
    have hEq := h2.2.2.2.2.2
    rw [wordVal_ext hx.hlen h1.1 ha, valAt_one hx] at hEq
    have hnb := h1.2.2.2.2
    have hlt_s := wordVal_lt (cAddCin nin g1 a nb 1).1 x (cAddCin nin g1 a nb 1).2.1
    cases hco : valAt (cAddCin nin g1 a nb 1).1 x (cAddCin nin g1 a nb 1).2.2 <;>
      simp [hco] at hEq <;> omega

/-- `cSubTruncW a b`: exact `Nat` truncated subtraction `a - b` (`16 * W` gates). -/
private def cSubTruncW (nin : ℕ) {W : ℕ} (g : List Gate) (a b : Word W) : List Gate × Word W :=
  let (g1, diff, ge) := cSubLeW nin g a b
  cMuxW nin g1 ge diff (cConst0 W)

private lemma cSubTruncW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Word W}
    (ha : WordIn (nin + g.length) a) (hb : WordIn (nin + g.length) b) :
    let res := cSubTruncW nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 16 * W ∧
    WordIn (nin + res.1.length) res.2 ∧
    wordVal res.1 x res.2 = wordVal g x a - wordVal g x b := by
  dsimp only [cSubTruncW]
  have h1 := cSubLeW_spec hx hv ha hb
  dsimp only at h1
  set g1 := (cSubLeW nin g a b).1
  set diff := (cSubLeW nin g a b).2.1
  set ge := (cSubLeW nin g a b).2.2
  have h0 := cConst0_spec (W := W) (g := g1) hx
  have h2 := cMuxW_spec hx h1.2.1 h1.2.2.2.2.1 h1.2.2.2.1 h0.1
  dsimp only at h2
  refine ⟨gExt_trans h1.1 h2.1, h2.2.1, by omega, h2.2.2.2.1, ?_⟩
  rw [h2.2.2.2.2, h1.2.2.2.2.2.1, h0.2]
  by_cases hle : wordVal g x b ≤ wordVal g x a
  · simp [hle, h1.2.2.2.2.2.2 hle]
  · simp [hle]; omega

private def cLeW (nin : ℕ) {W : ℕ} (g : List Gate) (a b : Word W) : List Gate × ℕ :=
  let (g1, _, ge) := cSubLeW nin g b a
  (g1, ge)

private lemma cLeW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Word W}
    (ha : WordIn (nin + g.length) a) (hb : WordIn (nin + g.length) b) :
    let res := cLeW nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 12 * W ∧
    res.2 < nin + res.1.length ∧
    valAt res.1 x res.2 = decide (wordVal g x a ≤ wordVal g x b) := by
  dsimp only [cLeW]
  have h1 := cSubLeW_spec hx hv hb ha
  dsimp only at h1
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.2.1, h1.2.2.2.2.2.1⟩

private def cLtW (nin : ℕ) {W : ℕ} (g : List Gate) (a b : Word W) : List Gate × ℕ :=
  let (g1, le) := cLeW nin g b a
  emitNot nin g1 le

private lemma cLtW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Word W}
    (ha : WordIn (nin + g.length) a) (hb : WordIn (nin + g.length) b) :
    let res := cLtW nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 12 * W + 1 ∧
    res.2 < nin + res.1.length ∧
    valAt res.1 x res.2 = decide (wordVal g x a < wordVal g x b) := by
  dsimp only [cLtW]
  have h1 := cLeW_spec hx hv hb ha
  dsimp only at h1
  have h2 := emitNot_spec hx h1.2.1 h1.2.2.2.1
  dsimp only at h2
  refine ⟨gExt_trans h1.1 h2.1, h2.2.1, by omega, h2.2.2.2.1, ?_⟩
  rw [h2.2.2.2.2, h1.2.2.2.2]
  by_cases h : wordVal g x a < wordVal g x b
  · have : ¬ wordVal g x b ≤ wordVal g x a := by omega
    simp [h, this]
  · have : wordVal g x b ≤ wordVal g x a := by omega
    simp [h, this]

private def cEqW (nin : ℕ) {W : ℕ} (g : List Gate) (a b : Word W) : List Gate × ℕ :=
  let (g1, le1) := cLeW nin g a b
  let (g2, le2) := cLeW nin g1 b a
  emitAnd nin g2 le1 le2

private lemma cEqW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Word W}
    (ha : WordIn (nin + g.length) a) (hb : WordIn (nin + g.length) b) :
    let res := cEqW nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 24 * W + 1 ∧
    res.2 < nin + res.1.length ∧
    valAt res.1 x res.2 = decide (wordVal g x a = wordVal g x b) := by
  dsimp only [cEqW]
  have h1 := cLeW_spec hx hv ha hb
  dsimp only at h1
  set g1 := (cLeW nin g a b).1; set le1 := (cLeW nin g a b).2
  have h2 := cLeW_spec hx h1.2.1 (wordIn_mono (by omega) hb) (wordIn_mono (by omega) ha)
  dsimp only at h2
  set g2 := (cLeW nin g1 b a).1; set le2 := (cLeW nin g1 b a).2
  have h3 := emitAnd_spec (a := le1) hx h2.2.1 (by omega) h2.2.2.2.1
  dsimp only at h3
  refine ⟨gExt_trans h1.1 (gExt_trans h2.1 h3.1), h3.2.1, by omega, h3.2.2.2.1, ?_⟩
  rw [h3.2.2.2.2, valAt_ext hx.hlen h2.1 h1.2.2.2.1, h1.2.2.2.2, h2.2.2.2.2,
    wordVal_ext hx.hlen h1.1 ha, wordVal_ext hx.hlen h1.1 hb]
  by_cases h : wordVal g x a = wordVal g x b <;> simp [h] <;> omega

private def cMinW (nin : ℕ) {W : ℕ} (g : List Gate) (a b : Word W) : List Gate × Word W :=
  let (g1, le) := cLeW nin g a b
  cMuxW nin g1 le a b

private lemma cMinW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Word W}
    (ha : WordIn (nin + g.length) a) (hb : WordIn (nin + g.length) b) :
    let res := cMinW nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 16 * W ∧
    WordIn (nin + res.1.length) res.2 ∧
    wordVal res.1 x res.2 = min (wordVal g x a) (wordVal g x b) := by
  dsimp only [cMinW]
  have h1 := cLeW_spec hx hv ha hb
  dsimp only at h1
  set g1 := (cLeW nin g a b).1; set le := (cLeW nin g a b).2
  have h2 := cMuxW_spec hx h1.2.1 h1.2.2.2.1 (wordIn_mono (by omega) ha) (wordIn_mono (by omega) hb)
  dsimp only at h2
  refine ⟨gExt_trans h1.1 h2.1, h2.2.1, by omega, h2.2.2.2.1, ?_⟩
  rw [h2.2.2.2.2, h1.2.2.2.2, wordVal_ext hx.hlen h1.1 ha, wordVal_ext hx.hlen h1.1 hb]
  by_cases h : wordVal g x a ≤ wordVal g x b <;> simp [h, min_eq_left, min_eq_right, le_of_not_ge]

private def cMaxW (nin : ℕ) {W : ℕ} (g : List Gate) (a b : Word W) : List Gate × Word W :=
  let (g1, le) := cLeW nin g a b
  cMuxW nin g1 le b a

private lemma cMaxW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Word W}
    (ha : WordIn (nin + g.length) a) (hb : WordIn (nin + g.length) b) :
    let res := cMaxW nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 16 * W ∧
    WordIn (nin + res.1.length) res.2 ∧
    wordVal res.1 x res.2 = max (wordVal g x a) (wordVal g x b) := by
  dsimp only [cMaxW]
  have h1 := cLeW_spec hx hv ha hb
  dsimp only at h1
  set g1 := (cLeW nin g a b).1; set le := (cLeW nin g a b).2
  have h2 := cMuxW_spec hx h1.2.1 h1.2.2.2.1 (wordIn_mono (by omega) hb) (wordIn_mono (by omega) ha)
  dsimp only at h2
  refine ⟨gExt_trans h1.1 h2.1, h2.2.1, by omega, h2.2.2.2.1, ?_⟩
  rw [h2.2.2.2.2, h1.2.2.2.2, wordVal_ext hx.hlen h1.1 ha, wordVal_ext hx.hlen h1.1 hb]
  by_cases h : wordVal g x a ≤ wordVal g x b <;> simp [h, max_eq_left, max_eq_right, le_of_not_ge]

private def cEqZeroW (nin : ℕ) {W : ℕ} (g : List Gate) (a : Word W) : List Gate × ℕ :=
  cLeW nin g a (cConst0 W)

private lemma cEqZeroW_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a : Word W} (ha : WordIn (nin + g.length) a) :
    let res := cEqZeroW nin g a
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 12 * W ∧
    res.2 < nin + res.1.length ∧
    valAt res.1 x res.2 = decide (wordVal g x a = 0) := by
  dsimp only [cEqZeroW]
  have h0 := cConst0_spec (W := W) (g := g) hx
  have h1 := cLeW_spec hx hv ha h0.1
  dsimp only at h1
  refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, ?_⟩
  rw [h1.2.2.2.2, h0.2]; simp

private def cEqOneW (nin : ℕ) {W : ℕ} (g : List Gate) (a : Word W) : List Gate × ℕ :=
  cEqW nin g a (cConstBit W 1)

private lemma cEqOneW_spec {nin W : ℕ} (hW : 1 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a : Word W} (ha : WordIn (nin + g.length) a) :
    let res := cEqOneW nin g a
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 24 * W + 1 ∧
    res.2 < nin + res.1.length ∧
    valAt res.1 x res.2 = decide (wordVal g x a = 1) := by
  have hnin := hx.hnin
  dsimp only [cEqOneW]
  have h1b := cConstBit_spec hW (g := g) hx (b := 1) (by omega)
  have h1 := cEqW_spec hx hv ha h1b.1
  dsimp only at h1
  refine ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, ?_⟩
  rw [h1.2.2.2.2, h1b.2, valAt_one hx]; rfl

/-!
## Part 4: `Sum8W` circuit combinators, `query`, `prep`, and `build`
-/

private lemma ctx_default {nin : ℕ} (hnin : 2 ≤ nin) :
    Ctx nin ([false, true] ++ List.replicate (nin - 2) false) := by
  refine ⟨by simp; omega, hnin, rfl, rfl⟩

private structure Sum8W (W : ℕ) where
  fr : Word W
  fb : Word W
  cr : Word W
  cb : Word W
  d00 : Word W
  d11 : Word W
  d01 : Word W
  d10 : Word W

private def Sum8W.In (bound : ℕ) {W : ℕ} (s : Sum8W W) : Prop :=
  WordIn bound s.fr ∧ WordIn bound s.fb ∧ WordIn bound s.cr ∧ WordIn bound s.cb ∧
  WordIn bound s.d00 ∧ WordIn bound s.d11 ∧ WordIn bound s.d01 ∧ WordIn bound s.d10

private lemma Sum8W.in_mono {b1 b2 W : ℕ} {s : Sum8W W} (hle : b1 ≤ b2) (hs : s.In b1) :
    s.In b2 :=
  ⟨wordIn_mono hle hs.1, wordIn_mono hle hs.2.1, wordIn_mono hle hs.2.2.1,
   wordIn_mono hle hs.2.2.2.1, wordIn_mono hle hs.2.2.2.2.1, wordIn_mono hle hs.2.2.2.2.2.1,
   wordIn_mono hle hs.2.2.2.2.2.2.1, wordIn_mono hle hs.2.2.2.2.2.2.2⟩

private lemma gExt_nin_le {nin : ℕ} {g g' : List Gate} (he : GExt g g') :
    nin + g.length ≤ nin + g'.length :=
  Nat.add_le_add_left (gExt_len_le he) nin

private lemma wire_ext {nin : ℕ} {g g' : List Gate} {a : ℕ}
    (he : GExt g g') (ha : a < nin + g.length) : a < nin + g'.length :=
  Nat.lt_of_lt_of_le ha (gExt_nin_le he)

private lemma wordIn_ext {nin W : ℕ} {g g' : List Gate} {w : Word W}
    (he : GExt g g') (hw : WordIn (nin + g.length) w) : WordIn (nin + g'.length) w :=
  wordIn_mono (gExt_nin_le he) hw

private lemma sum8_in_ext {nin W : ℕ} {g g' : List Gate} {s : Sum8W W}
    (he : GExt g g') (hs : s.In (nin + g.length)) : s.In (nin + g'.length) :=
  Sum8W.in_mono (gExt_nin_le he) hs

private def Sum8W.val {W : ℕ} (g : List Gate) (x : List Bool) (s : Sum8W W) : Sum8 :=
  ⟨wordVal g x s.fr, wordVal g x s.fb, wordVal g x s.cr, wordVal g x s.cb,
   wordVal g x s.d00, wordVal g x s.d11, wordVal g x s.d01, wordVal g x s.d10⟩

private lemma Sum8W.val_ext {nin W : ℕ} {g g' : List Gate} {x : List Bool}
    (hx : x.length = nin) (hext : GExt g g') {s : Sum8W W} (hs : s.In (nin + g.length)) :
    s.val g' x = s.val g x := by
  unfold Sum8W.val
  congr 1
  · exact wordVal_ext hx hext hs.1
  · exact wordVal_ext hx hext hs.2.1
  · exact wordVal_ext hx hext hs.2.2.1
  · exact wordVal_ext hx hext hs.2.2.2.1
  · exact wordVal_ext hx hext hs.2.2.2.2.1
  · exact wordVal_ext hx hext hs.2.2.2.2.2.1
  · exact wordVal_ext hx hext hs.2.2.2.2.2.2.1
  · exact wordVal_ext hx hext hs.2.2.2.2.2.2.2

private def Sum8.Bound (s : Sum8) (B : ℕ) : Prop :=
  s.fr ≤ B ∧ s.fb ≤ B ∧ s.cr ≤ B ∧ s.cb ≤ B ∧
  s.d00 ≤ B ∧ s.d11 ≤ B ∧ s.d01 ≤ B ∧ s.d10 ≤ B

private def Sum8.Cap (s : Sum8) (R B : ℕ) : Prop :=
  s.fr + s.cr ≤ R ∧ s.fb + s.cb ≤ B ∧
  s.d00 ≤ R ∧ s.d11 ≤ R ∧ s.d01 ≤ R ∧ s.d10 ≤ R ∧
  s.d00 ≤ B ∧ s.d11 ≤ B ∧ s.d01 ≤ B ∧ s.d10 ≤ B

private lemma Sum8.cap_zero : Sum8.zero.Cap 0 0 := by
  unfold Sum8.Cap Sum8.zero; simp

private lemma Sum8.cap_comb {s1 s2 : Sum8} {R1 B1 R2 B2 : ℕ}
    (h1 : s1.Cap R1 B1) (h2 : s2.Cap R2 B2) : (s1.comb s2).Cap (R1 + R2) (B1 + B2) := by
  rcases h1 with ⟨_, _, _, _, _, _, _, _, _, _⟩
  rcases h2 with ⟨_, _, _, _, _, _, _, _, _, _⟩
  unfold Sum8.Cap Sum8.comb; dsimp only; omega

private lemma Sum8.cap_ofSeg (R B : ℕ) (p : Bool) (h : R + B ≤ 1 ∨ (1 ≤ R ∧ 1 ≤ B)) :
    (Sum8.ofSeg R B p).Cap R B := by
  unfold Sum8.Cap Sum8.ofSeg
  split_ifs with h0 h1 hR
  · simp [Sum8.zero]
  · cases p <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · cases p <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  · cases p <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

private lemma Sum8.cap_bound {s : Sum8} {R B M : ℕ} (hc : s.Cap R B) (hR : R ≤ M) (hB : B ≤ M) :
    s.Bound M := by
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _⟩
  unfold Sum8.Bound; omega

private lemma Sum8.bound_mono {s : Sum8} {B1 B2 : ℕ} (hb : s.Bound B1) (hle : B1 ≤ B2) :
    s.Bound B2 := by
  rcases hb with ⟨_, _, _, _, _, _, _, _⟩; unfold Sum8.Bound; omega

private def cSum8Zero (W : ℕ) : Sum8W W :=
  ⟨cConst0 W, cConst0 W, cConst0 W, cConst0 W,
   cConst0 W, cConst0 W, cConst0 W, cConst0 W⟩

private lemma cSum8Zero_spec {nin W : ℕ} {g : List Gate} {x : List Bool} (hx : Ctx nin x) :
    (cSum8Zero W).In (nin + g.length) ∧ (cSum8Zero W).val g x = Sum8.zero := by
  have h0 := cConst0_spec (W := W) (g := g) hx
  refine ⟨⟨h0.1, h0.1, h0.1, h0.1, h0.1, h0.1, h0.1, h0.1⟩, ?_⟩
  unfold Sum8W.val cSum8Zero Sum8.zero; simp [h0.2]

private def cMuxSum8 (nin : ℕ) {W : ℕ} (g : List Gate) (sel : ℕ) (t f : Sum8W W) :
    List Gate × Sum8W W :=
  let (g1, fr) := cMuxW nin g sel t.fr f.fr
  let (g2, fb) := cMuxW nin g1 sel t.fb f.fb
  let (g3, cr) := cMuxW nin g2 sel t.cr f.cr
  let (g4, cb) := cMuxW nin g3 sel t.cb f.cb
  let (g5, d00) := cMuxW nin g4 sel t.d00 f.d00
  let (g6, d11) := cMuxW nin g5 sel t.d11 f.d11
  let (g7, d01) := cMuxW nin g6 sel t.d01 f.d01
  let (g8, d10) := cMuxW nin g7 sel t.d10 f.d10
  (g8, ⟨fr, fb, cr, cb, d00, d11, d01, d10⟩)

private lemma cMuxSum8_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {sel : ℕ} {t f : Sum8W W}
    (hs : sel < nin + g.length) (ht : t.In (nin + g.length)) (hf : f.In (nin + g.length)) :
    let res := cMuxSum8 nin g sel t f
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 32 * W ∧
    res.2.In (nin + res.1.length) ∧
    res.2.val res.1 x = (if valAt g x sel then t.val g x else f.val g x) := by
  unfold cMuxSum8
  have h1 := cMuxW_spec hx hv hs ht.1 hf.1
  generalize cMuxW nin g sel t.fr f.fr = _r1 at h1 ⊢; rcases _r1 with ⟨g1, _v1⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have h2 := cMuxW_spec (sel := sel) hx h1.2.1 (by omega) (wordIn_mono (by omega) ht.2.1) (wordIn_mono (by omega) hf.2.1)
  generalize cMuxW nin g1 sel t.fb f.fb = _r2 at h2 ⊢; rcases _r2 with ⟨g2, _v2⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have h3 := cMuxW_spec (sel := sel) hx h2.2.1 (by omega) (wordIn_mono (by omega) ht.2.2.1) (wordIn_mono (by omega) hf.2.2.1)
  generalize cMuxW nin g2 sel t.cr f.cr = _r3 at h3 ⊢; rcases _r3 with ⟨g3, _v3⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have h4 := cMuxW_spec (sel := sel) hx h3.2.1 (by omega) (wordIn_mono (by omega) ht.2.2.2.1) (wordIn_mono (by omega) hf.2.2.2.1)
  generalize cMuxW nin g3 sel t.cb f.cb = _r4 at h4 ⊢; rcases _r4 with ⟨g4, _v4⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have h5 := cMuxW_spec (sel := sel) hx h4.2.1 (by omega) (wordIn_mono (by omega) ht.2.2.2.2.1) (wordIn_mono (by omega) hf.2.2.2.2.1)
  generalize cMuxW nin g4 sel t.d00 f.d00 = _r5 at h5 ⊢; rcases _r5 with ⟨g5, _v5⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have h6 := cMuxW_spec (sel := sel) hx h5.2.1 (by omega) (wordIn_mono (by omega) ht.2.2.2.2.2.1) (wordIn_mono (by omega) hf.2.2.2.2.2.1)
  generalize cMuxW nin g5 sel t.d11 f.d11 = _r6 at h6 ⊢; rcases _r6 with ⟨g6, _v6⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have h7 := cMuxW_spec (sel := sel) hx h6.2.1 (by omega) (wordIn_mono (by omega) ht.2.2.2.2.2.2.1) (wordIn_mono (by omega) hf.2.2.2.2.2.2.1)
  generalize cMuxW nin g6 sel t.d01 f.d01 = _r7 at h7 ⊢; rcases _r7 with ⟨g7, _v7⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have h8 := cMuxW_spec (sel := sel) hx h7.2.1 (by omega) (wordIn_mono (by omega) ht.2.2.2.2.2.2.2) (wordIn_mono (by omega) hf.2.2.2.2.2.2.2)
  dsimp only at h8
  have he12 := gExt_trans h1.1 h2.1
  have he13 := gExt_trans he12 h3.1
  have he14 := gExt_trans he13 h4.1
  have he15 := gExt_trans he14 h5.1
  have he16 := gExt_trans he15 h6.1
  have he17 := gExt_trans he16 h7.1
  have he18 := gExt_trans he17 h8.1
  dsimp only
  refine ⟨he18, h8.2.1, by omega,
    ⟨wordIn_mono (by omega) h1.2.2.2.1, wordIn_mono (by omega) h2.2.2.2.1,
     wordIn_mono (by omega) h3.2.2.2.1, wordIn_mono (by omega) h4.2.2.2.1,
     wordIn_mono (by omega) h5.2.2.2.1, wordIn_mono (by omega) h6.2.2.2.1,
     wordIn_mono (by omega) h7.2.2.2.1, h8.2.2.2.1⟩, ?_⟩
  have e28 := gExt_trans h2.1 (gExt_trans h3.1 (gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 h8.1)))))
  have e38 := gExt_trans h3.1 (gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 h8.1))))
  have e48 := gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 h8.1)))
  have e58 := gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 h8.1))
  have e68 := gExt_trans h6.1 (gExt_trans h7.1 h8.1)
  have e78 := gExt_trans h7.1 h8.1
  unfold Sum8W.val
  rw [wordVal_ext hx.hlen e28 h1.2.2.2.1, h1.2.2.2.2,
      wordVal_ext hx.hlen e38 h2.2.2.2.1, h2.2.2.2.2, valAt_ext hx.hlen h1.1 hs,
      wordVal_ext hx.hlen h1.1 ht.2.1, wordVal_ext hx.hlen h1.1 hf.2.1,
      wordVal_ext hx.hlen e48 h3.2.2.2.1, h3.2.2.2.2, valAt_ext hx.hlen he12 hs,
      wordVal_ext hx.hlen he12 ht.2.2.1, wordVal_ext hx.hlen he12 hf.2.2.1,
      wordVal_ext hx.hlen e58 h4.2.2.2.1, h4.2.2.2.2, valAt_ext hx.hlen he13 hs,
      wordVal_ext hx.hlen he13 ht.2.2.2.1, wordVal_ext hx.hlen he13 hf.2.2.2.1,
      wordVal_ext hx.hlen e68 h5.2.2.2.1, h5.2.2.2.2, valAt_ext hx.hlen he14 hs,
      wordVal_ext hx.hlen he14 ht.2.2.2.2.1, wordVal_ext hx.hlen he14 hf.2.2.2.2.1,
      wordVal_ext hx.hlen e78 h6.2.2.2.1, h6.2.2.2.2, valAt_ext hx.hlen he15 hs,
      wordVal_ext hx.hlen he15 ht.2.2.2.2.2.1, wordVal_ext hx.hlen he15 hf.2.2.2.2.2.1,
      wordVal_ext hx.hlen h8.1 h7.2.2.2.1, h7.2.2.2.2, valAt_ext hx.hlen he16 hs,
      wordVal_ext hx.hlen he16 ht.2.2.2.2.2.2.1, wordVal_ext hx.hlen he16 hf.2.2.2.2.2.2.1,
      h8.2.2.2.2, valAt_ext hx.hlen he17 hs,
      wordVal_ext hx.hlen he17 ht.2.2.2.2.2.2.2, wordVal_ext hx.hlen he17 hf.2.2.2.2.2.2.2]
  cases valAt g x sel <;> rfl

private def cCombSum8 (nin : ℕ) {W : ℕ} (g : List Gate) (a b : Sum8W W) :
    List Gate × Sum8W W :=
  let (g1, fr) := cAddW nin g a.fr b.fr
  let (g2, fb) := cAddW nin g1 a.fb b.fb
  let (g3, cr) := cAddW nin g2 a.cr b.cr
  let (g4, cb) := cAddW nin g3 a.cb b.cb
  let (g5, d00) := cAddW nin g4 a.d00 b.d00
  let (g6, d11) := cAddW nin g5 a.d11 b.d11
  let (g7, d01) := cAddW nin g6 a.d01 b.d01
  let (g8, d10) := cAddW nin g7 a.d10 b.d10
  (g8, ⟨fr, fb, cr, cb, d00, d11, d01, d10⟩)

private lemma cCombSum8_spec {nin W : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {a b : Sum8W W}
    (ha : a.In (nin + g.length)) (hb : b.In (nin + g.length))
    (hno : ((a.val g x).comb (b.val g x)).Bound (2 ^ W - 1)) :
    let res := cCombSum8 nin g a b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 88 * W ∧
    res.2.In (nin + res.1.length) ∧
    res.2.val res.1 x = (a.val g x).comb (b.val g x) := by
  have hpow : 1 ≤ 2 ^ W := Nat.one_le_pow W 2 (by decide)
  rcases hno with ⟨hfr, hfb, hcr, hcb, hd00, hd11, hd01, hd10⟩
  simp only [Sum8.comb, Sum8W.val] at hfr hfb hcr hcb hd00 hd11 hd01 hd10
  unfold cCombSum8
  have h1 := cAddW_spec hx hv ha.1 hb.1 (by omega)
  generalize cAddW nin g a.fr b.fr = _r1 at h1 ⊢; rcases _r1 with ⟨g1, _v1⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have h2 := cAddW_spec hx h1.2.1 (wordIn_mono (by omega) ha.2.1) (wordIn_mono (by omega) hb.2.1)
    (by rw [wordVal_ext hx.hlen h1.1 ha.2.1, wordVal_ext hx.hlen h1.1 hb.2.1]; omega)
  generalize cAddW nin g1 a.fb b.fb = _r2 at h2 ⊢; rcases _r2 with ⟨g2, _v2⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have he12 := gExt_trans h1.1 h2.1
  have h3 := cAddW_spec hx h2.2.1 (wordIn_mono (by omega) ha.2.2.1) (wordIn_mono (by omega) hb.2.2.1)
    (by rw [wordVal_ext hx.hlen he12 ha.2.2.1, wordVal_ext hx.hlen he12 hb.2.2.1]; omega)
  generalize cAddW nin g2 a.cr b.cr = _r3 at h3 ⊢; rcases _r3 with ⟨g3, _v3⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he13 := gExt_trans he12 h3.1
  have h4 := cAddW_spec hx h3.2.1 (wordIn_mono (by omega) ha.2.2.2.1) (wordIn_mono (by omega) hb.2.2.2.1)
    (by rw [wordVal_ext hx.hlen he13 ha.2.2.2.1, wordVal_ext hx.hlen he13 hb.2.2.2.1]; omega)
  generalize cAddW nin g3 a.cb b.cb = _r4 at h4 ⊢; rcases _r4 with ⟨g4, _v4⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have he14 := gExt_trans he13 h4.1
  have h5 := cAddW_spec hx h4.2.1 (wordIn_mono (by omega) ha.2.2.2.2.1) (wordIn_mono (by omega) hb.2.2.2.2.1)
    (by rw [wordVal_ext hx.hlen he14 ha.2.2.2.2.1, wordVal_ext hx.hlen he14 hb.2.2.2.2.1]; omega)
  generalize cAddW nin g4 a.d00 b.d00 = _r5 at h5 ⊢; rcases _r5 with ⟨g5, _v5⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have he15 := gExt_trans he14 h5.1
  have h6 := cAddW_spec hx h5.2.1 (wordIn_mono (by omega) ha.2.2.2.2.2.1) (wordIn_mono (by omega) hb.2.2.2.2.2.1)
    (by rw [wordVal_ext hx.hlen he15 ha.2.2.2.2.2.1, wordVal_ext hx.hlen he15 hb.2.2.2.2.2.1]; omega)
  generalize cAddW nin g5 a.d11 b.d11 = _r6 at h6 ⊢; rcases _r6 with ⟨g6, _v6⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have he16 := gExt_trans he15 h6.1
  have h7 := cAddW_spec hx h6.2.1 (wordIn_mono (by omega) ha.2.2.2.2.2.2.1) (wordIn_mono (by omega) hb.2.2.2.2.2.2.1)
    (by rw [wordVal_ext hx.hlen he16 ha.2.2.2.2.2.2.1, wordVal_ext hx.hlen he16 hb.2.2.2.2.2.2.1]; omega)
  generalize cAddW nin g6 a.d01 b.d01 = _r7 at h7 ⊢; rcases _r7 with ⟨g7, _v7⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have he17 := gExt_trans he16 h7.1
  have h8 := cAddW_spec hx h7.2.1 (wordIn_mono (by omega) ha.2.2.2.2.2.2.2) (wordIn_mono (by omega) hb.2.2.2.2.2.2.2)
    (by rw [wordVal_ext hx.hlen he17 ha.2.2.2.2.2.2.2, wordVal_ext hx.hlen he17 hb.2.2.2.2.2.2.2]; omega)
  dsimp only at h8
  have he18 := gExt_trans he17 h8.1
  dsimp only
  refine ⟨he18, h8.2.1, by omega,
    ⟨wordIn_mono (by omega) h1.2.2.2.1, wordIn_mono (by omega) h2.2.2.2.1,
     wordIn_mono (by omega) h3.2.2.2.1, wordIn_mono (by omega) h4.2.2.2.1,
     wordIn_mono (by omega) h5.2.2.2.1, wordIn_mono (by omega) h6.2.2.2.1,
     wordIn_mono (by omega) h7.2.2.2.1, h8.2.2.2.1⟩, ?_⟩
  have e28 := gExt_trans h2.1 (gExt_trans h3.1 (gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 h8.1)))))
  have e38 := gExt_trans h3.1 (gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 h8.1))))
  have e48 := gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 h8.1)))
  have e58 := gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 h8.1))
  have e68 := gExt_trans h6.1 (gExt_trans h7.1 h8.1)
  have e78 := gExt_trans h7.1 h8.1
  unfold Sum8W.val Sum8.comb
  rw [wordVal_ext hx.hlen e28 h1.2.2.2.1, h1.2.2.2.2,
      wordVal_ext hx.hlen e38 h2.2.2.2.1, h2.2.2.2.2, wordVal_ext hx.hlen h1.1 ha.2.1, wordVal_ext hx.hlen h1.1 hb.2.1,
      wordVal_ext hx.hlen e48 h3.2.2.2.1, h3.2.2.2.2, wordVal_ext hx.hlen he12 ha.2.2.1, wordVal_ext hx.hlen he12 hb.2.2.1,
      wordVal_ext hx.hlen e58 h4.2.2.2.1, h4.2.2.2.2, wordVal_ext hx.hlen he13 ha.2.2.2.1, wordVal_ext hx.hlen he13 hb.2.2.2.1,
      wordVal_ext hx.hlen e68 h5.2.2.2.1, h5.2.2.2.2, wordVal_ext hx.hlen he14 ha.2.2.2.2.1, wordVal_ext hx.hlen he14 hb.2.2.2.2.1,
      wordVal_ext hx.hlen e78 h6.2.2.2.1, h6.2.2.2.2, wordVal_ext hx.hlen he15 ha.2.2.2.2.2.1, wordVal_ext hx.hlen he15 hb.2.2.2.2.2.1,
      wordVal_ext hx.hlen h8.1 h7.2.2.2.1, h7.2.2.2.2, wordVal_ext hx.hlen he16 ha.2.2.2.2.2.2.1, wordVal_ext hx.hlen he16 hb.2.2.2.2.2.2.1,
      h8.2.2.2.2, wordVal_ext hx.hlen he17 ha.2.2.2.2.2.2.2, wordVal_ext hx.hlen he17 hb.2.2.2.2.2.2.2]

private def cOfSeg (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (R B : Word W) (p : ℕ) :
    List Gate × Sum8W W :=
  let (g1, L) := cAddW nin g R B
  let (g2, isL0) := cEqZeroW nin g1 L
  let (g3, isL1) := cEqOneW nin g2 L
  let (g4, isR1) := cEqOneW nin g3 R
  let (g5, b11) := cXor nin g4 (L ⟨0, hW⟩) p
  let (g6, b01) := cXor nin g5 (B ⟨0, hW⟩) p
  let (g7, b10) := cXor nin g6 (R ⟨0, hW⟩) p
  let (g8, sL1) := cMuxSum8 nin g7 isR1
    ⟨cConstBit W p, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W⟩
    ⟨cConst0 W, cConstBit W p, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W⟩
  let (g9, sPos) := cMuxSum8 nin g8 isL1 sL1
    ⟨cConst0 W, cConst0 W, R, B, cConstBit W p, cConstBit W b11, cConstBit W b01, cConstBit W b10⟩
  cMuxSum8 nin g9 isL0 (cSum8Zero W) sPos

private lemma cOfSeg_spec {nin W : ℕ} (hW : 1 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {R B : Word W} {p : ℕ}
    (hR : WordIn (nin + g.length) R) (hB : WordIn (nin + g.length) B)
    (hp : p < nin + g.length) (hno : wordVal g x R + wordVal g x B < 2 ^ W) :
    let res := cOfSeg nin hW g R B p
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 185 * W ∧
    res.2.In (nin + res.1.length) ∧
    res.2.val res.1 x = Sum8.ofSeg (wordVal g x R) (wordVal g x B) (valAt g x p) := by
  unfold cOfSeg
  have h1 := cAddW_spec hx hv hR hB hno
  generalize cAddW nin g R B = _r1 at h1 ⊢; rcases _r1 with ⟨g1, L⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have h2 := cEqZeroW_spec hx h1.2.1 h1.2.2.2.1
  generalize cEqZeroW nin g1 L = _r2 at h2 ⊢; rcases _r2 with ⟨g2, isL0⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have h3 := cEqOneW_spec hW hx h2.2.1 (wordIn_mono (by omega) h1.2.2.2.1)
  generalize cEqOneW nin g2 L = _r3 at h3 ⊢; rcases _r3 with ⟨g3, isL1⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have h4 := cEqOneW_spec hW hx h3.2.1 (wordIn_mono (by omega) hR)
  generalize cEqOneW nin g3 R = _r4 at h4 ⊢; rcases _r4 with ⟨g4, isR1⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have h5 := cXor_spec (a := (L ⟨0, hW⟩)) (b := p) hx h4.2.1 (by have := h1.2.2.2.1 ⟨0, hW⟩; omega) (by omega)
  generalize cXor nin g4 (L ⟨0, hW⟩) p = _r5 at h5 ⊢; rcases _r5 with ⟨g5, b11⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have h6 := cXor_spec (a := (B ⟨0, hW⟩)) (b := p) hx h5.2.1 (by have := hB ⟨0, hW⟩; omega) (by omega)
  generalize cXor nin g5 (B ⟨0, hW⟩) p = _r6 at h6 ⊢; rcases _r6 with ⟨g6, b01⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have h7 := cXor_spec (a := (R ⟨0, hW⟩)) (b := p) hx h6.2.1 (by have := hR ⟨0, hW⟩; omega) (by omega)
  generalize cXor nin g6 (R ⟨0, hW⟩) p = _r7 at h7 ⊢; rcases _r7 with ⟨g7, b10⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have he12 := gExt_trans h1.1 h2.1
  have he13 := gExt_trans he12 h3.1
  have he14 := gExt_trans he13 h4.1
  have he15 := gExt_trans he14 h5.1
  have he16 := gExt_trans he15 h6.1
  have he17 := gExt_trans he16 h7.1
  have hz7 := cConst0_spec (W := W) (g := g7) hx
  have hpW7 := cConstBit_spec hW (g := g7) hx (b := p) (by omega)
  have hb11_7 := cConstBit_spec hW (g := g7) hx (b := b11) (by omega)
  have hb01_7 := cConstBit_spec hW (g := g7) hx (b := b01) (by omega)
  have hb10_7 := cConstBit_spec hW (g := g7) hx (b := b10) h7.2.2.2.1
  have hsL1R_in : (⟨cConstBit W p, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W⟩ : Sum8W W).In (nin + g7.length) :=
    ⟨hpW7.1, hz7.1, hz7.1, hz7.1, hz7.1, hz7.1, hz7.1, hz7.1⟩
  have hsL1B_in : (⟨cConst0 W, cConstBit W p, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W⟩ : Sum8W W).In (nin + g7.length) :=
    ⟨hz7.1, hpW7.1, hz7.1, hz7.1, hz7.1, hz7.1, hz7.1, hz7.1⟩
  have hsL2_in : (⟨cConst0 W, cConst0 W, R, B, cConstBit W p, cConstBit W b11, cConstBit W b01, cConstBit W b10⟩ : Sum8W W).In (nin + g7.length) :=
    ⟨hz7.1, hz7.1, wordIn_mono (by omega) hR, wordIn_mono (by omega) hB, hpW7.1, hb11_7.1, hb01_7.1, hb10_7.1⟩
  have h8 := cMuxSum8_spec (sel := isR1) hx h7.2.1 (by omega) hsL1R_in hsL1B_in
  generalize cMuxSum8 nin g7 isR1 ⟨cConstBit W p, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W⟩ ⟨cConst0 W, cConstBit W p, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W, cConst0 W⟩ = _r8 at h8 ⊢; rcases _r8 with ⟨g8, _v8⟩; dsimp only at h8; dsimp (config := { zeta := false }) only at ⊢
  have h9 := cMuxSum8_spec (sel := isL1) hx h8.2.1 (by omega) h8.2.2.2.1 (Sum8W.in_mono (by omega) hsL2_in)
  generalize cMuxSum8 nin g8 isL1 _v8 ⟨cConst0 W, cConst0 W, R, B, cConstBit W p, cConstBit W b11, cConstBit W b01, cConstBit W b10⟩ = _r9 at h9 ⊢; rcases _r9 with ⟨g9, _v9⟩; dsimp only at h9; dsimp (config := { zeta := false }) only at ⊢
  have hz9 := cSum8Zero_spec (W := W) (g := g9) hx
  have h10 := cMuxSum8_spec (sel := isL0) hx h9.2.1 (by omega) hz9.1 h9.2.2.2.1
  dsimp only at h10
  have he18 := gExt_trans he17 h8.1
  have he19 := gExt_trans he18 h9.1
  have he110 := gExt_trans he19 h10.1
  dsimp only
  refine ⟨he110, h10.2.1,
    by linarith only [hW, h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1,
       h5.2.2.1, h6.2.2.1, h7.2.2.1, h8.2.2.1, h9.2.2.1, h10.2.2.1],
    h10.2.2.2.1, ?_⟩
  rw [h10.2.2.2.2, hz9.2, h9.2.2.2.2,
      valAt_ext hx.hlen (gExt_trans h3.1 (gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 (gExt_trans h8.1 h9.1)))))) h2.2.2.2.1,
      h2.2.2.2.2, h1.2.2.2.2,
      valAt_ext hx.hlen (gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 h8.1)))) h3.2.2.2.1,
      h3.2.2.2.2, wordVal_ext hx.hlen h2.1 h1.2.2.2.1, h1.2.2.2.2,
      h8.2.2.2.2, valAt_ext hx.hlen (gExt_trans h5.1 (gExt_trans h6.1 h7.1)) h4.2.2.2.1,
      h4.2.2.2.2, wordVal_ext hx.hlen he13 hR,
      Sum8W.val_ext hx.hlen h8.1 hsL2_in]
  unfold Sum8W.val Sum8.ofSeg
  rw [hz7.2, hpW7.2, hb11_7.2, hb01_7.2, hb10_7.2,
      valAt_ext hx.hlen he17 hp, wordVal_ext hx.hlen he17 hR, wordVal_ext hx.hlen he17 hB,
      valAt_ext hx.hlen (gExt_trans h6.1 h7.1) h5.2.2.2.1, h5.2.2.2.2,
      valAt_ext hx.hlen (gExt_trans h2.1 (gExt_trans h3.1 h4.1)) (h1.2.2.2.1 ⟨0, hW⟩),
      valAt_ext hx.hlen he14 hp,
      valAt_ext hx.hlen h7.1 h6.2.2.2.1, h6.2.2.2.2,
      valAt_ext hx.hlen he15 (hB ⟨0, hW⟩), valAt_ext hx.hlen he15 hp,
      h7.2.2.2.2, valAt_ext hx.hlen he16 (hR ⟨0, hW⟩), valAt_ext hx.hlen he16 hp]
  have hLm := wordVal_mod_two hW g1 x L
  rw [h1.2.2.2.2] at hLm
  have hBm := wordVal_mod_two hW g x B
  have hRm := wordVal_mod_two hW g x R
  have hx11 : (xor (valAt g1 x (L ⟨0, hW⟩)) (valAt g x p)).toNat =
      (wordVal g x R + wordVal g x B + (valAt g x p).toNat) % 2 := by
    cases hL0 : valAt g1 x (L ⟨0, hW⟩) <;> cases hp0 : valAt g x p <;> simp [hL0, hp0] at hLm ⊢ <;> omega
  have hx01 : (xor (valAt g x (B ⟨0, hW⟩)) (valAt g x p)).toNat =
      (wordVal g x B + (valAt g x p).toNat) % 2 := by
    cases hB0 : valAt g x (B ⟨0, hW⟩) <;> cases hp0 : valAt g x p <;> simp [hB0, hp0] at hBm ⊢ <;> omega
  have hx10 : (xor (valAt g x (R ⟨0, hW⟩)) (valAt g x p)).toNat =
      (wordVal g x R + (valAt g x p).toNat) % 2 := by
    cases hR0 : valAt g x (R ⟨0, hW⟩) <;> cases hp0 : valAt g x p <;> simp [hR0, hp0] at hRm ⊢ <;> omega
  rw [hx11, hx01, hx10]
  by_cases hL0 : wordVal g x R + wordVal g x B = 0
  · simp [hL0]
  · simp only [hL0, decide_false, Bool.false_eq_true, ↓reduceIte]
    by_cases hL1 : wordVal g x R + wordVal g x B = 1
    · simp only [hL1, decide_true, ↓reduceIte]
      by_cases hR1 : wordVal g x R = 1 <;> simp [hR1]
    · simp [hL1]

private lemma arith_sub_add_sub_lt4 {r fr b fb M P : ℕ} (hP : P = 4 * M)
    (hr : r < M) (hb : b < M) : (r - fr) + (b - fb) < P := by omega

private lemma arith_sub_add_sub_add_lt4 {r fr b fb d M P : ℕ} (hP : P = 4 * M)
    (hr : r < M) (hb : b < M) (hd : d ≤ M - 1) : (r - fr) + (b - fb) + d < P := by omega

private lemma arith_le_add_le_lt4 {a b M P : ℕ} (hP : P = 4 * M) (hpos : 1 ≤ M)
    (ha : a ≤ M - 1) (hb : b ≤ M - 1) : a + b < P := by omega

private lemma arith_le_add_sub_lt4 {d x fx M P : ℕ} (hP : P = 4 * M) (hpos : 1 ≤ M)
    (hd : d ≤ M - 1) (hx : x < M) : d + (x - fx) < P := by omega

private lemma arith_sub_add_le_lt4 {x fx c M P : ℕ} (hP : P = 4 * M) (hpos : 1 ≤ M)
    (hx : x < M) (hc : c ≤ M - 1) : (x - fx) + c < P := by omega

private lemma arith_bool_eq_iff_mod2 {b1 b2 : Bool} {m n : ℕ}
    (h1 : m % 2 = b1.toNat) (h2 : n % 2 = b2.toNat) :
    (b1 == b2) = true ↔ m % 2 = n % 2 := by
  rw [h1, h2]; cases b1 <;> cases b2 <;> decide

private lemma arith_ite01_lt8_of_lt {a M P : ℕ} {c : Prop} [Decidable c]
    (hP : P = 8 * M) (hpos : 2 ≤ M) (ha : a < M) :
    a + (if c then 0 else 1) < P := by split_ifs <;> omega

private lemma arith_ite01_lt8_of_le2 {a M P : ℕ} {c : Prop} [Decidable c]
    (hP : P = 8 * M) (hpos : 2 ≤ M) (ha : a ≤ 2 * M) :
    a + (if c then 0 else 1) < P := by split_ifs <;> omega

private lemma arith_ite01_le_of_lt {a M : ℕ} {c : Prop} [Decidable c]
    (ha : a < M) : a + (if c then 0 else 1) ≤ M := by split_ifs <;> omega

private lemma arith_ite01_le_succ {a B : ℕ} {c : Prop} [Decidable c]
    (ha : a ≤ B) : a + (if c then 0 else 1) ≤ B + 1 := by split_ifs <;> omega

private lemma arith_leM_add_sub1_lt8 {a b M P : ℕ} (hP : P = 8 * M) (hpos : 2 ≤ M)
    (ha : a ≤ M) (hb : b ≤ M - 1) : a + b < P := by omega

private lemma arith_sub1_add_sub1_lt8 {a b M P : ℕ} (hP : P = 8 * M) (hpos : 2 ≤ M)
    (ha : a ≤ M - 1) (hb : b ≤ M - 1) : a + b < P := by omega

private lemma arith_sub1_add_leM_lt8 {a b M P : ℕ} (hP : P = 8 * M) (hpos : 2 ≤ M)
    (ha : a ≤ M - 1) (hb : b ≤ M) : a + b < P := by omega

private lemma arith_ltM_add_sub1_lt8 {a b M P : ℕ} (hP : P = 8 * M) (hpos : 2 ≤ M)
    (ha : a < M) (hb : b ≤ M - 1) : a + b < P := by omega

private lemma arith_sub1_add_le2p1_lt8 {a b M P : ℕ} (hP : P = 8 * M) (hpos : 2 ≤ M)
    (ha : a ≤ M - 1) (hb : b ≤ 2 * M + 1) : a + b < P := by omega

private lemma arith_sub1_add_le3p1_lt8 {a b M P : ℕ} (hP : P = 8 * M) (hpos : 2 ≤ M)
    (ha : a ≤ M - 1) (hb : b ≤ 3 * M + 1) : a + b < P := by omega

private lemma arith_rplo_le2 {r0 b0p d01 cb d00 b1p M : ℕ}
    (hr0 : r0 < M) (hb0p : b0p ≤ M) (hd01 : d01 ≤ M - 1) (hd00 : d00 ≤ M - 1) :
    max r0 (max (b0p + d01 - cb) (d00 - b1p)) ≤ 2 * M := by omega

private lemma arith_bp_le3p1 {b0p d00 rpt d10 cr M : ℕ}
    (hb0p : b0p ≤ M) (hd00 : d00 ≤ M - 1) (hd10 : d10 ≤ M - 1) (hrpt : rpt ≤ 2 * M + 1) :
    max b0p (max (d00 - rpt) (d10 + rpt - cr)) ≤ 3 * M + 1 := by omega

private lemma arith_max_sub_lt {a b M : ℕ} (ha : a ≤ M - 1) (hb : b < M) :
    max a b - a < M := by omega

private lemma arith_min_sub_lt {a c b M : ℕ} (hb : b < M) :
    min (a + c) b - a < M := by omega

private def cMemSum8 (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (s : Sum8W W)
    (r b : Word W) : List Gate × ℕ :=
  let (g1, rp, ok_fr) := cSubLeW nin g r s.fr
  let (g2, bp, ok_fb) := cSubLeW nin g1 b s.fb
  let (g3, ok_cr) := cLeW nin g2 rp s.cr
  let (g4, ok_cb) := cLeW nin g3 bp s.cb
  let (g5, sum_rb) := cAddW nin g4 rp bp
  let (g6, ok_par) := cEqBit nin g5 (sum_rb ⟨0, hW⟩) (s.d00 ⟨0, hW⟩)
  let (g7, ok_d00) := cLeW nin g6 s.d00 sum_rb
  let (g8, lhs11) := cAddW nin g7 sum_rb s.d11
  let (g9, rhs11) := cAddW nin g8 s.cr s.cb
  let (g10, ok_d11) := cLeW nin g9 lhs11 rhs11
  let (g11, lhs01) := cAddW nin g10 s.d01 bp
  let (g12, rhs01) := cAddW nin g11 rp s.cb
  let (g13, ok_d01) := cLeW nin g12 lhs01 rhs01
  let (g14, lhs10) := cAddW nin g13 s.d10 rp
  let (g15, rhs10) := cAddW nin g14 s.cr bp
  let (g16, ok_d10) := cLeW nin g15 lhs10 rhs10
  let (g17, a1) := emitAnd nin g16 ok_fr ok_fb
  let (g18, a2) := emitAnd nin g17 a1 ok_cr
  let (g19, a3) := emitAnd nin g18 a2 ok_cb
  let (g20, a4) := emitAnd nin g19 a3 ok_par
  let (g21, a5) := emitAnd nin g20 a4 ok_d00
  let (g22, a6) := emitAnd nin g21 a5 ok_d11
  let (g23, a7) := emitAnd nin g22 a6 ok_d01
  emitAnd nin g23 a7 ok_d10

private lemma cMemSum8_spec {nin W : ℕ} (hW : 1 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {s : Sum8W W} {r b : Word W}
    (hs : s.In (nin + g.length)) (hr : WordIn (nin + g.length) r) (hb : WordIn (nin + g.length) b)
    (hB : (s.val g x).Bound (2 ^ (W - 2) - 1) ∧ wordVal g x r < 2 ^ (W - 2) ∧ wordVal g x b < 2 ^ (W - 2))
    (hW3 : 3 ≤ W) :
    let res := cMemSum8 nin hW g s r b
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 200 * W ∧
    res.2 < nin + res.1.length ∧
    (valAt res.1 x res.2 = true ↔ (s.val g x).Mem (wordVal g x r) (wordVal g x b)) := by
  have hpow : 2 ^ W = 4 * 2 ^ (W - 2) := by
    calc 2 ^ W = 2 ^ ((W - 2) + 2) := by congr 1; omega
      _ = 4 * 2 ^ (W - 2) := by rw [pow_add]; ring
  have hpos : 1 ≤ 2 ^ (W - 2) := Nat.one_le_pow _ 2 (by decide)
  rcases hB with ⟨⟨hfrB, hfbB, hcrB, hcbB, hd00B, hd11B, hd01B, hd10B⟩, hrB, hbB⟩
  simp only [Sum8W.val] at hfrB hfbB hcrB hcbB hd00B hd11B hd01B hd10B
  unfold cMemSum8
  have h1 := cSubLeW_spec hx hv hr hs.1
  generalize cSubLeW nin g r s.fr = _r1 at h1 ⊢; rcases _r1 with ⟨g1, rp, ok_fr⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have h2 := cSubLeW_spec hx h1.2.1 (wordIn_ext h1.1 hb) (wordIn_ext h1.1 hs.2.1)
  generalize cSubLeW nin g1 b s.fb = _r2 at h2 ⊢; rcases _r2 with ⟨g2, bp, ok_fb⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have he12 := gExt_trans h1.1 h2.1
  have h3 := cLeW_spec hx h2.2.1 (wordIn_ext h2.1 h1.2.2.2.1) (wordIn_ext he12 hs.2.2.1)
  generalize cLeW nin g2 rp s.cr = _r3 at h3 ⊢; rcases _r3 with ⟨g3, ok_cr⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he13 := gExt_trans he12 h3.1
  have h4 := cLeW_spec hx h3.2.1 (wordIn_ext h3.1 h2.2.2.2.1) (wordIn_ext he13 hs.2.2.2.1)
  generalize cLeW nin g3 bp s.cb = _r4 at h4 ⊢; rcases _r4 with ⟨g4, ok_cb⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have he14 := gExt_trans he13 h4.1
  have e2_4 := gExt_trans h3.1 h4.1
  have e1_4 := gExt_trans h2.1 e2_4
  have h5 := cAddW_struct hx h4.2.1 (wordIn_ext e1_4 h1.2.2.2.1) (wordIn_ext e2_4 h2.2.2.2.1)
  generalize cAddW nin g4 rp bp = _r5 at h5 ⊢; rcases _r5 with ⟨g5, sum_rb⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have he15 := gExt_trans he14 h5.1
  have h6 := cEqBit_spec (a := (sum_rb ⟨0, hW⟩)) (b := (s.d00 ⟨0, hW⟩)) hx h5.2.1 (h5.2.2.2.1 ⟨0, hW⟩) (wire_ext he15 (hs.2.2.2.2.1 ⟨0, hW⟩))
  generalize cEqBit nin g5 (sum_rb ⟨0, hW⟩) (s.d00 ⟨0, hW⟩) = _r6 at h6 ⊢; rcases _r6 with ⟨g6, ok_par⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have he16 := gExt_trans he15 h6.1
  have h7 := cLeW_spec hx h6.2.1 (wordIn_ext he16 hs.2.2.2.2.1) (wordIn_ext h6.1 h5.2.2.2.1)
  generalize cLeW nin g6 s.d00 sum_rb = _r7 at h7 ⊢; rcases _r7 with ⟨g7, ok_d00⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have he17 := gExt_trans he16 h7.1
  have e5_7 := gExt_trans h6.1 h7.1
  have h8 := cAddW_struct hx h7.2.1 (wordIn_ext e5_7 h5.2.2.2.1) (wordIn_ext he17 hs.2.2.2.2.2.1)
  generalize cAddW nin g7 sum_rb s.d11 = _r8 at h8 ⊢; rcases _r8 with ⟨g8, lhs11⟩; dsimp only at h8; dsimp (config := { zeta := false }) only at ⊢
  have he18 := gExt_trans he17 h8.1
  have h9 := cAddW_struct hx h8.2.1 (wordIn_ext he18 hs.2.2.1) (wordIn_ext he18 hs.2.2.2.1)
  generalize cAddW nin g8 s.cr s.cb = _r9 at h9 ⊢; rcases _r9 with ⟨g9, rhs11⟩; dsimp only at h9; dsimp (config := { zeta := false }) only at ⊢
  have he19 := gExt_trans he18 h9.1
  have h10 := cLeW_spec hx h9.2.1 (wordIn_ext h9.1 h8.2.2.2.1) h9.2.2.2.1
  generalize cLeW nin g9 lhs11 rhs11 = _r10 at h10 ⊢; rcases _r10 with ⟨g10, ok_d11⟩; dsimp only at h10; dsimp (config := { zeta := false }) only at ⊢
  have he110 := gExt_trans he19 h10.1
  have e4_10 := gExt_trans h5.1 (gExt_trans e5_7 (gExt_trans h8.1 (gExt_trans h9.1 h10.1)))
  have e2_10 := gExt_trans e2_4 e4_10
  have h11 := cAddW_struct hx h10.2.1 (wordIn_ext he110 hs.2.2.2.2.2.2.1) (wordIn_ext e2_10 h2.2.2.2.1)
  generalize cAddW nin g10 s.d01 bp = _r11 at h11 ⊢; rcases _r11 with ⟨g11, lhs01⟩; dsimp only at h11; dsimp (config := { zeta := false }) only at ⊢
  have he111 := gExt_trans he110 h11.1
  have e1_11 := gExt_trans h2.1 (gExt_trans e2_10 h11.1)
  have h12 := cAddW_struct hx h11.2.1 (wordIn_ext e1_11 h1.2.2.2.1) (wordIn_ext he111 hs.2.2.2.1)
  generalize cAddW nin g11 rp s.cb = _r12 at h12 ⊢; rcases _r12 with ⟨g12, rhs01⟩; dsimp only at h12; dsimp (config := { zeta := false }) only at ⊢
  have he112 := gExt_trans he111 h12.1
  have h13 := cLeW_spec hx h12.2.1 (wordIn_ext h12.1 h11.2.2.2.1) h12.2.2.2.1
  generalize cLeW nin g12 lhs01 rhs01 = _r13 at h13 ⊢; rcases _r13 with ⟨g13, ok_d01⟩; dsimp only at h13; dsimp (config := { zeta := false }) only at ⊢
  have he113 := gExt_trans he112 h13.1
  have e1_13 := gExt_trans e1_11 (gExt_trans h12.1 h13.1)
  have h14 := cAddW_struct hx h13.2.1 (wordIn_ext he113 hs.2.2.2.2.2.2.2) (wordIn_ext e1_13 h1.2.2.2.1)
  generalize cAddW nin g13 s.d10 rp = _r14 at h14 ⊢; rcases _r14 with ⟨g14, lhs10⟩; dsimp only at h14; dsimp (config := { zeta := false }) only at ⊢
  have he114 := gExt_trans he113 h14.1
  have e2_14 := gExt_trans e2_10 (gExt_trans h11.1 (gExt_trans h12.1 (gExt_trans h13.1 h14.1)))
  have h15 := cAddW_struct hx h14.2.1 (wordIn_ext he114 hs.2.2.1) (wordIn_ext e2_14 h2.2.2.2.1)
  generalize cAddW nin g14 s.cr bp = _r15 at h15 ⊢; rcases _r15 with ⟨g15, rhs10⟩; dsimp only at h15; dsimp (config := { zeta := false }) only at ⊢
  have he115 := gExt_trans he114 h15.1
  have h16 := cLeW_spec hx h15.2.1 (wordIn_ext h15.1 h14.2.2.2.1) h15.2.2.2.1
  generalize cLeW nin g15 lhs10 rhs10 = _r16 at h16 ⊢; rcases _r16 with ⟨g16, ok_d10⟩; dsimp only at h16; dsimp (config := { zeta := false }) only at ⊢
  have he116 := gExt_trans he115 h16.1
  have e2_16 := gExt_trans e2_14 (gExt_trans h15.1 h16.1)
  have e1_16 := gExt_trans h2.1 e2_16
  have h17 := emitAnd_spec (a := ok_fr) (b := ok_fb) hx h16.2.1 (wire_ext e1_16 h1.2.2.2.2.1) (wire_ext e2_16 h2.2.2.2.2.1)
  generalize emitAnd nin g16 ok_fr ok_fb = _r17 at h17 ⊢; rcases _r17 with ⟨g17, a1⟩; dsimp only at h17; dsimp (config := { zeta := false }) only at ⊢
  have e10_16 := gExt_trans h11.1 (gExt_trans h12.1 (gExt_trans h13.1 (gExt_trans h14.1 (gExt_trans h15.1 h16.1))))
  have e4_17 := gExt_trans e4_10 (gExt_trans e10_16 h17.1)
  have e3_17 := gExt_trans h4.1 e4_17
  have h18 := emitAnd_spec (a := a1) (b := ok_cr) hx h17.2.1 h17.2.2.2.1 (wire_ext e3_17 h3.2.2.2.1)
  generalize emitAnd nin g17 a1 ok_cr = _r18 at h18 ⊢; rcases _r18 with ⟨g18, a2⟩; dsimp only at h18; dsimp (config := { zeta := false }) only at ⊢
  have e4_18 := gExt_trans e4_17 h18.1
  have h19 := emitAnd_spec (a := a2) (b := ok_cb) hx h18.2.1 h18.2.2.2.1 (wire_ext e4_18 h4.2.2.2.1)
  generalize emitAnd nin g18 a2 ok_cb = _r19 at h19 ⊢; rcases _r19 with ⟨g19, a3⟩; dsimp only at h19; dsimp (config := { zeta := false }) only at ⊢
  have e7_19 := gExt_trans h8.1 (gExt_trans h9.1 (gExt_trans h10.1 (gExt_trans e10_16 (gExt_trans h17.1 (gExt_trans h18.1 h19.1)))))
  have e6_19 := gExt_trans h7.1 e7_19
  have h20 := emitAnd_spec (a := a3) (b := ok_par) hx h19.2.1 h19.2.2.2.1 (wire_ext e6_19 h6.2.2.2.1)
  generalize emitAnd nin g19 a3 ok_par = _r20 at h20 ⊢; rcases _r20 with ⟨g20, a4⟩; dsimp only at h20; dsimp (config := { zeta := false }) only at ⊢
  have e7_20 := gExt_trans e7_19 h20.1
  have h21 := emitAnd_spec (a := a4) (b := ok_d00) hx h20.2.1 h20.2.2.2.1 (wire_ext e7_20 h7.2.2.2.1)
  generalize emitAnd nin g20 a4 ok_d00 = _r21 at h21 ⊢; rcases _r21 with ⟨g21, a5⟩; dsimp only at h21; dsimp (config := { zeta := false }) only at ⊢
  have e16_21 := gExt_trans h17.1 (gExt_trans h18.1 (gExt_trans h19.1 (gExt_trans h20.1 h21.1)))
  have e10_21 := gExt_trans e10_16 e16_21
  have h22 := emitAnd_spec (a := a5) (b := ok_d11) hx h21.2.1 h21.2.2.2.1 (wire_ext e10_21 h10.2.2.2.1)
  generalize emitAnd nin g21 a5 ok_d11 = _r22 at h22 ⊢; rcases _r22 with ⟨g22, a6⟩; dsimp only at h22; dsimp (config := { zeta := false }) only at ⊢
  have e13_22 := gExt_trans h14.1 (gExt_trans h15.1 (gExt_trans h16.1 (gExt_trans e16_21 h22.1)))
  have h23 := emitAnd_spec (a := a6) (b := ok_d01) hx h22.2.1 h22.2.2.2.1 (wire_ext e13_22 h13.2.2.2.1)
  generalize emitAnd nin g22 a6 ok_d01 = _r23 at h23 ⊢; rcases _r23 with ⟨g23, a7⟩; dsimp only at h23; dsimp (config := { zeta := false }) only at ⊢
  have e16_23 := gExt_trans e16_21 (gExt_trans h22.1 h23.1)
  have h24 := emitAnd_spec (a := a7) (b := ok_d10) hx h23.2.1 h23.2.2.2.1 (wire_ext e16_23 h16.2.2.2.1)
  generalize emitAnd nin g23 a7 ok_d10 = _r24 at h24 ⊢; rcases _r24 with ⟨g24, out⟩; dsimp only at h24 ⊢
  have he16_24 := gExt_trans e16_23 h24.1
  refine ⟨gExt_trans he116 he16_24, h24.2.1,
    by linarith only [hW, h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1, h6.2.2.1,
      h7.2.2.1, h8.2.2.1, h9.2.2.1, h10.2.2.1, h11.2.2.1, h12.2.2.1, h13.2.2.1, h14.2.2.1,
      h15.2.2.1, h16.2.2.1, h17.2.2.1, h18.2.2.1, h19.2.2.1, h20.2.2.1, h21.2.2.1,
      h22.2.2.1, h23.2.2.1, h24.2.2.1],
    h24.2.2.2.1, ?_⟩
  have hand_val : valAt g24 x out =
      ((((((((valAt g1 x ok_fr && valAt g2 x ok_fb) && valAt g3 x ok_cr) && valAt g4 x ok_cb) &&
        valAt g6 x ok_par) && valAt g7 x ok_d00) && valAt g10 x ok_d11) && valAt g13 x ok_d01) &&
        valAt g16 x ok_d10) := by
    rw [h24.2.2.2.2, h23.2.2.2.2, h22.2.2.2.2, h21.2.2.2.2, h20.2.2.2.2, h19.2.2.2.2, h18.2.2.2.2, h17.2.2.2.2]
    rw [valAt_ext hx.hlen e1_16 h1.2.2.2.2.1, valAt_ext hx.hlen e2_16 h2.2.2.2.2.1,
        valAt_ext hx.hlen e3_17 h3.2.2.2.1, valAt_ext hx.hlen e4_18 h4.2.2.2.1,
        valAt_ext hx.hlen e6_19 h6.2.2.2.1, valAt_ext hx.hlen e7_20 h7.2.2.2.1,
        valAt_ext hx.hlen e10_21 h10.2.2.2.1, valAt_ext hx.hlen e13_22 h13.2.2.2.1,
        valAt_ext hx.hlen e16_23 h16.2.2.2.1]
  rw [hand_val, h1.2.2.2.2.2.1, h2.2.2.2.2.2.1, wordVal_ext hx.hlen h1.1 hb, wordVal_ext hx.hlen h1.1 hs.2.1]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hvals : wordVal g x s.fr ≤ wordVal g x r → wordVal g x s.fb ≤ wordVal g x b →
      wordVal g1 x rp = wordVal g x r - wordVal g x s.fr ∧
      wordVal g2 x bp = wordVal g x b - wordVal g x s.fb ∧
      wordVal g5 x sum_rb = (wordVal g x r - wordVal g x s.fr) + (wordVal g x b - wordVal g x s.fb) ∧
      wordVal g8 x lhs11 = (wordVal g x r - wordVal g x s.fr) + (wordVal g x b - wordVal g x s.fb) + wordVal g x s.d11 ∧
      wordVal g9 x rhs11 = wordVal g x s.cr + wordVal g x s.cb ∧
      wordVal g11 x lhs01 = wordVal g x s.d01 + (wordVal g x b - wordVal g x s.fb) ∧
      wordVal g12 x rhs01 = (wordVal g x r - wordVal g x s.fr) + wordVal g x s.cb ∧
      wordVal g14 x lhs10 = wordVal g x s.d10 + (wordVal g x r - wordVal g x s.fr) ∧
      wordVal g15 x rhs10 = wordVal g x s.cr + (wordVal g x b - wordVal g x s.fb) := by
    intro hle_r hle_b
    have hrp := h1.2.2.2.2.2.2 hle_r
    have hbp := h2.2.2.2.2.2.2 (by rw [wordVal_ext hx.hlen h1.1 hb, wordVal_ext hx.hlen h1.1 hs.2.1]; exact hle_b)
    rw [wordVal_ext hx.hlen h1.1 hb, wordVal_ext hx.hlen h1.1 hs.2.1] at hbp
    have h5v : wordVal g5 x sum_rb = (wordVal g x r - wordVal g x s.fr) + (wordVal g x b - wordVal g x s.fb) := by
      rw [h5.2.2.2.2 (by rw [wordVal_ext hx.hlen e1_4 h1.2.2.2.1, wordVal_ext hx.hlen e2_4 h2.2.2.2.1, hrp, hbp]; exact arith_sub_add_sub_lt4 hpow hrB hbB),
        wordVal_ext hx.hlen e1_4 h1.2.2.2.1, wordVal_ext hx.hlen e2_4 h2.2.2.2.1, hrp, hbp]
    have h8v : wordVal g8 x lhs11 = (wordVal g x r - wordVal g x s.fr) + (wordVal g x b - wordVal g x s.fb) + wordVal g x s.d11 := by
      rw [h8.2.2.2.2 (by rw [wordVal_ext hx.hlen e5_7 h5.2.2.2.1, wordVal_ext hx.hlen he17 hs.2.2.2.2.2.1, h5v]; exact arith_sub_add_sub_add_lt4 hpow hrB hbB hd11B),
        wordVal_ext hx.hlen e5_7 h5.2.2.2.1, wordVal_ext hx.hlen he17 hs.2.2.2.2.2.1, h5v]
    have h9v : wordVal g9 x rhs11 = wordVal g x s.cr + wordVal g x s.cb := by
      rw [h9.2.2.2.2 (by rw [wordVal_ext hx.hlen he18 hs.2.2.1, wordVal_ext hx.hlen he18 hs.2.2.2.1]; exact arith_le_add_le_lt4 hpow hpos hcrB hcbB),
        wordVal_ext hx.hlen he18 hs.2.2.1, wordVal_ext hx.hlen he18 hs.2.2.2.1]
    have h11v : wordVal g11 x lhs01 = wordVal g x s.d01 + (wordVal g x b - wordVal g x s.fb) := by
      rw [h11.2.2.2.2 (by rw [wordVal_ext hx.hlen he110 hs.2.2.2.2.2.2.1, wordVal_ext hx.hlen e2_10 h2.2.2.2.1, hbp]; exact arith_le_add_sub_lt4 hpow hpos hd01B hbB),
        wordVal_ext hx.hlen he110 hs.2.2.2.2.2.2.1, wordVal_ext hx.hlen e2_10 h2.2.2.2.1, hbp]
    have h12v : wordVal g12 x rhs01 = (wordVal g x r - wordVal g x s.fr) + wordVal g x s.cb := by
      rw [h12.2.2.2.2 (by rw [wordVal_ext hx.hlen e1_11 h1.2.2.2.1, wordVal_ext hx.hlen he111 hs.2.2.2.1, hrp]; exact arith_sub_add_le_lt4 hpow hpos hrB hcbB),
        wordVal_ext hx.hlen e1_11 h1.2.2.2.1, wordVal_ext hx.hlen he111 hs.2.2.2.1, hrp]
    have h14v : wordVal g14 x lhs10 = wordVal g x s.d10 + (wordVal g x r - wordVal g x s.fr) := by
      rw [h14.2.2.2.2 (by rw [wordVal_ext hx.hlen he113 hs.2.2.2.2.2.2.2, wordVal_ext hx.hlen e1_13 h1.2.2.2.1, hrp]; exact arith_le_add_sub_lt4 hpow hpos hd10B hrB),
        wordVal_ext hx.hlen he113 hs.2.2.2.2.2.2.2, wordVal_ext hx.hlen e1_13 h1.2.2.2.1, hrp]
    have h15v : wordVal g15 x rhs10 = wordVal g x s.cr + (wordVal g x b - wordVal g x s.fb) := by
      rw [h15.2.2.2.2 (by rw [wordVal_ext hx.hlen he114 hs.2.2.1, wordVal_ext hx.hlen e2_14 h2.2.2.2.1, hbp]; exact arith_le_add_sub_lt4 hpow hpos hcrB hbB),
        wordVal_ext hx.hlen he114 hs.2.2.1, wordVal_ext hx.hlen e2_14 h2.2.2.2.1, hbp]
    exact ⟨hrp, hbp, h5v, h8v, h9v, h11v, h12v, h14v, h15v⟩
  have hchecks : wordVal g x s.fr ≤ wordVal g x r → wordVal g x s.fb ≤ wordVal g x b →
      (valAt g3 x ok_cr = true ↔ wordVal g x r ≤ wordVal g x s.fr + wordVal g x s.cr) ∧
      (valAt g4 x ok_cb = true ↔ wordVal g x b ≤ wordVal g x s.fb + wordVal g x s.cb) ∧
      (valAt g6 x ok_par = true ↔ ((wordVal g x r - wordVal g x s.fr) + (wordVal g x b - wordVal g x s.fb)) % 2 = wordVal g x s.d00 % 2) ∧
      (valAt g7 x ok_d00 = true ↔ wordVal g x s.d00 ≤ (wordVal g x r - wordVal g x s.fr) + (wordVal g x b - wordVal g x s.fb)) ∧
      (valAt g10 x ok_d11 = true ↔ (wordVal g x r - wordVal g x s.fr) + (wordVal g x b - wordVal g x s.fb) + wordVal g x s.d11 ≤ wordVal g x s.cr + wordVal g x s.cb) ∧
      (valAt g13 x ok_d01 = true ↔ wordVal g x s.d01 + (wordVal g x b - wordVal g x s.fb) ≤ (wordVal g x r - wordVal g x s.fr) + wordVal g x s.cb) ∧
      (valAt g16 x ok_d10 = true ↔ wordVal g x s.d10 + (wordVal g x r - wordVal g x s.fr) ≤ wordVal g x s.cr + (wordVal g x b - wordVal g x s.fb)) := by
    intro hle_r hle_b
    rcases hvals hle_r hle_b with ⟨hrp, hbp, h5v, h8v, h9v, h11v, h12v, h14v, h15v⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h3.2.2.2.2, wordVal_ext hx.hlen h2.1 h1.2.2.2.1, wordVal_ext hx.hlen he12 hs.2.2.1, hrp, decide_eq_true_eq]
      exact Nat.sub_le_iff_le_add'
    · rw [h4.2.2.2.2, wordVal_ext hx.hlen h3.1 h2.2.2.2.1, wordVal_ext hx.hlen he13 hs.2.2.2.1, hbp, decide_eq_true_eq]
      exact Nat.sub_le_iff_le_add'
    · rw [h6.2.2.2.2, valAt_ext hx.hlen he15 (hs.2.2.2.2.1 ⟨0, hW⟩)]
      have hm1 := wordVal_mod_two hW g5 x sum_rb
      have hm2 := wordVal_mod_two hW g x s.d00
      rw [h5v] at hm1
      exact arith_bool_eq_iff_mod2 hm1 hm2
    · rw [h7.2.2.2.2, wordVal_ext hx.hlen he16 hs.2.2.2.2.1, wordVal_ext hx.hlen h6.1 h5.2.2.2.1, h5v]; simp
    · rw [h10.2.2.2.2, wordVal_ext hx.hlen h9.1 h8.2.2.2.1, h8v, h9v]; simp
    · rw [h13.2.2.2.2, wordVal_ext hx.hlen h12.1 h11.2.2.2.1, h11v, h12v]; simp
    · rw [h16.2.2.2.2, wordVal_ext hx.hlen h15.1 h14.2.2.2.1, h14v, h15v]; simp
  unfold Sum8.Mem Sum8W.val
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨hfr', hfb'⟩, hcr'⟩, hcb'⟩, hpar'⟩, hd00'⟩, hd11'⟩, hd01'⟩, hd10'⟩
    rcases hchecks hfr' hfb' with ⟨c1, c2, c3, c4, c5, c6, c7⟩
    exact ⟨hfr', c1.mp hcr', hfb', c2.mp hcb', c3.mp hpar', c4.mp hd00', c5.mp hd11', c6.mp hd01', c7.mp hd10'⟩
  · rintro ⟨hfr', hcr', hfb', hcb', hpar', hd00', hd11', hd01', hd10'⟩
    rcases hchecks hfr' hfb' with ⟨c1, c2, c3, c4, c5, c6, c7⟩
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hfr', hfb'⟩, c1.mpr hcr'⟩, c2.mpr hcb'⟩, c3.mpr hpar'⟩,
      c4.mpr hd00'⟩, c5.mpr hd11'⟩, c6.mpr hd01'⟩, c7.mpr hd10'⟩

private def cQueryParity1 (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (s : Sum8W W)
    (r0 r1 b0 b1 : Word W) (tBit : ℕ) : List Gate × ℕ × Word W × Word W × Word W :=
  let (g1, pB) := cXor nin g tBit (s.d00 ⟨0, hW⟩)
  let (g2, eq_b0) := cEqBit nin g1 (b0 ⟨0, hW⟩) pB
  let (g3, add_b0) := emitNot nin g2 eq_b0
  let (g4, b0p) := cAddW nin g3 b0 (cConstBit W add_b0)
  let (g5, b1_z) := cEqZeroW nin g4 b1
  let (g6, b1_u) := emitAnd nin g5 b1_z pB
  let (g7, eq_b1) := cEqBit nin g6 (b1 ⟨0, hW⟩) pB
  let (g8, sub_b1) := emitNot nin g7 eq_b1
  let (g9, b1p) := cSubTruncW nin g8 b1 (cConstBit W sub_b1)
  let (g10, nb1u) := emitNot nin g9 b1_u
  let (g11, le_b) := cLeW nin g10 b0p b1p
  let (g12, ok_b) := emitAnd nin g11 nb1u le_b
  let (g13, t1) := cAddW nin g12 b0p s.d01
  let (g14, lb2) := cSubTruncW nin g13 t1 s.cb
  let (g15, lb3) := cSubTruncW nin g14 s.d00 b1p
  let (g16, lb23) := cMaxW nin g15 lb2 lb3
  let (g17, rp_lo) := cMaxW nin g16 r0 lb23
  let (g18, crcb) := cAddW nin g17 s.cr s.cb
  let (g19, d11b0) := cAddW nin g18 s.d11 b0p
  let (g20, ub2) := cSubTruncW nin g19 crcb d11b0
  let (g21, b1cr) := cAddW nin g20 b1p s.cr
  let (g22, ub3) := cSubTruncW nin g21 b1cr s.d10
  let (g23, ub23) := cMinW nin g22 ub2 ub3
  let (g24, rp_hi) := cMinW nin g23 r1 ub23
  (g24, ok_b, b0p, rp_lo, rp_hi)

private lemma cQueryParity1_spec {nin W : ℕ} (hW : 1 ≤ W) (hW4 : 4 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {s : Sum8W W} {r0 r1 b0 b1 : Word W} {tBit : ℕ}
    (hs : s.In (nin + g.length))
    (hr0 : WordIn (nin + g.length) r0) (hr1 : WordIn (nin + g.length) r1)
    (hb0 : WordIn (nin + g.length) b0) (hb1 : WordIn (nin + g.length) b1)
    (ht : tBit < nin + g.length)
    (hB : (s.val g x).Bound (2 ^ (W - 3) - 1) ∧
      wordVal g x r0 < 2 ^ (W - 3) ∧ wordVal g x r1 < 2 ^ (W - 3) ∧
      wordVal g x b0 < 2 ^ (W - 3) ∧ wordVal g x b1 < 2 ^ (W - 3)) :
    let res := cQueryParity1 nin hW g s r0 r1 b0 b1 tBit
    let sv := s.val g x
    let pB : Bool := xor (valAt g x tBit) (decide (sv.d00 % 2 = 1))
    let b0p : ℕ := wordVal g x b0 + if decide (wordVal g x b0 % 2 = 1) == pB then 0 else 1
    let b1_u : Bool := decide (wordVal g x b1 = 0) && pB
    let b1p : ℕ := wordVal g x b1 - if decide (wordVal g x b1 % 2 = 1) == pB then 0 else 1
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 240 * W ∧
    res.2.1 < nin + res.1.length ∧
    WordIn (nin + res.1.length) res.2.2.1 ∧
    WordIn (nin + res.1.length) res.2.2.2.1 ∧
    WordIn (nin + res.1.length) res.2.2.2.2 ∧
    valAt res.1 x res.2.1 = ((!b1_u) && decide (b0p ≤ b1p)) ∧
    wordVal res.1 x res.2.2.1 = b0p ∧
    wordVal res.1 x res.2.2.2.1 = max (wordVal g x r0) (max (b0p + sv.d01 - sv.cb) (sv.d00 - b1p)) ∧
    wordVal res.1 x res.2.2.2.2 = min (wordVal g x r1) (min (sv.cr + sv.cb - (sv.d11 + b0p)) (b1p + sv.cr - sv.d10)) := by
  have hpow : 2 ^ W = 8 * 2 ^ (W - 3) := by
    calc 2 ^ W = 2 ^ ((W - 3) + 3) := by congr 1; omega
      _ = 8 * 2 ^ (W - 3) := by rw [pow_add]; ring
  have hpos : 2 ≤ 2 ^ (W - 3) := by
    have : 2 ^ 1 ≤ 2 ^ (W - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  rcases hB with ⟨⟨hfrB, hfbB, hcrB, hcbB, hd00B, hd11B, hd01B, hd10B⟩, hr0B, hr1B, hb0B, hb1B⟩
  simp only [Sum8W.val] at hfrB hfbB hcrB hcbB hd00B hd11B hd01B hd10B
  unfold cQueryParity1
  have h1 := cXor_spec hx hv ht (hs.2.2.2.2.1 ⟨0, hW⟩)
  generalize cXor nin g tBit (s.d00 ⟨0, hW⟩) = _r1 at h1 ⊢; rcases _r1 with ⟨g1, pB⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have hpB_val : valAt g1 x pB = xor (valAt g x tBit) (decide (wordVal g x s.d00 % 2 = 1)) := by
    rw [h1.2.2.2.2]; have hm := wordVal_mod_two hW g x s.d00
    cases hd : valAt g x (s.d00 ⟨0, hW⟩) <;> simp [hd] at hm ⊢ <;> simp [hm]
  have h2 := cEqBit_spec (a := (b0 ⟨0, hW⟩)) (b := pB) hx h1.2.1 (wire_ext h1.1 (hb0 ⟨0, hW⟩)) h1.2.2.2.1
  generalize cEqBit nin g1 (b0 ⟨0, hW⟩) pB = _r2 at h2 ⊢; rcases _r2 with ⟨g2, eq_b0⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have he12 := gExt_trans h1.1 h2.1
  have h3 := emitNot_spec hx h2.2.1 h2.2.2.2.1
  generalize emitNot nin g2 eq_b0 = _r3 at h3 ⊢; rcases _r3 with ⟨g3, add_b0⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he13 := gExt_trans he12 h3.1
  have hadd_b0_val : (valAt g3 x add_b0).toNat =
      if decide (wordVal g x b0 % 2 = 1) == xor (valAt g x tBit) (decide (wordVal g x s.d00 % 2 = 1)) then 0 else 1 := by
    rw [h3.2.2.2.2, h2.2.2.2.2, valAt_ext hx.hlen h1.1 (hb0 ⟨0, hW⟩), hpB_val]
    have hm := wordVal_mod_two hW g x b0
    cases h0 : valAt g x (b0 ⟨0, hW⟩) <;> cases hpx : xor (valAt g x tBit) (decide (wordVal g x s.d00 % 2 = 1)) <;>
      simp [h0, hpx] at hm ⊢ <;> simp [hm]
  have hcb0 := cConstBit_spec hW (g := g3) hx h3.2.2.2.1
  have h4 := cAddW_spec hx h3.2.1 (wordIn_ext he13 hb0) hcb0.1
    (by rw [wordVal_ext hx.hlen he13 hb0, hcb0.2, hadd_b0_val]; exact arith_ite01_lt8_of_lt hpow hpos hb0B)
  generalize cAddW nin g3 b0 (cConstBit W add_b0) = _r4 at h4 ⊢; rcases _r4 with ⟨g4, b0p⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have he14 := gExt_trans he13 h4.1
  have hb0p_val : wordVal g4 x b0p = wordVal g x b0 +
      if decide (wordVal g x b0 % 2 = 1) == xor (valAt g x tBit) (decide (wordVal g x s.d00 % 2 = 1)) then 0 else 1 := by
    rw [h4.2.2.2.2, wordVal_ext hx.hlen he13 hb0, hcb0.2, hadd_b0_val]
  have hb0p_lt : wordVal g4 x b0p ≤ 2 ^ (W - 3) := by rw [hb0p_val]; exact arith_ite01_le_of_lt hb0B
  have h5 := cEqZeroW_spec hx h4.2.1 (wordIn_ext he14 hb1)
  generalize cEqZeroW nin g4 b1 = _r5 at h5 ⊢; rcases _r5 with ⟨g5, b1_z⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have he15 := gExt_trans he14 h5.1
  have e1_5 := gExt_trans h2.1 (gExt_trans h3.1 (gExt_trans h4.1 h5.1))
  have h6 := emitAnd_spec (a := b1_z) (b := pB) hx h5.2.1 h5.2.2.2.1 (wire_ext e1_5 h1.2.2.2.1)
  generalize emitAnd nin g5 b1_z pB = _r6 at h6 ⊢; rcases _r6 with ⟨g6, b1_u⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have he16 := gExt_trans he15 h6.1
  have e1_6 := gExt_trans e1_5 h6.1
  have hb1u_val : valAt g6 x b1_u =
      (decide (wordVal g x b1 = 0) && xor (valAt g x tBit) (decide (wordVal g x s.d00 % 2 = 1))) := by
    rw [h6.2.2.2.2, h5.2.2.2.2, wordVal_ext hx.hlen he14 hb1, valAt_ext hx.hlen e1_5 h1.2.2.2.1, hpB_val]
  have h7 := cEqBit_spec (a := (b1 ⟨0, hW⟩)) (b := pB) hx h6.2.1 (wire_ext he16 (hb1 ⟨0, hW⟩)) (wire_ext e1_6 h1.2.2.2.1)
  generalize cEqBit nin g6 (b1 ⟨0, hW⟩) pB = _r7 at h7 ⊢; rcases _r7 with ⟨g7, eq_b1⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have he17 := gExt_trans he16 h7.1
  have h8 := emitNot_spec hx h7.2.1 h7.2.2.2.1
  generalize emitNot nin g7 eq_b1 = _r8 at h8 ⊢; rcases _r8 with ⟨g8, sub_b1⟩; dsimp only at h8; dsimp (config := { zeta := false }) only at ⊢
  have he18 := gExt_trans he17 h8.1
  have hsub_b1_val : (valAt g8 x sub_b1).toNat =
      if decide (wordVal g x b1 % 2 = 1) == xor (valAt g x tBit) (decide (wordVal g x s.d00 % 2 = 1)) then 0 else 1 := by
    rw [h8.2.2.2.2, h7.2.2.2.2, valAt_ext hx.hlen he16 (hb1 ⟨0, hW⟩),
      valAt_ext hx.hlen e1_6 h1.2.2.2.1, hpB_val]
    have hm := wordVal_mod_two hW g x b1
    cases h0 : valAt g x (b1 ⟨0, hW⟩) <;> cases hpx : xor (valAt g x tBit) (decide (wordVal g x s.d00 % 2 = 1)) <;>
      simp [h0, hpx] at hm ⊢ <;> simp [hm]
  have hcb1 := cConstBit_spec hW (g := g8) hx h8.2.2.2.1
  have h9 := cSubTruncW_spec hx h8.2.1 (wordIn_ext he18 hb1) hcb1.1
  generalize cSubTruncW nin g8 b1 (cConstBit W sub_b1) = _r9 at h9 ⊢; rcases _r9 with ⟨g9, b1p⟩; dsimp only at h9; dsimp (config := { zeta := false }) only at ⊢
  have he19 := gExt_trans he18 h9.1
  have hb1p_val : wordVal g9 x b1p = wordVal g x b1 -
      if decide (wordVal g x b1 % 2 = 1) == xor (valAt g x tBit) (decide (wordVal g x s.d00 % 2 = 1)) then 0 else 1 := by
    rw [h9.2.2.2.2, wordVal_ext hx.hlen he18 hb1, hcb1.2, hsub_b1_val]
  have hb1p_lt : wordVal g9 x b1p < 2 ^ (W - 3) := by
    rw [hb1p_val]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb1B
  have e6_9 := gExt_trans h7.1 (gExt_trans h8.1 h9.1)
  have h10 := emitNot_spec (a := b1_u) hx h9.2.1 (wire_ext e6_9 h6.2.2.2.1)
  generalize emitNot nin g9 b1_u = _r10 at h10 ⊢; rcases _r10 with ⟨g10, nb1u⟩; dsimp only at h10; dsimp (config := { zeta := false }) only at ⊢
  have he110 := gExt_trans he19 h10.1
  have e4_10 := gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans e6_9 h10.1))
  have h11 := cLeW_spec hx h10.2.1 (wordIn_ext e4_10 h4.2.2.2.1) (wordIn_ext h10.1 h9.2.2.2.1)
  generalize cLeW nin g10 b0p b1p = _r11 at h11 ⊢; rcases _r11 with ⟨g11, le_b⟩; dsimp only at h11; dsimp (config := { zeta := false }) only at ⊢
  have he111 := gExt_trans he110 h11.1
  have h12 := emitAnd_spec (a := nb1u) (b := le_b) hx h11.2.1 (wire_ext h11.1 h10.2.2.2.1) h11.2.2.2.1
  generalize emitAnd nin g11 nb1u le_b = _r12 at h12 ⊢; rcases _r12 with ⟨g12, ok_b⟩; dsimp only at h12; dsimp (config := { zeta := false }) only at ⊢
  have he112 := gExt_trans he111 h12.1
  have e4_12 := gExt_trans e4_10 (gExt_trans h11.1 h12.1)
  have h13 := cAddW_spec hx h12.2.1 (wordIn_ext e4_12 h4.2.2.2.1) (wordIn_ext he112 hs.2.2.2.2.2.2.1)
    (by rw [wordVal_ext hx.hlen e4_12 h4.2.2.2.1, wordVal_ext hx.hlen he112 hs.2.2.2.2.2.2.1]; exact arith_leM_add_sub1_lt8 hpow hpos hb0p_lt hd01B)
  generalize cAddW nin g12 b0p s.d01 = _r13 at h13 ⊢; rcases _r13 with ⟨g13, t1⟩; dsimp only at h13; dsimp (config := { zeta := false }) only at ⊢
  have he113 := gExt_trans he112 h13.1
  have ht1_val : wordVal g13 x t1 = wordVal g4 x b0p + wordVal g x s.d01 := by
    rw [h13.2.2.2.2, wordVal_ext hx.hlen e4_12 h4.2.2.2.1, wordVal_ext hx.hlen he112 hs.2.2.2.2.2.2.1]
  have h14 := cSubTruncW_spec hx h13.2.1 h13.2.2.2.1 (wordIn_ext he113 hs.2.2.2.1)
  generalize cSubTruncW nin g13 t1 s.cb = _r14 at h14 ⊢; rcases _r14 with ⟨g14, lb2⟩; dsimp only at h14; dsimp (config := { zeta := false }) only at ⊢
  have he114 := gExt_trans he113 h14.1
  have hlb2_val : wordVal g14 x lb2 = wordVal g4 x b0p + wordVal g x s.d01 - wordVal g x s.cb := by
    rw [h14.2.2.2.2, ht1_val, wordVal_ext hx.hlen he113 hs.2.2.2.1]
  have e9_14 := gExt_trans h10.1 (gExt_trans h11.1 (gExt_trans h12.1 (gExt_trans h13.1 h14.1)))
  have h15 := cSubTruncW_spec hx h14.2.1 (wordIn_ext he114 hs.2.2.2.2.1) (wordIn_ext e9_14 h9.2.2.2.1)
  generalize cSubTruncW nin g14 s.d00 b1p = _r15 at h15 ⊢; rcases _r15 with ⟨g15, lb3⟩; dsimp only at h15; dsimp (config := { zeta := false }) only at ⊢
  have he115 := gExt_trans he114 h15.1
  have hlb3_val : wordVal g15 x lb3 = wordVal g x s.d00 - wordVal g9 x b1p := by
    rw [h15.2.2.2.2, wordVal_ext hx.hlen he114 hs.2.2.2.2.1, wordVal_ext hx.hlen e9_14 h9.2.2.2.1]
  have h16 := cMaxW_spec hx h15.2.1 (wordIn_ext h15.1 h14.2.2.2.1) h15.2.2.2.1
  generalize cMaxW nin g15 lb2 lb3 = _r16 at h16 ⊢; rcases _r16 with ⟨g16, lb23⟩; dsimp only at h16; dsimp (config := { zeta := false }) only at ⊢
  have he116 := gExt_trans he115 h16.1
  have h17 := cMaxW_spec hx h16.2.1 (wordIn_ext he116 hr0) h16.2.2.2.1
  generalize cMaxW nin g16 r0 lb23 = _r17 at h17 ⊢; rcases _r17 with ⟨g17, rp_lo⟩; dsimp only at h17; dsimp (config := { zeta := false }) only at ⊢
  have he117 := gExt_trans he116 h17.1
  have h18 := cAddW_spec hx h17.2.1 (wordIn_ext he117 hs.2.2.1) (wordIn_ext he117 hs.2.2.2.1)
    (by rw [wordVal_ext hx.hlen he117 hs.2.2.1, wordVal_ext hx.hlen he117 hs.2.2.2.1]; exact arith_sub1_add_sub1_lt8 hpow hpos hcrB hcbB)
  generalize cAddW nin g17 s.cr s.cb = _r18 at h18 ⊢; rcases _r18 with ⟨g18, crcb⟩; dsimp only at h18; dsimp (config := { zeta := false }) only at ⊢
  have he118 := gExt_trans he117 h18.1
  have e12_18 := gExt_trans h13.1 (gExt_trans h14.1 (gExt_trans h15.1 (gExt_trans h16.1 (gExt_trans h17.1 h18.1))))
  have e4_18 := gExt_trans e4_12 e12_18
  have h19 := cAddW_spec hx h18.2.1 (wordIn_ext he118 hs.2.2.2.2.2.1) (wordIn_ext e4_18 h4.2.2.2.1)
    (by rw [wordVal_ext hx.hlen he118 hs.2.2.2.2.2.1, wordVal_ext hx.hlen e4_18 h4.2.2.2.1]; exact arith_sub1_add_leM_lt8 hpow hpos hd11B hb0p_lt)
  generalize cAddW nin g18 s.d11 b0p = _r19 at h19 ⊢; rcases _r19 with ⟨g19, d11b0⟩; dsimp only at h19; dsimp (config := { zeta := false }) only at ⊢
  have he119 := gExt_trans he118 h19.1
  have h20 := cSubTruncW_spec hx h19.2.1 (wordIn_ext h19.1 h18.2.2.2.1) h19.2.2.2.1
  generalize cSubTruncW nin g19 crcb d11b0 = _r20 at h20 ⊢; rcases _r20 with ⟨g20, ub2⟩; dsimp only at h20; dsimp (config := { zeta := false }) only at ⊢
  have he120 := gExt_trans he119 h20.1
  have e14_20 := gExt_trans h15.1 (gExt_trans h16.1 (gExt_trans h17.1 (gExt_trans h18.1 (gExt_trans h19.1 h20.1))))
  have e9_20 := gExt_trans e9_14 e14_20
  have h21 := cAddW_spec hx h20.2.1 (wordIn_ext e9_20 h9.2.2.2.1) (wordIn_ext he120 hs.2.2.1)
    (by rw [wordVal_ext hx.hlen e9_20 h9.2.2.2.1, wordVal_ext hx.hlen he120 hs.2.2.1]; exact arith_ltM_add_sub1_lt8 hpow hpos hb1p_lt hcrB)
  generalize cAddW nin g20 b1p s.cr = _r21 at h21 ⊢; rcases _r21 with ⟨g21, b1cr⟩; dsimp only at h21; dsimp (config := { zeta := false }) only at ⊢
  have he121 := gExt_trans he120 h21.1
  have h22 := cSubTruncW_spec hx h21.2.1 h21.2.2.2.1 (wordIn_ext he121 hs.2.2.2.2.2.2.2)
  generalize cSubTruncW nin g21 b1cr s.d10 = _r22 at h22 ⊢; rcases _r22 with ⟨g22, ub3⟩; dsimp only at h22; dsimp (config := { zeta := false }) only at ⊢
  have he122 := gExt_trans he121 h22.1
  have e20_22 := gExt_trans h21.1 h22.1
  have h23 := cMinW_spec hx h22.2.1 (wordIn_ext e20_22 h20.2.2.2.1) h22.2.2.2.1
  generalize cMinW nin g22 ub2 ub3 = _r23 at h23 ⊢; rcases _r23 with ⟨g23, ub23⟩; dsimp only at h23; dsimp (config := { zeta := false }) only at ⊢
  have he123 := gExt_trans he122 h23.1
  have h24 := cMinW_spec hx h23.2.1 (wordIn_ext he123 hr1) h23.2.2.2.1
  generalize cMinW nin g23 r1 ub23 = _r24 at h24 ⊢; rcases _r24 with ⟨g24, rp_hi⟩; dsimp only at h24 ⊢
  have he124 := gExt_trans he123 h24.1
  have e18_24 := gExt_trans h19.1 (gExt_trans h20.1 (gExt_trans e20_22 (gExt_trans h23.1 h24.1)))
  have e17_24 := gExt_trans h18.1 e18_24
  have e12_24 := gExt_trans e12_18 e18_24
  have e4_24 := gExt_trans e4_18 e18_24
  refine ⟨he124, h24.2.1,
    by linarith only [hW4, h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1, h6.2.2.1,
      h7.2.2.1, h8.2.2.1, h9.2.2.1, h10.2.2.1, h11.2.2.1, h12.2.2.1, h13.2.2.1, h14.2.2.1,
      h15.2.2.1, h16.2.2.1, h17.2.2.1, h18.2.2.1, h19.2.2.1, h20.2.2.1, h21.2.2.1,
      h22.2.2.1, h23.2.2.1, h24.2.2.1],
    wire_ext e12_24 h12.2.2.2.1, wordIn_ext e4_24 h4.2.2.2.1,
    wordIn_ext e17_24 h17.2.2.2.1, h24.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · rw [valAt_ext hx.hlen e12_24 h12.2.2.2.1, h12.2.2.2.2, valAt_ext hx.hlen h11.1 h10.2.2.2.1,
      h10.2.2.2.2, valAt_ext hx.hlen e6_9 h6.2.2.2.1, hb1u_val, h11.2.2.2.2,
      wordVal_ext hx.hlen e4_10 h4.2.2.2.1, wordVal_ext hx.hlen h10.1 h9.2.2.2.1, hb0p_val, hb1p_val]
    rfl
  · rw [wordVal_ext hx.hlen e4_24 h4.2.2.2.1, hb0p_val]; rfl
  · rw [wordVal_ext hx.hlen e17_24 h17.2.2.2.1, h17.2.2.2.2, wordVal_ext hx.hlen he116 hr0,
      h16.2.2.2.2, wordVal_ext hx.hlen h15.1 h14.2.2.2.1, hlb2_val, hlb3_val, hb0p_val, hb1p_val]
    rfl
  · rw [h24.2.2.2.2, wordVal_ext hx.hlen he123 hr1, h23.2.2.2.2,
      wordVal_ext hx.hlen e20_22 h20.2.2.2.1, h20.2.2.2.2, wordVal_ext hx.hlen h19.1 h18.2.2.2.1,
      h18.2.2.2.2, h19.2.2.2.2, wordVal_ext hx.hlen he117 hs.2.2.1, wordVal_ext hx.hlen he117 hs.2.2.2.1,
      wordVal_ext hx.hlen he118 hs.2.2.2.2.2.1, wordVal_ext hx.hlen e4_18 h4.2.2.2.1,
      h22.2.2.2.2, h21.2.2.2.2, wordVal_ext hx.hlen e9_20 h9.2.2.2.1, wordVal_ext hx.hlen he120 hs.2.2.1,
      wordVal_ext hx.hlen he121 hs.2.2.2.2.2.2.2, hb0p_val, hb1p_val]
    rfl

private def cQueryParity2 (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (s : Sum8W W)
    (tBit ok_b : ℕ) (b0p rp_lo rp_hi : Word W) : List Gate × ℕ × Word W × Word W :=
  let (g1, eq_rl) := cEqBit nin g (rp_lo ⟨0, hW⟩) tBit
  let (g2, add_rl) := emitNot nin g1 eq_rl
  let (g3, rp_lo_t) := cAddW nin g2 rp_lo (cConstBit W add_rl)
  let (g4, rh_z) := cEqZeroW nin g3 rp_hi
  let (g5, rh_u) := emitAnd nin g4 rh_z tBit
  let (g6, eq_rh) := cEqBit nin g5 (rp_hi ⟨0, hW⟩) tBit
  let (g7, sub_rh) := emitNot nin g6 eq_rh
  let (g8, rp_hi_t) := cSubTruncW nin g7 rp_hi (cConstBit W sub_rh)
  let (g9, nrhu) := emitNot nin g8 rh_u
  let (g10, le_r) := cLeW nin g9 rp_lo_t rp_hi_t
  let (g11, ok1) := emitAnd nin g10 ok_b nrhu
  let (g12, ok) := emitAnd nin g11 ok1 le_r
  let (g13, bp2) := cSubTruncW nin g12 s.d00 rp_lo_t
  let (g14, d10rp) := cAddW nin g13 s.d10 rp_lo_t
  let (g15, bp3) := cSubTruncW nin g14 d10rp s.cr
  let (g16, bp23) := cMaxW nin g15 bp2 bp3
  let (g17, bp) := cMaxW nin g16 b0p bp23
  let (g18, outR) := cAddW nin g17 s.fr rp_lo_t
  let (g19, outB) := cAddW nin g18 s.fb bp
  (g19, ok, outR, outB)

private lemma cQueryParity2_spec {nin W : ℕ} (hW : 1 ≤ W) (hW4 : 4 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {s : Sum8W W} {tBit ok_b : ℕ} {b0p rp_lo rp_hi : Word W}
    (hs : s.In (nin + g.length)) (ht : tBit < nin + g.length) (hokb : ok_b < nin + g.length)
    (hb0p : WordIn (nin + g.length) b0p) (hrplo : WordIn (nin + g.length) rp_lo) (hrphi : WordIn (nin + g.length) rp_hi)
    (hB : (s.val g x).Bound (2 ^ (W - 3) - 1) ∧
      wordVal g x b0p ≤ 2 ^ (W - 3) ∧ wordVal g x rp_lo ≤ 2 * 2 ^ (W - 3)) :
    let res := cQueryParity2 nin hW g s tBit ok_b b0p rp_lo rp_hi
    let sv := s.val g x
    let t := valAt g x tBit
    let rp_lo_t := wordVal g x rp_lo + if decide (wordVal g x rp_lo % 2 = 1) == t then 0 else 1
    let rh_u := decide (wordVal g x rp_hi = 0) && t
    let rp_hi_t := wordVal g x rp_hi - if decide (wordVal g x rp_hi % 2 = 1) == t then 0 else 1
    let bp := max (wordVal g x b0p) (max (sv.d00 - rp_lo_t) (sv.d10 + rp_lo_t - sv.cr))
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 160 * W ∧
    res.2.1 < nin + res.1.length ∧ WordIn (nin + res.1.length) res.2.2.1 ∧
    WordIn (nin + res.1.length) res.2.2.2 ∧
    valAt res.1 x res.2.1 = (valAt g x ok_b && (!rh_u) && decide (rp_lo_t ≤ rp_hi_t)) ∧
    wordVal res.1 x res.2.2.1 = sv.fr + rp_lo_t ∧
    wordVal res.1 x res.2.2.2 = sv.fb + bp := by
  have hpow : 2 ^ W = 8 * 2 ^ (W - 3) := by
    calc 2 ^ W = 2 ^ ((W - 3) + 3) := by congr 1; omega
      _ = 8 * 2 ^ (W - 3) := by rw [pow_add]; ring
  have hpos : 2 ≤ 2 ^ (W - 3) := by
    have : 2 ^ 1 ≤ 2 ^ (W - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  rcases hB with ⟨⟨hfrB, hfbB, hcrB, hcbB, hd00B, hd11B, hd01B, hd10B⟩, hb0p_lt, hrplo_lt⟩
  simp only [Sum8W.val] at hfrB hfbB hcrB hcbB hd00B hd11B hd01B hd10B
  unfold cQueryParity2
  have h1 := cEqBit_spec (a := (rp_lo ⟨0, hW⟩)) (b := tBit) hx hv (hrplo ⟨0, hW⟩) ht
  generalize cEqBit nin g (rp_lo ⟨0, hW⟩) tBit = _r1 at h1 ⊢; rcases _r1 with ⟨g1, eq_rl⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have h2 := emitNot_spec hx h1.2.1 h1.2.2.2.1
  generalize emitNot nin g1 eq_rl = _r2 at h2 ⊢; rcases _r2 with ⟨g2, add_rl⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have he12 := gExt_trans h1.1 h2.1
  have hadd_rl_val : (valAt g2 x add_rl).toNat =
      if decide (wordVal g x rp_lo % 2 = 1) == valAt g x tBit then 0 else 1 := by
    rw [h2.2.2.2.2, h1.2.2.2.2]
    have hm := wordVal_mod_two hW g x rp_lo
    cases h0 : valAt g x (rp_lo ⟨0, hW⟩) <;> cases ht0 : valAt g x tBit <;>
      simp [h0, ht0] at hm ⊢ <;> simp [hm]
  have hcrl := cConstBit_spec hW (g := g2) hx h2.2.2.2.1
  have h3 := cAddW_spec hx h2.2.1 (wordIn_ext he12 hrplo) hcrl.1
    (by rw [wordVal_ext hx.hlen he12 hrplo, hcrl.2, hadd_rl_val]; exact arith_ite01_lt8_of_le2 hpow hpos hrplo_lt)
  generalize cAddW nin g2 rp_lo (cConstBit W add_rl) = _r3 at h3 ⊢; rcases _r3 with ⟨g3, rp_lo_t⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he13 := gExt_trans he12 h3.1
  have hrplot_val : wordVal g3 x rp_lo_t = wordVal g x rp_lo +
      if decide (wordVal g x rp_lo % 2 = 1) == valAt g x tBit then 0 else 1 := by
    rw [h3.2.2.2.2, wordVal_ext hx.hlen he12 hrplo, hcrl.2, hadd_rl_val]
  have hrplot_lt : wordVal g3 x rp_lo_t ≤ 2 * 2 ^ (W - 3) + 1 := by
    rw [hrplot_val]; exact arith_ite01_le_succ hrplo_lt
  have h4 := cEqZeroW_spec hx h3.2.1 (wordIn_ext he13 hrphi)
  generalize cEqZeroW nin g3 rp_hi = _r4 at h4 ⊢; rcases _r4 with ⟨g4, rh_z⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have he14 := gExt_trans he13 h4.1
  have h5 := emitAnd_spec (a := rh_z) (b := tBit) hx h4.2.1 h4.2.2.2.1 (wire_ext he14 ht)
  generalize emitAnd nin g4 rh_z tBit = _r5 at h5 ⊢; rcases _r5 with ⟨g5, rh_u⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have he15 := gExt_trans he14 h5.1
  have hrhu_val : valAt g5 x rh_u = (decide (wordVal g x rp_hi = 0) && valAt g x tBit) := by
    rw [h5.2.2.2.2, h4.2.2.2.2, wordVal_ext hx.hlen he13 hrphi, valAt_ext hx.hlen he14 ht]
  have h6 := cEqBit_spec (a := (rp_hi ⟨0, hW⟩)) (b := tBit) hx h5.2.1 (wire_ext he15 (hrphi ⟨0, hW⟩)) (wire_ext he15 ht)
  generalize cEqBit nin g5 (rp_hi ⟨0, hW⟩) tBit = _r6 at h6 ⊢; rcases _r6 with ⟨g6, eq_rh⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have he16 := gExt_trans he15 h6.1
  have h7 := emitNot_spec hx h6.2.1 h6.2.2.2.1
  generalize emitNot nin g6 eq_rh = _r7 at h7 ⊢; rcases _r7 with ⟨g7, sub_rh⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have he17 := gExt_trans he16 h7.1
  have hsub_rh_val : (valAt g7 x sub_rh).toNat =
      if decide (wordVal g x rp_hi % 2 = 1) == valAt g x tBit then 0 else 1 := by
    rw [h7.2.2.2.2, h6.2.2.2.2, valAt_ext hx.hlen he15 (hrphi ⟨0, hW⟩), valAt_ext hx.hlen he15 ht]
    have hm := wordVal_mod_two hW g x rp_hi
    cases h0 : valAt g x (rp_hi ⟨0, hW⟩) <;> cases ht0 : valAt g x tBit <;>
      simp [h0, ht0] at hm ⊢ <;> simp [hm]
  have hcrh := cConstBit_spec hW (g := g7) hx h7.2.2.2.1
  have h8 := cSubTruncW_spec hx h7.2.1 (wordIn_ext he17 hrphi) hcrh.1
  generalize cSubTruncW nin g7 rp_hi (cConstBit W sub_rh) = _r8 at h8 ⊢; rcases _r8 with ⟨g8, rp_hi_t⟩; dsimp only at h8; dsimp (config := { zeta := false }) only at ⊢
  have he18 := gExt_trans he17 h8.1
  have hrphit_val : wordVal g8 x rp_hi_t = wordVal g x rp_hi -
      if decide (wordVal g x rp_hi % 2 = 1) == valAt g x tBit then 0 else 1 := by
    rw [h8.2.2.2.2, wordVal_ext hx.hlen he17 hrphi, hcrh.2, hsub_rh_val]
  have e5_8 := gExt_trans h6.1 (gExt_trans h7.1 h8.1)
  have h9 := emitNot_spec (a := rh_u) hx h8.2.1 (wire_ext e5_8 h5.2.2.2.1)
  generalize emitNot nin g8 rh_u = _r9 at h9 ⊢; rcases _r9 with ⟨g9, nrhu⟩; dsimp only at h9; dsimp (config := { zeta := false }) only at ⊢
  have he19 := gExt_trans he18 h9.1
  have e3_9 := gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans e5_8 h9.1))
  have h10 := cLeW_spec hx h9.2.1 (wordIn_ext e3_9 h3.2.2.2.1) (wordIn_ext h9.1 h8.2.2.2.1)
  generalize cLeW nin g9 rp_lo_t rp_hi_t = _r10 at h10 ⊢; rcases _r10 with ⟨g10, le_r⟩; dsimp only at h10; dsimp (config := { zeta := false }) only at ⊢
  have he110 := gExt_trans he19 h10.1
  have h11 := emitAnd_spec (a := ok_b) (b := nrhu) hx h10.2.1 (wire_ext he110 hokb) (wire_ext h10.1 h9.2.2.2.1)
  generalize emitAnd nin g10 ok_b nrhu = _r11 at h11 ⊢; rcases _r11 with ⟨g11, ok1⟩; dsimp only at h11; dsimp (config := { zeta := false }) only at ⊢
  have he111 := gExt_trans he110 h11.1
  have h12 := emitAnd_spec (a := ok1) (b := le_r) hx h11.2.1 h11.2.2.2.1 (wire_ext h11.1 h10.2.2.2.1)
  generalize emitAnd nin g11 ok1 le_r = _r12 at h12 ⊢; rcases _r12 with ⟨g12, ok⟩; dsimp only at h12; dsimp (config := { zeta := false }) only at ⊢
  have he112 := gExt_trans he111 h12.1
  have e3_12 := gExt_trans e3_9 (gExt_trans h10.1 (gExt_trans h11.1 h12.1))
  have h13 := cSubTruncW_spec hx h12.2.1 (wordIn_ext he112 hs.2.2.2.2.1) (wordIn_ext e3_12 h3.2.2.2.1)
  generalize cSubTruncW nin g12 s.d00 rp_lo_t = _r13 at h13 ⊢; rcases _r13 with ⟨g13, bp2⟩; dsimp only at h13; dsimp (config := { zeta := false }) only at ⊢
  have he113 := gExt_trans he112 h13.1
  have hbp2_val : wordVal g13 x bp2 = wordVal g x s.d00 - wordVal g3 x rp_lo_t := by
    rw [h13.2.2.2.2, wordVal_ext hx.hlen he112 hs.2.2.2.2.1, wordVal_ext hx.hlen e3_12 h3.2.2.2.1]
  have e3_13 := gExt_trans e3_12 h13.1
  have h14 := cAddW_spec hx h13.2.1 (wordIn_ext he113 hs.2.2.2.2.2.2.2) (wordIn_ext e3_13 h3.2.2.2.1)
    (by rw [wordVal_ext hx.hlen he113 hs.2.2.2.2.2.2.2, wordVal_ext hx.hlen e3_13 h3.2.2.2.1]; exact arith_sub1_add_le2p1_lt8 hpow hpos hd10B hrplot_lt)
  generalize cAddW nin g13 s.d10 rp_lo_t = _r14 at h14 ⊢; rcases _r14 with ⟨g14, d10rp⟩; dsimp only at h14; dsimp (config := { zeta := false }) only at ⊢
  have he114 := gExt_trans he113 h14.1
  have h15 := cSubTruncW_spec hx h14.2.1 h14.2.2.2.1 (wordIn_ext he114 hs.2.2.1)
  generalize cSubTruncW nin g14 d10rp s.cr = _r15 at h15 ⊢; rcases _r15 with ⟨g15, bp3⟩; dsimp only at h15; dsimp (config := { zeta := false }) only at ⊢
  have he115 := gExt_trans he114 h15.1
  have hbp3_val : wordVal g15 x bp3 = wordVal g x s.d10 + wordVal g3 x rp_lo_t - wordVal g x s.cr := by
    rw [h15.2.2.2.2, h14.2.2.2.2, wordVal_ext hx.hlen he113 hs.2.2.2.2.2.2.2,
      wordVal_ext hx.hlen e3_13 h3.2.2.2.1, wordVal_ext hx.hlen he114 hs.2.2.1]
  have e13_15 := gExt_trans h14.1 h15.1
  have h16 := cMaxW_spec hx h15.2.1 (wordIn_ext e13_15 h13.2.2.2.1) h15.2.2.2.1
  generalize cMaxW nin g15 bp2 bp3 = _r16 at h16 ⊢; rcases _r16 with ⟨g16, bp23⟩; dsimp only at h16; dsimp (config := { zeta := false }) only at ⊢
  have he116 := gExt_trans he115 h16.1
  have h17 := cMaxW_spec hx h16.2.1 (wordIn_ext he116 hb0p) h16.2.2.2.1
  generalize cMaxW nin g16 b0p bp23 = _r17 at h17 ⊢; rcases _r17 with ⟨g17, bp⟩; dsimp only at h17; dsimp (config := { zeta := false }) only at ⊢
  have he117 := gExt_trans he116 h17.1
  have hbp_val : wordVal g17 x bp =
      max (wordVal g x b0p) (max (wordVal g x s.d00 - wordVal g3 x rp_lo_t)
        (wordVal g x s.d10 + wordVal g3 x rp_lo_t - wordVal g x s.cr)) := by
    rw [h17.2.2.2.2, wordVal_ext hx.hlen he116 hb0p, h16.2.2.2.2,
      wordVal_ext hx.hlen e13_15 h13.2.2.2.1, hbp2_val, hbp3_val]
  have hbp_lt : wordVal g17 x bp ≤ 3 * 2 ^ (W - 3) + 1 := by
    rw [hbp_val]; exact arith_bp_le3p1 hb0p_lt hd00B hd10B hrplot_lt
  have e3_17 := gExt_trans e3_13 (gExt_trans e13_15 (gExt_trans h16.1 h17.1))
  have h18 := cAddW_spec hx h17.2.1 (wordIn_ext he117 hs.1) (wordIn_ext e3_17 h3.2.2.2.1)
    (by rw [wordVal_ext hx.hlen he117 hs.1, wordVal_ext hx.hlen e3_17 h3.2.2.2.1]; exact arith_sub1_add_le2p1_lt8 hpow hpos hfrB hrplot_lt)
  generalize cAddW nin g17 s.fr rp_lo_t = _r18 at h18 ⊢; rcases _r18 with ⟨g18, outR⟩; dsimp only at h18; dsimp (config := { zeta := false }) only at ⊢
  have he118 := gExt_trans he117 h18.1
  have h19 := cAddW_spec hx h18.2.1 (wordIn_ext he118 hs.2.1) (wordIn_ext h18.1 h17.2.2.2.1)
    (by rw [wordVal_ext hx.hlen he118 hs.2.1, wordVal_ext hx.hlen h18.1 h17.2.2.2.1]; exact arith_sub1_add_le3p1_lt8 hpow hpos hfbB hbp_lt)
  generalize cAddW nin g18 s.fb bp = _r19 at h19 ⊢; rcases _r19 with ⟨g19, outB⟩; dsimp only at h19 ⊢
  have he119 := gExt_trans he118 h19.1
  have e12_19 := gExt_trans h13.1 (gExt_trans e13_15 (gExt_trans h16.1 (gExt_trans h17.1 (gExt_trans h18.1 h19.1))))
  refine ⟨he119, h19.2.1,
    by linarith only [hW4, h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1, h6.2.2.1,
      h7.2.2.1, h8.2.2.1, h9.2.2.1, h10.2.2.1, h11.2.2.1, h12.2.2.1, h13.2.2.1, h14.2.2.1,
      h15.2.2.1, h16.2.2.1, h17.2.2.1, h18.2.2.1, h19.2.2.1],
    wire_ext e12_19 h12.2.2.2.1, wordIn_ext h19.1 h18.2.2.2.1, h19.2.2.2.1, ?_, ?_, ?_⟩
  · rw [valAt_ext hx.hlen e12_19 h12.2.2.2.1, h12.2.2.2.2, h11.2.2.2.2,
      valAt_ext hx.hlen he110 hokb, valAt_ext hx.hlen h10.1 h9.2.2.2.1, h9.2.2.2.2,
      valAt_ext hx.hlen e5_8 h5.2.2.2.1, hrhu_val,
      valAt_ext hx.hlen h11.1 h10.2.2.2.1, h10.2.2.2.2,
      wordVal_ext hx.hlen e3_9 h3.2.2.2.1, wordVal_ext hx.hlen h9.1 h8.2.2.2.1,
      hrplot_val, hrphit_val]
  · rw [wordVal_ext hx.hlen h19.1 h18.2.2.2.1, h18.2.2.2.2,
      wordVal_ext hx.hlen he117 hs.1, wordVal_ext hx.hlen e3_17 h3.2.2.2.1, hrplot_val]
    rfl
  · rw [h19.2.2.2.2, wordVal_ext hx.hlen he118 hs.2.1, wordVal_ext hx.hlen h18.1 h17.2.2.2.1,
      hbp_val, hrplot_val]
    rfl

private def cQueryParity (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (s : Sum8W W)
    (r0 r1 b0 b1 : Word W) (tBit : ℕ) : List Gate × ℕ × Word W × Word W :=
  let (g1, ok_b, b0p, rp_lo, rp_hi) := cQueryParity1 nin hW g s r0 r1 b0 b1 tBit
  cQueryParity2 nin hW g1 s tBit ok_b b0p rp_lo rp_hi

private lemma cQueryParity_spec {nin W : ℕ} (hW : 1 ≤ W) (hW4 : 4 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {s : Sum8W W} {r0 r1 b0 b1 : Word W} {tBit : ℕ}
    (hs : s.In (nin + g.length))
    (hr0 : WordIn (nin + g.length) r0) (hr1 : WordIn (nin + g.length) r1)
    (hb0 : WordIn (nin + g.length) b0) (hb1 : WordIn (nin + g.length) b1)
    (ht : tBit < nin + g.length)
    (hB : (s.val g x).Bound (2 ^ (W - 3) - 1) ∧
      wordVal g x r0 < 2 ^ (W - 3) ∧ wordVal g x r1 < 2 ^ (W - 3) ∧
      wordVal g x b0 < 2 ^ (W - 3) ∧ wordVal g x b1 < 2 ^ (W - 3)) :
    let res := cQueryParity nin hW g s r0 r1 b0 b1 tBit
    let q := (s.val g x).queryParity (wordVal g x r0) (wordVal g x r1)
      (wordVal g x b0) (wordVal g x b1) (valAt g x tBit)
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 400 * W ∧
    res.2.1 < nin + res.1.length ∧ WordIn (nin + res.1.length) res.2.2.1 ∧
    WordIn (nin + res.1.length) res.2.2.2 ∧
    valAt res.1 x res.2.1 = q.1 ∧
    wordVal res.1 x res.2.2.1 = q.2.1 ∧
    wordVal res.1 x res.2.2.2 = q.2.2 := by
  unfold cQueryParity
  have h1 := cQueryParity1_spec hW hW4 hx hv hs hr0 hr1 hb0 hb1 ht hB
  generalize cQueryParity1 nin hW g s r0 r1 b0 b1 tBit = _r1 at h1 ⊢
  rcases _r1 with ⟨g1, ok_b, b0p, rp_lo, rp_hi⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  rcases h1 with ⟨he1, hv1, hlen1, hokb_in, hb0p_in, hrplo_in, hrphi_in, hokb_v, hb0p_v, hrplo_v, hrphi_v⟩
  have hs1 : s.val g1 x = s.val g x := Sum8W.val_ext hx.hlen he1 hs
  have hb0p_lt : wordVal g1 x b0p ≤ 2 ^ (W - 3) := by rw [hb0p_v]; exact arith_ite01_le_of_lt hB.2.2.2.1
  have hrplo_lt : wordVal g1 x rp_lo ≤ 2 * 2 ^ (W - 3) := by
    rw [hrplo_v]
    exact arith_rplo_le2 hB.2.1 (arith_ite01_le_of_lt hB.2.2.2.1) hB.1.2.2.2.2.2.2.1 hB.1.2.2.2.2.1
  have h2 := cQueryParity2_spec hW hW4 hx hv1 (sum8_in_ext he1 hs) (wire_ext he1 ht)
    hokb_in hb0p_in hrplo_in hrphi_in ⟨by rw [hs1]; exact hB.1, hb0p_lt, hrplo_lt⟩
  generalize cQueryParity2 nin hW g1 s tBit ok_b b0p rp_lo rp_hi = _r2 at h2 ⊢
  rcases _r2 with ⟨g2, ok, outR, outB⟩; dsimp only at h2 ⊢
  rcases h2 with ⟨he2, hv2, hlen2, hok_in, houtR_in, houtB_in, hok_v, houtR_v, houtB_v⟩
  have ht1 : valAt g1 x tBit = valAt g x tBit := valAt_ext hx.hlen he1 ht
  refine ⟨gExt_trans he1 he2, hv2, by linarith only [hlen1, hlen2], hok_in, houtR_in, houtB_in, ?_, ?_, ?_⟩
  · rw [hok_v, hokb_v, hrplo_v, hrphi_v, ht1]; rfl
  · rw [houtR_v, hs1, hrplo_v, ht1]; rfl
  · rw [houtB_v, hs1, hb0p_v, hrplo_v, ht1]; rfl

private def cQueryBox (nin : ℕ) {W : ℕ} (g : List Gate) (s : Sum8W W)
    (loR hiR loB hiB : Word W) : List Gate × ℕ × Word W × Word W × Word W × Word W :=
  let (g1, R0) := cMaxW nin g s.fr loR
  let (g2, frcr) := cAddW nin g1 s.fr s.cr
  let (g3, R1) := cMinW nin g2 frcr hiR
  let (g4, B0) := cMaxW nin g3 s.fb loB
  let (g5, fbcb) := cAddW nin g4 s.fb s.cb
  let (g6, B1) := cMinW nin g5 fbcb hiB
  let (g7, ok1) := cLeW nin g6 loR hiR
  let (g8, ok2) := cLeW nin g7 loB hiB
  let (g9, ok3) := cLeW nin g8 R0 R1
  let (g10, ok4) := cLeW nin g9 B0 B1
  let (g11, b12) := emitAnd nin g10 ok1 ok2
  let (g12, b123) := emitAnd nin g11 b12 ok3
  let (g13, box_ok) := emitAnd nin g12 b123 ok4
  let (g14, r0) := cSubTruncW nin g13 R0 s.fr
  let (g15, r1) := cSubTruncW nin g14 R1 s.fr
  let (g16, b0) := cSubTruncW nin g15 B0 s.fb
  let (g17, b1) := cSubTruncW nin g16 B1 s.fb
  (g17, box_ok, r0, r1, b0, b1)

private lemma cQueryBox_spec {nin W : ℕ} (hW : 1 ≤ W) (hW4 : 4 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {s : Sum8W W} {loR hiR loB hiB : Word W}
    (hs : s.In (nin + g.length))
    (hloR : WordIn (nin + g.length) loR) (hhiR : WordIn (nin + g.length) hiR)
    (hloB : WordIn (nin + g.length) loB) (hhiB : WordIn (nin + g.length) hiB)
    (hB : (s.val g x).Bound (2 ^ (W - 3) - 1) ∧
      wordVal g x loR < 2 ^ (W - 3) ∧ wordVal g x hiR < 2 ^ (W - 3) ∧
      wordVal g x loB < 2 ^ (W - 3) ∧ wordVal g x hiB < 2 ^ (W - 3)) :
    let res := cQueryBox nin g s loR hiR loB hiB
    let sv := s.val g x
    let R0 := max sv.fr (wordVal g x loR)
    let R1 := min (sv.fr + sv.cr) (wordVal g x hiR)
    let B0 := max sv.fb (wordVal g x loB)
    let B1 := min (sv.fb + sv.cb) (wordVal g x hiB)
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 210 * W ∧
    res.2.1 < nin + res.1.length ∧
    WordIn (nin + res.1.length) res.2.2.1 ∧
    WordIn (nin + res.1.length) res.2.2.2.1 ∧
    WordIn (nin + res.1.length) res.2.2.2.2.1 ∧
    WordIn (nin + res.1.length) res.2.2.2.2.2 ∧
    valAt res.1 x res.2.1 =
      (decide (wordVal g x loR ≤ wordVal g x hiR) && decide (wordVal g x loB ≤ wordVal g x hiB) &&
       decide (R0 ≤ R1) && decide (B0 ≤ B1)) ∧
    wordVal res.1 x res.2.2.1 = R0 - sv.fr ∧
    wordVal res.1 x res.2.2.2.1 = R1 - sv.fr ∧
    wordVal res.1 x res.2.2.2.2.1 = B0 - sv.fb ∧
    wordVal res.1 x res.2.2.2.2.2 = B1 - sv.fb := by
  have hpow : 2 ^ W = 8 * 2 ^ (W - 3) := by
    calc 2 ^ W = 2 ^ ((W - 3) + 3) := by congr 1; omega
      _ = 8 * 2 ^ (W - 3) := by rw [pow_add]; ring
  have hpos : 2 ≤ 2 ^ (W - 3) := by
    have : 2 ^ 1 ≤ 2 ^ (W - 3) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  rcases hB with ⟨hSB, hloRB, hhiRB, hloBB, hhiBB⟩
  have hfrB := hSB.1; have hfbB := hSB.2.1; have hcrB := hSB.2.2.1; have hcbB := hSB.2.2.2.1
  simp only [Sum8W.val] at hfrB hfbB hcrB hcbB
  unfold cQueryBox
  have h1 := cMaxW_spec hx hv hs.1 hloR
  generalize cMaxW nin g s.fr loR = _r1 at h1 ⊢; rcases _r1 with ⟨g1, R0⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have h2 := cAddW_spec hx h1.2.1 (wordIn_ext h1.1 hs.1) (wordIn_ext h1.1 hs.2.2.1)
    (by rw [wordVal_ext hx.hlen h1.1 hs.1, wordVal_ext hx.hlen h1.1 hs.2.2.1]; exact arith_sub1_add_sub1_lt8 hpow hpos hfrB hcrB)
  generalize cAddW nin g1 s.fr s.cr = _r2 at h2 ⊢; rcases _r2 with ⟨g2, frcr⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have he12 := gExt_trans h1.1 h2.1
  have h3 := cMinW_spec hx h2.2.1 h2.2.2.2.1 (wordIn_ext he12 hhiR)
  generalize cMinW nin g2 frcr hiR = _r3 at h3 ⊢; rcases _r3 with ⟨g3, R1⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he13 := gExt_trans he12 h3.1
  have h4 := cMaxW_spec hx h3.2.1 (wordIn_ext he13 hs.2.1) (wordIn_ext he13 hloB)
  generalize cMaxW nin g3 s.fb loB = _r4 at h4 ⊢; rcases _r4 with ⟨g4, B0⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have he14 := gExt_trans he13 h4.1
  have h5 := cAddW_spec hx h4.2.1 (wordIn_ext he14 hs.2.1) (wordIn_ext he14 hs.2.2.2.1)
    (by rw [wordVal_ext hx.hlen he14 hs.2.1, wordVal_ext hx.hlen he14 hs.2.2.2.1]; exact arith_sub1_add_sub1_lt8 hpow hpos hfbB hcbB)
  generalize cAddW nin g4 s.fb s.cb = _r5 at h5 ⊢; rcases _r5 with ⟨g5, fbcb⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have he15 := gExt_trans he14 h5.1
  have h6 := cMinW_spec hx h5.2.1 h5.2.2.2.1 (wordIn_ext he15 hhiB)
  generalize cMinW nin g5 fbcb hiB = _r6 at h6 ⊢; rcases _r6 with ⟨g6, B1⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have he16 := gExt_trans he15 h6.1
  have hR0_v : wordVal g1 x R0 = max (wordVal g x s.fr) (wordVal g x loR) := h1.2.2.2.2
  have hR1_v : wordVal g3 x R1 = min (wordVal g x s.fr + wordVal g x s.cr) (wordVal g x hiR) := by
    rw [h3.2.2.2.2, h2.2.2.2.2, wordVal_ext hx.hlen h1.1 hs.1, wordVal_ext hx.hlen h1.1 hs.2.2.1, wordVal_ext hx.hlen he12 hhiR]
  have hB0_v : wordVal g4 x B0 = max (wordVal g x s.fb) (wordVal g x loB) := by
    rw [h4.2.2.2.2, wordVal_ext hx.hlen he13 hs.2.1, wordVal_ext hx.hlen he13 hloB]
  have hB1_v : wordVal g6 x B1 = min (wordVal g x s.fb + wordVal g x s.cb) (wordVal g x hiB) := by
    rw [h6.2.2.2.2, h5.2.2.2.2, wordVal_ext hx.hlen he14 hs.2.1, wordVal_ext hx.hlen he14 hs.2.2.2.1, wordVal_ext hx.hlen he15 hhiB]
  have h7 := cLeW_spec hx h6.2.1 (wordIn_ext he16 hloR) (wordIn_ext he16 hhiR)
  generalize cLeW nin g6 loR hiR = _r7 at h7 ⊢; rcases _r7 with ⟨g7, ok1⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have he17 := gExt_trans he16 h7.1
  have h8 := cLeW_spec hx h7.2.1 (wordIn_ext he17 hloB) (wordIn_ext he17 hhiB)
  generalize cLeW nin g7 loB hiB = _r8 at h8 ⊢; rcases _r8 with ⟨g8, ok2⟩; dsimp only at h8; dsimp (config := { zeta := false }) only at ⊢
  have he18 := gExt_trans he17 h8.1
  have e6_8 := gExt_trans h7.1 h8.1
  have e4_8 := gExt_trans h5.1 (gExt_trans h6.1 e6_8)
  have e3_8 := gExt_trans h4.1 e4_8
  have e1_8 := gExt_trans h2.1 (gExt_trans h3.1 e3_8)
  have h9 := cLeW_spec hx h8.2.1 (wordIn_ext e1_8 h1.2.2.2.1) (wordIn_ext e3_8 h3.2.2.2.1)
  generalize cLeW nin g8 R0 R1 = _r9 at h9 ⊢; rcases _r9 with ⟨g9, ok3⟩; dsimp only at h9; dsimp (config := { zeta := false }) only at ⊢
  have he19 := gExt_trans he18 h9.1
  have e6_9 := gExt_trans e6_8 h9.1
  have e4_9 := gExt_trans e4_8 h9.1
  have h10 := cLeW_spec hx h9.2.1 (wordIn_ext e4_9 h4.2.2.2.1) (wordIn_ext e6_9 h6.2.2.2.1)
  generalize cLeW nin g9 B0 B1 = _r10 at h10 ⊢; rcases _r10 with ⟨g10, ok4⟩; dsimp only at h10; dsimp (config := { zeta := false }) only at ⊢
  have he110 := gExt_trans he19 h10.1
  have e8_10 := gExt_trans h9.1 h10.1
  have e7_10 := gExt_trans h8.1 e8_10
  have h11 := emitAnd_spec (a := ok1) (b := ok2) hx h10.2.1 (wire_ext e7_10 h7.2.2.2.1) (wire_ext e8_10 h8.2.2.2.1)
  generalize emitAnd nin g10 ok1 ok2 = _r11 at h11 ⊢; rcases _r11 with ⟨g11, b12⟩; dsimp only at h11; dsimp (config := { zeta := false }) only at ⊢
  have he111 := gExt_trans he110 h11.1
  have e9_11 := gExt_trans h10.1 h11.1
  have h12 := emitAnd_spec (a := b12) (b := ok3) hx h11.2.1 h11.2.2.2.1 (wire_ext e9_11 h9.2.2.2.1)
  generalize emitAnd nin g11 b12 ok3 = _r12 at h12 ⊢; rcases _r12 with ⟨g12, b123⟩; dsimp only at h12; dsimp (config := { zeta := false }) only at ⊢
  have he112 := gExt_trans he111 h12.1
  have e10_12 := gExt_trans h11.1 h12.1
  have h13 := emitAnd_spec (a := b123) (b := ok4) hx h12.2.1 h12.2.2.2.1 (wire_ext e10_12 h10.2.2.2.1)
  generalize emitAnd nin g12 b123 ok4 = _r13 at h13 ⊢; rcases _r13 with ⟨g13, box_ok⟩; dsimp only at h13; dsimp (config := { zeta := false }) only at ⊢
  have he113 := gExt_trans he112 h13.1
  have e9_13 := gExt_trans e9_11 (gExt_trans h12.1 h13.1)
  have e8_13 := gExt_trans h9.1 e9_13
  have e1_13 := gExt_trans e1_8 e8_13
  have h14 := cSubTruncW_spec hx h13.2.1 (wordIn_ext e1_13 h1.2.2.2.1) (wordIn_ext he113 hs.1)
  generalize cSubTruncW nin g13 R0 s.fr = _r14 at h14 ⊢; rcases _r14 with ⟨g14, r0⟩; dsimp only at h14; dsimp (config := { zeta := false }) only at ⊢
  have he114 := gExt_trans he113 h14.1
  have e3_14 := gExt_trans e3_8 (gExt_trans e8_13 h14.1)
  have h15 := cSubTruncW_spec hx h14.2.1 (wordIn_ext e3_14 h3.2.2.2.1) (wordIn_ext he114 hs.1)
  generalize cSubTruncW nin g14 R1 s.fr = _r15 at h15 ⊢; rcases _r15 with ⟨g15, r1⟩; dsimp only at h15; dsimp (config := { zeta := false }) only at ⊢
  have he115 := gExt_trans he114 h15.1
  have e4_15 := gExt_trans e4_9 (gExt_trans e9_13 (gExt_trans h14.1 h15.1))
  have h16 := cSubTruncW_spec hx h15.2.1 (wordIn_ext e4_15 h4.2.2.2.1) (wordIn_ext he115 hs.2.1)
  generalize cSubTruncW nin g15 B0 s.fb = _r16 at h16 ⊢; rcases _r16 with ⟨g16, b0⟩; dsimp only at h16; dsimp (config := { zeta := false }) only at ⊢
  have he116 := gExt_trans he115 h16.1
  have e6_16 := gExt_trans e6_9 (gExt_trans e9_13 (gExt_trans h14.1 (gExt_trans h15.1 h16.1)))
  have h17 := cSubTruncW_spec hx h16.2.1 (wordIn_ext e6_16 h6.2.2.2.1) (wordIn_ext he116 hs.2.1)
  generalize cSubTruncW nin g16 B1 s.fb = _r17 at h17 ⊢; rcases _r17 with ⟨g17, b1⟩; dsimp only at h17 ⊢
  have he117 := gExt_trans he116 h17.1
  have e15_17 := gExt_trans h16.1 h17.1
  have e14_17 := gExt_trans h15.1 e15_17
  have e13_17 := gExt_trans h14.1 e14_17
  refine ⟨he117, h17.2.1,
    by linarith only [hW, h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1, h6.2.2.1,
      h7.2.2.1, h8.2.2.1, h9.2.2.1, h10.2.2.1, h11.2.2.1, h12.2.2.1, h13.2.2.1, h14.2.2.1,
      h15.2.2.1, h16.2.2.1, h17.2.2.1],
    wire_ext e13_17 h13.2.2.2.1,
    wordIn_ext e14_17 h14.2.2.2.1, wordIn_ext e15_17 h15.2.2.2.1,
    wordIn_ext h17.1 h16.2.2.2.1, h17.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [valAt_ext hx.hlen e13_17 h13.2.2.2.1, h13.2.2.2.2, h12.2.2.2.2, h11.2.2.2.2,
      valAt_ext hx.hlen e7_10 h7.2.2.2.1, h7.2.2.2.2,
      wordVal_ext hx.hlen he16 hloR, wordVal_ext hx.hlen he16 hhiR,
      valAt_ext hx.hlen e8_10 h8.2.2.2.1, h8.2.2.2.2,
      wordVal_ext hx.hlen he17 hloB, wordVal_ext hx.hlen he17 hhiB,
      valAt_ext hx.hlen e9_11 h9.2.2.2.1, h9.2.2.2.2,
      wordVal_ext hx.hlen e1_8 h1.2.2.2.1, hR0_v, wordVal_ext hx.hlen e3_8 h3.2.2.2.1, hR1_v,
      valAt_ext hx.hlen e10_12 h10.2.2.2.1, h10.2.2.2.2,
      wordVal_ext hx.hlen e4_9 h4.2.2.2.1, hB0_v, wordVal_ext hx.hlen e6_9 h6.2.2.2.1, hB1_v]
    rfl
  · rw [wordVal_ext hx.hlen e14_17 h14.2.2.2.1, h14.2.2.2.2, wordVal_ext hx.hlen e1_13 h1.2.2.2.1,
      hR0_v, wordVal_ext hx.hlen he113 hs.1]; rfl
  · rw [wordVal_ext hx.hlen e15_17 h15.2.2.2.1, h15.2.2.2.2, wordVal_ext hx.hlen e3_14 h3.2.2.2.1,
      hR1_v, wordVal_ext hx.hlen he114 hs.1]; rfl
  · rw [wordVal_ext hx.hlen h17.1 h16.2.2.2.1, h16.2.2.2.2, wordVal_ext hx.hlen e4_15 h4.2.2.2.1,
      hB0_v, wordVal_ext hx.hlen he115 hs.2.1]; rfl
  · rw [h17.2.2.2.2, wordVal_ext hx.hlen e6_16 h6.2.2.2.1, hB1_v, wordVal_ext hx.hlen he116 hs.2.1]; rfl

private def cQueryPick (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (s : Sum8W W)
    (box_ok : ℕ) (r0 r1 b0 b1 : Word W) : List Gate × ℕ × Word W × Word W :=
  let (g1, q0_ok, q0_r, q0_b) := cQueryParity nin hW g s r0 r1 b0 b1 0
  let (g2, q1_ok, q1_r, q1_b) := cQueryParity nin hW g1 s r0 r1 b0 b1 1
  let (g3, f0) := emitAnd nin g2 box_ok q0_ok
  let (g4, f1) := emitAnd nin g3 box_ok q1_ok
  let (g5, flag) := emitOr nin g4 f0 f1
  let (g6, nf1) := emitNot nin g5 f1
  let (g7, rlt) := cLtW nin g6 q0_r q1_r
  let (g8, req) := cEqW nin g7 q0_r q1_r
  let (g9, ble) := cLeW nin g8 q0_b q1_b
  let (g10, eqble) := emitAnd nin g9 req ble
  let (g11, o1) := emitOr nin g10 nf1 rlt
  let (g12, o2) := emitOr nin g11 o1 eqble
  let (g13, pick0) := emitAnd nin g12 f0 o2
  let (g14, outR) := cMuxW nin g13 pick0 q0_r q1_r
  let (g15, outB) := cMuxW nin g14 pick0 q0_b q1_b
  (g15, flag, outR, outB)

private lemma cQueryPick_spec {nin W : ℕ} (hW : 1 ≤ W) (hW4 : 4 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {s : Sum8W W} {box_ok : ℕ} {r0 r1 b0 b1 : Word W}
    (hs : s.In (nin + g.length)) (hbox : box_ok < nin + g.length)
    (hr0 : WordIn (nin + g.length) r0) (hr1 : WordIn (nin + g.length) r1)
    (hb0 : WordIn (nin + g.length) b0) (hb1 : WordIn (nin + g.length) b1)
    (hB : (s.val g x).Bound (2 ^ (W - 3) - 1) ∧
      wordVal g x r0 < 2 ^ (W - 3) ∧ wordVal g x r1 < 2 ^ (W - 3) ∧
      wordVal g x b0 < 2 ^ (W - 3) ∧ wordVal g x b1 < 2 ^ (W - 3)) :
    let res := cQueryPick nin hW g s box_ok r0 r1 b0 b1
    let q0 := (s.val g x).queryParity (wordVal g x r0) (wordVal g x r1) (wordVal g x b0) (wordVal g x b1) false
    let q1 := (s.val g x).queryParity (wordVal g x r0) (wordVal g x r1) (wordVal g x b0) (wordVal g x b1) true
    let f0 := valAt g x box_ok && q0.1
    let f1 := valAt g x box_ok && q1.1
    let pick0 := f0 && ((!f1) || decide (q0.2.1 < q1.2.1) || (decide (q0.2.1 = q1.2.1) && decide (q0.2.2 ≤ q1.2.2)))
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 890 * W ∧
    res.2.1 < nin + res.1.length ∧ WordIn (nin + res.1.length) res.2.2.1 ∧
    WordIn (nin + res.1.length) res.2.2.2 ∧
    valAt res.1 x res.2.1 = (f0 || f1) ∧
    wordVal res.1 x res.2.2.1 = (if pick0 then q0.2.1 else q1.2.1) ∧
    wordVal res.1 x res.2.2.2 = (if pick0 then q0.2.2 else q1.2.2) := by
  have hnin := hx.hnin
  unfold cQueryPick
  have h1 := cQueryParity_spec (tBit := 0) hW hW4 hx hv hs hr0 hr1 hb0 hb1
    (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide : 0 < 2) hnin) (Nat.le_add_right _ _)) hB
  generalize cQueryParity nin hW g s r0 r1 b0 b1 0 = _r1 at h1 ⊢
  rcases _r1 with ⟨g1, q0_ok, q0_r, q0_b⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have hs1 : s.val g1 x = s.val g x := Sum8W.val_ext hx.hlen h1.1 hs
  have hr0_1 : wordVal g1 x r0 = wordVal g x r0 := wordVal_ext hx.hlen h1.1 hr0
  have hr1_1 : wordVal g1 x r1 = wordVal g x r1 := wordVal_ext hx.hlen h1.1 hr1
  have hb0_1 : wordVal g1 x b0 = wordVal g x b0 := wordVal_ext hx.hlen h1.1 hb0
  have hb1_1 : wordVal g1 x b1 = wordVal g x b1 := wordVal_ext hx.hlen h1.1 hb1
  have h2 := cQueryParity_spec (tBit := 1) hW hW4 hx h1.2.1 (sum8_in_ext h1.1 hs)
    (wordIn_ext h1.1 hr0) (wordIn_ext h1.1 hr1) (wordIn_ext h1.1 hb0) (wordIn_ext h1.1 hb1)
    (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (by decide : 1 < 2) hnin) (Nat.le_add_right _ _))
    ⟨by rw [hs1]; exact hB.1, by rw [hr0_1]; exact hB.2.1, by rw [hr1_1]; exact hB.2.2.1,
     by rw [hb0_1]; exact hB.2.2.2.1, by rw [hb1_1]; exact hB.2.2.2.2⟩
  generalize cQueryParity nin hW g1 s r0 r1 b0 b1 1 = _r2 at h2 ⊢
  rcases _r2 with ⟨g2, q1_ok, q1_r, q1_b⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have he12 := gExt_trans h1.1 h2.1
  have h3 := emitAnd_spec (a := box_ok) (b := q0_ok) hx h2.2.1 (wire_ext he12 hbox) (wire_ext h2.1 h1.2.2.2.1)
  generalize emitAnd nin g2 box_ok q0_ok = _r3 at h3 ⊢; rcases _r3 with ⟨g3, f0⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he13 := gExt_trans he12 h3.1
  have h4 := emitAnd_spec (a := box_ok) (b := q1_ok) hx h3.2.1 (wire_ext he13 hbox) (wire_ext h3.1 h2.2.2.2.1)
  generalize emitAnd nin g3 box_ok q1_ok = _r4 at h4 ⊢; rcases _r4 with ⟨g4, f1⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have h5 := emitOr_spec (a := f0) (b := f1) hx h4.2.1 (wire_ext h4.1 h3.2.2.2.1) h4.2.2.2.1
  generalize emitOr nin g4 f0 f1 = _r5 at h5 ⊢; rcases _r5 with ⟨g5, flag⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have h6 := emitNot_spec (a := f1) hx h5.2.1 (wire_ext h5.1 h4.2.2.2.1)
  generalize emitNot nin g5 f1 = _r6 at h6 ⊢; rcases _r6 with ⟨g6, nf1⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have e2_6 := gExt_trans h3.1 (gExt_trans h4.1 (gExt_trans h5.1 h6.1))
  have e1_6 := gExt_trans h2.1 e2_6
  have h7 := cLtW_spec hx h6.2.1 (wordIn_ext e1_6 h1.2.2.2.2.1) (wordIn_ext e2_6 h2.2.2.2.2.1)
  generalize cLtW nin g6 q0_r q1_r = _r7 at h7 ⊢; rcases _r7 with ⟨g7, rlt⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have e2_7 := gExt_trans e2_6 h7.1
  have e1_7 := gExt_trans e1_6 h7.1
  have h8 := cEqW_spec hx h7.2.1 (wordIn_ext e1_7 h1.2.2.2.2.1) (wordIn_ext e2_7 h2.2.2.2.2.1)
  generalize cEqW nin g7 q0_r q1_r = _r8 at h8 ⊢; rcases _r8 with ⟨g8, req⟩; dsimp only at h8; dsimp (config := { zeta := false }) only at ⊢
  have e2_8 := gExt_trans e2_7 h8.1
  have e1_8 := gExt_trans e1_7 h8.1
  have h9 := cLeW_spec hx h8.2.1 (wordIn_ext e1_8 h1.2.2.2.2.2.1) (wordIn_ext e2_8 h2.2.2.2.2.2.1)
  generalize cLeW nin g8 q0_b q1_b = _r9 at h9 ⊢; rcases _r9 with ⟨g9, ble⟩; dsimp only at h9; dsimp (config := { zeta := false }) only at ⊢
  have h10 := emitAnd_spec (a := req) (b := ble) hx h9.2.1 (wire_ext h9.1 h8.2.2.2.1) h9.2.2.2.1
  generalize emitAnd nin g9 req ble = _r10 at h10 ⊢; rcases _r10 with ⟨g10, eqble⟩; dsimp only at h10; dsimp (config := { zeta := false }) only at ⊢
  have e7_10 := gExt_trans h8.1 (gExt_trans h9.1 h10.1)
  have e6_10 := gExt_trans h7.1 e7_10
  have h11 := emitOr_spec (a := nf1) (b := rlt) hx h10.2.1 (wire_ext e6_10 h6.2.2.2.1) (wire_ext e7_10 h7.2.2.2.1)
  generalize emitOr nin g10 nf1 rlt = _r11 at h11 ⊢; rcases _r11 with ⟨g11, o1⟩; dsimp only at h11; dsimp (config := { zeta := false }) only at ⊢
  have h12 := emitOr_spec (a := o1) (b := eqble) hx h11.2.1 h11.2.2.2.1 (wire_ext h11.1 h10.2.2.2.1)
  generalize emitOr nin g11 o1 eqble = _r12 at h12 ⊢; rcases _r12 with ⟨g12, o2⟩; dsimp only at h12; dsimp (config := { zeta := false }) only at ⊢
  have e6_12 := gExt_trans e6_10 (gExt_trans h11.1 h12.1)
  have e3_12 := gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 e6_12))
  have h13 := emitAnd_spec (a := f0) (b := o2) hx h12.2.1 (wire_ext e3_12 h3.2.2.2.1) h12.2.2.2.1
  generalize emitAnd nin g12 f0 o2 = _r13 at h13 ⊢; rcases _r13 with ⟨g13, pick0⟩; dsimp only at h13; dsimp (config := { zeta := false }) only at ⊢
  have e6_13 := gExt_trans e6_12 h13.1
  have e2_13 := gExt_trans e2_6 e6_13
  have e1_13 := gExt_trans h2.1 e2_13
  have h14 := cMuxW_spec (sel := pick0) hx h13.2.1 h13.2.2.2.1 (wordIn_ext e1_13 h1.2.2.2.2.1) (wordIn_ext e2_13 h2.2.2.2.2.1)
  generalize cMuxW nin g13 pick0 q0_r q1_r = _r14 at h14 ⊢; rcases _r14 with ⟨g14, outR⟩; dsimp only at h14; dsimp (config := { zeta := false }) only at ⊢
  have e2_14 := gExt_trans e2_13 h14.1
  have e1_14 := gExt_trans h2.1 e2_14
  have h15 := cMuxW_spec (sel := pick0) hx h14.2.1 (wire_ext h14.1 h13.2.2.2.1) (wordIn_ext e1_14 h1.2.2.2.2.2.1) (wordIn_ext e2_14 h2.2.2.2.2.2.1)
  generalize cMuxW nin g14 pick0 q0_b q1_b = _r15 at h15 ⊢; rcases _r15 with ⟨g15, outB⟩; dsimp only at h15 ⊢
  have e2_15 := gExt_trans e2_14 h15.1
  have e5_15 := gExt_trans h6.1 (gExt_trans e6_13 (gExt_trans h14.1 h15.1))
  have hq0_ok_v : valAt g1 x q0_ok = ((s.val g x).queryParity (wordVal g x r0) (wordVal g x r1) (wordVal g x b0) (wordVal g x b1) false).1 := by
    rw [h1.2.2.2.2.2.2.1, valAt_zero hx]
  have hq0_r_v : wordVal g1 x q0_r = ((s.val g x).queryParity (wordVal g x r0) (wordVal g x r1) (wordVal g x b0) (wordVal g x b1) false).2.1 := by
    rw [h1.2.2.2.2.2.2.2.1, valAt_zero hx]
  have hq0_b_v : wordVal g1 x q0_b = ((s.val g x).queryParity (wordVal g x r0) (wordVal g x r1) (wordVal g x b0) (wordVal g x b1) false).2.2 := by
    rw [h1.2.2.2.2.2.2.2.2, valAt_zero hx]
  have hq1_ok_v : valAt g2 x q1_ok = ((s.val g x).queryParity (wordVal g x r0) (wordVal g x r1) (wordVal g x b0) (wordVal g x b1) true).1 := by
    rw [h2.2.2.2.2.2.2.1, hs1, hr0_1, hr1_1, hb0_1, hb1_1, valAt_one hx]
  have hq1_r_v : wordVal g2 x q1_r = ((s.val g x).queryParity (wordVal g x r0) (wordVal g x r1) (wordVal g x b0) (wordVal g x b1) true).2.1 := by
    rw [h2.2.2.2.2.2.2.2.1, hs1, hr0_1, hr1_1, hb0_1, hb1_1, valAt_one hx]
  have hq1_b_v : wordVal g2 x q1_b = ((s.val g x).queryParity (wordVal g x r0) (wordVal g x r1) (wordVal g x b0) (wordVal g x b1) true).2.2 := by
    rw [h2.2.2.2.2.2.2.2.2, hs1, hr0_1, hr1_1, hb0_1, hb1_1, valAt_one hx]
  have hf0_v : valAt g3 x f0 = (valAt g x box_ok && valAt g1 x q0_ok) := by
    rw [h3.2.2.2.2, valAt_ext hx.hlen he12 hbox, valAt_ext hx.hlen h2.1 h1.2.2.2.1]
  have hf1_v : valAt g4 x f1 = (valAt g x box_ok && valAt g2 x q1_ok) := by
    rw [h4.2.2.2.2, valAt_ext hx.hlen he13 hbox, valAt_ext hx.hlen h3.1 h2.2.2.2.1]
  have hpick0_v : valAt g13 x pick0 =
      (valAt g3 x f0 && ((!valAt g4 x f1) || decide (wordVal g1 x q0_r < wordVal g2 x q1_r) ||
        (decide (wordVal g1 x q0_r = wordVal g2 x q1_r) && decide (wordVal g1 x q0_b ≤ wordVal g2 x q1_b)))) := by
    rw [h13.2.2.2.2, valAt_ext hx.hlen e3_12 h3.2.2.2.1, h12.2.2.2.2, h11.2.2.2.2,
      valAt_ext hx.hlen e6_10 h6.2.2.2.1, h6.2.2.2.2, valAt_ext hx.hlen h5.1 h4.2.2.2.1,
      valAt_ext hx.hlen e7_10 h7.2.2.2.1, h7.2.2.2.2,
      wordVal_ext hx.hlen e1_6 h1.2.2.2.2.1, wordVal_ext hx.hlen e2_6 h2.2.2.2.2.1,
      valAt_ext hx.hlen h11.1 h10.2.2.2.1, h10.2.2.2.2,
      valAt_ext hx.hlen h9.1 h8.2.2.2.1, h8.2.2.2.2,
      wordVal_ext hx.hlen e1_7 h1.2.2.2.2.1, wordVal_ext hx.hlen e2_7 h2.2.2.2.2.1,
      h9.2.2.2.2, wordVal_ext hx.hlen e1_8 h1.2.2.2.2.2.1, wordVal_ext hx.hlen e2_8 h2.2.2.2.2.2.1]
  refine ⟨gExt_trans he12 e2_15, h15.2.1,
    by linarith only [hW, h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1, h6.2.2.1,
      h7.2.2.1, h8.2.2.1, h9.2.2.1, h10.2.2.1, h11.2.2.1, h12.2.2.1, h13.2.2.1, h14.2.2.1, h15.2.2.1],
    wire_ext e5_15 h5.2.2.2.1, wordIn_ext h15.1 h14.2.2.2.1, h15.2.2.2.1, ?_, ?_, ?_⟩
  · rw [valAt_ext hx.hlen e5_15 h5.2.2.2.1, h5.2.2.2.2, valAt_ext hx.hlen h4.1 h3.2.2.2.1,
      hf0_v, hf1_v, hq0_ok_v, hq1_ok_v]
  · rw [wordVal_ext hx.hlen h15.1 h14.2.2.2.1, h14.2.2.2.2,
      wordVal_ext hx.hlen e1_13 h1.2.2.2.2.1, wordVal_ext hx.hlen e2_13 h2.2.2.2.2.1,
      hpick0_v, hf0_v, hf1_v, hq0_ok_v, hq1_ok_v, hq0_r_v, hq1_r_v, hq0_b_v, hq1_b_v]
  · rw [h15.2.2.2.2, valAt_ext hx.hlen h14.1 h13.2.2.2.1,
      wordVal_ext hx.hlen e1_14 h1.2.2.2.2.2.1, wordVal_ext hx.hlen e2_14 h2.2.2.2.2.2.1,
      hpick0_v, hf0_v, hf1_v, hq0_ok_v, hq1_ok_v, hq0_r_v, hq1_r_v, hq0_b_v, hq1_b_v]

private def cQuery (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (s : Sum8W W)
    (loR hiR loB hiB : Word W) : List Gate × ℕ × Word W × Word W :=
  let (g1, box_ok, r0, r1, b0, b1) := cQueryBox nin g s loR hiR loB hiB
  cQueryPick nin hW g1 s box_ok r0 r1 b0 b1

private lemma cQuery_spec {nin W : ℕ} (hW : 1 ≤ W) (hW4 : 4 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {s : Sum8W W} {loR hiR loB hiB : Word W}
    (hs : s.In (nin + g.length))
    (hloR : WordIn (nin + g.length) loR) (hhiR : WordIn (nin + g.length) hiR)
    (hloB : WordIn (nin + g.length) loB) (hhiB : WordIn (nin + g.length) hiB)
    (hB : (s.val g x).Bound (2 ^ (W - 3) - 1) ∧
      wordVal g x loR < 2 ^ (W - 3) ∧ wordVal g x hiR < 2 ^ (W - 3) ∧
      wordVal g x loB < 2 ^ (W - 3) ∧ wordVal g x hiB < 2 ^ (W - 3)) :
    let res := cQuery nin hW g s loR hiR loB hiB
    let q := (s.val g x).query (wordVal g x loR) (wordVal g x hiR)
      (wordVal g x loB) (wordVal g x hiB)
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 1100 * W ∧
    res.2.1 < nin + res.1.length ∧ WordIn (nin + res.1.length) res.2.2.1 ∧
    WordIn (nin + res.1.length) res.2.2.2 ∧
    valAt res.1 x res.2.1 = q.1 ∧
    wordVal res.1 x res.2.2.1 = q.2.1 ∧
    wordVal res.1 x res.2.2.2 = q.2.2 := by
  unfold cQuery
  have h1 := cQueryBox_spec hW hW4 hx hv hs hloR hhiR hloB hhiB hB
  generalize cQueryBox nin g s loR hiR loB hiB = _r1 at h1 ⊢
  rcases _r1 with ⟨g1, box_ok, r0, r1, b0, b1⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  rcases h1 with ⟨he1, hv1, hlen1, hbox_in, hr0_in, hr1_in, hb0_in, hb1_in, hbox_v, hr0_v, hr1_v, hb0_v, hb1_v⟩
  have hs1 : s.val g1 x = s.val g x := Sum8W.val_ext hx.hlen he1 hs
  have h2 := cQueryPick_spec hW hW4 hx hv1 (sum8_in_ext he1 hs) hbox_in hr0_in hr1_in hb0_in hb1_in
    ⟨by rw [hs1]; exact hB.1,
     by rw [hr0_v]; exact arith_max_sub_lt hB.1.1 hB.2.1,
     by rw [hr1_v]; exact arith_min_sub_lt hB.2.2.1,
     by rw [hb0_v]; exact arith_max_sub_lt hB.1.2.1 hB.2.2.2.1,
     by rw [hb1_v]; exact arith_min_sub_lt hB.2.2.2.2⟩
  generalize cQueryPick nin hW g1 s box_ok r0 r1 b0 b1 = _r2 at h2 ⊢
  rcases _r2 with ⟨g2, flag, outR, outB⟩; dsimp only at h2 ⊢
  rcases h2 with ⟨he2, hv2, hlen2, hfl_in, houtR_in, houtB_in, hfl_v, houtR_v, houtB_v⟩
  refine ⟨gExt_trans he1 he2, hv2, by linarith only [hlen1, hlen2], hfl_in, houtR_in, houtB_in, ?_, ?_, ?_⟩
  · rw [hfl_v, hbox_v, hs1, hr0_v, hr1_v, hb0_v, hb1_v]; rfl
  · rw [houtR_v, hbox_v, hs1, hr0_v, hr1_v, hb0_v, hb1_v]; rfl
  · rw [houtB_v, hbox_v, hs1, hr0_v, hr1_v, hb0_v, hb1_v]; rfl

/-! ### `cPrep`: single-pass cycle prep circuit -/

private structure PrepStateW (W : ℕ) where
  hasPin : ℕ
  firstBit : ℕ
  preR : Word W
  preB : Word W
  curBit : ℕ
  curR : Word W
  curB : Word W
  acc : Sum8W W

private def PrepStateW.In (bound : ℕ) {W : ℕ} (st : PrepStateW W) : Prop :=
  st.hasPin < bound ∧ st.firstBit < bound ∧ WordIn bound st.preR ∧ WordIn bound st.preB ∧
  st.curBit < bound ∧ WordIn bound st.curR ∧ WordIn bound st.curB ∧ st.acc.In bound

private def PrepStateW.val {W : ℕ} (g : List Gate) (x : List Bool) (st : PrepStateW W) : PrepState :=
  ⟨valAt g x st.hasPin, valAt g x st.firstBit, wordVal g x st.preR, wordVal g x st.preB,
   valAt g x st.curBit, wordVal g x st.curR, wordVal g x st.curB, st.acc.val g x⟩

private def cPrepStep (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (e : ℕ) (pW bW : ℕ)
    (st : PrepStateW W) : List Gate × PrepStateW W :=
  let (g1, xr) := cXor nin g st.curBit bW
  let (g2, seg) := cOfSeg nin hW g1 st.curR st.curB xr
  let (g3, accAdd) := cCombSum8 nin g2 st.acc seg
  let (g4, nhp) := emitNot nin g3 st.hasPin
  let (g5, isFirst) := emitAnd nin g4 pW nhp
  let (g6, isLater) := emitAnd nin g5 pW st.hasPin
  let (g7, newHP) := emitOr nin g6 st.hasPin pW
  let (g8, newFB) := cMux nin g7 isFirst bW st.firstBit
  let (g9, newPreR) := cMuxW nin g8 isFirst st.curR st.preR
  let (g10, newPreB) := cMuxW nin g9 isFirst st.curB st.preB
  let (g11, newCB) := cMux nin g10 pW bW st.curBit
  let (g12, curR1) := cAddW nin g11 st.curR (if e % 2 = 0 then cConstBit W 1 else cConst0 W)
  let (g13, curB1) := cAddW nin g12 st.curB (if e % 2 = 0 then cConst0 W else cConstBit W 1)
  let (g14, newCurR) := cMuxW nin g13 pW (if e % 2 = 0 then cConstBit W 1 else cConst0 W) curR1
  let (g15, newCurB) := cMuxW nin g14 pW (if e % 2 = 0 then cConst0 W else cConstBit W 1) curB1
  let (g16, newAcc) := cMuxSum8 nin g15 isLater accAdd st.acc
  (g16, ⟨newHP, newFB, newPreR, newPreB, newCB, newCurR, newCurB, newAcc⟩)

private lemma cPrepStep_spec {nin W : ℕ} (hW : 1 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) (e : ℕ) {pW bW : ℕ} {st : PrepStateW W}
    (hp : pW < nin + g.length) (hb : bW < nin + g.length) (hst : st.In (nin + g.length))
    (hno : wordVal g x st.curR + wordVal g x st.curB < 2 ^ W ∧
      wordVal g x st.curR + 1 < 2 ^ W ∧ wordVal g x st.curB + 1 < 2 ^ W ∧
      ((st.acc.val g x).comb (Sum8.ofSeg (wordVal g x st.curR) (wordVal g x st.curB)
        (xor (valAt g x st.curBit) (valAt g x bW)))).Bound (2 ^ W - 1)) :
    let res := cPrepStep nin hW g e pW bW st
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 380 * W ∧
    res.2.In (nin + res.1.length) ∧
    res.2.val res.1 x = prepStep e (valAt g x pW) (valAt g x bW) (st.val g x) := by
  have hnin := hx.hnin
  rcases hst with ⟨hhp, hfb, hpr, hpb, hcb, hcr, hcb', hacc⟩
  unfold cPrepStep
  have h1 := cXor_spec hx hv hcb hb
  generalize cXor nin g st.curBit bW = _r1 at h1 ⊢; rcases _r1 with ⟨g1, xr⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have h2 := cOfSeg_spec (p := xr) hW hx h1.2.1 (wordIn_mono (by omega) hcr) (wordIn_mono (by omega) hcb') h1.2.2.2.1
    (by rw [wordVal_ext hx.hlen h1.1 hcr, wordVal_ext hx.hlen h1.1 hcb']; exact hno.1)
  generalize cOfSeg nin hW g1 st.curR st.curB xr = _r2 at h2 ⊢; rcases _r2 with ⟨g2, seg⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have _hl_h2 := gExt_len_le h2.1
  have he12 := gExt_trans h1.1 h2.1
  have hseg_val : seg.val g2 x = Sum8.ofSeg (wordVal g x st.curR) (wordVal g x st.curB)
      (xor (valAt g x st.curBit) (valAt g x bW)) := by
    rw [h2.2.2.2.2, wordVal_ext hx.hlen h1.1 hcr, wordVal_ext hx.hlen h1.1 hcb', h1.2.2.2.2]
  have h3 := cCombSum8_spec hx h2.2.1 (Sum8W.in_mono (by omega) hacc) h2.2.2.2.1
    (by rw [Sum8W.val_ext hx.hlen he12 hacc, hseg_val]; exact hno.2.2.2)
  generalize cCombSum8 nin g2 st.acc seg = _r3 at h3 ⊢; rcases _r3 with ⟨g3, accAdd⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he13 := gExt_trans he12 h3.1
  have h4 := emitNot_spec (a := st.hasPin) hx h3.2.1 (by omega)
  generalize emitNot nin g3 st.hasPin = _r4 at h4 ⊢; rcases _r4 with ⟨g4, nhp⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have he14 := gExt_trans he13 h4.1
  have h5 := emitAnd_spec (a := pW) (b := nhp) hx h4.2.1 (by omega) h4.2.2.2.1
  generalize emitAnd nin g4 pW nhp = _r5 at h5 ⊢; rcases _r5 with ⟨g5, isFirst⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have he15 := gExt_trans he14 h5.1
  have h6 := emitAnd_spec (a := pW) (b := st.hasPin) hx h5.2.1 (by omega) (by omega)
  generalize emitAnd nin g5 pW st.hasPin = _r6 at h6 ⊢; rcases _r6 with ⟨g6, isLater⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have he16 := gExt_trans he15 h6.1
  have h7 := emitOr_spec (a := st.hasPin) (b := pW) hx h6.2.1 (by omega) (by omega)
  generalize emitOr nin g6 st.hasPin pW = _r7 at h7 ⊢; rcases _r7 with ⟨g7, newHP⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have he17 := gExt_trans he16 h7.1
  have h8 := cMux_spec (sel := isFirst) (t := bW) (f := st.firstBit) hx h7.2.1 (by omega) (by omega) (by omega)
  generalize cMux nin g7 isFirst bW st.firstBit = _r8 at h8 ⊢; rcases _r8 with ⟨g8, newFB⟩; dsimp only at h8; dsimp (config := { zeta := false }) only at ⊢
  have he18 := gExt_trans he17 h8.1
  have h9 := cMuxW_spec (sel := isFirst) hx h8.2.1 (by omega) (wordIn_mono (by omega) hcr) (wordIn_mono (by omega) hpr)
  generalize cMuxW nin g8 isFirst st.curR st.preR = _r9 at h9 ⊢; rcases _r9 with ⟨g9, newPreR⟩; dsimp only at h9; dsimp (config := { zeta := false }) only at ⊢
  have he19 := gExt_trans he18 h9.1
  have h10 := cMuxW_spec (sel := isFirst) hx h9.2.1 (by omega) (wordIn_mono (by omega) hcb') (wordIn_mono (by omega) hpb)
  generalize cMuxW nin g9 isFirst st.curB st.preB = _r10 at h10 ⊢; rcases _r10 with ⟨g10, newPreB⟩; dsimp only at h10; dsimp (config := { zeta := false }) only at ⊢
  have he110 := gExt_trans he19 h10.1
  have h11 := cMux_spec (sel := pW) (t := bW) (f := st.curBit) hx h10.2.1 (by omega) (by omega) (by omega)
  generalize cMux nin g10 pW bW st.curBit = _r11 at h11 ⊢; rcases _r11 with ⟨g11, newCB⟩; dsimp only at h11; dsimp (config := { zeta := false }) only at ⊢
  have he111 := gExt_trans he110 h11.1
  let erW := if e % 2 = 0 then cConstBit W 1 else cConst0 W
  let ebW := if e % 2 = 0 then cConst0 W else cConstBit W 1
  have her_spec : ∀ g' : List Gate, WordIn (nin + g'.length) erW ∧
      wordVal g' x erW = if e % 2 = 0 then 1 else 0 := fun g' => by
    dsimp only [erW]; split_ifs
    · have h := cConstBit_spec hW (g := g') hx (b := 1) (by omega)
      exact ⟨h.1, by rw [h.2, valAt_one hx]; rfl⟩
    · exact cConst0_spec (W := W) (g := g') hx
  have heb_spec : ∀ g' : List Gate, WordIn (nin + g'.length) ebW ∧
      wordVal g' x ebW = if e % 2 = 0 then 0 else 1 := fun g' => by
    dsimp only [ebW]; split_ifs
    · exact cConst0_spec (W := W) (g := g') hx
    · have h := cConstBit_spec hW (g := g') hx (b := 1) (by omega)
      exact ⟨h.1, by rw [h.2, valAt_one hx]; rfl⟩
  have h12 := cAddW_spec hx h11.2.1 (wordIn_mono (by omega) hcr) (her_spec g11).1
    (by rw [wordVal_ext hx.hlen he111 hcr, (her_spec g11).2]; split_ifs <;> omega)
  dsimp only [erW] at h12
  generalize cAddW nin g11 st.curR (if e % 2 = 0 then cConstBit W 1 else cConst0 W) = _r12 at h12 ⊢; rcases _r12 with ⟨g12, curR1⟩; dsimp only at h12; dsimp (config := { zeta := false }) only at ⊢
  have he112 := gExt_trans he111 h12.1
  have h13 := cAddW_spec hx h12.2.1 (wordIn_mono (by omega) hcb') (heb_spec g12).1
    (by rw [wordVal_ext hx.hlen he112 hcb', (heb_spec g12).2]; split_ifs <;> omega)
  dsimp only [ebW] at h13
  generalize cAddW nin g12 st.curB (if e % 2 = 0 then cConst0 W else cConstBit W 1) = _r13 at h13 ⊢; rcases _r13 with ⟨g13, curB1⟩; dsimp only at h13; dsimp (config := { zeta := false }) only at ⊢
  have he113 := gExt_trans he112 h13.1
  have h14 := cMuxW_spec (sel := pW) hx h13.2.1 (by omega) (her_spec g13).1 (wordIn_mono (by omega) h12.2.2.2.1)
  dsimp only [erW] at h14
  generalize cMuxW nin g13 pW (if e % 2 = 0 then cConstBit W 1 else cConst0 W) curR1 = _r14 at h14 ⊢; rcases _r14 with ⟨g14, newCurR⟩; dsimp only at h14; dsimp (config := { zeta := false }) only at ⊢
  have he114 := gExt_trans he113 h14.1
  have h15 := cMuxW_spec (sel := pW) hx h14.2.1 (by omega) (heb_spec g14).1 (wordIn_mono (by omega) h13.2.2.2.1)
  dsimp only [ebW] at h15
  generalize cMuxW nin g14 pW (if e % 2 = 0 then cConst0 W else cConstBit W 1) curB1 = _r15 at h15 ⊢; rcases _r15 with ⟨g15, newCurB⟩; dsimp only at h15; dsimp (config := { zeta := false }) only at ⊢
  have he115 := gExt_trans he114 h15.1
  have h16 := cMuxSum8_spec (sel := isLater) hx h15.2.1 (by omega) (Sum8W.in_mono (by omega) h3.2.2.2.1) (Sum8W.in_mono (by omega) hacc)
  dsimp only at h16
  have _hl_h16 := gExt_len_le h16.1
  have he116 := gExt_trans he115 h16.1
  have e11_16 := gExt_trans h12.1 (gExt_trans h13.1 (gExt_trans h14.1 (gExt_trans h15.1 h16.1)))
  have e10_16 := gExt_trans h11.1 e11_16
  have e9_16 := gExt_trans h10.1 e10_16
  have e8_16 := gExt_trans h9.1 e9_16
  have e7_16 := gExt_trans h8.1 e8_16
  dsimp only
  refine ⟨he116, h16.2.1,
    by linarith only [hW, h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1, h6.2.2.1,
      h7.2.2.1, h8.2.2.1, h9.2.2.1, h10.2.2.1, h11.2.2.1, h12.2.2.1, h13.2.2.1, h14.2.2.1,
      h15.2.2.1, h16.2.2.1],
    ⟨wire_ext e7_16 h7.2.2.2.1, wire_ext e8_16 h8.2.2.2.1, wordIn_ext e9_16 h9.2.2.2.1,
     wordIn_ext e10_16 h10.2.2.2.1, wire_ext e11_16 h11.2.2.2.1,
     wordIn_ext (gExt_trans h15.1 h16.1) h14.2.2.2.1, wordIn_ext h16.1 h15.2.2.2.1, h16.2.2.2.1⟩, ?_⟩
  have hisF_v : valAt g5 x isFirst = (valAt g x pW && !(valAt g x st.hasPin)) := by
    rw [h5.2.2.2.2, valAt_ext hx.hlen he14 hp, h4.2.2.2.2, valAt_ext hx.hlen he13 hhp]
  have hisL_v : valAt g6 x isLater = (valAt g x pW && valAt g x st.hasPin) := by
    rw [h6.2.2.2.2, valAt_ext hx.hlen he15 hp, valAt_ext hx.hlen he15 hhp]
  have haccA_v : accAdd.val g3 x = (st.acc.val g x).comb
      (Sum8.ofSeg (wordVal g x st.curR) (wordVal g x st.curB) (xor (valAt g x st.curBit) (valAt g x bW))) := by
    rw [h3.2.2.2.2, Sum8W.val_ext hx.hlen he12 hacc, hseg_val]
  have e5_7 := gExt_trans h6.1 h7.1
  have e5_8 := gExt_trans e5_7 h8.1
  have e5_9 := gExt_trans e5_8 h9.1
  have e6_15 := gExt_trans h7.1 (gExt_trans h8.1 (gExt_trans h9.1 (gExt_trans h10.1
    (gExt_trans h11.1 (gExt_trans h12.1 (gExt_trans h13.1 (gExt_trans h14.1 h15.1)))))))
  have e3_15 := gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 e6_15))
  unfold PrepStateW.val prepStep
  rw [valAt_ext hx.hlen e7_16 h7.2.2.2.1, h7.2.2.2.2, valAt_ext hx.hlen he16 hhp, valAt_ext hx.hlen he16 hp,
      valAt_ext hx.hlen e8_16 h8.2.2.2.1, h8.2.2.2.2, valAt_ext hx.hlen e5_7 h5.2.2.2.1, hisF_v,
      valAt_ext hx.hlen he17 hb, valAt_ext hx.hlen he17 hfb,
      wordVal_ext hx.hlen e9_16 h9.2.2.2.1, h9.2.2.2.2, valAt_ext hx.hlen e5_8 h5.2.2.2.1, hisF_v,
      wordVal_ext hx.hlen he18 hcr, wordVal_ext hx.hlen he18 hpr,
      wordVal_ext hx.hlen e10_16 h10.2.2.2.1, h10.2.2.2.2, valAt_ext hx.hlen e5_9 h5.2.2.2.1, hisF_v,
      wordVal_ext hx.hlen he19 hcb', wordVal_ext hx.hlen he19 hpb,
      valAt_ext hx.hlen e11_16 h11.2.2.2.1, h11.2.2.2.2, valAt_ext hx.hlen he110 hp,
      valAt_ext hx.hlen he110 hb, valAt_ext hx.hlen he110 hcb,
      wordVal_ext hx.hlen (gExt_trans h15.1 h16.1) h14.2.2.2.1, h14.2.2.2.2,
      valAt_ext hx.hlen he113 hp, (her_spec g13).2, wordVal_ext hx.hlen h13.1 h12.2.2.2.1,
      h12.2.2.2.2, wordVal_ext hx.hlen he111 hcr, (her_spec g11).2,
      wordVal_ext hx.hlen h16.1 h15.2.2.2.1, h15.2.2.2.2,
      valAt_ext hx.hlen he114 hp, (heb_spec g14).2, wordVal_ext hx.hlen h14.1 h13.2.2.2.1, h13.2.2.2.2,
      wordVal_ext hx.hlen he112 hcb', (heb_spec g12).2,
      h16.2.2.2.2, valAt_ext hx.hlen e6_15 h6.2.2.2.1, hisL_v,
      Sum8W.val_ext hx.hlen e3_15 h3.2.2.2.1, haccA_v, Sum8W.val_ext hx.hlen he115 hacc]
  cases valAt g x pW <;> cases valAt g x st.hasPin <;> simp

private def cPrepLoop (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (pW bW : ℕ → ℕ) :
    ℕ → List Gate × PrepStateW W
  | 0 => (g, ⟨0, 0, cConst0 W, cConst0 W, 0, cConst0 W, cConst0 W, cSum8Zero W⟩)
  | j + 1 =>
    let (g1, st) := cPrepLoop nin hW g pW bW j
    cPrepStep nin hW g1 j (pW j) (bW j) st

private lemma cPrepLoop_spec {nin W : ℕ} (hW : 1 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {k : ℕ} {pW bW : ℕ → ℕ}
    (hpW : ∀ j < 2 * k, pW j < nin + g.length) (hbW : ∀ j < 2 * k, bW j < nin + g.length)
    (hlim : 2 * k + 2 < 2 ^ W) :
    ∀ j ≤ 2 * k,
      let res := cPrepLoop nin hW g pW bW j
      GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + j * (380 * W) ∧
      res.2.In (nin + res.1.length) ∧
      res.2.val res.1 x = prepLoop k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t)) j ∧
      (res.2.acc.val res.1 x).Cap ((j + 1) / 2 - wordVal res.1 x res.2.curR - wordVal res.1 x res.2.preR)
        (j / 2 - wordVal res.1 x res.2.curB - wordVal res.1 x res.2.preB) ∧
      wordVal res.1 x res.2.curR + wordVal res.1 x res.2.preR ≤ (j + 1) / 2 ∧
      wordVal res.1 x res.2.curB + wordVal res.1 x res.2.preB ≤ j / 2 := by
  have hnin := hx.hnin
  intro j
  induction j with
  | zero =>
    intro _
    dsimp only [cPrepLoop, PrepStateW.In]
    have hz := cConst0_spec (W := W) (g := g) hx
    have hs0 := cSum8Zero_spec (W := W) (g := g) hx
    refine ⟨gExt_refl g, hv, by simp, ⟨by omega, by omega, hz.1, hz.1, by omega, hz.1, hz.1, hs0.1⟩, ?_, ?_, ?_, ?_⟩
    · unfold PrepStateW.val prepLoop; simp [valAt_zero hx, hz.2, hs0.2]
    · simp [hs0.2, hz.2, Sum8.cap_zero]
    · simp [hz.2]
    · simp [hz.2]
  | succ j ih =>
    intro hj
    rcases ih (by omega) with ⟨he1, hv1, hlen1, hin1, hval1, hcap1, hcr1, hcb1⟩
    dsimp only [cPrepLoop]
    set g1 := (cPrepLoop nin hW g pW bW j).1
    set st1 := (cPrepLoop nin hW g pW bW j).2
    have hlen_le : g.length ≤ g1.length := gExt_len_le he1
    have hinv_p := prepLoop_inv k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t)) j (by omega)
    have hst_cur_alt : wordVal g1 x st1.curR + wordVal g1 x st1.curB ≤ 1 ∨
        (1 ≤ wordVal g1 x st1.curR ∧ 1 ≤ wordVal g1 x st1.curB) := by
      have h1 : st1.val g1 x = prepLoop k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t)) j := hval1
      cases hhp : (prepLoop k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t)) j).hasPin
      · rcases hinv_p.2.1 hhp with ⟨_, hcr, hcb, _⟩
        have hcr' : wordVal g1 x st1.curR = (j + 1) / 2 := by
          have := congrArg PrepState.curR h1; dsimp [PrepStateW.val] at this; rw [this, hcr]
        have hcb' : wordVal g1 x st1.curB = j / 2 := by
          have := congrArg PrepState.curB h1; dsimp [PrepStateW.val] at this; rw [this, hcb]
        omega
      · rcases hinv_p.2.2 hhp with ⟨e0, el, he0l, helj, _, _, _, _, _, _, _, _, hcr, hcb, _⟩
        have hcr' : wordVal g1 x st1.curR = (j + 1) / 2 - (el + 1) / 2 := by
          have := congrArg PrepState.curR h1; dsimp [PrepStateW.val] at this; rw [this, hcr]
        have hcb' : wordVal g1 x st1.curB = j / 2 - el / 2 := by
          have := congrArg PrepState.curB h1; dsimp [PrepStateW.val] at this; rw [this, hcb]
        omega
    have hseg_cap : (Sum8.ofSeg (wordVal g1 x st1.curR) (wordVal g1 x st1.curB)
        (xor (valAt g1 x st1.curBit) (valAt g1 x (bW j)))).Cap (wordVal g1 x st1.curR) (wordVal g1 x st1.curB) :=
      Sum8.cap_ofSeg _ _ _ hst_cur_alt
    have hcomb_cap := Sum8.cap_comb hcap1 hseg_cap
    have hno : wordVal g1 x st1.curR + wordVal g1 x st1.curB < 2 ^ W ∧
        wordVal g1 x st1.curR + 1 < 2 ^ W ∧ wordVal g1 x st1.curB + 1 < 2 ^ W ∧
        ((st1.acc.val g1 x).comb (Sum8.ofSeg (wordVal g1 x st1.curR) (wordVal g1 x st1.curB)
          (xor (valAt g1 x st1.curBit) (valAt g1 x (bW j))))).Bound (2 ^ W - 1) := by
      refine ⟨by omega, by omega, by omega,
        Sum8.cap_bound hcomb_cap (by omega) (by omega)⟩
    have h2 := cPrepStep_spec hW hx hv1 j (pW := pW j) (bW := bW j) (by have := hpW j (by omega); omega)
      (by have := hbW j (by omega); omega) hin1 hno
    generalize cPrepStep nin hW g1 j (pW j) (bW j) st1 = _r2 at h2 ⊢; rcases _r2 with ⟨g2, st2⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
    have _hl_h2 := gExt_len_le h2.1
    have hstep_val := h2.2.2.2.2
    have hacc_eq : st2.acc.val g2 x =
        (prepStep j (valAt g1 x (pW j)) (valAt g1 x (bW j)) (st1.val g1 x)).acc :=
      congrArg PrepState.acc hstep_val
    have hcr_eq : wordVal g2 x st2.curR =
        (prepStep j (valAt g1 x (pW j)) (valAt g1 x (bW j)) (st1.val g1 x)).curR :=
      congrArg PrepState.curR hstep_val
    have hcb_eq : wordVal g2 x st2.curB =
        (prepStep j (valAt g1 x (pW j)) (valAt g1 x (bW j)) (st1.val g1 x)).curB :=
      congrArg PrepState.curB hstep_val
    have hpr_eq : wordVal g2 x st2.preR =
        (prepStep j (valAt g1 x (pW j)) (valAt g1 x (bW j)) (st1.val g1 x)).preR :=
      congrArg PrepState.preR hstep_val
    have hpb_eq : wordVal g2 x st2.preB =
        (prepStep j (valAt g1 x (pW j)) (valAt g1 x (bW j)) (st1.val g1 x)).preB :=
      congrArg PrepState.preB hstep_val
    refine ⟨gExt_trans he1 h2.1, h2.2.1, by nlinarith [h2.2.2.1], h2.2.2.2.1, ?_, ?_, ?_, ?_⟩
    · rw [hstep_val, valAt_ext hx.hlen he1 (hpW j (by omega)),
        valAt_ext hx.hlen he1 (hbW j (by omega)), hval1]; rfl
    · rw [hacc_eq, hcr_eq, hcb_eq, hpr_eq, hpb_eq]
      dsimp only [prepStep, PrepStateW.val]
      by_cases hpj : valAt g1 x (pW j) = true
      · simp only [hpj, ↓reduceIte]
        cases hhp1 : valAt g1 x st1.hasPin
        · simp only [Bool.not_false, ↓reduceIte]
          have hhp_p : (prepLoop k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t)) j).hasPin = false := by
            have := congrArg PrepState.hasPin hval1; dsimp [PrepStateW.val] at this; rw [← this, hhp1]
          rcases hinv_p.2.1 hhp_p with ⟨hacc0, hcr0, hcb0, _⟩
          have ha0 : st1.acc.val g1 x = Sum8.zero := by
            have := congrArg PrepState.acc hval1; dsimp [PrepStateW.val] at this; rw [this, hacc0]
          rw [ha0]; unfold Sum8.Cap Sum8.zero; simp
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rcases hcomb_cap with ⟨_, _, _, _, _, _, _, _, _, _⟩
          unfold Sum8.Cap; split_ifs <;> ((try dsimp only); omega)
      · rw [if_neg hpj]
        rcases hcap1 with ⟨_, _, _, _, _, _, _, _, _, _⟩
        unfold Sum8.Cap; split_ifs <;> ((try dsimp only); omega)
    · rw [hcr_eq, hpr_eq]; dsimp only [prepStep, PrepStateW.val]
      split_ifs <;> ((try dsimp only); omega)
    · rw [hcb_eq, hpb_eq]; dsimp only [prepStep, PrepStateW.val]
      split_ifs <;> ((try dsimp only); omega)

private def cCyclePrep (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (k : ℕ)
    (pW bW : ℕ → ℕ) : List Gate × Sum8W W :=
  let (g1, st) := cPrepLoop nin hW g pW bW (2 * k)
  let (g2, totR) := cAddW nin g1 st.curR st.preR
  let (g3, totB) := cAddW nin g2 st.curB st.preB
  let (g4, wrapP) := cXor nin g3 st.curBit st.firstBit
  let (g5, segWrap) := cOfSeg nin hW g4 totR totB wrapP
  let (g6, segFree) := cOfSeg nin hW g5 st.curR st.curB 0
  let (g7, segLast) := cMuxSum8 nin g6 st.hasPin segWrap segFree
  cCombSum8 nin g7 st.acc segLast

private lemma cCyclePrep_spec {nin W : ℕ} (hW : 1 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {k : ℕ} (hk : 1 ≤ k) {pW bW : ℕ → ℕ}
    (hpW : ∀ j < 2 * k, pW j < nin + g.length) (hbW : ∀ j < 2 * k, bW j < nin + g.length)
    (hlim : 2 * k + 2 < 2 ^ W) :
    let res := cCyclePrep nin hW g k pW bW
    let ps := pureCycleSum k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t))
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + k * (1300 * W) ∧
    res.2.In (nin + res.1.length) ∧
    res.2.val res.1 x = ps ∧ ps.Cap k k ∧ ps.Good := by
  have hnin := hx.hnin
  unfold cCyclePrep
  have h1 := cPrepLoop_spec hW hx hv hpW hbW hlim (2 * k) le_rfl
  generalize cPrepLoop nin hW g pW bW (2 * k) = _r1 at h1 ⊢; rcases _r1 with ⟨g1, st⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  rcases h1 with ⟨he1, hv1, hlen1, hin1, hval1, hcap1, hcr1, hcb1⟩
  rcases hin1 with ⟨hhp, hfb, hpr, hpb, hcb, hcr, hcb', hacc⟩
  have h2k_r : (2 * k + 1) / 2 = k := by omega
  have h2k_b : (2 * k) / 2 = k := by omega
  rw [h2k_r] at hcap1 hcr1
  rw [h2k_b] at hcap1 hcb1
  have h2 := cAddW_spec hx hv1 hcr hpr (by omega)
  generalize cAddW nin g1 st.curR st.preR = _r2 at h2 ⊢; rcases _r2 with ⟨g2, totR⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have h3 := cAddW_spec hx h2.2.1 (wordIn_mono (by omega) hcb') (wordIn_mono (by omega) hpb)
    (by rw [wordVal_ext hx.hlen h2.1 hcb', wordVal_ext hx.hlen h2.1 hpb]; omega)
  generalize cAddW nin g2 st.curB st.preB = _r3 at h3 ⊢; rcases _r3 with ⟨g3, totB⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he23 := gExt_trans h2.1 h3.1
  have h4 := cXor_spec (a := st.curBit) (b := st.firstBit) hx h3.2.1 (by omega) (by omega)
  generalize cXor nin g3 st.curBit st.firstBit = _r4 at h4 ⊢; rcases _r4 with ⟨g4, wrapP⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have he24 := gExt_trans he23 h4.1
  have htotR_v : wordVal g4 x totR = wordVal g1 x st.curR + wordVal g1 x st.preR := by
    rw [wordVal_ext hx.hlen (gExt_trans h3.1 h4.1) h2.2.2.2.1, h2.2.2.2.2]
  have htotB_v : wordVal g4 x totB = wordVal g1 x st.curB + wordVal g1 x st.preB := by
    rw [wordVal_ext hx.hlen h4.1 h3.2.2.2.1, h3.2.2.2.2, wordVal_ext hx.hlen h2.1 hcb', wordVal_ext hx.hlen h2.1 hpb]
  have h5 := cOfSeg_spec (p := wrapP) hW hx h4.2.1 (wordIn_mono (by omega) h2.2.2.2.1)
    (wordIn_mono (by omega) h3.2.2.2.1) h4.2.2.2.1 (by rw [htotR_v, htotB_v]; omega)
  generalize cOfSeg nin hW g4 totR totB wrapP = _r5 at h5 ⊢; rcases _r5 with ⟨g5, segWrap⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have _hl_h5 := gExt_len_le h5.1
  have he25 := gExt_trans he24 h5.1
  have h6 := cOfSeg_spec (p := 0) hW hx h5.2.1 (wordIn_mono (by omega) hcr)
    (wordIn_mono (by omega) hcb') (by omega)
    (by rw [wordVal_ext hx.hlen he25 hcr, wordVal_ext hx.hlen he25 hcb']; omega)
  generalize cOfSeg nin hW g5 st.curR st.curB 0 = _r6 at h6 ⊢; rcases _r6 with ⟨g6, segFree⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have _hl_h6 := gExt_len_le h6.1
  have he26 := gExt_trans he25 h6.1
  have h7 := cMuxSum8_spec (sel := st.hasPin) hx h6.2.1 (by omega) (Sum8W.in_mono (by omega) h5.2.2.2.1) h6.2.2.2.1
  generalize cMuxSum8 nin g6 st.hasPin segWrap segFree = _r7 at h7 ⊢; rcases _r7 with ⟨g7, segLast⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have he27 := gExt_trans he26 h7.1
  have hwrap_v : segWrap.val g5 x = Sum8.ofSeg (wordVal g1 x st.curR + wordVal g1 x st.preR)
      (wordVal g1 x st.curB + wordVal g1 x st.preB) (xor (valAt g1 x st.curBit) (valAt g1 x st.firstBit)) := by
    rw [h5.2.2.2.2, htotR_v, htotB_v, h4.2.2.2.2, valAt_ext hx.hlen he23 hcb, valAt_ext hx.hlen he23 hfb]
  have hfree_v : segFree.val g6 x = Sum8.ofSeg (wordVal g1 x st.curR) (wordVal g1 x st.curB) false := by
    rw [h6.2.2.2.2, wordVal_ext hx.hlen he25 hcr, wordVal_ext hx.hlen he25 hcb', valAt_zero hx]
  have hlast_v : segLast.val g7 x =
      if valAt g1 x st.hasPin then
        Sum8.ofSeg (wordVal g1 x st.curR + wordVal g1 x st.preR)
          (wordVal g1 x st.curB + wordVal g1 x st.preB) (xor (valAt g1 x st.curBit) (valAt g1 x st.firstBit))
      else Sum8.ofSeg (wordVal g1 x st.curR) (wordVal g1 x st.curB) false := by
    rw [h7.2.2.2.2, valAt_ext hx.hlen he26 hhp, Sum8W.val_ext hx.hlen h6.1 h5.2.2.2.1, hwrap_v, hfree_v]
  have hinv_p := prepLoop_inv k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t)) (2 * k) le_rfl
  have hcap_final : ((st.acc.val g1 x).comb (segLast.val g7 x)).Cap k k := by
    rw [hlast_v]
    cases hhp_v : valAt g1 x st.hasPin
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hhp_p : (prepLoop k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t)) (2 * k)).hasPin = false := by
        have := congrArg PrepState.hasPin hval1; dsimp [PrepStateW.val] at this; rw [← this, hhp_v]
      rcases hinv_p.2.1 hhp_p with ⟨hacc0, hcr0, hcb0, _⟩
      have hcr' : wordVal g1 x st.curR = k := by
        have := congrArg PrepState.curR hval1; dsimp [PrepStateW.val] at this; rw [this, hcr0]; omega
      have hcb' : wordVal g1 x st.curB = k := by
        have := congrArg PrepState.curB hval1; dsimp [PrepStateW.val] at this; rw [this, hcb0]; omega
      have ha' : st.acc.val g1 x = Sum8.zero := by
        have := congrArg PrepState.acc hval1; dsimp [PrepStateW.val] at this; rw [this, hacc0]
      rw [ha', Sum8.comb_zero_left, hcr', hcb']
      exact Sum8.cap_ofSeg k k false (by omega)
    · simp only [↓reduceIte]
      have hhp_p : (prepLoop k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t)) (2 * k)).hasPin = true := by
        have := congrArg PrepState.hasPin hval1; dsimp [PrepStateW.val] at this; rw [← this, hhp_v]
      rcases hinv_p.2.2 hhp_p with ⟨e0, el, he0l, helk, _, _, _, _, _, _, hpr0, hpb0, hcr0, hcb0, _⟩
      have hcr' : wordVal g1 x st.curR = k - (el + 1) / 2 := by
        have := congrArg PrepState.curR hval1; dsimp [PrepStateW.val] at this; rw [this, hcr0]; omega
      have hcb' : wordVal g1 x st.curB = k - el / 2 := by
        have := congrArg PrepState.curB hval1; dsimp [PrepStateW.val] at this; rw [this, hcb0]; omega
      have hpr' : wordVal g1 x st.preR = (e0 + 1) / 2 := by
        have := congrArg PrepState.preR hval1; dsimp [PrepStateW.val] at this; rw [this, hpr0]
      have hpb' : wordVal g1 x st.preB = e0 / 2 := by
        have := congrArg PrepState.preB hval1; dsimp [PrepStateW.val] at this; rw [this, hpb0]
      have hseg_c := Sum8.cap_ofSeg (wordVal g1 x st.curR + wordVal g1 x st.preR)
        (wordVal g1 x st.curB + wordVal g1 x st.preB)
        (xor (valAt g1 x st.curBit) (valAt g1 x st.firstBit)) (by omega)
      have hc := Sum8.cap_comb hcap1 hseg_c
      rcases hc with ⟨_, _, _, _, _, _, _, _, _, _⟩
      unfold Sum8.Cap; omega
  have h8 := cCombSum8_spec hx h7.2.1 (Sum8W.in_mono (by omega) hacc) h7.2.2.2.1
    (by rw [Sum8W.val_ext hx.hlen he27 hacc]; exact Sum8.cap_bound hcap_final (by omega) (by omega))
  generalize cCombSum8 nin g7 st.acc segLast = _r8 at h8 ⊢; rcases _r8 with ⟨g8, resS⟩; dsimp only at h8
  have hres_eq : resS.val g8 x =
      pureCycleSum k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t)) := by
    rw [h8.2.2.2.2, Sum8W.val_ext hx.hlen he27 hacc, hlast_v]
    unfold pureCycleSum
    rw [← hval1]
    dsimp only [PrepStateW.val]
    cases valAt g1 x st.hasPin <;> rfl
  dsimp only
  refine ⟨gExt_trans he1 (gExt_trans he27 h8.1), h8.2.1, ?_, h8.2.2.2.1, hres_eq, ?_,
    pureCycleSum_good hk _ _⟩
  · have hkw : W ≤ k * W := Nat.le_mul_of_pos_left W hk
    linarith only [hkw, hW, hlen1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1, h6.2.2.1, h7.2.2.1, h8.2.2.1]
  · rw [← hres_eq, h8.2.2.2.2, Sum8W.val_ext hx.hlen he27 hacc]; exact hcap_final

/-! ### `cBackScan`, `cWalkLoop`, and `cCycleBuild`: rotation-free reconstruction -/

private structure BackStateW (W : ℕ) where
  nxtBit : ℕ
  remR : Word W
  remB : Word W
  later : Sum8W W

private def BackStateW.In (bound : ℕ) {W : ℕ} (st : BackStateW W) : Prop :=
  st.nxtBit < bound ∧ WordIn bound st.remR ∧ WordIn bound st.remB ∧ st.later.In bound

private lemma BackStateW.in_mono {b1 b2 W : ℕ} {st : BackStateW W} (hle : b1 ≤ b2)
    (hst : st.In b1) : st.In b2 :=
  ⟨lt_of_lt_of_le hst.1 hle, wordIn_mono hle hst.2.1, wordIn_mono hle hst.2.2.1,
   Sum8W.in_mono hle hst.2.2.2⟩

private def BackStateW.val {W : ℕ} (g : List Gate) (x : List Bool) (st : BackStateW W) : BackState :=
  ⟨valAt g x st.nxtBit, wordVal g x st.remR, wordVal g x st.remB, st.later.val g x⟩

private lemma BackStateW.val_ext {nin W : ℕ} {g g' : List Gate} {x : List Bool}
    (hx : x.length = nin) (hext : GExt g g') {st : BackStateW W} (hst : st.In (nin + g.length)) :
    st.val g' x = st.val g x := by
  unfold BackStateW.val
  congr 1
  · exact valAt_ext hx hext hst.1
  · exact wordVal_ext hx hext hst.2.1
  · exact wordVal_ext hx hext hst.2.2.1
  · exact Sum8W.val_ext hx hext hst.2.2.2

private def cBackStep (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (j : ℕ)
    (pNext bNext : ℕ) (stNext : BackStateW W) : List Gate × BackStateW W :=
  let (g1, xr) := cXor nin g bNext stNext.nxtBit
  let (g2, seg) := cOfSeg nin hW g1 stNext.remR stNext.remB xr
  let (g3, latAdd) := cCombSum8 nin g2 seg stNext.later
  let (g4, newNxt) := cMux nin g3 pNext bNext stNext.nxtBit
  let (g5, rAdd) := cAddW nin g4 stNext.remR (if j % 2 = 0 then cConstBit W 1 else cConst0 W)
  let (g6, bAdd) := cAddW nin g5 stNext.remB (if j % 2 = 0 then cConst0 W else cConstBit W 1)
  let (g7, newR) := cMuxW nin g6 pNext (if j % 2 = 0 then cConstBit W 1 else cConst0 W) rAdd
  let (g8, newB) := cMuxW nin g7 pNext (if j % 2 = 0 then cConst0 W else cConstBit W 1) bAdd
  let (g9, newLat) := cMuxSum8 nin g8 pNext latAdd stNext.later
  (g9, ⟨newNxt, newR, newB, newLat⟩)

private lemma cBackStep_spec {nin W : ℕ} (hW : 1 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) (j : ℕ) {pNext bNext : ℕ} {stNext : BackStateW W}
    (hp : pNext < nin + g.length) (hb : bNext < nin + g.length) (hst : stNext.In (nin + g.length))
    (hno : wordVal g x stNext.remR + wordVal g x stNext.remB < 2 ^ W ∧
      wordVal g x stNext.remR + 1 < 2 ^ W ∧ wordVal g x stNext.remB + 1 < 2 ^ W ∧
      ((Sum8.ofSeg (wordVal g x stNext.remR) (wordVal g x stNext.remB)
        (xor (valAt g x bNext) (valAt g x stNext.nxtBit))).comb (stNext.later.val g x)).Bound (2 ^ W - 1)) :
    let res := cBackStep nin hW g j pNext bNext stNext
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 360 * W ∧
    res.2.In (nin + res.1.length) ∧
    res.2.val res.1 x = backStep j (valAt g x pNext) (valAt g x bNext) (stNext.val g x) := by
  have hnin := hx.hnin
  rcases hst with ⟨hnx, hrr, hrb, hlat⟩
  unfold cBackStep
  have h1 := cXor_spec hx hv hb hnx
  generalize cXor nin g bNext stNext.nxtBit = _r1 at h1 ⊢; rcases _r1 with ⟨g1, xr⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have h2 := cOfSeg_spec (p := xr) hW hx h1.2.1 (wordIn_mono (by omega) hrr) (wordIn_mono (by omega) hrb) h1.2.2.2.1
    (by rw [wordVal_ext hx.hlen h1.1 hrr, wordVal_ext hx.hlen h1.1 hrb]; exact hno.1)
  generalize cOfSeg nin hW g1 stNext.remR stNext.remB xr = _r2 at h2 ⊢; rcases _r2 with ⟨g2, seg⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have _hl_h2 := gExt_len_le h2.1
  have he12 := gExt_trans h1.1 h2.1
  have hseg_v : seg.val g2 x = Sum8.ofSeg (wordVal g x stNext.remR) (wordVal g x stNext.remB)
      (xor (valAt g x bNext) (valAt g x stNext.nxtBit)) := by
    rw [h2.2.2.2.2, wordVal_ext hx.hlen h1.1 hrr, wordVal_ext hx.hlen h1.1 hrb, h1.2.2.2.2]
  have h3 := cCombSum8_spec hx h2.2.1 h2.2.2.2.1 (Sum8W.in_mono (by omega) hlat)
    (by rw [hseg_v, Sum8W.val_ext hx.hlen he12 hlat]; exact hno.2.2.2)
  generalize cCombSum8 nin g2 seg stNext.later = _r3 at h3 ⊢; rcases _r3 with ⟨g3, latAdd⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he13 := gExt_trans he12 h3.1
  have h4 := cMux_spec (sel := pNext) (t := bNext) (f := stNext.nxtBit) hx h3.2.1 (by omega) (by omega) (by omega)
  generalize cMux nin g3 pNext bNext stNext.nxtBit = _r4 at h4 ⊢; rcases _r4 with ⟨g4, newNxt⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have he14 := gExt_trans he13 h4.1
  let erW := if j % 2 = 0 then cConstBit W 1 else cConst0 W
  let ebW := if j % 2 = 0 then cConst0 W else cConstBit W 1
  have her_spec : ∀ g' : List Gate, WordIn (nin + g'.length) erW ∧
      wordVal g' x erW = if j % 2 = 0 then 1 else 0 := fun g' => by
    dsimp only [erW]; split_ifs
    · have h := cConstBit_spec hW (g := g') hx (b := 1) (by omega)
      exact ⟨h.1, by rw [h.2, valAt_one hx]; rfl⟩
    · exact cConst0_spec (W := W) (g := g') hx
  have heb_spec : ∀ g' : List Gate, WordIn (nin + g'.length) ebW ∧
      wordVal g' x ebW = if j % 2 = 0 then 0 else 1 := fun g' => by
    dsimp only [ebW]; split_ifs
    · exact cConst0_spec (W := W) (g := g') hx
    · have h := cConstBit_spec hW (g := g') hx (b := 1) (by omega)
      exact ⟨h.1, by rw [h.2, valAt_one hx]; rfl⟩
  have h5 := cAddW_spec hx h4.2.1 (wordIn_mono (by omega) hrr) (her_spec g4).1
    (by rw [wordVal_ext hx.hlen he14 hrr, (her_spec g4).2]; split_ifs <;> omega)
  dsimp only [erW] at h5
  generalize cAddW nin g4 stNext.remR (if j % 2 = 0 then cConstBit W 1 else cConst0 W) = _r5 at h5 ⊢; rcases _r5 with ⟨g5, rAdd⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have he15 := gExt_trans he14 h5.1
  have h6 := cAddW_spec hx h5.2.1 (wordIn_mono (by omega) hrb) (heb_spec g5).1
    (by rw [wordVal_ext hx.hlen he15 hrb, (heb_spec g5).2]; split_ifs <;> omega)
  dsimp only [ebW] at h6
  generalize cAddW nin g5 stNext.remB (if j % 2 = 0 then cConst0 W else cConstBit W 1) = _r6 at h6 ⊢; rcases _r6 with ⟨g6, bAdd⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have he16 := gExt_trans he15 h6.1
  have h7 := cMuxW_spec (sel := pNext) hx h6.2.1 (by omega) (her_spec g6).1 (wordIn_mono (by omega) h5.2.2.2.1)
  dsimp only [erW] at h7
  generalize cMuxW nin g6 pNext (if j % 2 = 0 then cConstBit W 1 else cConst0 W) rAdd = _r7 at h7 ⊢; rcases _r7 with ⟨g7, newR⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have he17 := gExt_trans he16 h7.1
  have h8 := cMuxW_spec (sel := pNext) hx h7.2.1 (by omega) (heb_spec g7).1 (wordIn_mono (by omega) h6.2.2.2.1)
  dsimp only [ebW] at h8
  generalize cMuxW nin g7 pNext (if j % 2 = 0 then cConst0 W else cConstBit W 1) bAdd = _r8 at h8 ⊢; rcases _r8 with ⟨g8, newB⟩; dsimp only at h8; dsimp (config := { zeta := false }) only at ⊢
  have he18 := gExt_trans he17 h8.1
  have h9 := cMuxSum8_spec (sel := pNext) hx h8.2.1 (by omega) (Sum8W.in_mono (by omega) h3.2.2.2.1) (Sum8W.in_mono (by omega) hlat)
  dsimp only at h9
  have _hl_h9 := gExt_len_le h9.1
  have he19 := gExt_trans he18 h9.1
  have e4_9 := gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 (gExt_trans h8.1 h9.1)))
  dsimp only
  refine ⟨he19, h9.2.1,
    by linarith only [hW, h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1, h6.2.2.1,
      h7.2.2.1, h8.2.2.1, h9.2.2.1],
    ⟨wire_ext e4_9 h4.2.2.2.1, wordIn_ext (gExt_trans h8.1 h9.1) h7.2.2.2.1,
     wordIn_ext h9.1 h8.2.2.2.1, h9.2.2.2.1⟩, ?_⟩
  have e3_8 := gExt_trans h4.1 (gExt_trans h5.1 (gExt_trans h6.1 (gExt_trans h7.1 h8.1)))
  unfold BackStateW.val backStep
  rw [valAt_ext hx.hlen e4_9 h4.2.2.2.1, h4.2.2.2.2, valAt_ext hx.hlen he13 hp,
      valAt_ext hx.hlen he13 hb, valAt_ext hx.hlen he13 hnx,
      wordVal_ext hx.hlen (gExt_trans h8.1 h9.1) h7.2.2.2.1, h7.2.2.2.2,
      valAt_ext hx.hlen he16 hp, (her_spec g6).2, wordVal_ext hx.hlen h6.1 h5.2.2.2.1,
      h5.2.2.2.2, wordVal_ext hx.hlen he14 hrr, (her_spec g4).2,
      wordVal_ext hx.hlen h9.1 h8.2.2.2.1, h8.2.2.2.2,
      valAt_ext hx.hlen he17 hp, (heb_spec g7).2, wordVal_ext hx.hlen h7.1 h6.2.2.2.1, h6.2.2.2.2,
      wordVal_ext hx.hlen he15 hrb, (heb_spec g5).2,
      h9.2.2.2.2, valAt_ext hx.hlen he18 hp, Sum8W.val_ext hx.hlen e3_8 h3.2.2.2.1,
      h3.2.2.2.2, hseg_v, Sum8W.val_ext hx.hlen he12 hlat, Sum8W.val_ext hx.hlen he18 hlat]
  cases valAt g x pNext <;> rfl

private def cBackScan (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (k : ℕ)
    (pW bW : ℕ → ℕ) (a0W : ℕ) (laterCyc : Sum8W W) :
    ℕ → List Gate × (ℕ → BackStateW W)
  | 0 => (g, fun _ => ⟨a0W, cConst0 W, cConst0 W, laterCyc⟩)
  | d + 1 =>
    let (g1, arr) := cBackScan nin hW g k pW bW a0W laterCyc d
    if d = 0 then
      let st1 : BackStateW W := ⟨a0W, cConst0 W, cConstBit W 1, laterCyc⟩
      (g1, fun m => if m = 1 then st1 else arr m)
    else
      let j := 2 * k - 1 - d
      let (g2, stNew) := cBackStep nin hW g1 j (pW (j + 1)) (bW (j + 1)) (arr d)
      (g2, fun m => if m = d + 1 then stNew else arr m)

private lemma cBackScan_spec {nin W : ℕ} (hW : 1 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {k : ℕ} (hk : 1 ≤ k) {pW bW : ℕ → ℕ}
    {a0W : ℕ} {laterCyc : Sum8W W} {nLat : ℕ}
    (hpW : ∀ j < 2 * k, pW j < nin + g.length) (hbW : ∀ j < 2 * k, bW j < nin + g.length)
    (ha0 : a0W < nin + g.length) (hlatIn : laterCyc.In (nin + g.length))
    (hlatG : (laterCyc.val g x).Good) (hlatCap : (laterCyc.val g x).Cap nLat nLat)
    (hlim : 2 * k + nLat + 2 < 2 ^ W) :
    ∀ d ≤ 2 * k,
      let res := cBackScan nin hW g k pW bW a0W laterCyc d
      GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + d * (360 * W) ∧
      (∀ m ≤ d, (res.2 m).In (nin + res.1.length) ∧
        (res.2 m).val res.1 x =
          backScanList k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t))
            (valAt g x a0W) (laterCyc.val g x) m ∧
        ((res.2 m).later.val res.1 x).Cap (nLat + m / 2 - wordVal res.1 x (res.2 m).remR)
          (nLat + (m + 1) / 2 - wordVal res.1 x (res.2 m).remB) ∧
        wordVal res.1 x (res.2 m).remR + wordVal res.1 x (res.2 m).remB ≤ m) := by
  have hnin := hx.hnin
  intro d
  induction d with
  | zero =>
    intro _
    dsimp only [cBackScan]
    have hz := cConst0_spec (W := W) (g := g) hx
    refine ⟨gExt_refl g, hv, by simp, fun m hm => ?_⟩
    have hm0 : m = 0 := by omega
    subst hm0
    refine ⟨⟨ha0, hz.1, hz.1, hlatIn⟩, ?_, ?_, ?_⟩
    · unfold BackStateW.val backScanList; simp [hz.2]
    · simp only [hz.2, Nat.sub_zero, Nat.add_zero]; exact hlatCap
    · simp [hz.2]
  | succ d ih =>
    intro hd
    rcases ih (by omega) with ⟨he1, hv1, hlen1, harr1⟩
    dsimp only [cBackScan]
    set g1 := (cBackScan nin hW g k pW bW a0W laterCyc d).1
    set arr := (cBackScan nin hW g k pW bW a0W laterCyc d).2
    have hlen_le : g.length ≤ g1.length := gExt_len_le he1
    by_cases hd0 : d = 0
    · subst hd0
      simp only [↓reduceIte]
      have hz := cConst0_spec (W := W) (g := g1) hx
      have h1b := cConstBit_spec hW (g := g1) hx (b := 1) (by omega)
      refine ⟨he1, hv1, by omega, fun m hm => ?_⟩
      by_cases hm1 : m = 1
      · subst hm1
        simp only [↓reduceIte]
        have hpar_last : (2 * k - 1 - 0) % 2 ≠ 0 := by omega
        refine ⟨⟨lt_of_lt_of_le ha0 (Nat.add_le_add_left hlen_le nin), hz.1, h1b.1, Sum8W.in_mono (by omega) hlatIn⟩, ?_, ?_, ?_⟩
        · unfold BackStateW.val backScanList
          simp only [↓reduceIte, hpar_last, hz.2, h1b.2, valAt_one hx, Bool.toNat_true,
            valAt_ext hx.hlen he1 ha0, Sum8W.val_ext hx.hlen he1 hlatIn]
        · rw [Sum8W.val_ext hx.hlen he1 hlatIn, hz.2, h1b.2, valAt_one hx, Bool.toNat_true]
          rcases hlatCap with ⟨_, _, _, _, _, _, _, _, _, _⟩; unfold Sum8.Cap; omega
        · rw [hz.2, h1b.2, valAt_one hx]; decide
      · simp only [hm1, ↓reduceIte]
        exact harr1 m (by omega)
    · simp only [hd0, ↓reduceIte]
      set j := 2 * k - 1 - d
      have hj_def : j = 2 * k - 1 - d := rfl
      have hj1 : j + 1 < 2 * k := by omega
      rcases harr1 d le_rfl with ⟨hinD, hvalD, hcapD, hleD⟩
      have halt := backAt_rem_alt hk (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t))
        (valAt g x a0W) (laterCyc.val g x) hlatG d (by omega) (by omega)
      dsimp only at halt
      have hbd_eq : backAt k (fun t => valAt g x (pW t)) (fun t => valAt g x (bW t))
          (valAt g x a0W) (laterCyc.val g x) (2 * k - d) = (arr d).val g1 x := by
        unfold backAt; rw [show 2 * k - (2 * k - d) = d by omega]; exact hvalD.symm
      rw [hbd_eq] at halt
      have hseg_alt : wordVal g1 x (arr d).remR + wordVal g1 x (arr d).remB ≤ 1 ∨
          (1 ≤ wordVal g1 x (arr d).remR ∧ 1 ≤ wordVal g1 x (arr d).remB) := by
        rcases halt with ⟨_, _, hev, hod, _⟩
        by_cases hpar : (2 * k - d) % 2 = 0
        · have := hev hpar; dsimp [BackStateW.val] at this; omega
        · have := hod (by omega); dsimp [BackStateW.val] at this; omega
      have hrem_ub : wordVal g1 x (arr d).remR ≤ d / 2 ∧ wordVal g1 x (arr d).remB ≤ (d + 1) / 2 := by
        rcases halt with ⟨_, _, hev, hod, _⟩
        by_cases hpar : (2 * k - d) % 2 = 0
        · have := hev hpar; dsimp [BackStateW.val] at this; omega
        · have := hod (by omega); dsimp [BackStateW.val] at this; omega
      have hseg_cap := Sum8.cap_ofSeg (wordVal g1 x (arr d).remR) (wordVal g1 x (arr d).remB)
        (xor (valAt g1 x (bW (j + 1))) (valAt g1 x (arr d).nxtBit)) hseg_alt
      have hcomb_cap := Sum8.cap_comb hseg_cap hcapD
      have hno : wordVal g1 x (arr d).remR + wordVal g1 x (arr d).remB < 2 ^ W ∧
          wordVal g1 x (arr d).remR + 1 < 2 ^ W ∧ wordVal g1 x (arr d).remB + 1 < 2 ^ W ∧
          ((Sum8.ofSeg (wordVal g1 x (arr d).remR) (wordVal g1 x (arr d).remB)
            (xor (valAt g1 x (bW (j + 1))) (valAt g1 x (arr d).nxtBit))).comb
            ((arr d).later.val g1 x)).Bound (2 ^ W - 1) := by
        refine ⟨by omega, by omega, by omega, Sum8.cap_bound hcomb_cap (by omega) (by omega)⟩
      have h2 := cBackStep_spec hW hx hv1 j (pNext := pW (j + 1)) (bNext := bW (j + 1))
        (wire_ext he1 (hpW (j + 1) hj1)) (wire_ext he1 (hbW (j + 1) hj1)) hinD hno
      generalize cBackStep nin hW g1 j (pW (j + 1)) (bW (j + 1)) (arr d) = _r2 at h2 ⊢
      rcases _r2 with ⟨g2, stNew⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
      have hstep_v := h2.2.2.2.2
      refine ⟨gExt_trans he1 h2.1, h2.2.1, by nlinarith [hlen1, h2.2.2.1], fun m hm => ?_⟩
      by_cases hmeq : m = d + 1
      · subst hmeq
        simp only [↓reduceIte]
        have hlat_eq : stNew.later.val g2 x =
            (backStep j (valAt g1 x (pW (j + 1))) (valAt g1 x (bW (j + 1))) ((arr d).val g1 x)).later :=
          congrArg BackState.later hstep_v
        have hrr_eq : wordVal g2 x stNew.remR =
            (backStep j (valAt g1 x (pW (j + 1))) (valAt g1 x (bW (j + 1))) ((arr d).val g1 x)).remR :=
          congrArg BackState.remR hstep_v
        have hrb_eq : wordVal g2 x stNew.remB =
            (backStep j (valAt g1 x (pW (j + 1))) (valAt g1 x (bW (j + 1))) ((arr d).val g1 x)).remB :=
          congrArg BackState.remB hstep_v
        refine ⟨h2.2.2.2.1, ?_, ?_, ?_⟩
        · conv_rhs => unfold backScanList
          simp only [hd0, ↓reduceIte]
          rw [hstep_v, valAt_ext hx.hlen he1 (hpW (j + 1) hj1),
            valAt_ext hx.hlen he1 (hbW (j + 1) hj1), hvalD]
        · rw [hlat_eq, hrr_eq, hrb_eq]
          dsimp only [backStep, BackStateW.val]
          by_cases hpn : valAt g1 x (pW (j + 1)) = true
          · simp only [hpn, ↓reduceIte]
            rcases hcomb_cap with ⟨_, _, _, _, _, _, _, _, _, _⟩
            unfold Sum8.Cap; split_ifs <;> ((try dsimp only); omega)
          · simp only [if_neg hpn]
            rcases hcapD with ⟨_, _, _, _, _, _, _, _, _, _⟩
            unfold Sum8.Cap; split_ifs <;> ((try dsimp only); omega)
        · rw [hrr_eq, hrb_eq]; dsimp only [backStep, BackStateW.val]; split_ifs <;> ((try dsimp only); omega)
      · simp only [hmeq, ↓reduceIte]
        rcases harr1 m (by omega) with ⟨hinM, hvalM, hcapM, hleM⟩
        refine ⟨BackStateW.in_mono (gExt_nin_le h2.1) hinM, ?_, ?_, ?_⟩
        · rw [BackStateW.val_ext hx.hlen h2.1 hinM, hvalM]
        · rw [Sum8W.val_ext hx.hlen h2.1 hinM.2.2.2, wordVal_ext hx.hlen h2.1 hinM.2.1,
            wordVal_ext hx.hlen h2.1 hinM.2.2.1]; exact hcapM
        · rw [wordVal_ext hx.hlen h2.1 hinM.2.1, wordVal_ext hx.hlen h2.1 hinM.2.2.1]; exact hleM

private structure WalkStateW (W : ℕ) where
  curX : ℕ
  remR : Word W
  remB : Word W

private def WalkStateW.In (bound : ℕ) {W : ℕ} (st : WalkStateW W) : Prop :=
  st.curX < bound ∧ WordIn bound st.remR ∧ WordIn bound st.remB

private def WalkStateW.val {W : ℕ} (g : List Gate) (x : List Bool) (st : WalkStateW W) : WalkState :=
  ⟨valAt g x st.curX, wordVal g x st.remR, wordVal g x st.remB⟩

private def cWalkStep (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (k e : ℕ)
    (pNext bNext : ℕ) (a0W : ℕ) (stBackNext : BackStateW W) (st : WalkStateW W) :
    List Gate × WalkStateW W :=
  let (g1, eqB) := cEqBit nin g st.curX (if decide (e + 1 = 2 * k) then a0W else bNext)
  let (g2, xr) := cXor nin g1 st.curX stBackNext.nxtBit
  let (g3, seg) := cOfSeg nin hW g2 stBackNext.remR stBackNext.remB xr
  let (g4, tsum) := cCombSum8 nin g3 seg stBackNext.later
  let (g5, mem0) := cMemSum8 nin hW g4 tsum st.remR st.remB
  let (g6, take0) := cMux nin g5 (if decide (e + 1 = 2 * k) then 1 else pNext) eqB mem0
  let (g7, ncurX) := emitNot nin g6 st.curX
  let (g8, newX) := cMux nin g7 take0 st.curX ncurX
  let (g9, subR) := cSubTruncW nin g8 st.remR (if e % 2 = 0 then cConstBit W 1 else cConst0 W)
  let (g10, subB) := cSubTruncW nin g9 st.remB (if e % 2 = 0 then cConst0 W else cConstBit W 1)
  let (g11, newR) := cMuxW nin g10 take0 st.remR subR
  let (g12, newB) := cMuxW nin g11 take0 st.remB subB
  (g12, ⟨newX, newR, newB⟩)

private lemma cWalkStep_full_spec {nin W : ℕ} (hW : 1 ≤ W) (hW3 : 3 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) (k e : ℕ)
    (pins bits : ℕ → Bool) (a0 : Bool) (laterCyc : Sum8)
    {pNext bNext a0W : ℕ} {stBackNext : BackStateW W} {st : WalkStateW W}
    (hp : pNext < nin + g.length) (hb : bNext < nin + g.length) (ha0 : a0W < nin + g.length)
    (hbk : stBackNext.In (nin + g.length)) (hst : st.In (nin + g.length))
    (hpv : valAt g x pNext = pins (e + 1)) (hbv : valAt g x bNext = bits (e + 1))
    (ha0v : valAt g x a0W = a0)
    (hbk_v : stBackNext.val g x = backAt k pins bits a0 laterCyc (e + 1))
    (hno : wordVal g x stBackNext.remR + wordVal g x stBackNext.remB < 2 ^ W ∧
      ((Sum8.ofSeg (wordVal g x stBackNext.remR) (wordVal g x stBackNext.remB)
        (xor (valAt g x st.curX) (valAt g x stBackNext.nxtBit))).comb
        (stBackNext.later.val g x)).Bound (2 ^ (W - 2) - 1) ∧
      wordVal g x st.remR < 2 ^ (W - 2) ∧ wordVal g x st.remB < 2 ^ (W - 2)) :
    let res := cWalkStep nin hW g k e pNext bNext a0W stBackNext st
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + 550 * W ∧
    res.2.In (nin + res.1.length) ∧
    res.2.val res.1 x = walkStep k pins bits a0 laterCyc e (st.val g x) := by
  have hnin := hx.hnin
  have hpow_le : 2 ^ (W - 2) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) (by omega)
  rcases hbk with ⟨hnx, hrr, hrb, hlat⟩
  rcases hst with ⟨hcx, hsr, hsb⟩
  unfold cWalkStep
  let isLast := decide (e + 1 = 2 * k)
  let pEff := if isLast then 1 else pNext
  let bEff := if isLast then a0W else bNext
  have hpEff : pEff < nin + g.length := by dsimp [pEff]; split_ifs <;> omega
  have hbEff : bEff < nin + g.length := by dsimp [bEff]; split_ifs <;> omega
  have h1 := cEqBit_spec hx hv hcx hbEff
  dsimp only [bEff, isLast] at h1
  generalize cEqBit nin g st.curX (if decide (e + 1 = 2 * k) then a0W else bNext) = _r1 at h1 ⊢; rcases _r1 with ⟨g1, eqB⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have h2 := cXor_spec (a := st.curX) (b := stBackNext.nxtBit) hx h1.2.1 (by omega) (by omega)
  generalize cXor nin g1 st.curX stBackNext.nxtBit = _r2 at h2 ⊢; rcases _r2 with ⟨g2, xr⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have he12 := gExt_trans h1.1 h2.1
  have h3 := cOfSeg_spec (p := xr) hW hx h2.2.1 (wordIn_mono (by omega) hrr) (wordIn_mono (by omega) hrb) h2.2.2.2.1
    (by rw [wordVal_ext hx.hlen he12 hrr, wordVal_ext hx.hlen he12 hrb]; exact hno.1)
  generalize cOfSeg nin hW g2 stBackNext.remR stBackNext.remB xr = _r3 at h3 ⊢; rcases _r3 with ⟨g3, seg⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have _hl_h3 := gExt_len_le h3.1
  have he13 := gExt_trans he12 h3.1
  have hseg_v : seg.val g3 x = Sum8.ofSeg (wordVal g x stBackNext.remR) (wordVal g x stBackNext.remB)
      (xor (valAt g x st.curX) (valAt g x stBackNext.nxtBit)) := by
    rw [h3.2.2.2.2, wordVal_ext hx.hlen he12 hrr, wordVal_ext hx.hlen he12 hrb, h2.2.2.2.2,
      valAt_ext hx.hlen h1.1 hcx, valAt_ext hx.hlen h1.1 hnx]
  have h4 := cCombSum8_spec hx h3.2.1 h3.2.2.2.1 (Sum8W.in_mono (by omega) hlat)
    (by rw [hseg_v, Sum8W.val_ext hx.hlen he13 hlat]; exact Sum8.bound_mono hno.2.1 (by omega))
  generalize cCombSum8 nin g3 seg stBackNext.later = _r4 at h4 ⊢; rcases _r4 with ⟨g4, tsum⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have he14 := gExt_trans he13 h4.1
  have htsum_v : tsum.val g4 x = tailSum k pins bits a0 laterCyc (e + 1) (valAt g x st.curX) := by
    rw [h4.2.2.2.2, hseg_v, Sum8W.val_ext hx.hlen he13 hlat]
    unfold tailSum; rw [← hbk_v]; rfl
  have h5 := cMemSum8_spec hW hx h4.2.1 h4.2.2.2.1 (wordIn_mono (by omega) hsr) (wordIn_mono (by omega) hsb)
    ⟨by rw [h4.2.2.2.2, hseg_v, Sum8W.val_ext hx.hlen he13 hlat]; exact hno.2.1,
     by rw [wordVal_ext hx.hlen he14 hsr]; exact hno.2.2.1,
     by rw [wordVal_ext hx.hlen he14 hsb]; exact hno.2.2.2⟩ hW3
  generalize cMemSum8 nin hW g4 tsum st.remR st.remB = _r5 at h5 ⊢; rcases _r5 with ⟨g5, mem0⟩; dsimp only at h5; dsimp (config := { zeta := false }) only at ⊢
  have _hl_h5 := gExt_len_le h5.1
  have he15 := gExt_trans he14 h5.1
  have h6 := cMux_spec (sel := (if decide (e + 1 = 2 * k) then 1 else pNext)) (t := eqB) (f := mem0) hx h5.2.1 (by split_ifs <;> omega) (by omega) h5.2.2.2.1
  dsimp only [pEff, isLast] at h6
  generalize cMux nin g5 (if decide (e + 1 = 2 * k) then 1 else pNext) eqB mem0 = _r6 at h6 ⊢; rcases _r6 with ⟨g6, take0⟩; dsimp only at h6; dsimp (config := { zeta := false }) only at ⊢
  have he16 := gExt_trans he15 h6.1
  have h7 := emitNot_spec (a := st.curX) hx h6.2.1 (by omega)
  generalize emitNot nin g6 st.curX = _r7 at h7 ⊢; rcases _r7 with ⟨g7, ncurX⟩; dsimp only at h7; dsimp (config := { zeta := false }) only at ⊢
  have he17 := gExt_trans he16 h7.1
  have h8 := cMux_spec (sel := take0) (t := st.curX) (f := ncurX) hx h7.2.1 (by omega) (by omega) h7.2.2.2.1
  generalize cMux nin g7 take0 st.curX ncurX = _r8 at h8 ⊢; rcases _r8 with ⟨g8, newX⟩; dsimp only at h8; dsimp (config := { zeta := false }) only at ⊢
  have he18 := gExt_trans he17 h8.1
  let erW := if e % 2 = 0 then cConstBit W 1 else cConst0 W
  let ebW := if e % 2 = 0 then cConst0 W else cConstBit W 1
  have her_spec : ∀ g' : List Gate, WordIn (nin + g'.length) erW ∧
      wordVal g' x erW = if e % 2 = 0 then 1 else 0 := fun g' => by
    dsimp only [erW]; split_ifs
    · have h := cConstBit_spec hW (g := g') hx (b := 1) (by omega)
      exact ⟨h.1, by rw [h.2, valAt_one hx]; rfl⟩
    · exact cConst0_spec (W := W) (g := g') hx
  have heb_spec : ∀ g' : List Gate, WordIn (nin + g'.length) ebW ∧
      wordVal g' x ebW = if e % 2 = 0 then 0 else 1 := fun g' => by
    dsimp only [ebW]; split_ifs
    · exact cConst0_spec (W := W) (g := g') hx
    · have h := cConstBit_spec hW (g := g') hx (b := 1) (by omega)
      exact ⟨h.1, by rw [h.2, valAt_one hx]; rfl⟩
  have h9 := cSubTruncW_spec hx h8.2.1 (wordIn_mono (by omega) hsr) (her_spec g8).1
  dsimp only [erW] at h9
  generalize cSubTruncW nin g8 st.remR (if e % 2 = 0 then cConstBit W 1 else cConst0 W) = _r9 at h9 ⊢; rcases _r9 with ⟨g9, subR⟩; dsimp only at h9; dsimp (config := { zeta := false }) only at ⊢
  have he19 := gExt_trans he18 h9.1
  have h10 := cSubTruncW_spec hx h9.2.1 (wordIn_mono (by omega) hsb) (heb_spec g9).1
  dsimp only [ebW] at h10
  generalize cSubTruncW nin g9 st.remB (if e % 2 = 0 then cConst0 W else cConstBit W 1) = _r10 at h10 ⊢; rcases _r10 with ⟨g10, subB⟩; dsimp only at h10; dsimp (config := { zeta := false }) only at ⊢
  have he110 := gExt_trans he19 h10.1
  have h11 := cMuxW_spec (sel := take0) hx h10.2.1 (by omega) (wordIn_mono (by omega) hsr) (wordIn_mono (by omega) h9.2.2.2.1)
  generalize cMuxW nin g10 take0 st.remR subR = _r11 at h11 ⊢; rcases _r11 with ⟨g11, newR⟩; dsimp only at h11; dsimp (config := { zeta := false }) only at ⊢
  have he111 := gExt_trans he110 h11.1
  have h12 := cMuxW_spec (sel := take0) hx h11.2.1 (by omega) (wordIn_mono (by omega) hsb) (wordIn_mono (by omega) h10.2.2.2.1)
  dsimp only at h12
  have _hl_h12 := gExt_len_le h12.1
  have he112 := gExt_trans he111 h12.1
  have htake0_v : valAt g6 x take0 =
      (if (isLast || pins (e + 1)) then (valAt g x st.curX == (if isLast then a0 else bits (e + 1)))
       else decide ((tailSum k pins bits a0 laterCyc (e + 1) (valAt g x st.curX)).Mem
         (wordVal g x st.remR) (wordVal g x st.remB))) := by
    rw [h6.2.2.2.2, valAt_ext hx.hlen he15 hpEff,
      valAt_ext hx.hlen (gExt_trans h2.1 (gExt_trans h3.1 (gExt_trans h4.1 h5.1))) h1.2.2.2.1, h1.2.2.2.2]
    have hmem_b : valAt g5 x mem0 = decide ((tailSum k pins bits a0 laterCyc (e + 1) (valAt g x st.curX)).Mem
        (wordVal g x st.remR) (wordVal g x st.remB)) := by
      have hiff := h5.2.2.2.2
      rw [htsum_v, wordVal_ext hx.hlen he14 hsr, wordVal_ext hx.hlen he14 hsb] at hiff
      cases hv5 : valAt g5 x mem0 <;> simp [hv5] at hiff ⊢
      · exact hiff
      · exact hiff
    rw [hmem_b]
    dsimp only [pEff, bEff, isLast]
    by_cases hlast : e + 1 = 2 * k
    · simp [hlast, valAt_one hx, ha0v]
    · simp [hlast, hpv, hbv]
  have e8_12 := gExt_trans h9.1 (gExt_trans h10.1 (gExt_trans h11.1 h12.1))
  have e6_10 := gExt_trans h7.1 (gExt_trans h8.1 (gExt_trans h9.1 h10.1))
  have e6_11 := gExt_trans e6_10 h11.1
  dsimp only
  refine ⟨he112, h12.2.1,
    by linarith only [hW, h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1, h6.2.2.1,
      h7.2.2.1, h8.2.2.1, h9.2.2.1, h10.2.2.1, h11.2.2.1, h12.2.2.1],
    ⟨wire_ext e8_12 h8.2.2.2.1, wordIn_ext h12.1 h11.2.2.2.1, h12.2.2.2.1⟩, ?_⟩
  unfold WalkStateW.val walkStep
  rw [valAt_ext hx.hlen e8_12 h8.2.2.2.1, h8.2.2.2.2, valAt_ext hx.hlen h7.1 h6.2.2.2.1,
      valAt_ext hx.hlen he17 hcx, h7.2.2.2.2, valAt_ext hx.hlen he16 hcx,
      wordVal_ext hx.hlen h12.1 h11.2.2.2.1, h11.2.2.2.2, valAt_ext hx.hlen e6_10 h6.2.2.2.1,
      wordVal_ext hx.hlen he110 hsr, wordVal_ext hx.hlen h10.1 h9.2.2.2.1, h9.2.2.2.2,
      wordVal_ext hx.hlen he18 hsr, (her_spec g8).2,
      h12.2.2.2.2, valAt_ext hx.hlen e6_11 h6.2.2.2.1, wordVal_ext hx.hlen he111 hsb,
      wordVal_ext hx.hlen h11.1 h10.2.2.2.1, h10.2.2.2.2, wordVal_ext hx.hlen he19 hsb, (heb_spec g9).2, htake0_v]
  dsimp only [isLast]
  cases h : (if (decide (e + 1 = 2 * k) || pins (e + 1)) then (valAt g x st.curX == (if decide (e + 1 = 2 * k) then a0 else bits (e + 1)))
      else decide ((tailSum k pins bits a0 laterCyc (e + 1) (valAt g x st.curX)).Mem
        (wordVal g x st.remR) (wordVal g x st.remB))) <;> rfl

private def cWalkLoop (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (k : ℕ)
    (pW bW : ℕ → ℕ) (a0W : ℕ) (backArr : ℕ → BackStateW W) (remR0 remB0 : Word W) :
    ℕ → List Gate × WalkStateW W × (ℕ → ℕ)
  | 0 => (g, ⟨a0W, remR0, remB0⟩, fun _ => a0W)
  | j + 1 =>
    let (g1, st, xW) := cWalkLoop nin hW g k pW bW a0W backArr remR0 remB0 j
    let (g2, st') := cWalkStep nin hW g1 k j (pW (j + 1)) (bW (j + 1)) a0W (backArr (2 * k - (j + 1))) st
    (g2, st', fun t => if t = j + 1 then st'.curX else xW t)

private lemma cWalkLoop_spec {nin W : ℕ} (hW : 1 ≤ W) (hW3 : 3 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {k : ℕ} (hk : 1 ≤ k)
    (pins bits : ℕ → Bool) (a0 : Bool) {laterCyc : Sum8} (hlat : laterCyc.Good) {nLat : ℕ}
    {pW bW : ℕ → ℕ} {a0W : ℕ} {backArr : ℕ → BackStateW W} {remR0 remB0 : Word W}
    (hpW : ∀ j, pW j < nin + g.length) (hbW : ∀ j, bW j < nin + g.length)
    (hpv : ∀ j, valAt g x (pW j) = pins j) (hbv : ∀ j, valAt g x (bW j) = bits j)
    (ha0 : a0W < nin + g.length) (ha0v : valAt g x a0W = a0)
    (hrr0 : WordIn (nin + g.length) remR0) (hrb0 : WordIn (nin + g.length) remB0)
    (hback_in : ∀ m ≤ 2 * k, (backArr m).In (nin + g.length))
    (hback_v : ∀ m ≤ 2 * k, (backArr m).val g x = backScanList k pins bits a0 laterCyc m)
    (hback_cap : ∀ m ≤ 2 * k,
      ((backArr m).later.val g x).Cap (nLat + m / 2 - wordVal g x (backArr m).remR)
        (nLat + (m + 1) / 2 - wordVal g x (backArr m).remB) ∧
      wordVal g x (backArr m).remR + wordVal g x (backArr m).remB ≤ m)
    (hlim : 2 * k + nLat + 2 < 2 ^ (W - 2))
    (hrem_lim : wordVal g x remR0 < 2 ^ (W - 2) ∧ wordVal g x remB0 < 2 ^ (W - 2)) :
    ∀ j ≤ 2 * k,
      let res := cWalkLoop nin hW g k pW bW a0W backArr remR0 remB0 j
      GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + j * (550 * W) ∧
      res.2.1.In (nin + res.1.length) ∧
      res.2.1.val res.1 x = walkLoop k pins bits a0 laterCyc (wordVal g x remR0) (wordVal g x remB0) j ∧
      wordVal res.1 x res.2.1.remR ≤ wordVal g x remR0 ∧
      wordVal res.1 x res.2.1.remB ≤ wordVal g x remB0 ∧
      (∀ t ≤ j, res.2.2 t < nin + res.1.length ∧
        valAt res.1 x (res.2.2 t) = (walkLoop k pins bits a0 laterCyc (wordVal g x remR0) (wordVal g x remB0) t).curX) := by
  have hnin := hx.hnin
  have hpow_le : 2 ^ (W - 2) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) (by omega)
  intro j
  induction j with
  | zero =>
    intro _
    dsimp only [cWalkLoop]
    refine ⟨gExt_refl g, hv, by simp, ⟨ha0, hrr0, hrb0⟩, ?_, le_rfl, le_rfl, fun t ht => ?_⟩
    · unfold WalkStateW.val walkLoop; simp [ha0v]
    · have ht0 : t = 0 := by omega
      subst ht0; exact ⟨ha0, ha0v⟩
  | succ j ih =>
    intro hj
    rcases ih (by omega) with ⟨he1, hv1, hlen1, hin1, hval1, hrl1, hbl1, hxw1⟩
    dsimp only [cWalkLoop]
    set g1 := (cWalkLoop nin hW g k pW bW a0W backArr remR0 remB0 j).1
    set st1 := (cWalkLoop nin hW g k pW bW a0W backArr remR0 remB0 j).2.1
    set xW1 := (cWalkLoop nin hW g k pW bW a0W backArr remR0 remB0 j).2.2
    have hlen_le : g.length ≤ g1.length := gExt_len_le he1
    set m := 2 * k - (j + 1)
    have hm_le : m ≤ 2 * k := by omega
    have hbk_in1 : (backArr m).In (nin + g1.length) := BackStateW.in_mono (by omega) (hback_in m hm_le)
    have hbk_v1 : (backArr m).val g1 x = backAt k pins bits a0 laterCyc (j + 1) := by
      rw [BackStateW.val_ext hx.hlen he1 (hback_in m hm_le), hback_v m hm_le]; rfl
    have hcapM := hback_cap m hm_le
    have hseg_cap : (Sum8.ofSeg (wordVal g1 x (backArr m).remR) (wordVal g1 x (backArr m).remB)
        (xor (valAt g1 x st1.curX) (valAt g1 x (backArr m).nxtBit))).Cap
        (wordVal g1 x (backArr m).remR) (wordVal g1 x (backArr m).remB) := by
      apply Sum8.cap_ofSeg
      by_cases hm0 : m = 0
      · have : wordVal g1 x (backArr m).remR + wordVal g1 x (backArr m).remB ≤ 0 := by
          rw [wordVal_ext hx.hlen he1 (hback_in m hm_le).2.1, wordVal_ext hx.hlen he1 (hback_in m hm_le).2.2.1]; omega
        omega
      · have halt := backAt_rem_alt hk pins bits a0 laterCyc hlat m (by omega) hm_le
        dsimp only at halt
        have hba : backAt k pins bits a0 laterCyc (2 * k - m) = (backArr m).val g1 x := by
          rw [show 2 * k - m = j + 1 by omega]; exact hbk_v1.symm
        rw [hba] at halt
        rcases halt with ⟨_, _, hev, hod, _⟩
        by_cases hpar : (2 * k - m) % 2 = 0
        · have := hev hpar; dsimp [BackStateW.val] at this; omega
        · have := hod (by omega); dsimp [BackStateW.val] at this; omega
    have hlat_cap1 : ((backArr m).later.val g1 x).Cap
        (nLat + m / 2 - wordVal g1 x (backArr m).remR)
        (nLat + (m + 1) / 2 - wordVal g1 x (backArr m).remB) := by
      rw [Sum8W.val_ext hx.hlen he1 (hback_in m hm_le).2.2.2,
          wordVal_ext hx.hlen he1 (hback_in m hm_le).2.1,
          wordVal_ext hx.hlen he1 (hback_in m hm_le).2.2.1]
      exact hcapM.1
    have hcomb_cap := Sum8.cap_comb hseg_cap hlat_cap1
    have hno : wordVal g1 x (backArr m).remR + wordVal g1 x (backArr m).remB < 2 ^ W ∧
        ((Sum8.ofSeg (wordVal g1 x (backArr m).remR) (wordVal g1 x (backArr m).remB)
          (xor (valAt g1 x st1.curX) (valAt g1 x (backArr m).nxtBit))).comb
          ((backArr m).later.val g1 x)).Bound (2 ^ (W - 2) - 1) ∧
        wordVal g1 x st1.remR < 2 ^ (W - 2) ∧ wordVal g1 x st1.remB < 2 ^ (W - 2) := by
      have hrm : wordVal g1 x (backArr m).remR + wordVal g1 x (backArr m).remB ≤ m := by
        rw [wordVal_ext hx.hlen he1 (hback_in m hm_le).2.1, wordVal_ext hx.hlen he1 (hback_in m hm_le).2.2.1]
        exact hcapM.2
      refine ⟨by omega, Sum8.cap_bound hcomb_cap (by omega) (by omega), by omega, by omega⟩
    have h2 := cWalkStep_full_spec hW hW3 hx hv1 k j pins bits a0 laterCyc
      (pNext := pW (j + 1)) (bNext := bW (j + 1)) (a0W := a0W)
      (by have := hpW (j + 1); omega) (by have := hbW (j + 1); omega) (by omega)
      hbk_in1 hin1
      (by rw [valAt_ext hx.hlen he1 (hpW (j + 1)), hpv])
      (by rw [valAt_ext hx.hlen he1 (hbW (j + 1)), hbv])
      (by rw [valAt_ext hx.hlen he1 ha0, ha0v]) hbk_v1 hno
    generalize cWalkStep nin hW g1 k j (pW (j + 1)) (bW (j + 1)) a0W (backArr m) st1 = _r2 at h2 ⊢; rcases _r2 with ⟨g2, st2⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
    have hlen12 : g1.length ≤ g2.length := gExt_len_le h2.1
    have hstep_v := h2.2.2.2.2
    have hrr2_le : wordVal g2 x st2.remR ≤ wordVal g1 x st1.remR := by
      have h := congrArg WalkState.remR hstep_v
      dsimp only [WalkStateW.val, walkStep] at h
      rw [h]; rw [apply_ite WalkState.remR]; split_ifs <;> (dsimp only; omega)
    have hrb2_le : wordVal g2 x st2.remB ≤ wordVal g1 x st1.remB := by
      have h := congrArg WalkState.remB hstep_v
      dsimp only [WalkStateW.val, walkStep] at h
      rw [h]; rw [apply_ite WalkState.remB]; split_ifs <;> (dsimp only; omega)
    refine ⟨gExt_trans he1 h2.1, h2.2.1, by nlinarith [h2.2.2.1], h2.2.2.2.1, ?_,
      le_trans hrr2_le hrl1, le_trans hrb2_le hbl1, fun t ht => ?_⟩
    · rw [hstep_v, hval1]; rfl
    · by_cases hteq : t = j + 1
      · subst hteq
        simp only [↓reduceIte]
        refine ⟨h2.2.2.2.1.1, ?_⟩
        have h := congrArg WalkState.curX hstep_v
        rw [hval1] at h; exact h
      · simp only [hteq, ↓reduceIte]
        rcases hxw1 t (by omega) with ⟨ht_in, ht_v⟩
        exact ⟨by omega, by rw [valAt_ext hx.hlen h2.1 ht_in, ht_v]⟩

private def cPickA0Bit (nin : ℕ) (g : List Gate) (p0 b0 mem0 : ℕ) : List Gate × ℕ :=
  let (g1, np0) := emitNot nin g p0
  let (g2, nb0) := emitNot nin g1 b0
  let (g3, ok0) := emitOr nin g2 np0 nb0
  let (g4, can0) := emitAnd nin g3 ok0 mem0
  emitNot nin g4 can0

private lemma cPickA0Bit_spec {nin : ℕ} {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {p0 b0 mem0 : ℕ}
    (hp0 : p0 < nin + g.length) (hb0 : b0 < nin + g.length) (hmem : mem0 < nin + g.length) :
    let res := cPickA0Bit nin g p0 b0 mem0
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length = g.length + 5 ∧
    res.2 < nin + res.1.length ∧
    valAt res.1 x res.2 = !((!(valAt g x p0) || !(valAt g x b0)) && valAt g x mem0) := by
  unfold cPickA0Bit
  have h1 := emitNot_spec hx hv hp0
  generalize emitNot nin g p0 = _r1 at h1 ⊢; rcases _r1 with ⟨g1, np0⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  have h2 := emitNot_spec hx h1.2.1 (wire_ext h1.1 hb0)
  generalize emitNot nin g1 b0 = _r2 at h2 ⊢; rcases _r2 with ⟨g2, nb0⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have he12 := gExt_trans h1.1 h2.1
  have h3 := emitOr_spec (a := np0) (b := nb0) hx h2.2.1 (wire_ext h2.1 h1.2.2.2.1) h2.2.2.2.1
  generalize emitOr nin g2 np0 nb0 = _r3 at h3 ⊢; rcases _r3 with ⟨g3, ok0⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he13 := gExt_trans he12 h3.1
  have h4 := emitAnd_spec (a := ok0) (b := mem0) hx h3.2.1 h3.2.2.2.1 (wire_ext he13 hmem)
  generalize emitAnd nin g3 ok0 mem0 = _r4 at h4 ⊢; rcases _r4 with ⟨g4, can0⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have h5 := emitNot_spec hx h4.2.1 h4.2.2.2.1
  generalize emitNot nin g4 can0 = _r5 at h5 ⊢; rcases _r5 with ⟨g5, a0W⟩; dsimp only at h5 ⊢
  refine ⟨gExt_trans he13 (gExt_trans h4.1 h5.1), h5.2.1,
    by linarith only [h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1],
    h5.2.2.2.1, ?_⟩
  rw [h5.2.2.2.2, h4.2.2.2.2, h3.2.2.2.2, valAt_ext hx.hlen h2.1 h1.2.2.2.1,
    h1.2.2.2.2, h2.2.2.2.2, valAt_ext hx.hlen h1.1 hb0, valAt_ext hx.hlen he13 hmem]

private def cCyclePickA0 (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (k : ℕ)
    (pW bW : ℕ → ℕ) (laterCyc : Sum8W W) (remR0 remB0 : Word W) : List Gate × ℕ :=
  let (g1, arr0) := cBackScan nin hW g k pW bW 0 laterCyc (2 * k)
  let (g2, seg0) := cOfSeg nin hW g1 (arr0 (2 * k)).remR (arr0 (2 * k)).remB (arr0 (2 * k)).nxtBit
  let (g3, ts0) := cCombSum8 nin g2 seg0 (arr0 (2 * k)).later
  let (g4, mem0) := cMemSum8 nin hW g3 ts0 remR0 remB0
  cPickA0Bit nin g4 (pW 0) (bW 0) mem0

private lemma cCyclePickA0_spec {nin W : ℕ} (hW : 1 ≤ W) (hW3 : 3 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {k : ℕ} (hk : 1 ≤ k)
    (pins bits : ℕ → Bool) {laterCyc : Sum8W W} {nLat : ℕ}
    {pW bW : ℕ → ℕ} {remR0 remB0 : Word W}
    (hpW : ∀ j, pW j < nin + g.length) (hbW : ∀ j, bW j < nin + g.length)
    (hpv : ∀ j, valAt g x (pW j) = pins j) (hbv : ∀ j, valAt g x (bW j) = bits j)
    (hlatIn : laterCyc.In (nin + g.length))
    (hlatG : (laterCyc.val g x).Good) (hlatCap : (laterCyc.val g x).Cap nLat nLat)
    (hrr0 : WordIn (nin + g.length) remR0) (hrb0 : WordIn (nin + g.length) remB0)
    (hlim : 2 * k + nLat + 2 < 2 ^ (W - 2))
    (hrem_lim : wordVal g x remR0 < 2 ^ (W - 2) ∧ wordVal g x remB0 < 2 ^ (W - 2))
    (hmem_in : ((pureCycleSum k pins bits).comb (laterCyc.val g x)).Mem (wordVal g x remR0) (wordVal g x remB0)) :
    let res := cCyclePickA0 nin hW g k pW bW laterCyc remR0 remB0
    let a0 := valAt res.1 x res.2
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + (2 * k) * (360 * W) + 500 * W ∧
    res.2 < nin + res.1.length ∧
    (pins 0 = true → a0 = bits 0) ∧
    (tailSum k pins bits a0 (laterCyc.val g x) 0 a0).Mem (wordVal g x remR0) (wordVal g x remB0) := by
  have hnin := hx.hnin
  have hpow_le : 2 ^ (W - 2) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) (by omega)
  unfold cCyclePickA0
  have h1 := cBackScan_spec hW hx hv hk (a0W := 0) (fun j _ => hpW j) (fun j _ => hbW j)
    (by omega) hlatIn hlatG hlatCap (by omega) (2 * k) le_rfl
  generalize cBackScan nin hW g k pW bW 0 laterCyc (2 * k) = _r1 at h1 ⊢
  rcases _r1 with ⟨g1, arr0⟩; dsimp only at h1; dsimp (config := { zeta := false }) only at ⊢
  rcases h1 with ⟨he1, hv1, hlen1, harr0⟩
  rcases harr0 (2 * k) le_rfl with ⟨hst0_in, hst0_v, hst0_cap, hst0_le⟩
  have hst0_val : (arr0 (2 * k)).val g1 x = backAt k pins bits false (laterCyc.val g x) 0 := by
    rw [hst0_v]; unfold backAt; simp [valAt_zero hx, hpv, hbv]
  have halt0 := backAt_rem_alt hk pins bits false (laterCyc.val g x) hlatG (2 * k) (by omega) le_rfl
  dsimp only at halt0
  rw [Nat.sub_self, ← hst0_val] at halt0
  have hseg0_alt : wordVal g1 x (arr0 (2 * k)).remR + wordVal g1 x (arr0 (2 * k)).remB ≤ 1 ∨
      (1 ≤ wordVal g1 x (arr0 (2 * k)).remR ∧ 1 ≤ wordVal g1 x (arr0 (2 * k)).remB) := by
    have := halt0.2.2.1 rfl; dsimp [BackStateW.val] at this; omega
  have hseg0_cap := Sum8.cap_ofSeg (wordVal g1 x (arr0 (2 * k)).remR) (wordVal g1 x (arr0 (2 * k)).remB)
    (valAt g1 x (arr0 (2 * k)).nxtBit) hseg0_alt
  have hcomb0_cap := Sum8.cap_comb hseg0_cap hst0_cap
  have h2 := cOfSeg_spec (p := (arr0 (2 * k)).nxtBit) hW hx hv1 hst0_in.2.1 hst0_in.2.2.1 hst0_in.1 (by omega)
  generalize cOfSeg nin hW g1 (arr0 (2 * k)).remR (arr0 (2 * k)).remB (arr0 (2 * k)).nxtBit = _r2 at h2 ⊢
  rcases _r2 with ⟨g2, seg0⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
  have he12 := gExt_trans he1 h2.1
  have h3 := cCombSum8_spec hx h2.2.1 h2.2.2.2.1 (sum8_in_ext h2.1 hst0_in.2.2.2)
    (by rw [h2.2.2.2.2, Sum8W.val_ext hx.hlen h2.1 hst0_in.2.2.2]
        exact Sum8.cap_bound hcomb0_cap (by omega) (by omega))
  generalize cCombSum8 nin g2 seg0 (arr0 (2 * k)).later = _r3 at h3 ⊢
  rcases _r3 with ⟨g3, ts0⟩; dsimp only at h3; dsimp (config := { zeta := false }) only at ⊢
  have he13 := gExt_trans he12 h3.1
  have hts0_v : ts0.val g3 x = tailSum k pins bits false (laterCyc.val g x) 0 false := by
    rw [h3.2.2.2.2, h2.2.2.2.2, Sum8W.val_ext hx.hlen h2.1 hst0_in.2.2.2]
    unfold tailSum; rw [← hst0_val]; simp [BackStateW.val]
  have h4 := cMemSum8_spec hW hx h3.2.1 h3.2.2.2.1 (wordIn_ext he13 hrr0) (wordIn_ext he13 hrb0)
    ⟨by rw [h3.2.2.2.2, h2.2.2.2.2, Sum8W.val_ext hx.hlen h2.1 hst0_in.2.2.2]
        exact Sum8.cap_bound hcomb0_cap (by omega) (by omega),
     by rw [wordVal_ext hx.hlen he13 hrr0]; exact hrem_lim.1,
     by rw [wordVal_ext hx.hlen he13 hrb0]; exact hrem_lim.2⟩ hW3
  generalize cMemSum8 nin hW g3 ts0 remR0 remB0 = _r4 at h4 ⊢
  rcases _r4 with ⟨g4, mem0⟩; dsimp only at h4; dsimp (config := { zeta := false }) only at ⊢
  have he14 := gExt_trans he13 h4.1
  have h5 := cPickA0Bit_spec hx h4.2.1 (wire_ext he14 (hpW 0)) (wire_ext he14 (hbW 0)) h4.2.2.2.1
  generalize cPickA0Bit nin g4 (pW 0) (bW 0) mem0 = _r5 at h5 ⊢
  rcases _r5 with ⟨g5, a0W⟩; dsimp only at h5 ⊢
  have ha0_eq : valAt g5 x a0W = !((!(pins 0) || !(bits 0)) && valAt g4 x mem0) := by
    rw [h5.2.2.2.2, valAt_ext hx.hlen he14 (hpW 0), hpv 0, valAt_ext hx.hlen he14 (hbW 0), hbv 0]
  have hmem0_iff : valAt g4 x mem0 = true ↔
      (tailSum k pins bits false (laterCyc.val g x) 0 false).Mem (wordVal g x remR0) (wordVal g x remB0) := by
    have h4iff := h4.2.2.2.2
    rw [hts0_v, wordVal_ext hx.hlen he13 hrr0, wordVal_ext hx.hlen he13 hrb0] at h4iff
    exact h4iff
  have hcan0_iff : ((!(pins 0) || !(bits 0)) && valAt g4 x mem0) = true ↔
      (pins 0 = false ∨ bits 0 = false) ∧
      (tailSum k pins bits false (laterCyc.val g x) 0 false).Mem (wordVal g x remR0) (wordVal g x remB0) := by
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', hmem0_iff]
  have ha0_props : (pins 0 = true → valAt g5 x a0W = bits 0) ∧
      (tailSum k pins bits (valAt g5 x a0W) (laterCyc.val g x) 0 (valAt g5 x a0W)).Mem (wordVal g x remR0) (wordVal g x remB0) := by
    have hsplit := pureCycleSum_split_a0 hk pins bits hlatG hmem_in
    cases hc0 : ((!(pins 0) || !(bits 0)) && valAt g4 x mem0)
    · have ha0t : valAt g5 x a0W = true := by rw [ha0_eq, hc0]; rfl
      rw [ha0t]
      rcases hsplit with h0 | h1
      · exfalso
        have := hcan0_iff.mpr h0; rw [hc0] at this; exact Bool.false_ne_true this
      · refine ⟨fun hp0 => ?_, h1.2⟩
        rcases h1.1 with h | h
        · rw [hp0] at h; exact absurd h (by decide)
        · exact h.symm
    · have ha0f : valAt g5 x a0W = false := by rw [ha0_eq, hc0]; rfl
      rw [ha0f]
      rcases hcan0_iff.mp hc0 with ⟨hpb0, hm0⟩
      refine ⟨fun hp0 => ?_, hm0⟩
      rcases hpb0 with h | h
      · rw [hp0] at h; exact absurd h (by decide)
      · exact h.symm
  refine ⟨gExt_trans he14 h5.1, h5.2.1,
    by linarith only [hW, hlen1, h2.2.2.1, h3.2.2.1, h4.2.2.1, h5.2.2.1],
    h5.2.2.2.1, ha0_props.1, ha0_props.2⟩

private def cCycleBuild (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (g : List Gate) (k : ℕ)
    (pW bW : ℕ → ℕ) (laterCyc : Sum8W W) (remR0 remB0 : Word W) :
    List Gate × Word W × Word W × (ℕ → ℕ) :=
  let (g1, a0W) := cCyclePickA0 nin hW g k pW bW laterCyc remR0 remB0
  let (g2, arr) := cBackScan nin hW g1 k pW bW a0W laterCyc (2 * k)
  let (g3, stEnd, xW) := cWalkLoop nin hW g2 k pW bW a0W arr remR0 remB0 (2 * k)
  (g3, stEnd.remR, stEnd.remB, xW)

private lemma cCycleBuild_spec {nin W : ℕ} (hW : 1 ≤ W) (hW3 : 3 ≤ W) {g : List Gate} {x : List Bool}
    (hx : Ctx nin x) (hv : ValidG nin g) {k : ℕ} (hk : 1 ≤ k)
    (pins bits : ℕ → Bool) {laterCyc : Sum8W W} {nLat : ℕ}
    {pW bW : ℕ → ℕ} {remR0 remB0 : Word W}
    (hpW : ∀ j, pW j < nin + g.length) (hbW : ∀ j, bW j < nin + g.length)
    (hpv : ∀ j, valAt g x (pW j) = pins j) (hbv : ∀ j, valAt g x (bW j) = bits j)
    (hlatIn : laterCyc.In (nin + g.length))
    (hlatG : (laterCyc.val g x).Good) (hlatCap : (laterCyc.val g x).Cap nLat nLat)
    (hrr0 : WordIn (nin + g.length) remR0) (hrb0 : WordIn (nin + g.length) remB0)
    (hlim : 2 * k + nLat + 2 < 2 ^ (W - 2))
    (hrem_lim : wordVal g x remR0 < 2 ^ (W - 2) ∧ wordVal g x remB0 < 2 ^ (W - 2))
    (hmem_in : ((pureCycleSum k pins bits).comb (laterCyc.val g x)).Mem (wordVal g x remR0) (wordVal g x remB0)) :
    let res := cCycleBuild nin hW g k pW bW laterCyc remR0 remB0
    let xs := fun j => valAt res.1 x (res.2.2.2 j)
    GExt g res.1 ∧ ValidG nin res.1 ∧ res.1.length ≤ g.length + k * (3100 * W) ∧
    WordIn (nin + res.1.length) res.2.1 ∧ WordIn (nin + res.1.length) res.2.2.1 ∧
    (∀ j < 2 * k, res.2.2.2 j < nin + res.1.length) ∧
    (∀ j < 2 * k, pins j = true → xs j = bits j) ∧
    (laterCyc.val g x).Mem (wordVal res.1 x res.2.1) (wordVal res.1 x res.2.2.1) ∧
    wordVal res.1 x res.2.1 ≤ wordVal g x remR0 ∧
    wordVal res.1 x res.2.2.1 ≤ wordVal g x remB0 ∧
    wordVal g x remR0 - wordVal res.1 x res.2.1 =
      ((List.range (2 * k)).filter (fun e => decide (e % 2 = 0 ∧ xs e ≠ xs ((e + 1) % (2 * k))))).length ∧
    wordVal g x remB0 - wordVal res.1 x res.2.2.1 =
      ((List.range (2 * k)).filter (fun e => decide (e % 2 = 1 ∧ xs e ≠ xs ((e + 1) % (2 * k))))).length := by
  have hpow_le : 2 ^ (W - 2) ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) (by omega)
  have h1 := cCyclePickA0_spec hW hW3 hx hv hk pins bits hpW hbW hpv hbv hlatIn hlatG hlatCap hrr0 hrb0 hlim hrem_lim hmem_in
  obtain ⟨g1, a0W, h1_eq⟩ : ∃ g1 a0W, cCyclePickA0 nin hW g k pW bW laterCyc remR0 remB0 = (g1, a0W) := ⟨_, _, rfl⟩
  rw [h1_eq] at h1; dsimp only at h1
  rcases h1 with ⟨he1, hv1, hlen1, ha0_in, ha0_pin, ha0_mem⟩
  have h2 := cBackScan_spec hW hx hv1 hk
    (fun j _ => wire_ext he1 (hpW j)) (fun j _ => wire_ext he1 (hbW j))
    ha0_in (sum8_in_ext he1 hlatIn)
    (by rw [Sum8W.val_ext hx.hlen he1 hlatIn]; exact hlatG)
    (by rw [Sum8W.val_ext hx.hlen he1 hlatIn]; exact hlatCap) (by omega) (2 * k) le_rfl
  obtain ⟨g2, arr, h2_eq⟩ : ∃ g2 arr, cBackScan nin hW g1 k pW bW a0W laterCyc (2 * k) = (g2, arr) := ⟨_, _, rfl⟩
  rw [h2_eq] at h2; dsimp only at h2
  rcases h2 with ⟨he2, hv2, hlen2, harr⟩
  have he12 := gExt_trans he1 he2
  have h3 := cWalkLoop_spec hW hW3 hx hv2 hk pins bits (valAt g1 x a0W) hlatG (nLat := nLat)
    (fun j => wire_ext he12 (hpW j)) (fun j => wire_ext he12 (hbW j))
    (fun j => by rw [valAt_ext hx.hlen he12 (hpW j), hpv j])
    (fun j => by rw [valAt_ext hx.hlen he12 (hbW j), hbv j])
    (wire_ext he2 ha0_in) (valAt_ext hx.hlen he2 ha0_in)
    (wordIn_ext he12 hrr0) (wordIn_ext he12 hrb0)
    (fun m hm => (harr m hm).1)
    (fun m hm => by
      have hv := (harr m hm).2.1
      rw [Sum8W.val_ext hx.hlen he1 hlatIn] at hv
      have hp_eq : (fun t => valAt g1 x (pW t)) = pins := funext fun t => by rw [valAt_ext hx.hlen he1 (hpW t), hpv t]
      have hb_eq : (fun t => valAt g1 x (bW t)) = bits := funext fun t => by rw [valAt_ext hx.hlen he1 (hbW t), hbv t]
      rw [hp_eq, hb_eq] at hv; exact hv)
    (fun m hm => (harr m hm).2.2)
    hlim
    ⟨by rw [wordVal_ext hx.hlen he12 hrr0]; exact hrem_lim.1,
     by rw [wordVal_ext hx.hlen he12 hrb0]; exact hrem_lim.2⟩
    (2 * k) le_rfl
  obtain ⟨g3, stEnd, xW, h3_eq⟩ : ∃ g3 stEnd xW, cWalkLoop nin hW g2 k pW bW a0W arr remR0 remB0 (2 * k) = (g3, stEnd, xW) := ⟨_, _, _, rfl⟩
  rw [h3_eq] at h3; dsimp only at h3
  have hres_eq : cCycleBuild nin hW g k pW bW laterCyc remR0 remB0 = (g3, stEnd.remR, stEnd.remB, xW) := by
    unfold cCycleBuild; rw [h1_eq]; dsimp only; rw [h2_eq]; dsimp only; rw [h3_eq]
  simp only [hres_eq]
  rcases h3 with ⟨he3, hv3, hlen3, hin3, hval3, hrl3, hbl3, hxw3⟩
  have he_all := gExt_trans he12 he3
  have hrr0_2 : wordVal g2 x remR0 = wordVal g x remR0 := wordVal_ext hx.hlen he12 hrr0
  have hrb0_2 : wordVal g2 x remB0 = wordVal g x remB0 := wordVal_ext hx.hlen he12 hrb0
  rw [hrr0_2] at hval3 hrl3 hxw3
  rw [hrb0_2] at hval3 hbl3 hxw3
  have hwk := walkLoop_spec hk pins bits (valAt g1 x a0W) hlatG (wordVal g x remR0) (wordVal g x remB0) ha0_pin ha0_mem
  have hxs_eq : ∀ j < 2 * k, valAt g3 x (xW j) =
      (walkLoop k pins bits (valAt g1 x a0W) (laterCyc.val g x) (wordVal g x remR0) (wordVal g x remB0) j).curX :=
    fun j hj => (hxw3 j (by omega)).2
  have hremR_eq : wordVal g3 x stEnd.remR =
      (walkLoop k pins bits (valAt g1 x a0W) (laterCyc.val g x) (wordVal g x remR0) (wordVal g x remB0) (2 * k)).remR :=
    congrArg WalkState.remR hval3
  have hremB_eq : wordVal g3 x stEnd.remB =
      (walkLoop k pins bits (valAt g1 x a0W) (laterCyc.val g x) (wordVal g x remR0) (wordVal g x remB0) (2 * k)).remB :=
    congrArg WalkState.remB hval3
  refine ⟨he_all, hv3, ?_, hin3.2.1, hin3.2.2, fun j hj => (hxw3 j (by omega)).1,
    fun j hj hp => by rw [hxs_eq j hj]; exact hwk.1 j hj hp,
    by rw [hremR_eq, hremB_eq]; exact hwk.2.2.1,
    hrl3, hbl3, ?_, ?_⟩
  · have hkw : W ≤ k * W := Nat.le_mul_of_pos_left W hk
    linarith only [hkw, hlen1, hlen2, hlen3]
  · rw [hremR_eq, hwk.2.2.2.2.2.1]
    congr 1; refine List.filter_congr fun e he => ?_
    rw [List.mem_range] at he
    have he1' : (e + 1) % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
    rw [hxs_eq e he, hxs_eq _ he1']
  · rw [hremB_eq, hwk.2.2.2.2.2.2]
    congr 1; refine List.filter_congr fun e he => ?_
    rw [List.mem_range] at he
    have he1' : (e + 1) % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
    rw [hxs_eq e he, hxs_eq _ he1']

/-! ### Cycle-list helpers: wiring `pinWire`, `bitWire`, `cPrepList`, `cBuildList` -/

private def pinWire (n : ℕ) (v : Bool × Fin n) : ℕ :=
  if v.1 then 2 + n + v.2.val else 2 + v.2.val

private def bitWire (n : ℕ) (v : Bool × Fin n) : ℕ :=
  if v.1 then 2 + 3 * n + v.2.val else 2 + 2 * n + v.2.val

private def cycPinW {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (c : List (Fin n)) (j : ℕ) : ℕ :=
  if h : j < 2 * c.length then pinWire n (cycVert M c j h) else 0

private def cycBitW {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (c : List (Fin n)) (j : ℕ) : ℕ :=
  if h : j < 2 * c.length then bitWire n (cycVert M c j h) else 0

private def cycPins {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (pin : Bool × Fin n → Bool)
    (c : List (Fin n)) (j : ℕ) : Bool :=
  if h : j < 2 * c.length then pin (cycVert M c j h) else false

private def cycBits {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (bit : Bool × Fin n → Bool)
    (c : List (Fin n)) (j : ℕ) : Bool :=
  if h : j < 2 * c.length then bit (cycVert M c j h) else false

private lemma cyc_counts_eq_filter {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (c : List (Fin n))
    (hc_step : ∀ j (hj : j < c.length), ((M false).trans (M true).symm) (c.get ⟨j, hj⟩) =
      (c.get ⟨(j + 1) % c.length, Nat.mod_lt _ (by omega)⟩))
    (x : Bool × Fin n → Bool) :
    let xs := fun j => if h : j < 2 * c.length then x (cycVert M c j h) else false
    cycRedCount M c x =
      ((List.range (2 * c.length)).filter (fun e => decide (e % 2 = 0 ∧ xs e ≠ xs ((e + 1) % (2 * c.length))))).length ∧
    cycBlueCount M c x =
      ((List.range (2 * c.length)).filter (fun e => decide (e % 2 = 1 ∧ xs e ≠ xs ((e + 1) % (2 * c.length))))).length := by
  intro xs
  have hrange_split : ∀ (m : ℕ) (p : ℕ → Bool),
      ((List.range (2 * m)).filter p).length =
      ((List.range m).map (fun t => (p (2 * t)).toNat + (p (2 * t + 1)).toNat)).sum := by
    intro m p
    induction m with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, List.range_succ, List.filter_append,
        List.length_append, List.range_succ, List.filter_append, List.length_append, ih,
        List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_singleton, List.sum_singleton]
      have h1 : ([2 * m].filter p).length = (p (2 * m)).toNat := by cases hp : p (2 * m) <;> simp [hp]
      have h2 : ([2 * m + 1].filter p).length = (p (2 * m + 1)).toNat := by cases hp : p (2 * m + 1) <;> simp [hp]
      rw [h1, h2]; omega
  have hlist_sum : ∀ (f : Fin n → ℕ),
      (c.map f).sum = ((List.range c.length).map (fun t => if h : t < c.length then f (c.get ⟨t, h⟩) else 0)).sum := by
    intro f
    have hmap : c = (List.range c.length).pmap (fun t (h : t < c.length) => c.get ⟨t, h⟩) (fun _ h => List.mem_range.mp h) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2; simp
    conv_lhs => rw [hmap]
    rw [List.map_pmap]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.length_pmap, List.length_range] at hi1
      simp [hi1]
  constructor
  · rw [hrange_split]
    unfold cycRedCount
    rw [hlist_sum]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [List.mem_range] at ht
    have hmod1 : (2 * t) % 2 = 0 := by omega
    have hmod2 : (2 * t + 1) % 2 ≠ 0 := by omega
    have hlt1 : 2 * t < 2 * c.length := by omega
    have hlt2 : 2 * t + 1 < 2 * c.length := by omega
    have hmod_next : (2 * t + 1) % (2 * c.length) = 2 * t + 1 := Nat.mod_eq_of_lt hlt2
    have hxs1 : xs (2 * t) = x (false, c.get ⟨t, ht⟩) := by
      dsimp only [xs]; rw [dif_pos hlt1]; unfold cycVert; simp [hmod1, show 2 * t / 2 = t by omega]
    have hxs2 : xs (2 * t + 1) = x (true, M false (c.get ⟨t, ht⟩)) := by
      dsimp only [xs]; rw [dif_pos hlt2]; unfold cycVert; simp [hmod2, show (2 * t + 1) / 2 = t by omega]
    simp only [ht, ↓reduceDIte, hmod1, hmod2, hmod_next, true_and, false_and, decide_false,
      Bool.toNat_false, Nat.add_zero, hxs1, hxs2]
  · rw [hrange_split]
    unfold cycBlueCount
    rw [hlist_sum]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [List.mem_range] at ht
    have hmod1 : (2 * t) % 2 ≠ 1 := by omega
    have hmod2 : (2 * t + 1) % 2 = 1 := by omega
    have hlt2 : 2 * t + 1 < 2 * c.length := by omega
    have hmod_next : (2 * t + 1 + 1) % (2 * c.length) = 2 * ((t + 1) % c.length) := by
      by_cases hlast : t + 1 = c.length
      · rw [show 2 * t + 1 + 1 = 2 * c.length by omega, hlast, Nat.mod_self, Nat.mod_self]
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have hlt3 : 2 * ((t + 1) % c.length) < 2 * c.length := by have := Nat.mod_lt (t + 1) (by omega : 0 < c.length); omega
    have hxs2 : xs (2 * t + 1) = x (true, M false (c.get ⟨t, ht⟩)) := by
      dsimp only [xs]; rw [dif_pos hlt2]; unfold cycVert
      simp [show (2 * t + 1) % 2 ≠ 0 by omega, show (2 * t + 1) / 2 = t by omega]
    have hxs3 : xs (2 * ((t + 1) % c.length)) = x (false, ((M false).trans (M true).symm) (c.get ⟨t, ht⟩)) := by
      dsimp only [xs]; rw [dif_pos hlt3]; unfold cycVert
      simp only [show (2 * ((t + 1) % c.length)) % 2 = 0 by omega, ↓reduceIte,
        show 2 * ((t + 1) % c.length) / 2 = (t + 1) % c.length by omega]
      rw [hc_step t ht]
    simp only [ht, ↓reduceDIte, hmod1, hmod2, hmod_next, true_and, false_and, decide_false,
      Bool.toNat_false, Nat.zero_add, hxs2, hxs3]
    simp only [Equiv.trans_apply]
    congr 1; exact decide_eq_decide.mpr ne_comm

private def pureListSum {n : ℕ} (M : Bool → Equiv.Perm (Fin n))
    (pin bit : Bool × Fin n → Bool) : List (List (Fin n)) → Sum8
  | [] => Sum8.zero
  | c :: cs => (pureCycleSum c.length (cycPins M pin c) (cycBits M bit c)).comb (pureListSum M pin bit cs)

private lemma pureListSum_props {n : ℕ} (M : Bool → Equiv.Perm (Fin n))
    (pin bit : Bool × Fin n → Bool) :
    ∀ cs : List (List (Fin n)), (∀ c ∈ cs, 1 ≤ c.length) →
      (pureListSum M pin bit cs).Good ∧
      (pureListSum M pin bit cs).Cap (cs.map List.length).sum (cs.map List.length).sum := by
  intro cs
  induction cs with
  | nil => intro _; exact ⟨Sum8.good_zero, Sum8.cap_zero⟩
  | cons c cs ih =>
    intro hlen
    have h1 := ih (fun c' hc' => hlen c' (List.mem_cons_of_mem c hc'))
    have hc1 := hlen c List.mem_cons_self
    have hG := pureCycleSum_good hc1 (cycPins M pin c) (cycBits M bit c)
    -- Cap of pureCycleSum c.length: prove directly via prepLoop_inv
    have hC : (pureCycleSum c.length (cycPins M pin c) (cycBits M bit c)).Cap c.length c.length := by
      rcases prepLoop_inv c.length (cycPins M pin c) (cycBits M bit c) (2 * c.length) le_rfl with ⟨_, hF, hT⟩
      have hcap_loop : ∀ j ≤ 2 * c.length,
          let st := prepLoop c.length (cycPins M pin c) (cycBits M bit c) j
          st.acc.Cap ((j + 1) / 2 - st.curR - st.preR) (j / 2 - st.curB - st.preB) ∧
          st.curR + st.preR ≤ (j + 1) / 2 ∧ st.curB + st.preB ≤ j / 2 := by
        intro j
        induction j with
        | zero => intro _; exact ⟨Sum8.cap_zero, le_rfl, le_rfl⟩
        | succ j ihj =>
          intro hj
          rcases ihj (by omega) with ⟨hcj, hcrj, hcbj⟩
          rcases prepLoop_inv c.length (cycPins M pin c) (cycBits M bit c) j (by omega) with ⟨_, hFj, hTj⟩
          dsimp only [prepLoop, prepStep]
          generalize prepLoop c.length (cycPins M pin c) (cycBits M bit c) j = st at hcj hcrj hcbj hFj hTj ⊢
          by_cases hp : cycPins M pin c j = true
          · simp only [hp, ↓reduceIte]
            cases hhpj : st.hasPin
            · simp only [Bool.not_false, ↓reduceIte]
              rcases hFj hhpj with ⟨hacc0, hcr0, hcb0, _⟩
              rw [hacc0]; refine ⟨by unfold Sum8.Cap Sum8.zero; (try dsimp only); omega, by split_ifs <;> ((try dsimp only); omega), by split_ifs <;> ((try dsimp only); omega)⟩
            · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              rcases hTj hhpj with ⟨e0, el, _, _, _, _, _, _, _, _, _, _, hcr0, hcb0, _⟩
              have hsc := Sum8.cap_ofSeg st.curR st.curB (xor st.curBit (cycBits M bit c j)) (by omega)
              have hcomb := Sum8.cap_comb hcj hsc
              refine ⟨by rcases hcomb with ⟨_, _, _, _, _, _, _, _, _, _⟩; unfold Sum8.Cap; split_ifs <;> ((try dsimp only); omega),
                by split_ifs <;> ((try dsimp only); omega), by split_ifs <;> ((try dsimp only); omega)⟩
          · simp only [if_neg hp]
            refine ⟨by rcases hcj with ⟨_, _, _, _, _, _, _, _, _, _⟩; unfold Sum8.Cap; split_ifs <;> ((try dsimp only); omega),
              by split_ifs <;> ((try dsimp only); omega), by split_ifs <;> ((try dsimp only); omega)⟩
      rcases hcap_loop (2 * c.length) le_rfl with ⟨hc_end, hcr_end, hcb_end⟩
      unfold pureCycleSum; dsimp only
      generalize prepLoop c.length (cycPins M pin c) (cycBits M bit c) (2 * c.length) = stEnd at hc_end hcr_end hcb_end hF hT ⊢
      cases hhp : stEnd.hasPin
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hF hhp with ⟨hacc0, hcr, hcb, _⟩
        rw [hacc0, Sum8.comb_zero_left, hcr, hcb,
          show (2 * c.length + 1) / 2 = c.length by omega, show 2 * c.length / 2 = c.length by omega]
        exact Sum8.cap_ofSeg c.length c.length false (by omega)
      · rcases hT hhp with ⟨e0, el, he0l, helk, _, _, _, _, _, _, hpr0, hpb0, hcr0, hcb0, _⟩
        simp only [↓reduceIte]
        have hsc := Sum8.cap_ofSeg (stEnd.curR + stEnd.preR) (stEnd.curB + stEnd.preB)
          (xor stEnd.curBit stEnd.firstBit) (by omega)
        have hcomb := Sum8.cap_comb hc_end hsc
        rcases hcomb with ⟨_, _, _, _, _, _, _, _, _, _⟩
        unfold Sum8.Cap; omega
    exact ⟨Sum8.good_comb hG h1.1, by simpa [pureListSum, List.map_cons, List.sum_cons] using Sum8.cap_comb hC h1.2⟩

private lemma pureListSum_sound {n : ℕ} (M : Bool → Equiv.Perm (Fin n))
    (pin bit x : Bool × Fin n → Bool) (hpin : ∀ v, pin v = true → x v = bit v) :
    ∀ cs : List (List (Fin n)),
      (∀ c ∈ cs, 1 ≤ c.length ∧
        ∀ j (hj : j < c.length), ((M false).trans (M true).symm) (c.get ⟨j, hj⟩) =
          (c.get ⟨(j + 1) % c.length, Nat.mod_lt _ (by omega)⟩)) →
      (pureListSum M pin bit cs).Mem
        (cs.map (fun c => cycRedCount M c x)).sum
        (cs.map (fun c => cycBlueCount M c x)).sum := by
  intro cs
  induction cs with
  | nil => intro _; simp [pureListSum, Sum8.mem_zero_iff]
  | cons c cs ih =>
    intro hcs
    have hrec := ih (fun c' hc' => hcs c' (List.mem_cons_of_mem c hc'))
    rcases hcs c List.mem_cons_self with ⟨hc1, hc_step⟩
    dsimp only [pureListSum, List.map_cons, List.sum_cons]
    apply Sum8.mem_comb_of_mem _ hrec
    let xs := fun j => if h : j < 2 * c.length then x (cycVert M c j h) else false
    have hcnt := cyc_counts_eq_filter M c hc_step x
    dsimp only
    rw [hcnt.1, hcnt.2]
    exact pureCycleSum_sound hc1 (cycPins M pin c) (cycBits M bit c) xs
      (fun j hj hp => by
        dsimp only [cycPins, cycBits, xs] at hp ⊢
        simp only [hj, ↓reduceDIte] at hp ⊢
        exact hpin _ hp)

/-- Compute suffix-sum circuit list for `cs`: returns `(g', sufList)` where `sufList[0]` is total sum
    and `sufList[i]` is the `Sum8W` for `cs.drop i`. -/
private def cPrepSuf {n : ℕ} (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (M : Bool → Equiv.Perm (Fin n))
    (g : List Gate) : List (List (Fin n)) → List Gate × Sum8W W × List (Sum8W W)
  | [] => (g, cSum8Zero W, [cSum8Zero W])
  | c :: cs =>
    let (g1, sufRest, listRest) := cPrepSuf nin hW M g cs
    let (g2, cycS) := cCyclePrep nin hW g1 c.length (cycPinW M c) (cycBitW M c)
    let (g3, totS) := cCombSum8 nin g2 cycS sufRest
    (g3, totS, totS :: listRest)

private lemma cPrepSuf_spec {n nin W : ℕ} (hW : 1 ≤ W) (M : Bool → Equiv.Perm (Fin n))
    {g : List Gate} {x : List Bool} (hx : Ctx nin x) (hv : ValidG nin g)
    (pin bit : Bool × Fin n → Bool)
    (hpinW : ∀ v : Bool × Fin n, pinWire n v < nin ∧ valAt g x (pinWire n v) = pin v)
    (hbitW : ∀ v : Bool × Fin n, bitWire n v < nin ∧ valAt g x (bitWire n v) = bit v) :
    ∀ cs : List (List (Fin n)), (∀ c ∈ cs, 1 ≤ c.length) →
      2 * (cs.map List.length).sum + 2 < 2 ^ W →
      let res := cPrepSuf nin hW M g cs
      GExt g res.1 ∧ ValidG nin res.1 ∧
      res.1.length ≤ g.length + (cs.map List.length).sum * (1400 * W) ∧
      res.2.1.In (nin + res.1.length) ∧
      res.2.1.val res.1 x = pureListSum M pin bit cs ∧
      res.2.2.length = cs.length + 1 ∧
      (∀ i (hi : i < res.2.2.length),
        (res.2.2.get ⟨i, hi⟩).In (nin + res.1.length) ∧
        (res.2.2.get ⟨i, hi⟩).val res.1 x = pureListSum M pin bit (cs.drop i)) := by
  have hnin := hx.hnin
  intro cs
  induction cs with
  | nil =>
    intro _ _
    dsimp only [cPrepSuf]
    have hz := cSum8Zero_spec (W := W) (g := g) hx
    refine ⟨gExt_refl g, hv, by simp, hz.1, hz.2, rfl, fun i hi => ?_⟩
    simp only [List.length_singleton] at hi
    have hi0 : i = 0 := by omega
    subst hi0; exact ⟨hz.1, hz.2⟩
  | cons c cs ih =>
    intro hlen hlim
    simp only [List.map_cons, List.sum_cons] at hlim ⊢
    have hc1 := hlen c List.mem_cons_self
    have hih := ih (fun c' hc' => hlen c' (List.mem_cons_of_mem c hc')) (by omega)
    dsimp only [cPrepSuf]
    generalize cPrepSuf nin hW M g cs = _r1 at hih ⊢; rcases _r1 with ⟨g1, sufRest, listRest⟩
    dsimp only at hih; dsimp (config := { zeta := false }) only at ⊢
    rcases hih with ⟨he1, hv1, hlen1, hsuf_in, hsuf_v, hl_len, hdrop⟩
    have hpW : ∀ j < 2 * c.length, cycPinW M c j < nin + g1.length := fun j hj => by
      unfold cycPinW; rw [dif_pos hj]; have := (hpinW (cycVert M c j hj)).1; omega
    have hbW : ∀ j < 2 * c.length, cycBitW M c j < nin + g1.length := fun j hj => by
      unfold cycBitW; rw [dif_pos hj]; have := (hbitW (cycVert M c j hj)).1; omega
    have h2 := cCyclePrep_spec hW hx hv1 hc1 hpW hbW (by omega)
    generalize cCyclePrep nin hW g1 c.length (cycPinW M c) (cycBitW M c) = _r2 at h2 ⊢
    rcases _r2 with ⟨g2, cycS⟩; dsimp only at h2; dsimp (config := { zeta := false }) only at ⊢
    have he12 := gExt_trans he1 h2.1
    have hp_eq : (fun t => valAt g1 x (cycPinW M c t)) = cycPins M pin c := funext fun t => by
      unfold cycPinW cycPins; split_ifs with h
      · rw [valAt_ext hx.hlen he1 (by have := (hpinW (cycVert M c t h)).1; omega), (hpinW (cycVert M c t h)).2]
      · exact valAt_zero hx
    have hb_eq : (fun t => valAt g1 x (cycBitW M c t)) = cycBits M bit c := funext fun t => by
      unfold cycBitW cycBits; split_ifs with h
      · rw [valAt_ext hx.hlen he1 (by have := (hbitW (cycVert M c t h)).1; omega), (hbitW (cycVert M c t h)).2]
      · exact valAt_zero hx
    have hcyc_v : cycS.val g2 x = pureCycleSum c.length (cycPins M pin c) (cycBits M bit c) := by
      rw [h2.2.2.2.2.1, hp_eq, hb_eq]
    have hcyc_cap : (cycS.val g2 x).Cap c.length c.length := by rw [h2.2.2.2.2.1]; exact h2.2.2.2.2.2.1
    have hsuf_cap : (sufRest.val g2 x).Cap (cs.map List.length).sum (cs.map List.length).sum := by
      rw [Sum8W.val_ext hx.hlen h2.1 hsuf_in, hsuf_v]
      exact (pureListSum_props M pin bit cs (fun c' hc' => hlen c' (List.mem_cons_of_mem c hc'))).2
    have h3 := cCombSum8_spec hx h2.2.1 h2.2.2.2.1 (sum8_in_ext h2.1 hsuf_in)
      (Sum8.cap_bound (Sum8.cap_comb hcyc_cap hsuf_cap) (by omega) (by omega))
    generalize cCombSum8 nin g2 cycS sufRest = _r3 at h3 ⊢
    rcases _r3 with ⟨g3, totS⟩; dsimp only at h3; dsimp only
    have htot_v : totS.val g3 x = pureListSum M pin bit (c :: cs) := by
      rw [h3.2.2.2.2, hcyc_v, Sum8W.val_ext hx.hlen h2.1 hsuf_in, hsuf_v]; rfl
    have he23 := gExt_trans h2.1 h3.1
    refine ⟨gExt_trans he12 h3.1, h3.2.1, ?_, h3.2.2.2.1, htot_v, by simp [hl_len], fun i hi => ?_⟩
    · have hcw : W ≤ c.length * W := by nlinarith
      nlinarith [hlen1, h2.2.2.1, h3.2.2.1]
    · cases i with
      | zero => exact ⟨h3.2.2.2.1, htot_v⟩
      | succ i =>
        simp only [List.length_cons] at hi
        rcases hdrop i (by omega) with ⟨hd_in, hd_v⟩
        refine ⟨sum8_in_ext he23 hd_in, ?_⟩
        dsimp only [List.get]
        rw [Sum8W.val_ext hx.hlen he23 hd_in, hd_v]; rfl

/-- Build witness wires across a list of cycles `cs`, given matching suffix summaries `sufList`
    (`sufList.length = cs.length + 1`, where `sufList[1..]` are the summaries strictly after each cycle). -/
private noncomputable def cBuildWalk {n : ℕ} (nin : ℕ) {W : ℕ} (hW : 1 ≤ W) (M : Bool → Equiv.Perm (Fin n))
    (g : List Gate) (remR remB : Word W) (outMap : Bool × Fin n → ℕ) :
    List (List (Fin n)) → List (Sum8W W) → List Gate × Word W × Word W × (Bool × Fin n → ℕ)
  | [], _ => (g, remR, remB, outMap)
  | c :: cs, sufList =>
    let laterCyc := sufList.getD 1 (cSum8Zero W)
    let (g1, remR1, remB1, xW) := cCycleBuild nin hW g c.length (cycPinW M c) (cycBitW M c) laterCyc remR remB
    let outMap1 : Bool × Fin n → ℕ := fun v =>
      if h : ∃ j : Fin (2 * c.length), cycVert M c j.val j.isLt = v then
        xW (Classical.choose h).val
      else outMap v
    cBuildWalk nin hW M g1 remR1 remB1 outMap1 cs sufList.tail

private lemma cycVert_inj_in_cycle {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (c : List (Fin n))
    (hc_nodup : c.Nodup) {j1 j2 : ℕ} (h1 : j1 < 2 * c.length) (h2 : j2 < 2 * c.length)
    (heq : cycVert M c j1 h1 = cycVert M c j2 h2) : j1 = j2 := by
  unfold cycVert at heq
  split_ifs at heq with p1 p2 p2
  · have hval : (c.get ⟨j1 / 2, by omega⟩) = (c.get ⟨j2 / 2, by omega⟩) := congrArg Prod.snd heq
    have hidx := (List.nodup_iff_injective_get.mp hc_nodup) hval
    have : j1 / 2 = j2 / 2 := congrArg Fin.val hidx
    omega
  · exact absurd (congrArg Prod.fst heq) Bool.false_ne_true
  · exact absurd (congrArg Prod.fst heq) Bool.false_ne_true.symm
  · have hval : M false (c.get ⟨j1 / 2, by omega⟩) = M false (c.get ⟨j2 / 2, by omega⟩) := congrArg Prod.snd heq
    have hval' : (c.get ⟨j1 / 2, by omega⟩) = (c.get ⟨j2 / 2, by omega⟩) := (M false).injective hval
    have hidx := (List.nodup_iff_injective_get.mp hc_nodup) hval'
    have : j1 / 2 = j2 / 2 := congrArg Fin.val hidx
    omega

private lemma cycVert_disj_cycles {n : ℕ} (M : Bool → Equiv.Perm (Fin n)) (c1 c2 : List (Fin n))
    (hdisj : ∀ a ∈ c1, a ∉ c2) {j1 j2 : ℕ} (h1 : j1 < 2 * c1.length) (h2 : j2 < 2 * c2.length) :
    cycVert M c1 j1 h1 ≠ cycVert M c2 j2 h2 := by
  intro heq
  unfold cycVert at heq
  split_ifs at heq with p1 p2 p2
  · have hval : (c1.get ⟨j1 / 2, by omega⟩) = (c2.get ⟨j2 / 2, by omega⟩) := congrArg Prod.snd heq
    exact hdisj _ (List.get_mem c1 ⟨j1 / 2, by omega⟩) (hval ▸ List.get_mem c2 ⟨j2 / 2, by omega⟩)
  · exact absurd (congrArg Prod.fst heq) Bool.false_ne_true
  · exact absurd (congrArg Prod.fst heq) Bool.false_ne_true.symm
  · have hval : M false (c1.get ⟨j1 / 2, by omega⟩) = M false (c2.get ⟨j2 / 2, by omega⟩) := congrArg Prod.snd heq
    have hval' : (c1.get ⟨j1 / 2, by omega⟩) = (c2.get ⟨j2 / 2, by omega⟩) := (M false).injective hval
    exact hdisj _ (List.get_mem c1 ⟨j1 / 2, by omega⟩) (hval' ▸ List.get_mem c2 ⟨j2 / 2, by omega⟩)

private lemma cBuildWalk_spec {n nin W : ℕ} (hW : 1 ≤ W) (hW3 : 3 ≤ W)
    (M : Bool → Equiv.Perm (Fin n)) {x : List Bool} (hx : Ctx nin x)
    (pin bit : Bool × Fin n → Bool)
    (hpinW : ∀ v : Bool × Fin n, pinWire n v < nin ∧ valAt [] x (pinWire n v) = pin v)
    (hbitW : ∀ v : Bool × Fin n, bitWire n v < nin ∧ valAt [] x (bitWire n v) = bit v) :
    ∀ (cs : List (List (Fin n))) (sufList : List (Sum8W W)) (g : List Gate)
      (remR remB : Word W) (outMap : Bool × Fin n → ℕ),
      ValidG nin g →
      (∀ c ∈ cs, 1 ≤ c.length ∧ c.Nodup ∧
        ∀ j (hj : j < c.length), ((M false).trans (M true).symm) (c.get ⟨j, hj⟩) =
          (c.get ⟨(j + 1) % c.length, Nat.mod_lt _ (by omega)⟩)) →
      cs.flatten.Nodup →
      sufList.length = cs.length + 1 →
      (∀ i (hi : i < sufList.length), (sufList.get ⟨i, hi⟩).In (nin + g.length) ∧
        (sufList.get ⟨i, hi⟩).val g x = pureListSum M pin bit (cs.drop i)) →
      WordIn (nin + g.length) remR → WordIn (nin + g.length) remB →
      (∀ v, outMap v < nin + g.length) →
      2 * (cs.map List.length).sum + 2 < 2 ^ (W - 2) →
      wordVal g x remR < 2 ^ (W - 2) → wordVal g x remB < 2 ^ (W - 2) →
      (pureListSum M pin bit cs).Mem (wordVal g x remR) (wordVal g x remB) →
      let res := cBuildWalk nin hW M g remR remB outMap cs sufList
      let wit := fun v => valAt res.1 x (res.2.2.2 v)
      GExt g res.1 ∧ ValidG nin res.1 ∧
      res.1.length ≤ g.length + (cs.map List.length).sum * (3100 * W) ∧
      (∀ v, res.2.2.2 v < nin + res.1.length) ∧
      (∀ v, (∀ c ∈ cs, ∀ j (hj : j < 2 * c.length), cycVert M c j hj ≠ v) →
        res.2.2.2 v = outMap v) ∧
      (∀ c ∈ cs, ∀ j (hj : j < 2 * c.length), pin (cycVert M c j hj) = true →
        wit (cycVert M c j hj) = bit (cycVert M c j hj)) ∧
      wordVal res.1 x res.2.1 = 0 ∧ wordVal res.1 x res.2.2.1 = 0 ∧
      wordVal g x remR = (cs.map (fun c => cycRedCount M c wit)).sum ∧
      wordVal g x remB = (cs.map (fun c => cycBlueCount M c wit)).sum := by
  have hnin := hx.hnin
  intro cs
  induction cs with
  | nil =>
    intro sufList g remR remB outMap hv _ _ _ _ _ _ hout _ _ _ hmem
    dsimp only [cBuildWalk]
    rw [pureListSum, Sum8.mem_zero_iff] at hmem
    refine ⟨gExt_refl g, hv, by simp, hout, fun _ _ => rfl, fun _ hc => by simp at hc,
      hmem.1, hmem.2, by simpa using hmem.1, by simpa using hmem.2⟩
  | cons c cs ih =>
    intro sufList g remR remB outMap hv hcs hnodup hslen hdrop hrr hrb hout hlim hrl hbl hmem
    simp only [List.map_cons, List.sum_cons] at hlim ⊢
    rcases hcs c List.mem_cons_self with ⟨hc1, hc_nodup, hc_step⟩
    have hcs' : ∀ c' ∈ cs, 1 ≤ c'.length ∧ c'.Nodup ∧
        ∀ j (hj : j < c'.length), ((M false).trans (M true).symm) (c'.get ⟨j, hj⟩) =
          (c'.get ⟨(j + 1) % c'.length, Nat.mod_lt _ (by omega)⟩) :=
      fun c' hc' => hcs c' (List.mem_cons_of_mem c hc')
    have hnodup_cs : cs.flatten.Nodup := (List.nodup_append.mp (List.flatten_cons ▸ hnodup)).2.1
    have hdisj_c : ∀ c' ∈ cs, ∀ a ∈ c, a ∉ c' := by
      have hd := (List.nodup_append.mp (List.flatten_cons ▸ hnodup)).2.2
      intro c' hc' a hac hac'
      exact hd a hac a (List.mem_flatten.mpr ⟨c', hc', hac'⟩) rfl
    dsimp only [cBuildWalk]
    have h1_lt : 1 < sufList.length := by simp only [List.length_cons] at hslen; omega
    have hlat_eq_get : sufList.getD 1 (cSum8Zero W) = (sufList.get ⟨1, h1_lt⟩) := by
      simp [List.getD_eq_getElem?_getD, h1_lt]
    set laterCyc := sufList.getD 1 (cSum8Zero W)
    have hlat_spec := hdrop 1 h1_lt
    rw [← hlat_eq_get] at hlat_spec
    have hlat_drop : (c :: cs).drop 1 = cs := rfl
    rw [hlat_drop] at hlat_spec
    have hlat_props := pureListSum_props M pin bit cs (fun c' hc' => (hcs' c' hc').1)
    have hpW_in : ∀ j, cycPinW M c j < nin + g.length := fun j => by
      unfold cycPinW; split_ifs with h
      · have := (hpinW (cycVert M c j h)).1; omega
      · omega
    have hbW_in : ∀ j, cycBitW M c j < nin + g.length := fun j => by
      unfold cycBitW; split_ifs with h
      · have := (hbitW (cycVert M c j h)).1; omega
      · omega
    have hpv_g : ∀ j, valAt g x (cycPinW M c j) = cycPins M pin c j := fun j => by
      unfold cycPinW cycPins; split_ifs with h
      · rw [valAt_ext hx.hlen ⟨g, (List.nil_append g).symm⟩ (by simp; exact (hpinW (cycVert M c j h)).1), (hpinW (cycVert M c j h)).2]
      · exact valAt_zero hx
    have hbv_g : ∀ j, valAt g x (cycBitW M c j) = cycBits M bit c j := fun j => by
      unfold cycBitW cycBits; split_ifs with h
      · rw [valAt_ext hx.hlen ⟨g, (List.nil_append g).symm⟩ (by simp; exact (hbitW (cycVert M c j h)).1), (hbitW (cycVert M c j h)).2]
      · exact valAt_zero hx
    have hcb := cCycleBuild_spec hW hW3 hx hv hc1 (cycPins M pin c) (cycBits M bit c)
      hpW_in hbW_in hpv_g hbv_g hlat_spec.1
      (by rw [hlat_spec.2]; exact hlat_props.1) (by rw [hlat_spec.2]; exact hlat_props.2)
      hrr hrb (by omega) ⟨hrl, hbl⟩ (by rw [hlat_spec.2]; exact hmem)
    generalize cCycleBuild nin hW g c.length (cycPinW M c) (cycBitW M c) laterCyc remR remB = _r1 at hcb ⊢
    rcases _r1 with ⟨g1, remR1, remB1, xW⟩; dsimp only at hcb; dsimp (config := { zeta := false }) only at ⊢
    rcases hcb with ⟨he1, hv1, hlen1, hrr1, hrb1, hxw_in, hxw_pin, hmem1, hrl1, hbl1, hrc1, hbc1⟩
    rw [hlat_spec.2] at hmem1
    let outMap1 : Bool × Fin n → ℕ := fun v =>
      if h : ∃ j : Fin (2 * c.length), cycVert M c j.val j.isLt = v then
        xW (Classical.choose h).val
      else outMap v
    have hout1_in : ∀ v, outMap1 v < nin + g1.length := fun v => by
      dsimp only [outMap1]; split_ifs with h
      · exact hxw_in _ (Classical.choose h).isLt
      · exact wire_ext he1 (hout v)
    have hout1_cyc : ∀ j (hj : j < 2 * c.length), outMap1 (cycVert M c j hj) = xW j := fun j hj => by
      dsimp only [outMap1]
      have hex : ∃ j' : Fin (2 * c.length), cycVert M c j'.val j'.isLt = cycVert M c j hj := ⟨⟨j, hj⟩, rfl⟩
      rw [dif_pos hex]
      have heq := cycVert_inj_in_cycle M c hc_nodup (Classical.choose hex).isLt hj (Classical.choose_spec hex)
      rw [heq]
    have hrec := ih sufList.tail g1 remR1 remB1 outMap1 hv1 hcs' hnodup_cs
      (by simp [hslen])
      (fun i hi => by
        have hidx : i + 1 < sufList.length := by
          cases sufList with
          | nil => simp at hi
          | cons hd tl => simp only [List.tail_cons, List.length_cons] at hi ⊢; omega
        have htail_eq : (sufList.tail.get ⟨i, hi⟩) = (sufList.get ⟨i + 1, hidx⟩) := by
          cases sufList with
          | nil => simp at hi
          | cons hd tl => rfl
        rw [htail_eq]
        rcases hdrop (i + 1) hidx with ⟨hi_in, hi_v⟩
        exact ⟨sum8_in_ext he1 hi_in, by rw [Sum8W.val_ext hx.hlen he1 hi_in, hi_v]; rfl⟩)
      hrr1 hrb1 hout1_in (by omega) (by omega) (by omega) hmem1
    generalize cBuildWalk nin hW M g1 remR1 remB1 outMap1 cs sufList.tail = res at hrec ⊢
    dsimp only at hrec
    rcases hrec with ⟨he2, hv2, hlen2, hout2, hpres2, hpin2, hzR2, hzB2, hred2, hblue2⟩
    let wit := fun v => valAt res.1 x (res.2.2.2 v)
    have hwit_c : ∀ j (hj : j < 2 * c.length), wit (cycVert M c j hj) = valAt g1 x (xW j) := by
      intro j hj
      dsimp only [wit]
      have hpr := hpres2 (cycVert M c j hj) (fun c' hc' j' hj' =>
        (cycVert_disj_cycles M c c' (hdisj_c c' hc') hj hj').symm)
      rw [hpr, hout1_cyc j hj, valAt_ext hx.hlen he2 (hxw_in j hj)]
    refine ⟨gExt_trans he1 he2, hv2, by nlinarith, hout2, ?_, ?_, hzR2, hzB2, ?_, ?_⟩
    · intro v hne
      have hpr := hpres2 v (fun c' hc' => hne c' (List.mem_cons_of_mem c hc'))
      rw [hpr]
      dsimp only [outMap1]
      rw [dif_neg (fun ⟨j, hj⟩ => hne c List.mem_cons_self j.val j.isLt hj)]
    · intro c' hc' j hj hp
      rcases List.mem_cons.mp hc' with rfl | hc''
      · change wit (cycVert M c' j hj) = _; rw [hwit_c j hj]
        have := hxw_pin j hj (by unfold cycPins; rw [dif_pos hj]; exact hp)
        unfold cycBits at this; rw [dif_pos hj] at this; exact this
      · exact hpin2 c' hc'' j hj hp
    · have hcnt := cyc_counts_eq_filter M c hc_step wit
      have hcr_eq : cycRedCount M c wit = wordVal g x remR - wordVal g1 x remR1 := by
        rw [hcnt.1, hrc1]
        congr 1; refine List.filter_congr fun e he => ?_
        rw [List.mem_range] at he
        have he' : (e + 1) % (2 * c.length) < 2 * c.length := Nat.mod_lt _ (by omega)
        simp only [he, he', ↓reduceDIte, hwit_c e he, hwit_c _ he']
      rw [hcr_eq, ← hred2]; omega
    · have hcnt := cyc_counts_eq_filter M c hc_step wit
      have hcb_eq : cycBlueCount M c wit = wordVal g x remB - wordVal g1 x remB1 := by
        rw [hcnt.2, hbc1]
        congr 1; refine List.filter_congr fun e he => ?_
        rw [List.mem_range] at he
        have he' : (e + 1) % (2 * c.length) < 2 * c.length := Nat.mod_lt _ (by omega)
        simp only [he, he', ↓reduceDIte, hwit_c e he, hwit_c _ he']
      rw [hcb_eq, ← hblue2]; omega

/-!
## Part 5: Assembly of `query`, `prep`, `build`, and final theorem `L_pcx_353`
-/

private lemma list_ofFn_getD {α : Type} (d : α) {m : ℕ} (f : Fin m → α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

private lemma append_getD_left {α : Type} (d : α) (l1 l2 : List α) {i : ℕ} (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma append_getD_right {α : Type} (d : α) (l1 l2 : List α) {i : ℕ} (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

private lemma value_lt_pow {w : ℕ} (d : Fin w → Bool) :
    (∑ i : Fin w, (d i).toNat * 2 ^ i.val) < 2 ^ w := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun i : Fin w => d i.castSucc)
    have h2 : (d (Fin.last w)).toNat ≤ 1 := by cases d (Fin.last w) <;> decide
    have h3 : (d (Fin.last w)).toNat * 2 ^ w ≤ 2 ^ w := by simpa using Nat.mul_le_mul_right (2 ^ w) h2
    simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢
    rw [pow_succ]; omega

private lemma validG_to_spec {nin budget : ℕ} {g : List Gate}
    (hv : ValidG nin g) (hsz : g.length ≤ budget) :
    ReadsBack nin ⟨g, 0⟩ ∧ (Circuit.mk g 0).size ≤ budget ∧
    ∀ gate ∈ (Circuit.mk g 0).gates,
      ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1) :=
  ⟨hv.1, hsz, hv.2⟩

private lemma let_prod3 {α β γ : Type*} {Q : Prop}
    (p : α × β × γ) (h : ∀ a b c, p = (a, b, c) → Q) : Q := by
  rcases p with ⟨a, b, c⟩; exact h a b c rfl

private lemma let_prod4 {α β γ δ : Type*} {Q : Prop}
    (p : α × β × γ × δ) (h : ∀ a b c d, p = (a, b, c, d) → Q) : Q := by
  rcases p with ⟨a, b, c, d⟩; exact h a b c d rfl

private lemma main_query_bundle (n : ℕ) :
    let w := 1 + Nat.clog 2 (n + 1)
    ∃ (query : Circuit) (flag : Fin (2 + 12 * w + query.size))
      (result : Bool → Fin w → Fin (2 + 12 * w + query.size)),
      (ReadsBack (2 + 12 * w) query ∧ query.size ≤ 30000 * w ∧
        ∀ gate ∈ query.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
          (gate.op = .not ∧ gate.inputs.length = 1)) ∧
      ∀ (S_tot : Sum8) (sumBits : Fin (8 * w) → Bool) (loR hiR loB hiB : Fin w → Bool),
        S_tot.Bound n →
        (∑ i : Fin w, (sumBits ⟨0 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.fr →
        (∑ i : Fin w, (sumBits ⟨1 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.fb →
        (∑ i : Fin w, (sumBits ⟨2 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.cr →
        (∑ i : Fin w, (sumBits ⟨3 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.cb →
        (∑ i : Fin w, (sumBits ⟨4 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.d00 →
        (∑ i : Fin w, (sumBits ⟨5 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.d11 →
        (∑ i : Fin w, (sumBits ⟨6 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.d01 →
        (∑ i : Fin w, (sumBits ⟨7 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.d10 →
        let qIn := [false, true] ++ List.ofFn sumBits ++
          List.ofFn loR ++ List.ofFn hiR ++ List.ofFn loB ++ List.ofFn hiB
        let qs := query.wires qIn
        let vLoR := ∑ i : Fin w, (loR i).toNat * 2 ^ i.val
        let vHiR := ∑ i : Fin w, (hiR i).toNat * 2 ^ i.val
        let vLoB := ∑ i : Fin w, (loB i).toNat * 2 ^ i.val
        let vHiB := ∑ i : Fin w, (hiB i).toNat * 2 ^ i.val
        let q := S_tot.query vLoR vHiR vLoB vHiB
        qs.getD flag.val false = q.1 ∧
        (q.2.1 < 2 ^ w → (∑ i : Fin w, (qs.getD (result false i).val false).toNat * 2 ^ i.val) = q.2.1) ∧
        (q.2.2 < 2 ^ w → (∑ i : Fin w, (qs.getD (result true i).val false).toNat * 2 ^ i.val) = q.2.2) := by
  dsimp only
  set w := 1 + Nat.clog 2 (n + 1)
  have hw1 : 1 ≤ w := by omega
  have hclog : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by decide) (n + 1)
  have h2w : 2 * (n + 1) ≤ 2 ^ w := by
    have : 2 ^ w = 2 * 2 ^ Nat.clog 2 (n + 1) := by rw [show w = Nat.clog 2 (n + 1) + 1 by omega, pow_succ]; ring
    omega
  set W := w + 3
  have hW1 : 1 ≤ W := by omega
  have hW4 : 4 ≤ W := by omega
  have hwW : w ≤ W := by omega
  have hW_le : W ≤ 4 * w := by omega
  have h2Wm3 : 2 ^ (W - 3) = 2 ^ w := by rw [show W - 3 = w by omega]
  let ninQ := 2 + 12 * w
  let qField (k : ℕ) : Word W := cPadW (fun i : Fin w => 2 + k * w + i.val)
  let qSum : Sum8W W := ⟨qField 0, qField 1, qField 2, qField 3, qField 4, qField 5, qField 6, qField 7⟩
  let qLoR : Word W := qField 8
  let qHiR : Word W := qField 9
  let qLoB : Word W := qField 10
  let qHiB : Word W := qField 11
  apply let_prod4 (cQuery ninQ hW1 [] qSum qLoR qHiR qLoB qHiB)
  intro qG qFlag qR qB hq_eq
  let queryC : Circuit := ⟨qG, 0⟩
  have hqField_in : ∀ k < 12, WordIn (ninQ + ([] : List Gate).length) (qField k) := fun k hk i => by
    dsimp only [qField, cPadW, ninQ]; split_ifs with hi
    · have hmul : (k + 1) * w ≤ 12 * w := Nat.mul_le_mul_right w hk
      rw [Nat.add_mul, one_mul] at hmul
      simp <;> omega
    · simp
  have hqSum_in : qSum.In (ninQ + ([] : List Gate).length) :=
    ⟨hqField_in 0 (by omega), hqField_in 1 (by omega), hqField_in 2 (by omega), hqField_in 3 (by omega),
     hqField_in 4 (by omega), hqField_in 5 (by omega), hqField_in 6 (by omega), hqField_in 7 (by omega)⟩
  have hloR_in : WordIn (ninQ + ([] : List Gate).length) qLoR := hqField_in 8 (by omega)
  have hhiR_in : WordIn (ninQ + ([] : List Gate).length) qHiR := hqField_in 9 (by omega)
  have hloB_in : WordIn (ninQ + ([] : List Gate).length) qLoB := hqField_in 10 (by omega)
  have hhiB_in : WordIn (ninQ + ([] : List Gate).length) qHiB := hqField_in 11 (by omega)
  have hq_def_ctx := ctx_default (nin := ninQ) (by omega)
  have hpad_eq : ∀ (x : List Bool) (k : ℕ), Ctx ninQ x →
      wordVal [] x (qField k) = wordVal [] x (fun i : Fin w => 2 + k * w + i.val) := fun x k hx => by
    dsimp only [qField]; unfold wordVal cPadW
    rw [← Finset.sum_subset (s₁ := (Finset.univ : Finset (Fin w)).image (fun i : Fin w => (⟨i.val, by omega⟩ : Fin W)))
      (Finset.subset_univ _)]
    · rw [Finset.sum_image (fun i _ j _ h => Fin.ext (by simpa using congrArg Fin.val h))]
      refine Finset.sum_congr rfl fun i _ => by simp
    · intro i _ hni
      have hge : ¬ i.val < w := fun hlt =>
        hni (Finset.mem_image.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      simp [hge, valAt_zero hx]
  have hqField_lt : ∀ (x : List Bool) (k : ℕ), Ctx ninQ x → wordVal [] x (qField k) < 2 ^ w := fun x k hx => by
    rw [hpad_eq x k hx]; exact wordVal_lt [] x _
  have hq_struct := cQuery_spec hW1 hW4 hq_def_ctx (validG_nil ninQ) hqSum_in
    hloR_in hhiR_in hloB_in hhiB_in
    ⟨⟨by dsimp only [Sum8W.val, qSum]; rw [h2Wm3]; exact Nat.le_pred_of_lt (hqField_lt _ 0 hq_def_ctx),
      by dsimp only [Sum8W.val, qSum]; rw [h2Wm3]; exact Nat.le_pred_of_lt (hqField_lt _ 1 hq_def_ctx),
      by dsimp only [Sum8W.val, qSum]; rw [h2Wm3]; exact Nat.le_pred_of_lt (hqField_lt _ 2 hq_def_ctx),
      by dsimp only [Sum8W.val, qSum]; rw [h2Wm3]; exact Nat.le_pred_of_lt (hqField_lt _ 3 hq_def_ctx),
      by dsimp only [Sum8W.val, qSum]; rw [h2Wm3]; exact Nat.le_pred_of_lt (hqField_lt _ 4 hq_def_ctx),
      by dsimp only [Sum8W.val, qSum]; rw [h2Wm3]; exact Nat.le_pred_of_lt (hqField_lt _ 5 hq_def_ctx),
      by dsimp only [Sum8W.val, qSum]; rw [h2Wm3]; exact Nat.le_pred_of_lt (hqField_lt _ 6 hq_def_ctx),
      by dsimp only [Sum8W.val, qSum]; rw [h2Wm3]; exact Nat.le_pred_of_lt (hqField_lt _ 7 hq_def_ctx)⟩,
     by dsimp only [qLoR]; rw [h2Wm3]; exact hqField_lt _ 8 hq_def_ctx,
     by dsimp only [qHiR]; rw [h2Wm3]; exact hqField_lt _ 9 hq_def_ctx,
     by dsimp only [qLoB]; rw [h2Wm3]; exact hqField_lt _ 10 hq_def_ctx,
     by dsimp only [qHiB]; rw [h2Wm3]; exact hqField_lt _ 11 hq_def_ctx⟩
  rw [hq_eq] at hq_struct; dsimp only at hq_struct
  have hq_valid : ReadsBack ninQ queryC ∧ queryC.size ≤ 30000 * w ∧
      ∀ gate ∈ queryC.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
        (gate.op = .not ∧ gate.inputs.length = 1) :=
    validG_to_spec hq_struct.2.1 (by
      have hsz : qG.length ≤ 1100 * W := by simpa using hq_struct.2.2.1
      linarith only [hsz, hW_le])
  let flagFin : Fin (2 + 12 * w + queryC.size) := ⟨qFlag, hq_struct.2.2.2.1⟩
  let resFin : Bool → Fin w → Fin (2 + 12 * w + queryC.size) := fun b i =>
    if b then ⟨(cTruncW hwW qB) i, hq_struct.2.2.2.2.2.1 ⟨i.val, by omega⟩⟩
    else ⟨(cTruncW hwW qR) i, hq_struct.2.2.2.2.1 ⟨i.val, by omega⟩⟩
  refine ⟨queryC, flagFin, resFin, hq_valid, fun S_tot sumBits loR hiR loB hiB hS_bd hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 => ?_⟩
  set qIn := [false, true] ++ List.ofFn sumBits ++
    List.ofFn loR ++ List.ofFn hiR ++ List.ofFn loB ++ List.ofFn hiB
  have hqIn_len : qIn.length = ninQ := by simp [qIn, ninQ]; omega
  have hctxQ : Ctx ninQ qIn := ⟨hqIn_len, by omega, rfl, rfl⟩
  have hkw_lt : ∀ k < 8, ∀ i : Fin w, k * w + i.val < 8 * w := fun k hk i => by
    have hmul : (k + 1) * w ≤ 8 * w := Nat.mul_le_mul_right w hk
    rw [Nat.add_mul, one_mul] at hmul; omega
  have hqField_val_sum : ∀ k (hk : k < 8),
      wordVal [] qIn (qField k) =
        ∑ i : Fin w, (sumBits ⟨k * w + i.val, hkw_lt k hk i⟩).toNat * 2 ^ i.val := by
    intro k hk
    rw [hpad_eq qIn k hctxQ]
    unfold wordVal
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    unfold valAt evalW Circuit.wires qIn
    simp only [List.foldl_nil]
    have hkw : k * w + i.val < 8 * w := hkw_lt k hk i
    rw [append_getD_left false _ _ (by simp <;> omega), append_getD_left false _ _ (by simp <;> omega),
      append_getD_left false _ _ (by simp <;> omega), append_getD_left false _ _ (by simp <;> omega),
      append_getD_right false [false, true] _ (by simp <;> omega)]
    simp only [List.length_cons, List.length_nil, show 2 + k * w + i.val - 2 = k * w + i.val by omega]
    rw [list_ofFn_getD false _ _ hkw]
  have hqSum_val : qSum.val [] qIn = S_tot := by
    cases S_tot with
    | mk s0 s1 s2 s3 s4 s5 s6 s7 =>
      dsimp only [Sum8W.val, qSum]
      rw [hqField_val_sum 0 (by omega), hqField_val_sum 1 (by omega), hqField_val_sum 2 (by omega),
        hqField_val_sum 3 (by omega), hqField_val_sum 4 (by omega), hqField_val_sum 5 (by omega),
        hqField_val_sum 6 (by omega), hqField_val_sum 7 (by omega),
        hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  have hqDigit_val : ∀ (k : ℕ) (d : Fin w → Bool),
      (∀ i : Fin w, qIn.getD (2 + k * w + i.val) false = d i) →
      wordVal [] qIn (qField k) = ∑ i : Fin w, (d i).toNat * 2 ^ i.val := by
    intro k d hd
    rw [hpad_eq qIn k hctxQ]; unfold wordVal
    refine Finset.sum_congr rfl fun i _ => by congr 2; exact hd i
  have hloR_v : wordVal [] qIn qLoR = ∑ i : Fin w, (loR i).toNat * 2 ^ i.val := by
    refine hqDigit_val 8 loR fun i => ?_
    dsimp only [qIn]
    rw [append_getD_left false _ _ (by simp <;> omega), append_getD_left false _ _ (by simp <;> omega),
      append_getD_left false _ _ (by simp <;> omega), append_getD_right false _ _ (by simp <;> omega)]
    trans (List.ofFn loR).getD i.val false
    · congr 1; simp [w] <;> omega
    · exact list_ofFn_getD false loR i.val i.isLt
  have hhiR_v : wordVal [] qIn qHiR = ∑ i : Fin w, (hiR i).toNat * 2 ^ i.val := by
    refine hqDigit_val 9 hiR fun i => ?_
    dsimp only [qIn]
    rw [append_getD_left false _ _ (by simp <;> omega), append_getD_left false _ _ (by simp <;> omega),
      append_getD_right false _ _ (by simp <;> omega)]
    trans (List.ofFn hiR).getD i.val false
    · congr 1; simp [w] <;> omega
    · exact list_ofFn_getD false hiR i.val i.isLt
  have hloB_v : wordVal [] qIn qLoB = ∑ i : Fin w, (loB i).toNat * 2 ^ i.val := by
    refine hqDigit_val 10 loB fun i => ?_
    dsimp only [qIn]
    rw [append_getD_left false _ _ (by simp <;> omega), append_getD_right false _ _ (by simp <;> omega)]
    trans (List.ofFn loB).getD i.val false
    · congr 1; simp [w] <;> omega
    · exact list_ofFn_getD false loB i.val i.isLt
  have hhiB_v : wordVal [] qIn qHiB = ∑ i : Fin w, (hiB i).toNat * 2 ^ i.val := by
    refine hqDigit_val 11 hiB fun i => ?_
    dsimp only [qIn]
    rw [append_getD_right false _ _ (by simp <;> omega)]
    trans (List.ofFn hiB).getD i.val false
    · congr 1; simp [w] <;> omega
    · exact list_ofFn_getD false hiB i.val i.isLt
  have hq_run := cQuery_spec hW1 hW4 hctxQ (validG_nil ninQ) hqSum_in
    hloR_in hhiR_in hloB_in hhiB_in
    ⟨by rw [hqSum_val, h2Wm3]; exact Sum8.bound_mono hS_bd (by omega),
     by rw [hloR_v, h2Wm3]; exact value_lt_pow loR,
     by rw [hhiR_v, h2Wm3]; exact value_lt_pow hiR,
     by rw [hloB_v, h2Wm3]; exact value_lt_pow loB,
     by rw [hhiB_v, h2Wm3]; exact value_lt_pow hiB⟩
  rw [hq_eq] at hq_run; dsimp only at hq_run
  have hflag_eq : (queryC.wires qIn).getD flagFin.val false =
      (S_tot.query (∑ i : Fin w, (loR i).toNat * 2 ^ i.val) (∑ i : Fin w, (hiR i).toNat * 2 ^ i.val)
        (∑ i : Fin w, (loB i).toNat * 2 ^ i.val) (∑ i : Fin w, (hiB i).toNat * 2 ^ i.val)).1 := by
    have h := hq_run.2.2.2.2.2.2.1
    rw [hqSum_val, hloR_v, hhiR_v, hloB_v, hhiB_v] at h; exact h
  have hqR_eq : wordVal qG qIn qR =
      (S_tot.query (∑ i : Fin w, (loR i).toNat * 2 ^ i.val) (∑ i : Fin w, (hiR i).toNat * 2 ^ i.val)
        (∑ i : Fin w, (loB i).toNat * 2 ^ i.val) (∑ i : Fin w, (hiB i).toNat * 2 ^ i.val)).2.1 := by
    have h := hq_run.2.2.2.2.2.2.2.1
    rw [hqSum_val, hloR_v, hhiR_v, hloB_v, hhiB_v] at h; exact h
  have hqB_eq : wordVal qG qIn qB =
      (S_tot.query (∑ i : Fin w, (loR i).toNat * 2 ^ i.val) (∑ i : Fin w, (hiR i).toNat * 2 ^ i.val)
        (∑ i : Fin w, (loB i).toNat * 2 ^ i.val) (∑ i : Fin w, (hiB i).toNat * 2 ^ i.val)).2.2 := by
    have h := hq_run.2.2.2.2.2.2.2.2
    rw [hqSum_val, hloR_v, hhiR_v, hloB_v, hhiB_v] at h; exact h
  refine ⟨hflag_eq, fun hltR => ?_, fun hltB => ?_⟩
  · have htr := cTruncW_spec hwW qG qIn qR (by rw [hqR_eq]; exact hltR)
    rw [← hqR_eq, ← htr]; rfl
  · have htr := cTruncW_spec hwW qG qIn qB (by rw [hqB_eq]; exact hltB)
    rw [← hqB_eq, ← htr]; rfl

private lemma main_prep_bundle (n : ℕ) (M : Bool → Equiv.Perm (Fin n)) :
    let w := 1 + Nat.clog 2 (n + 1)
    let raw := fun x : Bool × Fin n → Bool =>
      List.ofFn (fun i : Fin n => x (false, i)) ++ List.ofFn (fun i : Fin n => x (true, i))
    ∃ (prep : Circuit) (summary : Fin (8 * w) → Fin (2 + 4 * n + prep.size)),
      (ReadsBack (2 + 4 * n) prep ∧ prep.size ≤ 30000 * (n + 1) * w ∧
        ∀ gate ∈ prep.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
          (gate.op = .not ∧ gate.inputs.length = 1)) ∧
      ∀ (pin bit : Bool × Fin n → Bool),
        let inputs := [false, true] ++ raw pin ++ raw bit
        let z := prep.wires inputs
        let sumBits := fun i : Fin (8 * w) => z.getD (summary i).val false
        let S_tot := pureListSum M pin bit (permCycles M)
        (∑ i : Fin w, (sumBits ⟨0 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.fr ∧
        (∑ i : Fin w, (sumBits ⟨1 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.fb ∧
        (∑ i : Fin w, (sumBits ⟨2 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.cr ∧
        (∑ i : Fin w, (sumBits ⟨3 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.cb ∧
        (∑ i : Fin w, (sumBits ⟨4 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.d00 ∧
        (∑ i : Fin w, (sumBits ⟨5 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.d11 ∧
        (∑ i : Fin w, (sumBits ⟨6 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.d01 ∧
        (∑ i : Fin w, (sumBits ⟨7 * w + i.val, by omega⟩).toNat * 2 ^ i.val) = S_tot.d10 := by
  dsimp only
  set w := 1 + Nat.clog 2 (n + 1)
  have hw1 : 1 ≤ w := by omega
  have hclog : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by decide) (n + 1)
  have h2w : 2 * (n + 1) ≤ 2 ^ w := by
    have : 2 ^ w = 2 * 2 ^ Nat.clog 2 (n + 1) := by rw [show w = Nat.clog 2 (n + 1) + 1 by omega, pow_succ]; ring
    omega
  set W := w + 3
  have hW1 : 1 ≤ W := by omega
  have hwW : w ≤ W := by omega
  have hW_le : W ≤ 4 * w := by omega
  have h2W : 2 ^ W = 8 * 2 ^ w := by rw [show W = w + 3 by omega, pow_add]; ring
  let cs := permCycles M
  have hcp := permCycles_props M
  have hcs_sum : (cs.map List.length).sum = n := hcp.2.2.2
  have hcs_len1 : ∀ c ∈ cs, 1 ≤ c.length := fun c hc => (hcp.1 c hc).1
  let ninP := 2 + 4 * n
  apply let_prod3 (cPrepSuf ninP hW1 M [] cs)
  intro pG pS pSuf hp_eq
  let prepC : Circuit := ⟨pG, 0⟩
  have hp_def_ctx := ctx_default (nin := ninP) (by omega)
  have hp_struct := cPrepSuf_spec hW1 M hp_def_ctx (validG_nil ninP)
    (fun v => ([false, true] ++ List.replicate (ninP - 2) false).getD (pinWire n v) false)
    (fun v => ([false, true] ++ List.replicate (ninP - 2) false).getD (bitWire n v) false)
    (fun v => ⟨by unfold pinWire; split_ifs <;> omega, rfl⟩)
    (fun v => ⟨by unfold bitWire; split_ifs <;> omega, rfl⟩) cs hcs_len1 (by omega)
  rw [hp_eq] at hp_struct; dsimp only at hp_struct
  have hp_valid : ReadsBack ninP prepC ∧ prepC.size ≤ 30000 * (n + 1) * w ∧
      ∀ gate ∈ prepC.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
        (gate.op = .not ∧ gate.inputs.length = 1) :=
    validG_to_spec hp_struct.2.1 (by
      have hsz : pG.length ≤ n * (1400 * W) := by simpa [hcs_sum] using hp_struct.2.2.1
      nlinarith)
  have hp_in := hp_struct.2.2.2.1
  unfold Sum8W.In at hp_in
  rcases hp_in with ⟨hpin_fr, hpin_fb, hpin_cr, hpin_cb, hpin_d00, hpin_d11, hpin_d01, hpin_d10⟩
  let summaryFin : Fin (8 * w) → Fin (2 + 4 * n + prepC.size) := fun idx =>
    let k := idx.val / w
    let b : Fin w := ⟨idx.val % w, Nat.mod_lt _ (by omega)⟩
    if k = 0 then ⟨(cTruncW hwW pS.fr) b, hpin_fr ⟨b.val, by omega⟩⟩
    else if k = 1 then ⟨(cTruncW hwW pS.fb) b, hpin_fb ⟨b.val, by omega⟩⟩
    else if k = 2 then ⟨(cTruncW hwW pS.cr) b, hpin_cr ⟨b.val, by omega⟩⟩
    else if k = 3 then ⟨(cTruncW hwW pS.cb) b, hpin_cb ⟨b.val, by omega⟩⟩
    else if k = 4 then ⟨(cTruncW hwW pS.d00) b, hpin_d00 ⟨b.val, by omega⟩⟩
    else if k = 5 then ⟨(cTruncW hwW pS.d11) b, hpin_d11 ⟨b.val, by omega⟩⟩
    else if k = 6 then ⟨(cTruncW hwW pS.d01) b, hpin_d01 ⟨b.val, by omega⟩⟩
    else ⟨(cTruncW hwW pS.d10) b, hpin_d10 ⟨b.val, by omega⟩⟩
  have hdiv : ∀ (k : ℕ) (i : Fin w), (k * w + i.val) / w = k ∧ (k * w + i.val) % w = i.val := fun k i =>
    ⟨by rw [Nat.mul_comm k w, Nat.mul_add_div (by omega), Nat.div_eq_of_lt i.isLt, Nat.add_zero],
     by rw [Nat.mul_comm k w, Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]⟩
  have hsum_val : ∀ (k : ℕ) (i : Fin w) (h : k * w + i.val < 8 * w),
      (summaryFin ⟨k * w + i.val, h⟩).val =
        if k = 0 then cTruncW hwW pS.fr i
        else if k = 1 then cTruncW hwW pS.fb i
        else if k = 2 then cTruncW hwW pS.cr i
        else if k = 3 then cTruncW hwW pS.cb i
        else if k = 4 then cTruncW hwW pS.d00 i
        else if k = 5 then cTruncW hwW pS.d11 i
        else if k = 6 then cTruncW hwW pS.d01 i
        else cTruncW hwW pS.d10 i := by
    intro k i h
    dsimp only [summaryFin]
    have hk_eq : (k * w + i.val) / w = k := (hdiv k i).1
    have hb_eq : (⟨(k * w + i.val) % w, Nat.mod_lt _ (by omega)⟩ : Fin w) = i := Fin.ext (hdiv k i).2
    simp only [hk_eq, hb_eq]
    split_ifs <;> rfl
  refine ⟨prepC, summaryFin, hp_valid, fun pin bit => ?_⟩
  set raw := fun x : Bool × Fin n → Bool =>
    List.ofFn (fun i : Fin n => x (false, i)) ++ List.ofFn (fun i : Fin n => x (true, i))
  set inputs := [false, true] ++ raw pin ++ raw bit
  have hraw_len : ∀ x : Bool × Fin n → Bool, (raw x).length = 2 * n := fun x => by simp [raw]; omega
  have hinputs_len : inputs.length = ninP := by simp [inputs, hraw_len, ninP]; omega
  have hctxP : Ctx ninP inputs := ⟨hinputs_len, by omega, rfl, rfl⟩
  have hpinW_inP : ∀ v : Bool × Fin n, pinWire n v < ninP ∧ valAt [] inputs (pinWire n v) = pin v := by
    intro ⟨b, i⟩
    refine ⟨by unfold pinWire; cases b <;> simp <;> omega, ?_⟩
    unfold valAt evalW Circuit.wires pinWire inputs raw
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, List.foldl_nil]
      rw [List.append_assoc, append_getD_right false [false, true] _ (by simp <;> omega)]
      simp only [List.length_cons, List.length_nil, show 2 + i.val - 2 = i.val by omega]
      rw [append_getD_left false _ _ (by simp <;> omega), append_getD_left false _ _ (by simp <;> omega),
        list_ofFn_getD false _ i.val i.isLt]
    · simp only [↓reduceIte, List.foldl_nil]
      rw [List.append_assoc, append_getD_right false [false, true] _ (by simp <;> omega)]
      simp only [List.length_cons, List.length_nil, show 2 + n + i.val - 2 = n + i.val by omega]
      rw [append_getD_left false _ _ (by simp <;> omega),
        append_getD_right false (List.ofFn _) _ (by simp <;> omega)]
      simp only [List.length_ofFn, show n + i.val - n = i.val by omega]
      rw [list_ofFn_getD false _ i.val i.isLt]
  have hbitW_inP : ∀ v : Bool × Fin n, bitWire n v < ninP ∧ valAt [] inputs (bitWire n v) = bit v := by
    intro ⟨b, i⟩
    refine ⟨by unfold bitWire; cases b <;> simp <;> omega, ?_⟩
    unfold valAt evalW Circuit.wires bitWire inputs raw
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, List.foldl_nil]
      rw [append_getD_right false ([false, true] ++ _) _ (by simp <;> omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
        show 2 + 2 * n + i.val - (2 + (n + n)) = i.val by omega]
      rw [append_getD_left false _ _ (by simp <;> omega), list_ofFn_getD false _ i.val i.isLt]
    · simp only [↓reduceIte, List.foldl_nil]
      rw [append_getD_right false ([false, true] ++ _) _ (by simp <;> omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
        show 2 + 3 * n + i.val - (2 + (n + n)) = n + i.val by omega]
      rw [append_getD_right false (List.ofFn _) _ (by simp <;> omega)]
      simp only [List.length_ofFn, show n + i.val - n = i.val by omega]
      rw [list_ofFn_getD false _ i.val i.isLt]
  have hp_run := cPrepSuf_spec hW1 M hctxP (validG_nil ninP) pin bit hpinW_inP hbitW_inP cs hcs_len1 (by omega)
  rw [hp_eq] at hp_run; dsimp only at hp_run
  have hS_cap : (pureListSum M pin bit cs).Cap n n := by
    simpa [hcs_sum] using (pureListSum_props M pin bit cs hcs_len1).2
  rcases Sum8.cap_bound hS_cap le_rfl le_rfl with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
  have hval_p := hp_run.2.2.2.2.1
  have htrunc_field : ∀ (fw : Word W) (hfw : wordVal pG inputs fw < 2 ^ w),
      (∑ i : Fin w, ((prepC.wires inputs).getD (cTruncW hwW fw i) false).toNat * 2 ^ i.val) =
        wordVal pG inputs fw := fun fw hfw => by
    have := cTruncW_spec hwW pG inputs fw hfw
    rw [← this]; rfl
  have hfr_eq : wordVal pG inputs pS.fr = (pureListSum M pin bit cs).fr := congrArg Sum8.fr hval_p
  have hfb_eq : wordVal pG inputs pS.fb = (pureListSum M pin bit cs).fb := congrArg Sum8.fb hval_p
  have hcr_eq : wordVal pG inputs pS.cr = (pureListSum M pin bit cs).cr := congrArg Sum8.cr hval_p
  have hcb_eq : wordVal pG inputs pS.cb = (pureListSum M pin bit cs).cb := congrArg Sum8.cb hval_p
  have hd00_eq : wordVal pG inputs pS.d00 = (pureListSum M pin bit cs).d00 := congrArg Sum8.d00 hval_p
  have hd11_eq : wordVal pG inputs pS.d11 = (pureListSum M pin bit cs).d11 := congrArg Sum8.d11 hval_p
  have hd01_eq : wordVal pG inputs pS.d01 = (pureListSum M pin bit cs).d01 := congrArg Sum8.d01 hval_p
  have hd10_eq : wordVal pG inputs pS.d10 = (pureListSum M pin bit cs).d10 := congrArg Sum8.d10 hval_p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hfr_eq, ← htrunc_field pS.fr (by omega)]
    refine Finset.sum_congr rfl fun i _ => congrArg (fun b => b.toNat * 2 ^ i.val)
      (congrArg (fun idx => (prepC.wires inputs).getD idx false) (hsum_val 0 i (by have := i.isLt; omega)))
  · rw [← hfb_eq, ← htrunc_field pS.fb (by omega)]
    refine Finset.sum_congr rfl fun i _ => congrArg (fun b => b.toNat * 2 ^ i.val)
      (congrArg (fun idx => (prepC.wires inputs).getD idx false) (hsum_val 1 i (by have := i.isLt; omega)))
  · rw [← hcr_eq, ← htrunc_field pS.cr (by omega)]
    refine Finset.sum_congr rfl fun i _ => congrArg (fun b => b.toNat * 2 ^ i.val)
      (congrArg (fun idx => (prepC.wires inputs).getD idx false) (hsum_val 2 i (by have := i.isLt; omega)))
  · rw [← hcb_eq, ← htrunc_field pS.cb (by omega)]
    refine Finset.sum_congr rfl fun i _ => congrArg (fun b => b.toNat * 2 ^ i.val)
      (congrArg (fun idx => (prepC.wires inputs).getD idx false) (hsum_val 3 i (by have := i.isLt; omega)))
  · rw [← hd00_eq, ← htrunc_field pS.d00 (by omega)]
    refine Finset.sum_congr rfl fun i _ => congrArg (fun b => b.toNat * 2 ^ i.val)
      (congrArg (fun idx => (prepC.wires inputs).getD idx false) (hsum_val 4 i (by have := i.isLt; omega)))
  · rw [← hd11_eq, ← htrunc_field pS.d11 (by omega)]
    refine Finset.sum_congr rfl fun i _ => congrArg (fun b => b.toNat * 2 ^ i.val)
      (congrArg (fun idx => (prepC.wires inputs).getD idx false) (hsum_val 5 i (by have := i.isLt; omega)))
  · rw [← hd01_eq, ← htrunc_field pS.d01 (by omega)]
    refine Finset.sum_congr rfl fun i _ => congrArg (fun b => b.toNat * 2 ^ i.val)
      (congrArg (fun idx => (prepC.wires inputs).getD idx false) (hsum_val 6 i (by have := i.isLt; omega)))
  · rw [← hd10_eq, ← htrunc_field pS.d10 (by omega)]
    refine Finset.sum_congr rfl fun i _ => congrArg (fun b => b.toNat * 2 ^ i.val)
      (congrArg (fun idx => (prepC.wires inputs).getD idx false) (hsum_val 7 i (by have := i.isLt; omega)))

private lemma main_build_bundle (n : ℕ) (M : Bool → Equiv.Perm (Fin n)) :
    let w := 1 + Nat.clog 2 (n + 1)
    let raw := fun x : Bool × Fin n → Bool =>
      List.ofFn (fun i : Fin n => x (false, i)) ++ List.ofFn (fun i : Fin n => x (true, i))
    ∃ (build : Circuit) (output : (Bool × Fin n) → Fin (2 + 4 * n + 2 * w + build.size)),
      (ReadsBack (2 + 4 * n + 2 * w) build ∧ build.size ≤ 30000 * (n + 1) * w ∧
        ∀ gate ∈ build.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
          (gate.op = .not ∧ gate.inputs.length = 1)) ∧
      ∀ (pin bit : Bool × Fin n → Bool) (readF readT : Fin w → Bool),
        let inputs := [false, true] ++ raw pin ++ raw bit
        let vR := ∑ i : Fin w, (readF i).toNat * 2 ^ i.val
        let vB := ∑ i : Fin w, (readT i).toNat * 2 ^ i.val
        vR ≤ n → vB ≤ n →
        (pureListSum M pin bit (permCycles M)).Mem vR vB →
        let ws := build.wires (inputs ++ List.ofFn readF ++ List.ofFn readT)
        let witness := fun v : Bool × Fin n => ws.getD (output v).val false
        (∀ v, pin v = true → witness v = bit v) ∧
        (Finset.univ.filter (fun i : Fin n => witness (false, i) ≠ witness (true, M false i))).card = vR ∧
        (Finset.univ.filter (fun i : Fin n => witness (false, i) ≠ witness (true, M true i))).card = vB := by
  dsimp only
  set w := 1 + Nat.clog 2 (n + 1)
  have hw1 : 1 ≤ w := by omega
  have hclog : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by decide) (n + 1)
  have h2w : 2 * (n + 1) ≤ 2 ^ w := by
    have : 2 ^ w = 2 * 2 ^ Nat.clog 2 (n + 1) := by rw [show w = Nat.clog 2 (n + 1) + 1 by omega, pow_succ]; ring
    omega
  set W := w + 3
  have hW1 : 1 ≤ W := by omega
  have hW3 : 3 ≤ W := by omega
  have hwW : w ≤ W := by omega
  have hW_le : W ≤ 4 * w := by omega
  have h2W : 2 ^ W = 8 * 2 ^ w := by rw [show W = w + 3 by omega, pow_add]; ring
  have h2Wm2 : 2 ^ (W - 2) = 2 * 2 ^ w := by rw [show W - 2 = w + 1 by omega, pow_add]; ring
  let cs := permCycles M
  have hcp := permCycles_props M
  have hcs_sum : (cs.map List.length).sum = n := hcp.2.2.2
  have hcs_len1 : ∀ c ∈ cs, 1 ≤ c.length := fun c hc => (hcp.1 c hc).1
  let ninB := 2 + 4 * n + 2 * w
  let bRemR0 : Word W := cPadW (fun i : Fin w => 2 + 4 * n + i.val)
  let bRemB0 : Word W := cPadW (fun i : Fin w => 2 + 4 * n + w + i.val)
  apply let_prod3 (cPrepSuf ninB hW1 M [] cs)
  intro bpG bpS bpSuf hbp_eq
  apply let_prod4 (cBuildWalk ninB hW1 M bpG bRemR0 bRemB0 (fun _ => 0) cs bpSuf)
  intro bwG bwR bwB bwOut hbw_eq
  let buildC : Circuit := ⟨bwG, 0⟩
  have hb_prep_def := cPrepSuf_spec hW1 M (ctx_default (nin := ninB) (by omega)) (validG_nil ninB)
    (fun v => ([false, true] ++ List.replicate (ninB - 2) false).getD (pinWire n v) false)
    (fun v => ([false, true] ++ List.replicate (ninB - 2) false).getD (bitWire n v) false)
    (fun v => ⟨by unfold pinWire; split_ifs <;> omega, rfl⟩)
    (fun v => ⟨by unfold bitWire; split_ifs <;> omega, rfl⟩) cs hcs_len1 (by omega)
  rw [hbp_eq] at hb_prep_def; dsimp only at hb_prep_def
  have hb_walk_def : ValidG ninB bwG ∧
      bwG.length ≤ bpG.length + (cs.map List.length).sum * (3100 * W) ∧
      ∀ v : Bool × Fin n, bwOut v < ninB + bwG.length := by
    let x0 : List Bool := [false, true] ++ List.replicate (4 * n + 2 * w) false
    have hx0 : Ctx ninB x0 := ⟨by simp [x0, ninB]; omega, by omega, rfl, rfl⟩
    have hx0_ge2 : ∀ k, 2 ≤ k → valAt [] x0 k = false := fun k hk => by
      unfold valAt evalW Circuit.wires x0
      simp only [List.foldl_nil]
      rw [append_getD_right false [false, true] _ (by simp <;> omega)]
      simp only [List.length_cons, List.length_nil, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> rfl
    have hp0 : ∀ v : Bool × Fin n, pinWire n v < ninB ∧ valAt [] x0 (pinWire n v) = false := fun v =>
      ⟨by unfold pinWire; split_ifs <;> omega, hx0_ge2 _ (by unfold pinWire; split_ifs <;> omega)⟩
    have hb0 : ∀ v : Bool × Fin n, bitWire n v < ninB ∧ valAt [] x0 (bitWire n v) = false := fun v =>
      ⟨by unfold bitWire; split_ifs <;> omega, hx0_ge2 _ (by unfold bitWire; split_ifs <;> omega)⟩
    have hbp0 := cPrepSuf_spec hW1 M hx0 (validG_nil ninB) (fun _ => false) (fun _ => false) hp0 hb0 cs hcs_len1 (by omega)
    rw [hbp_eq] at hbp0; dsimp only at hbp0
    have hmem0 : (pureListSum M (fun _ => false) (fun _ => false) cs).Mem 0 0 := by
      have hsnd := pureListSum_sound M (fun _ => false) (fun _ => false) (fun _ => false)
        (fun _ h => by cases h) cs (fun c hc => ⟨(hcp.1 c hc).1, (hcp.1 c hc).2.2⟩)
      have hr0 : (cs.map (fun c => cycRedCount M c (fun _ => false))).sum = 0 := by
        rw [List.sum_eq_zero_iff]; intro y hy
        rcases List.mem_map.mp hy with ⟨c, _, rfl⟩
        unfold cycRedCount; rw [List.sum_eq_zero_iff]; intro z hz
        rcases List.mem_map.mp hz with ⟨i, _, rfl⟩; rfl
      have hb0' : (cs.map (fun c => cycBlueCount M c (fun _ => false))).sum = 0 := by
        rw [List.sum_eq_zero_iff]; intro y hy
        rcases List.mem_map.mp hy with ⟨c, _, rfl⟩
        unfold cycBlueCount; rw [List.sum_eq_zero_iff]; intro z hz
        rcases List.mem_map.mp hz with ⟨i, _, rfl⟩; rfl
      rw [hr0, hb0'] at hsnd; exact hsnd
    have hremR_in : WordIn (ninB + bpG.length) bRemR0 := fun i => by
      dsimp only [bRemR0, cPadW, ninB]; split_ifs <;> omega
    have hremB_in : WordIn (ninB + bpG.length) bRemB0 := fun i => by
      dsimp only [bRemB0, cPadW, ninB]; split_ifs <;> omega
    have hremR_v0 : wordVal bpG x0 bRemR0 = 0 := by
      rw [wordVal_ext hx0.hlen hbp0.1 (fun i => by dsimp [bRemR0, cPadW, ninB]; split_ifs <;> omega)]
      unfold wordVal bRemR0 cPadW; refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with hi
      · rw [hx0_ge2 (2 + 4 * n + i.val) (by omega)]; simp
      · simp [valAt_zero hx0]
    have hremB_v0 : wordVal bpG x0 bRemB0 = 0 := by
      rw [wordVal_ext hx0.hlen hbp0.1 (fun i => by dsimp [bRemB0, cPadW, ninB]; split_ifs <;> omega)]
      unfold wordVal bRemB0 cPadW; refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with hi
      · rw [hx0_ge2 (2 + 4 * n + w + i.val) (by omega)]; simp
      · simp [valAt_zero hx0]
    have hbw0 := cBuildWalk_spec hW1 hW3 M hx0 (fun _ => false) (fun _ => false) hp0 hb0
      cs bpSuf bpG bRemR0 bRemB0 (fun _ => 0) hbp0.2.1 hcp.1 hcp.2.1 hbp0.2.2.2.2.2.1
      hbp0.2.2.2.2.2.2 hremR_in hremB_in (fun _ => by omega) (by omega)
      (by rw [hremR_v0]; omega) (by rw [hremB_v0]; omega) (by rw [hremR_v0, hremB_v0]; exact hmem0)
    rw [hbw_eq] at hbw0; dsimp only at hbw0
    exact ⟨hbw0.2.1, hbw0.2.2.1, hbw0.2.2.2.1⟩
  have hb_valid : ReadsBack ninB buildC ∧ buildC.size ≤ 30000 * (n + 1) * w ∧
      ∀ gate ∈ buildC.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
        (gate.op = .not ∧ gate.inputs.length = 1) :=
    validG_to_spec hb_walk_def.1 (by
      have hsz1 : bpG.length ≤ n * (1400 * W) := by simpa [hcs_sum] using hb_prep_def.2.2.1
      have hsz2 : bwG.length ≤ bpG.length + n * (3100 * W) := by simpa [hcs_sum] using hb_walk_def.2.1
      nlinarith)
  let outputFin : Bool × Fin n → Fin (2 + 4 * n + 2 * w + buildC.size) :=
    fun v => ⟨bwOut v, hb_walk_def.2.2 v⟩
  refine ⟨buildC, outputFin, hb_valid, fun pin bit readF readT hvR hvB hmem => ?_⟩
  set raw := fun x : Bool × Fin n → Bool =>
    List.ofFn (fun i : Fin n => x (false, i)) ++ List.ofFn (fun i : Fin n => x (true, i))
  set inputs := [false, true] ++ raw pin ++ raw bit
  set bIn := inputs ++ List.ofFn readF ++ List.ofFn readT
  have hraw_len : ∀ x : Bool × Fin n → Bool, (raw x).length = 2 * n := fun x => by simp [raw]; omega
  have hinputs_len : inputs.length = 2 + 4 * n := by simp [inputs, hraw_len]; omega
  have hbIn_len : bIn.length = ninB := by simp [bIn, hinputs_len, ninB]; omega
  have hctxB : Ctx ninB bIn := ⟨hbIn_len, by omega, by simp [bIn, inputs], by simp [bIn, inputs]⟩
  have hpinW_B : ∀ v : Bool × Fin n, pinWire n v < ninB ∧ valAt [] bIn (pinWire n v) = pin v := by
    intro ⟨b, i⟩
    refine ⟨by unfold pinWire; cases b <;> simp [ninB] <;> omega, ?_⟩
    unfold valAt evalW Circuit.wires bIn pinWire inputs raw
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, List.foldl_nil]
      rw [append_getD_left false _ _ (by simp [hinputs_len] <;> omega),
        append_getD_left false _ _ (by simp [hinputs_len] <;> omega),
        List.append_assoc, append_getD_right false [false, true] _ (by simp <;> omega)]
      simp only [List.length_cons, List.length_nil, show 2 + i.val - 2 = i.val by omega]
      rw [append_getD_left false _ _ (by simp <;> omega), append_getD_left false _ _ (by simp <;> omega),
        list_ofFn_getD false _ i.val i.isLt]
    · simp only [↓reduceIte, List.foldl_nil]
      rw [append_getD_left false _ _ (by simp [hinputs_len] <;> omega),
        append_getD_left false _ _ (by simp [hinputs_len] <;> omega),
        List.append_assoc, append_getD_right false [false, true] _ (by simp <;> omega)]
      simp only [List.length_cons, List.length_nil, show 2 + n + i.val - 2 = n + i.val by omega]
      rw [append_getD_left false _ _ (by simp <;> omega),
        append_getD_right false (List.ofFn _) _ (by simp <;> omega)]
      simp only [List.length_ofFn, show n + i.val - n = i.val by omega]
      rw [list_ofFn_getD false _ i.val i.isLt]
  have hbitW_B : ∀ v : Bool × Fin n, bitWire n v < ninB ∧ valAt [] bIn (bitWire n v) = bit v := by
    intro ⟨b, i⟩
    refine ⟨by unfold bitWire; cases b <;> simp [ninB] <;> omega, ?_⟩
    unfold valAt evalW Circuit.wires bIn bitWire inputs raw
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, List.foldl_nil]
      rw [append_getD_left false _ _ (by simp [hinputs_len] <;> omega),
        append_getD_left false _ _ (by simp [hinputs_len] <;> omega),
        append_getD_right false ([false, true] ++ _) _ (by simp <;> omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
        show 2 + 2 * n + i.val - (2 + (n + n)) = i.val by omega]
      rw [append_getD_left false _ _ (by simp <;> omega), list_ofFn_getD false _ i.val i.isLt]
    · simp only [↓reduceIte, List.foldl_nil]
      rw [append_getD_left false _ _ (by simp [hinputs_len] <;> omega),
        append_getD_left false _ _ (by simp [hinputs_len] <;> omega),
        append_getD_right false ([false, true] ++ _) _ (by simp <;> omega)]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_ofFn,
        show 2 + 3 * n + i.val - (2 + (n + n)) = n + i.val by omega]
      rw [append_getD_right false (List.ofFn _) _ (by simp <;> omega)]
      simp only [List.length_ofFn, show n + i.val - n = i.val by omega]
      rw [list_ofFn_getD false _ i.val i.isLt]
  have hbp_run := cPrepSuf_spec hW1 M hctxB (validG_nil ninB) pin bit hpinW_B hbitW_B cs hcs_len1 (by omega)
  rw [hbp_eq] at hbp_run; dsimp only at hbp_run
  have hremR_in : WordIn (ninB + bpG.length) bRemR0 := fun i => by
    dsimp only [bRemR0, cPadW, ninB]; split_ifs <;> omega
  have hremB_in : WordIn (ninB + bpG.length) bRemB0 := fun i => by
    dsimp only [bRemB0, cPadW, ninB]; split_ifs <;> omega
  have hremR_v : wordVal bpG bIn bRemR0 = ∑ i : Fin w, (readF i).toNat * 2 ^ i.val := by
    rw [wordVal_ext hctxB.hlen hbp_run.1 (fun i => by dsimp [bRemR0, cPadW, ninB]; split_ifs <;> omega)]
    have hpad_eq : wordVal [] bIn bRemR0 = wordVal [] bIn (fun i : Fin w => 2 + 4 * n + i.val) := by
      dsimp only [bRemR0]; unfold wordVal cPadW
      rw [← Finset.sum_subset (s₁ := (Finset.univ : Finset (Fin w)).image (fun i : Fin w => (⟨i.val, by omega⟩ : Fin W)))
        (Finset.subset_univ _)]
      · rw [Finset.sum_image (fun i _ j _ h => Fin.ext (by simpa using congrArg Fin.val h))]
        refine Finset.sum_congr rfl fun i _ => by simp
      · intro i _ hni
        have hge : ¬ i.val < w := fun hlt =>
          hni (Finset.mem_image.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        simp [hge, valAt_zero hctxB]
    rw [hpad_eq]; unfold wordVal
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2; unfold valAt evalW Circuit.wires bIn; simp only [List.foldl_nil]
    rw [append_getD_left false _ _ (by simp [hinputs_len] <;> omega),
      append_getD_right false _ _ (by simp [hinputs_len] <;> omega)]
    simp only [hinputs_len, show 2 + 4 * n + i.val - (2 + 4 * n) = i.val by omega]
    exact list_ofFn_getD false readF i.val i.isLt
  have hremB_v : wordVal bpG bIn bRemB0 = ∑ i : Fin w, (readT i).toNat * 2 ^ i.val := by
    rw [wordVal_ext hctxB.hlen hbp_run.1 (fun i => by dsimp [bRemB0, cPadW, ninB]; split_ifs <;> omega)]
    have hpad_eq : wordVal [] bIn bRemB0 = wordVal [] bIn (fun i : Fin w => 2 + 4 * n + w + i.val) := by
      dsimp only [bRemB0]; unfold wordVal cPadW
      rw [← Finset.sum_subset (s₁ := (Finset.univ : Finset (Fin w)).image (fun i : Fin w => (⟨i.val, by omega⟩ : Fin W)))
        (Finset.subset_univ _)]
      · rw [Finset.sum_image (fun i _ j _ h => Fin.ext (by simpa using congrArg Fin.val h))]
        refine Finset.sum_congr rfl fun i _ => by simp
      · intro i _ hni
        have hge : ¬ i.val < w := fun hlt =>
          hni (Finset.mem_image.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        simp [hge, valAt_zero hctxB]
    rw [hpad_eq]; unfold wordVal
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2; unfold valAt evalW Circuit.wires bIn; simp only [List.foldl_nil]
    rw [append_getD_right false _ _ (by simp [hinputs_len] <;> omega)]
    simp only [List.length_append, hinputs_len, List.length_ofFn,
      show 2 + 4 * n + w + i.val - (2 + 4 * n + w) = i.val by omega]
    exact list_ofFn_getD false readT i.val i.isLt
  have hbw_run := cBuildWalk_spec hW1 hW3 M hctxB pin bit hpinW_B hbitW_B
    cs bpSuf bpG bRemR0 bRemB0 (fun _ => 0) hbp_run.2.1 hcp.1 hcp.2.1
    hbp_run.2.2.2.2.2.1 hbp_run.2.2.2.2.2.2 hremR_in hremB_in (fun _ => by omega)
    (by omega) (by rw [hremR_v]; omega) (by rw [hremB_v]; omega)
    (by rw [hremR_v, hremB_v]; exact hmem)
  rw [hbw_eq] at hbw_run; dsimp only at hbw_run
  set witness := fun v : Bool × Fin n => (buildC.wires bIn).getD (outputFin v).val false
  have hwit_eq : witness = fun v => valAt bwG bIn (bwOut v) := rfl
  have hcnt_wit := count_eq_sum_cyc M witness
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨b, i⟩ hpv
    cases b
    · rcases List.mem_flatten.mp (hcp.2.2.1 i) with ⟨c, hc, hi_c⟩
      rcases List.mem_iff_get.mp hi_c with ⟨⟨t, ht⟩, rfl⟩
      have hveq : cycVert M c (2 * t) (by omega) = (false, c.get ⟨t, ht⟩) := by
        unfold cycVert; simp [show 2 * t % 2 = 0 by omega, show 2 * t / 2 = t by omega]
      rw [← hveq] at hpv ⊢
      exact hbw_run.2.2.2.2.2.1 c hc (2 * t) (by omega) hpv
    · let i' := (M false).symm i
      rcases List.mem_flatten.mp (hcp.2.2.1 i') with ⟨c, hc, hi_c⟩
      rcases List.mem_iff_get.mp hi_c with ⟨⟨t, ht⟩, hct⟩
      have hveq : cycVert M c (2 * t + 1) (by omega) = (true, i) := by
        unfold cycVert
        simp only [show (2 * t + 1) % 2 ≠ 0 by omega, ↓reduceIte, show (2 * t + 1) / 2 = t by omega]
        rw [hct]; simp [i']
      rw [← hveq] at hpv ⊢
      exact hbw_run.2.2.2.2.2.1 c hc (2 * t + 1) (by omega) hpv
  · rw [hcnt_wit.1, hwit_eq]
    change (cs.map (fun c => cycRedCount M c (fun v => valAt bwG bIn (bwOut v)))).sum = _
    rw [← hbw_run.2.2.2.2.2.2.2.2.1, hremR_v]
  · rw [hcnt_wit.2, hwit_eq]
    change (cs.map (fun c => cycBlueCount M c (fun v => valAt bwG bIn (bwOut v)))).sum = _
    rw [← hbw_run.2.2.2.2.2.2.2.2.2, hremB_v]

theorem main_proof :
∃ C : ℕ, 0 < C ∧ ∀ n : ℕ,
  let w := 1 + Nat.clog 2 (n+1)
  let V := Bool × Fin n
  let X := V → Bool
  let Digits := Fin w → Bool
  let value := fun (d : Digits) => ∑ i : Fin w, (d i).toNat * 2^i.val
  let raw := fun x : X => List.ofFn (fun i : Fin n => x (false,i)) ++
    List.ofFn (fun i : Fin n => x (true,i))
  let valid := fun (inputs budget : ℕ) (g : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs g ∧ g.size ≤ budget ∧
    ∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1)
  ∃ (query : PEqualNP.CircuitLowerBounds.Circuit) (flag : Fin (2+12*w+query.size))
    (result : Bool → Fin w → Fin (2+12*w+query.size)),
    valid (2+12*w) (C*w) query ∧
    ∀ M : Bool → Equiv.Perm (Fin n),
      ∃ (prep build : PEqualNP.CircuitLowerBounds.Circuit)
        (summary : Fin (8*w) → Fin (2+4*n+prep.size))
        (output : V → Fin (2+4*n+2*w+build.size)),
        valid (2+4*n) (C*(n+1)*w) prep ∧
        valid (2+4*n+2*w) (C*(n+1)*w) build ∧
        ∀ (pin bit : X) (loR hiR loB hiB : Digits),
          let inputs := [false,true] ++ raw pin ++ raw bit
          let z := prep.wires inputs
          let qs := query.wires ([false,true] ++ List.ofFn (fun i => z.getD (summary i).val false) ++
            List.ofFn loR ++ List.ofFn hiR ++ List.ofFn loB ++ List.ofFn hiB)
          let read := fun (j : Bool) (i : Fin w) => qs.getD (result j i).val false
          let ws := build.wires (inputs ++ List.ofFn (read false) ++ List.ofFn (read true))
          let witness := fun v : V => ws.getD (output v).val false
          let count := fun (x : X) (j : Bool) => (Finset.univ.filter (fun i : Fin n =>
            x (false,i) ≠ x (true,M j i))).card
          let ok := fun x : X => (∀ v, pin v = true → x v = bit v) ∧
            value loR ≤ count x false ∧ count x false ≤ value hiR ∧
            value loB ≤ count x true ∧ count x true ≤ value hiB
          (qs.getD flag.val false = true ↔ ∃ x : X, ok x) ∧
          (qs.getD flag.val false = true →
            ok witness ∧ count witness false = value (read false) ∧
            count witness true = value (read true) ∧
            ∀ x : X, ok x → count witness false < count x false ∨
              (count witness false = count x false ∧ count witness true ≤ count x true)) := by
  refine ⟨30000, by decide, fun n => ?_⟩
  dsimp only
  set w := 1 + Nat.clog 2 (n + 1)
  have hclog : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by decide) (n + 1)
  have h2w : 2 * (n + 1) ≤ 2 ^ w := by
    have : 2 ^ w = 2 * 2 ^ Nat.clog 2 (n + 1) := by rw [show w = Nat.clog 2 (n + 1) + 1 by omega, pow_succ]; ring
    omega
  rcases main_query_bundle n with ⟨queryC, flagFin, resFin, hq_valid, hq_eval⟩
  refine ⟨queryC, flagFin, resFin, hq_valid, fun M => ?_⟩
  rcases main_prep_bundle n M with ⟨prepC, summaryFin, hp_valid, hp_eval⟩
  rcases main_build_bundle n M with ⟨buildC, outputFin, hb_valid, hb_eval⟩
  refine ⟨prepC, buildC, summaryFin, outputFin, hp_valid, hb_valid, fun pin bit loR hiR loB hiB => ?_⟩
  have hcp := permCycles_props M
  have hcs_sum : ((permCycles M).map List.length).sum = n := hcp.2.2.2
  have hcs_len1 : ∀ c ∈ permCycles M, 1 ≤ c.length := fun c hc => (hcp.1 c hc).1
  set S_tot := pureListSum M pin bit (permCycles M)
  have hS_props := pureListSum_props M pin bit (permCycles M) hcs_len1
  have hS_good : S_tot.Good := hS_props.1
  have hS_cap : S_tot.Cap n n := by simpa [hcs_sum] using hS_props.2
  have hS_bd : S_tot.Bound n := Sum8.cap_bound hS_cap le_rfl le_rfl
  let sumBits : Fin (8 * w) → Bool := fun i =>
    (prepC.wires ([false, true] ++
      (List.ofFn (fun i : Fin n => pin (false, i)) ++ List.ofFn (fun i : Fin n => pin (true, i))) ++
      (List.ofFn (fun i : Fin n => bit (false, i)) ++ List.ofFn (fun i : Fin n => bit (true, i))))).getD (summaryFin i).val false
  rcases hp_eval pin bit with ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩
  rcases hq_eval S_tot sumBits loR hiR loB hiB hS_bd hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 with ⟨hflag_eq, hqR_read, hqB_read⟩
  set vLoR := ∑ i : Fin w, (loR i).toNat * 2 ^ i.val
  set vHiR := ∑ i : Fin w, (hiR i).toNat * 2 ^ i.val
  set vLoB := ∑ i : Fin w, (loB i).toNat * 2 ^ i.val
  set vHiB := ∑ i : Fin w, (hiB i).toNat * 2 ^ i.val
  have hqs_spec := Sum8.query_spec hS_good vLoR vHiR vLoB vHiB
  have hbuild_of_flag :
      (queryC.wires ([false, true] ++
        List.ofFn sumBits ++
        List.ofFn loR ++ List.ofFn hiR ++ List.ofFn loB ++ List.ofFn hiB)).getD flagFin.val false = true →
      let qs := queryC.wires ([false, true] ++
        List.ofFn sumBits ++
        List.ofFn loR ++ List.ofFn hiR ++ List.ofFn loB ++ List.ofFn hiB)
      let read := fun (j : Bool) (i : Fin w) => qs.getD (resFin j i).val false
      let ws := buildC.wires (([false, true] ++
          (List.ofFn (fun i : Fin n => pin (false, i)) ++ List.ofFn (fun i : Fin n => pin (true, i))) ++
          (List.ofFn (fun i : Fin n => bit (false, i)) ++ List.ofFn (fun i : Fin n => bit (true, i)))) ++
        List.ofFn (read false) ++ List.ofFn (read true))
      let witness := fun v : Bool × Fin n => ws.getD (outputFin v).val false
      (∀ v, pin v = true → witness v = bit v) ∧
      (Finset.univ.filter (fun i : Fin n => witness (false, i) ≠ witness (true, M false i))).card =
        (S_tot.query vLoR vHiR vLoB vHiB).2.1 ∧
      (Finset.univ.filter (fun i : Fin n => witness (false, i) ≠ witness (true, M true i))).card =
        (S_tot.query vLoR vHiR vLoB vHiB).2.2 ∧
      (∑ i : Fin w, (read false i).toNat * 2 ^ i.val) = (S_tot.query vLoR vHiR vLoB vHiB).2.1 ∧
      (∑ i : Fin w, (read true i).toNat * 2 ^ i.val) = (S_tot.query vLoR vHiR vLoB vHiB).2.2 := by
    intro hfl
    rw [hflag_eq] at hfl
    have hq_ok := hqs_spec.2 hfl
    have hqR_le : (S_tot.query vLoR vHiR vLoB vHiB).2.1 ≤ n := by
      have := hq_ok.1.2.1; have := hS_cap.1; omega
    have hqB_le : (S_tot.query vLoR vHiR vLoB vHiB).2.2 ≤ n := by
      have := hq_ok.1.2.2.2.1; have := hS_cap.2.1; omega
    have hrf := hqR_read (lt_of_le_of_lt hqR_le (by change n < 2 ^ w; omega))
    have hrt := hqB_read (lt_of_le_of_lt hqB_le (by change n < 2 ^ w; omega))
    rcases hb_eval pin bit _ _ (by rw [hrf]; exact hqR_le) (by rw [hrt]; exact hqB_le)
      (by rw [hrf, hrt]; exact hq_ok.1) with ⟨hwp, hwr, hwb⟩
    exact ⟨hwp, hwr.trans hrf, hwb.trans hrt, hrf, hrt⟩
  constructor
  · constructor
    · intro hfl
      rcases hbuild_of_flag hfl with ⟨hw_pin, hw_r, hw_b, _, _⟩
      rw [hflag_eq] at hfl
      have hq_ok := hqs_spec.2 hfl
      exact ⟨_, hw_pin, hw_r.symm ▸ hq_ok.2.1, hw_r.symm ▸ hq_ok.2.2.1,
        hw_b.symm ▸ hq_ok.2.2.2.1, hw_b.symm ▸ hq_ok.2.2.2.2.1⟩
    · rintro ⟨x, hxp, hxr1, hxr2, hxb1, hxb2⟩
      rw [hflag_eq, hqs_spec.1]
      have hcnt_x := count_eq_sum_cyc M x
      have hmem_x := pureListSum_sound M pin bit x hxp (permCycles M)
        (fun c hc => ⟨(hcp.1 c hc).1, (hcp.1 c hc).2.2⟩)
      rw [← hcnt_x.1, ← hcnt_x.2] at hmem_x
      exact ⟨_, _, hmem_x, hxr1, hxr2, hxb1, hxb2⟩
  · intro hfl
    rcases hbuild_of_flag hfl with ⟨hw_pin, hw_r, hw_b, hrf, hrt⟩
    rw [hflag_eq] at hfl
    have hq_ok := hqs_spec.2 hfl
    refine ⟨⟨hw_pin, hw_r.symm ▸ hq_ok.2.1, hw_r.symm ▸ hq_ok.2.2.1,
      hw_b.symm ▸ hq_ok.2.2.2.1, hw_b.symm ▸ hq_ok.2.2.2.2.1⟩,
      hw_r.trans hrf.symm, hw_b.trans hrt.symm, ?_⟩
    intro x ⟨hxp, hxr1, hxr2, hxb1, hxb2⟩
    have hcnt_x := count_eq_sum_cyc M x
    have hmem_x := pureListSum_sound M pin bit x hxp (permCycles M)
      (fun c hc => ⟨(hcp.1 c hc).1, (hcp.1 c hc).2.2⟩)
    rw [← hcnt_x.1, ← hcnt_x.2] at hmem_x
    rw [hw_r, hw_b]
    exact hq_ok.2.2.2.2.2 _ _ hmem_x hxr1 hxr2 hxb1 hxb2

end PEqualNP.Outside.L_pcx_353

theorem PEqualNP.Outside.L_pcx_353 :
∃ C : ℕ, 0 < C ∧ ∀ n : ℕ,
  let w := 1 + Nat.clog 2 (n+1)
  let V := Bool × Fin n
  let X := V → Bool
  let Digits := Fin w → Bool
  let value := fun (d : Digits) => ∑ i : Fin w, (d i).toNat * 2^i.val
  let raw := fun x : X => List.ofFn (fun i : Fin n => x (false,i)) ++
    List.ofFn (fun i : Fin n => x (true,i))
  let valid := fun (inputs budget : ℕ) (g : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs g ∧ g.size ≤ budget ∧
    ∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1)
  ∃ (query : PEqualNP.CircuitLowerBounds.Circuit) (flag : Fin (2+12*w+query.size))
    (result : Bool → Fin w → Fin (2+12*w+query.size)),
    valid (2+12*w) (C*w) query ∧
    ∀ M : Bool → Equiv.Perm (Fin n),
      ∃ (prep build : PEqualNP.CircuitLowerBounds.Circuit)
        (summary : Fin (8*w) → Fin (2+4*n+prep.size))
        (output : V → Fin (2+4*n+2*w+build.size)),
        valid (2+4*n) (C*(n+1)*w) prep ∧
        valid (2+4*n+2*w) (C*(n+1)*w) build ∧
        ∀ (pin bit : X) (loR hiR loB hiB : Digits),
          let inputs := [false,true] ++ raw pin ++ raw bit
          let z := prep.wires inputs
          let qs := query.wires ([false,true] ++ List.ofFn (fun i => z.getD (summary i).val false) ++
            List.ofFn loR ++ List.ofFn hiR ++ List.ofFn loB ++ List.ofFn hiB)
          let read := fun (j : Bool) (i : Fin w) => qs.getD (result j i).val false
          let ws := build.wires (inputs ++ List.ofFn (read false) ++ List.ofFn (read true))
          let witness := fun v : V => ws.getD (output v).val false
          let count := fun (x : X) (j : Bool) => (Finset.univ.filter (fun i : Fin n =>
            x (false,i) ≠ x (true,M j i))).card
          let ok := fun x : X => (∀ v, pin v = true → x v = bit v) ∧
            value loR ≤ count x false ∧ count x false ≤ value hiR ∧
            value loB ≤ count x true ∧ count x true ≤ value hiB
          (qs.getD flag.val false = true ↔ ∃ x : X, ok x) ∧
          (qs.getD flag.val false = true →
            ok witness ∧ count witness false = value (read false) ∧
            count witness true = value (read true) ∧
            ∀ x : X, ok x → count witness false < count x false ∨
              (count witness false = count x false ∧ count witness true ≤ count x true)) :=
  PEqualNP.Outside.L_pcx_353.main_proof
