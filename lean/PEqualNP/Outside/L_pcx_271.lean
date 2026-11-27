import Mathlib
import PEqualNP.Defs

-- Code constructions and circuit lemmas adapted from the checked file
-- lean/PEqualNP/Outside/L_pcx_257.lean at 580e3b9ec0d1ed10dae6aaf42d3c55dcfeb2949e.
-- The source tape now pairs the left port and suffix using ordered concatenation.

namespace PEqualNP.Outside.L_pcx_271_aux
section Part1

def Code257 (n k c : ℕ) (first : (Fin n → Bool) → Fin k → Bool) (gateBound : Option ℕ) : Prop :=
  let len := fun e : Fin 3 => if e = 2 then c else k
  let Word := Fin n → Bool
  let valid := fun (inputs limit : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧ C.size ≤ limit ∧
    ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)
  ∃ code : Word → (e : Fin 3) → Fin (len e) → Bool,
    (∀ u : Word, code u 0 = first u) ∧
    (∀ v : Fin 3 → Word, (∀ e : Fin 3, code (v e) e = code (v (e+1)) e) →
      ∀ p : Fin 3, v p = v 0) ∧
    ∀ limit : ℕ, gateBound = some limit →
      (∃ (enc : PEqualNP.CircuitLowerBounds.Circuit)
        (tap : (e : Fin 3) → Fin (len e) → Fin (n+enc.size)),
        valid n limit enc ∧ ∀ (u : Word) (e : Fin 3) (j : Fin (len e)),
          (enc.wires (List.ofFn u)).getD (tap e j).val false = code u e j) ∧
      ∀ e : Fin 3,
        let w := len e + len (e+1)
        ∃ (dec : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin n → Fin (w+dec.size)),
          valid w limit dec ∧ ∀ (u : Word) (j : Fin n),
            (dec.wires (List.ofFn (code u e) ++ List.ofFn (code u (e+1)))).getD
              (out j).val false = u j

end Part1
section Part2

structure Params257 (k : ℕ) where
  b : ℕ
  s : ℕ
  m : ℕ
  r : ℕ
  T : ℕ
  L : ℕ
  b_pos : 1 ≤ b
  s_pos : 1 ≤ s
  m_pos : 1 ≤ m
  k_pos : 1 ≤ k
  b_le_s : b ≤ s
  split : k = m*b+r
  s_le_r : s ≤ r
  m_le_pow : m ≤ 2^s
  k_le_pow : k ≤ 2^s
  size_lt : m*(2^b)^2 < 2^(3*s+3)
  threshold : 2*m*(2^b)^4 ≤ T^2
  L_eq : L = 2*(4*T*b+1)*(Nat.log2 (m*b+1)+2)

abbrev Params257.q {k : ℕ} (p : Params257 k) : ℕ := 2^p.b
abbrev Params257.lN {k : ℕ} (p : Params257 k) : ℕ := 3*p.s+3
abbrev Params257.H {k : ℕ} (p : Params257 k) : ℕ := 4*p.T*p.b
abbrev Params257.width {k : ℕ} (p : Params257 k) : ℕ :=
  p.m*(p.b+1)+2*p.r+p.lN+p.L

private theorem params257_linear_le_pow (b : ℕ) (hb : 32 ≤ b) :
    32*(b+1)+3 ≤ 2^b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
  clear hb
  induction d with
  | zero => decide
  | succ d ih =>
    rw [show 32+(d+1)=(32+d)+1 by omega, pow_succ]
    omega


theorem params257_exists :
    ∃ A0 C K : ℕ, ∀ k ≥ K, ∃ p : Params257 k,
      p.width ≤ k + A0*(k/(max 1 (Nat.log2 k))+1) ∧
      p.q ≤ (k+1)^C ∧ 2^p.s ≤ (k+1)^C ∧
      2^p.lN ≤ (k+1)^C ∧ p.T ≤ (k+1)^C := by
  refine ⟨34, 6, 2^1024, ?_⟩
  intro k hk
  let l := Nat.log2 k
  let b := l / 32
  let s := l + 1
  let q : ℕ := 2^b
  let m := (k-s)/b
  let r := k-m*b
  let T := q^20
  let L := 2*(4*T*b+1)*(Nat.log2 (m*b+1)+2)
  have hkpos : 0 < k := lt_of_lt_of_le (Nat.pow_pos (by decide)) hk
  have hl : 1024 ≤ l := by
    exact (Nat.le_log_iff_pow_le (b := 2) (by decide) hkpos.ne').2 hk |>.trans_eq
      Nat.log2_eq_log_two.symm
  have hb : 32 ≤ b := by dsimp [b]; omega
  have hbl : 32*b ≤ l := by dsimp [b]; omega
  have hlb : l < 32*(b+1) := by dsimp [b]; omega
  have hl33 : l ≤ 33*b := by omega
  have hbpos : 0 < b := by omega
  have hbs : b ≤ s := by dsimp [s]; omega
  have hql : l+3 ≤ q := le_trans (by omega) (params257_linear_le_pow b hb)
  have hq5 : 5 ≤ q := by omega
  have hbq : b ≤ q := by dsimp [s] at hbs; omega
  have hsq : s ≤ q := by dsimp [s]; omega
  have hqpos : 0 < q := by omega
  have hpow_l : 2^l ≤ k := by
    simpa only [l, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hkpos.ne'
  have hk_s : k < 2^s := by
    simpa only [s, l, Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (b := 2) (by decide) k
  have hs_hi : 2^s ≤ 2*k := by
    change 2^(l+1) ≤ 2*k
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 hpow_l
  have hq32 : q^32 ≤ k := by
    change (2^b)^32 ≤ k
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by decide) (by omega : b*32 ≤ l)).trans hpow_l
  have hq33 : k ≤ q^33 := by
    apply hk_s.le.trans
    change 2^s ≤ (2^b)^33
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    dsimp [s]
    omega
  have hqk : q ≤ k := by
    calc q = q^1 := (pow_one _).symm
         _ ≤ q^32 := Nat.pow_le_pow_right hqpos (by decide)
         _ ≤ k := hq32
  have hqensk : q^2 ≤ k :=
    (Nat.pow_le_pow_right hqpos (by decide : 2 ≤ 32)).trans hq32
  have hsbk : s+b ≤ k := by
    calc s+b ≤ q+q := Nat.add_le_add hsq hbq
         _ ≤ q^2 := by nlinarith only [Nat.mul_le_mul_right q (show 2 ≤ q by omega)]
         _ ≤ k := hqensk
  have hmpos : 0 < m := Nat.div_pos (by omega) hbpos
  have hmprod : m*b ≤ k-s := Nat.div_mul_le_self (k-s) b
  have hm_le : m ≤ k := by
    exact (Nat.le_mul_of_pos_right m hbpos).trans (hmprod.trans (Nat.sub_le _ _))
  have hsplit : k = m*b+r := by dsimp [r]; omega
  have hrs : s ≤ r := by dsimp [r]; omega
  have hrup : r < s+b := by
    have heq := Nat.div_add_mod (k-s) b
    rw [Nat.mul_comm b] at heq
    change m*b+(k-s)%b = k-s at heq
    have hmod := Nat.mod_lt (k-s) hbpos
    omega
  have hsize : m*(2^b)^2 < 2^(3*s+3) := by
    calc
      m*(2^b)^2 ≤ 2^s*(2^s)^2 := by
        gcongr
        exact hm_le.trans hk_s.le
      _ = 2^(3*s) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ < 2^(3*s+3) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hthreshold : 2*m*q^4 ≤ T^2 := by
    calc
      2*m*q^4 ≤ q*q^33*q^4 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (hm_le.trans hq33))
      _ = q^38 := by nth_rw 1 [← pow_one q]; rw [← pow_add, ← pow_add]
      _ ≤ q^40 := Nat.pow_le_pow_right hqpos (by decide)
      _ = T^2 := pow_mul q 20 2
  let p : Params257 k :=
    { b := b, s := s, m := m, r := r, T := T, L := L
      b_pos := hbpos, s_pos := by dsimp [s]; omega
      m_pos := hmpos, k_pos := hkpos, b_le_s := hbs
      split := hsplit, s_le_r := hrs
      m_le_pow := hm_le.trans hk_s.le, k_le_pow := hk_s.le
      size_lt := hsize, threshold := hthreshold, L_eq := rfl }
  refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
  · have hlog : Nat.log2 (m*b+1)+2 ≤ l+3 := by
      rw [Nat.log2_eq_log_two, show l = Nat.log 2 k from Nat.log2_eq_log_two]
      have hle : m*b+1 ≤ k := by omega
      have hlogle := Nat.log_mono_right (b := 2) hle
      omega
    have hTpos : 0 < T := Nat.pow_pos hqpos
    have hlarge_factor : 4*T*b+1 ≤ T*q^2 := by
      have ha : 4*b+1 ≤ q^2 := by
        have := Nat.mul_le_mul_right q hq5
        nlinarith only [this, hbq, hqpos]
      have hc := Nat.mul_le_mul_left T ha
      nlinarith only [hc, hTpos]
    have hL : L ≤ q^24 := by
      calc
        L ≤ q*(T*q^2)*q :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) hlarge_factor) (hlog.trans hql)
        _ = q^24 := by
          change q*(q^20*q^2)*q = q^24
          calc
            q*(q^20*q^2)*q = q^1*q^20*q^2*q^1 := by simp only [pow_one]; ac_rfl
            _ = q^24 := by rw [← pow_add, ← pow_add, ← pow_add]
    have hr' : r ≤ q^24 := by
      have hrq : r ≤ q+q := by omega
      calc r ≤ q+q := hrq
           _ ≤ q^2 := by nlinarith only [Nat.mul_le_mul_right q (show 2 ≤ q by omega)]
           _ ≤ q^24 := Nat.pow_le_pow_right hqpos (by decide)
    have hln' : 3*s+3 ≤ q^24 := by
      calc 3*s+3 ≤ q^2 := by nlinarith only [Nat.mul_le_mul_right q hq5, hsq, hq5]
           _ ≤ q^24 := Nat.pow_le_pow_right hqpos (by decide)
    have hextra : (r+(3*s+3)+L)*l ≤ k := by
      calc
        (r+(3*s+3)+L)*l ≤ (q^24+q^24+q^24)*q :=
          Nat.mul_le_mul (by omega) (by omega)
        _ ≤ (q*q^24)*q := by
          apply Nat.mul_le_mul_right
          have h := Nat.mul_le_mul_right (q^24) (show 3 ≤ q by omega)
          omega
        _ = q^26 := by
          calc
            (q*q^24)*q = q^1*q^24*q^1 := by simp
            _ = q^26 := by rw [← pow_add, ← pow_add]
        _ ≤ q^32 := Nat.pow_le_pow_right hqpos (by decide)
        _ ≤ k := hq32
    have hlpos : 0 < l := by omega
    have hextra' : r+(3*s+3)+L ≤ k/l :=
      (Nat.le_div_iff_mul_le hlpos).2 hextra
    have hmdiv : m ≤ 33*(k/l+1) := by
      apply Nat.le_of_mul_le_mul_right _ hlpos
      calc
        m*l ≤ m*(33*b) := Nat.mul_le_mul_left _ hl33
        _ = 33*(m*b) := by ac_rfl
        _ ≤ 33*k := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 33*((k/l+1)*l) :=
          Nat.mul_le_mul_left _ ((Nat.div_lt_iff_lt_mul hlpos).1 (Nat.lt_succ_self _)).le
        _ = (33*(k/l+1))*l := by ac_rfl
    change m*(b+1)+2*r+(3*s+3)+L ≤ k+34*(k/(max 1 l)+1)
    rw [max_eq_right (show 1 ≤ l by omega), Nat.mul_add, Nat.mul_one]
    omega
  · change q ≤ (k+1)^6
    exact hqk.trans ((Nat.le_succ k).trans (by
      simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos k) (by decide : 1 ≤ 6)))
  · change 2^s ≤ (k+1)^6
    calc
      2^s ≤ 2*k := hs_hi
      _ ≤ (k+1)^2 := by nlinarith
      _ ≤ (k+1)^6 := Nat.pow_le_pow_right (Nat.succ_pos k) (by decide)
  · change 2^(3*s+3) ≤ (k+1)^6
    have h : 2^(s+1) ≤ (k+1)^2 := by
      rw [pow_succ, Nat.mul_comm]
      have hk2 : 2 ≤ k := by omega
      nlinarith only [Nat.mul_le_mul_left 2 hs_hi, Nat.mul_le_mul_right k hk2]
    calc
      2^(3*s+3) = (2^(s+1))^3 := by rw [← pow_mul]; congr 1; omega
      _ ≤ ((k+1)^2)^3 := Nat.pow_le_pow_left h 3
      _ = (k+1)^6 := by rw [← pow_mul]
  · change q^20 ≤ (k+1)^6
    calc
      q^20 ≤ q^32 := Nat.pow_le_pow_right hqpos (by decide)
      _ ≤ k := hq32
      _ ≤ k+1 := Nat.le_succ k
      _ ≤ (k+1)^6 := by
        simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_pos k) (by decide : 1 ≤ 6)

end Part2

section Part3


def syndromeParity : {n : Nat} → (Fin n → Bool) → Bool
  | 0, _ => false
  | _ + 1, x => Bool.xor (x 0) (syndromeParity (fun i => x i.succ))

private theorem syndromeParity_congr_xor {n : Nat} (x y : Fin n → Bool) :
    syndromeParity (fun i => Bool.xor (x i) (y i)) =
      Bool.xor (syndromeParity x) (syndromeParity y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [syndromeParity, ih]
    cases x 0 <;> cases y 0 <;>
      cases syndromeParity (fun i : Fin n => x i.succ) <;>
      cases syndromeParity (fun i : Fin n => y i.succ) <;> rfl

private theorem syndromeParity_zero (n : Nat) :
    syndromeParity (fun _ : Fin n => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [syndromeParity, ih]

private theorem syndromeParity_single {n : Nat} (i : Fin n) :
    syndromeParity (fun j => decide (j = i)) = true := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [syndromeParity, syndromeParity_zero]
    · simp [syndromeParity, ih, Ne.symm (Fin.succ_ne_zero j)]


def syndromeBit {n : Nat} (mask x : Fin n → Bool) : Bool :=
  syndromeParity (fun i => mask i && x i)

private theorem syndromeBit_xor {n : Nat} (mask x y : Fin n → Bool) :
    syndromeBit mask (fun i => Bool.xor (x i) (y i)) =
      Bool.xor (syndromeBit mask x) (syndromeBit mask y) := by
  unfold syndromeBit
  rw [← syndromeParity_congr_xor]
  congr 1
  funext i
  dsimp only
  cases mask i <;> cases x i <;> cases y i <;> rfl

private theorem syndromeBit_xor_mask {n : Nat} (a b x : Fin n → Bool) :
    syndromeBit (fun i => Bool.xor (a i) (b i)) x =
      Bool.xor (syndromeBit a x) (syndromeBit b x) := by
  unfold syndromeBit
  rw [← syndromeParity_congr_xor]
  congr 1
  funext i
  dsimp only
  cases a i <;> cases b i <;> cases x i <;> rfl

private theorem syndrome_badRows_card {n : Nat} (d : Fin (n+1) → Bool)
    (i : Fin (n+1)) (hi : d i = true) :
    Fintype.card {h : Fin (n+1) → Bool // syndromeBit h d = false} ≤ 2 ^ n := by
  classical
  let f : {h : Fin (n+1) → Bool // syndromeBit h d = false} → (Fin n → Bool) :=
    fun h j => h.val (i.succAbove j)
  suffices Fintype.card {h : Fin (n+1) → Bool // syndromeBit h d = false} ≤
      Fintype.card (Fin n → Bool) by simpa using this
  refine Fintype.card_le_of_injective f ?_
  intro a b hab
  apply Subtype.ext
  funext j
  have haway (k : Fin n) : a.val (i.succAbove k) = b.val (i.succAbove k) :=
    congrFun hab k
  refine Fin.succAboveCases i ?_ haway j
  by_contra hne
  have hd : (fun k => Bool.xor (a.val k) (b.val k)) = fun k => decide (k = i) := by
    funext k
    refine Fin.succAboveCases i ?_ (fun l => ?_) k
    · have he : Bool.xor (a.val i) (b.val i) = true := by
        cases ha : a.val i <;> cases hb : b.val i <;> simp_all
      simpa using he
    · simp [haway, Fin.succAbove_ne]
  have hbit : syndromeBit (fun k => decide (k = i)) d = true := by
    unfold syndromeBit
    rw [← syndromeParity_single i]
    congr 1
    funext k
    by_cases h : k = i <;> simp [h, hi]
  rw [← hd, syndromeBit_xor_mask, a.property, b.property] at hbit
  contradiction

private def syndromeBadMatrices {n r : Nat} (d : Fin n → Bool) :
    Finset (Fin r → Fin n → Bool) :=
  Finset.univ.filter fun h => ∀ j, syndromeBit (h j) d = false

private theorem syndrome_badMatrices_card {n r : Nat} (d : Fin (n+1) → Bool)
    (i : Fin (n+1)) (hi : d i = true) :
    (syndromeBadMatrices (r := r) d).card ≤ (2 ^ n) ^ r := by
  classical
  let f : ↥(syndromeBadMatrices (r := r) d) →
      (Fin r → {h : Fin (n+1) → Bool // syndromeBit h d = false}) :=
    fun h j => ⟨h.val j, (Finset.mem_filter.mp h.property).2 j⟩
  have h := Fintype.card_le_of_injective f (by
    intro a b hab
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun hab j))
  rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] at h
  exact h.trans (Nat.pow_le_pow_left (syndrome_badRows_card d i hi) _)

private def syndromeSupports (n t : Nat) : Finset (Finset (Fin n)) :=
  (Finset.range (min t n + 1)).biUnion fun k =>
    (Finset.univ : Finset (Fin n)).powersetCard k

private theorem syndrome_mem_supports {n t : Nat} (s : Finset (Fin n)) (hs : s.card ≤ t) :
    s ∈ syndromeSupports n t := by
  apply Finset.mem_biUnion.mpr
  refine ⟨s.card, ?_, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (le_min hs (by simpa using Finset.card_le_univ s)))

private theorem syndrome_supports_card (n t : Nat) :
    (syndromeSupports n t).card ≤ (n+1) ^ (t+1) := by
  classical
  calc
    _ ≤ ∑ k ∈ Finset.range (min t n + 1),
        ((Finset.univ : Finset (Fin n)).powersetCard k).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.range (min t n + 1), (n+1) ^ t := by
      apply Finset.sum_le_sum
      intro k hk
      simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      apply (Nat.choose_le_pow n k).trans
      apply (Nat.pow_le_pow_left (Nat.le_succ n) k).trans
      exact Nat.pow_le_pow_right (by omega)
        ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)).trans (min_le_left _ _))
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, pow_succ]
      rw [Nat.mul_comm ((n+1)^t)]
      exact Nat.mul_le_mul_right _ (Nat.succ_le_succ (min_le_right _ _))

private theorem syndrome_supports_card_lt (n t : Nat) :
    (syndromeSupports n t).card < 2 ^ ((t+1) * (Nat.log2 (n+1) + 1)) := by
  apply (syndrome_supports_card n t).trans_lt
  rw [Nat.mul_comm, pow_mul]
  apply Nat.pow_lt_pow_left
  · simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (b := 2) (by decide) (n+1)
  · omega


theorem exists_sparse_syndrome (n t : Nat) :
    ∃ H : Fin ((t+1) * (Nat.log2 (n+1) + 1)) → Fin n → Bool,
      ∀ x y : Fin n → Bool, x ≠ y →
      (Finset.univ.filter (fun i => x i ≠ y i)).card ≤ t →
      ∃ j, syndromeBit (H j) x ≠ syndromeBit (H j) y := by
  classical
  cases n with
  | zero =>
    exact ⟨fun _ i => Fin.elim0 i, fun x y h _ => False.elim (h (Subsingleton.elim x y))⟩
  | succ n =>
    let r := (t+1) * (Nat.log2 (n+1+1) + 1)
    let s := syndromeSupports (n+1) t
    let b (u : Finset (Fin (n+1))) : Finset (Fin r → Fin (n+1) → Bool) :=
      if u.Nonempty then syndromeBadMatrices (fun i => decide (i ∈ u)) else ∅
    have hb (u : Finset (Fin (n+1))) : (b u).card ≤ (2 ^ n) ^ r := by
      by_cases h : u.Nonempty
      · obtain ⟨i, hi⟩ := h.exists_mem
        simpa [b, h] using
          syndrome_badMatrices_card (r := r) (fun k => decide (k ∈ u)) i (by simp [hi])
      · simp [b, h]
    have hlt : (s.biUnion b).card < Fintype.card (Fin r → Fin (n+1) → Bool) := by
      calc
        _ ≤ ∑ u ∈ s, (b u).card := Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ s, (2 ^ n) ^ r := Finset.sum_le_sum (fun u _ => hb u)
        _ = s.card * (2 ^ n) ^ r := by simp
        _ < 2 ^ r * (2 ^ n) ^ r :=
          Nat.mul_lt_mul_of_pos_right (syndrome_supports_card_lt (n+1) t) (by positivity)
        _ = _ := by
          simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← mul_pow]
          rw [pow_succ, Nat.mul_comm (2 ^ n)]
    obtain ⟨H, hH⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := s.biUnion b)
      (t := Finset.univ) (by simpa using hlt)
    refine ⟨H, fun x y hxy hdist => ?_⟩
    let u := Finset.univ.filter (fun i => x i ≠ y i)
    have hu : u.Nonempty := by
      by_contra he
      apply hxy
      funext i
      by_contra h
      exact he ⟨i, by simp [u, h]⟩
    have hn : H ∉ syndromeBadMatrices (fun i => decide (i ∈ u)) := by
      intro h
      exact hH.2 (Finset.mem_biUnion.mpr
        ⟨u, syndrome_mem_supports u hdist, by simpa [b, hu] using h⟩)
    have hu_eq : (fun i => decide (i ∈ u)) = (fun i => Bool.xor (x i) (y i)) := by
      funext i
      simp only [u, Finset.mem_filter, Finset.mem_univ, true_and]
      cases x i <;> cases y i <;> decide
    rw [hu_eq] at hn
    simp only [syndromeBadMatrices, Finset.mem_filter, Finset.mem_univ, true_and,
      not_forall] at hn
    obtain ⟨j, hj⟩ := hn
    rw [syndromeBit_xor] at hj
    exact ⟨j, fun h => hj (by rw [h]; simp)⟩

end Part3

section Part4

open scoped BigOperators

def dot257 {m : ℕ} (x y : Fin m → ℤ) : ℤ :=
  ∑ i, x i * y i

def norm257 {m : ℕ} (x : Fin m → ℤ) : ℤ :=
  dot257 x x


theorem squared_displacement257 {m : ℕ} {x x' y y' : Fin m → ℤ}
    (hsum : ∀ i, x i + y i = x' i + y' i)
    (hnorm : norm257 x = norm257 x') :
    (∑ i, (x i - x' i)^2) = 2 * (dot257 x y' - dot257 x y) := by
  have hcross (i : Fin m) : x i - x' i = y' i - y i := by
    linarith only [hsum i]
  calc
    (∑ i, (x i - x' i)^2) =
        (norm257 x' - norm257 x) + 2 * (dot257 x y' - dot257 x y) := by
      unfold norm257 dot257
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      calc
        (x i - x' i)^2 = (x' i * x' i - x i * x i) + 2 * (x i * (x i - x' i)) := by
          ring
        _ = _ := by rw [hcross i]; ring
    _ = _ := by rw [hnorm, sub_self, zero_add]

theorem digit_distance_le257 {m T : ℕ} {x x' y y' : Fin m → ℤ}
    (hsum : ∀ i, x i + y i = x' i + y' i)
    (hnorm : norm257 x = norm257 x')
    (hxy : |dot257 x y| ≤ (T : ℤ))
    (hxy' : |dot257 x y'| ≤ (T : ℤ)) :
    (Finset.univ.filter (fun i => x i ≠ x' i)).card ≤ 4 * T := by
  let d := Finset.univ.filter (fun i => x i ≠ x' i)
  have hc : (d.card : ℤ) ≤ ∑ i, (x i - x' i)^2 := by
    calc
      (d.card : ℤ) = ∑ _ ∈ d, (1 : ℤ) := by simp
      _ ≤ ∑ i ∈ d, (x i - x' i)^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hneq : x i ≠ x' i := (Finset.mem_filter.mp hi).2
        have hp := sq_pos_of_ne_zero (sub_ne_zero.mpr hneq)
        omega
      _ ≤ ∑ i, (x i - x' i)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ d)
          (fun i _ _ => sq_nonneg (x i - x' i))
  rw [squared_displacement257 hsum hnorm] at hc
  have h : (d.card : ℤ) ≤ 4 * (T : ℤ) := by
    have h₀ := (abs_le.mp hxy).1
    have h₁ := (abs_le.mp hxy').2
    omega
  exact_mod_cast h

theorem bit_distance_le257 {m b : ℕ} {pack : (Fin b → Bool) → ℤ}
    (hpack : Function.Injective pack) (x0 x1 : Fin m → Fin b → Bool) :
    (Finset.univ.filter (fun p : Fin m × Fin b => x0 p.1 p.2 ≠ x1 p.1 p.2)).card ≤
      (Finset.univ.filter (fun i => pack (x0 i) ≠ pack (x1 i))).card * b := by
  let d := Finset.univ.filter (fun i => pack (x0 i) ≠ pack (x1 i))
  have hsub :
      Finset.univ.filter (fun p : Fin m × Fin b => x0 p.1 p.2 ≠ x1 p.1 p.2) ⊆
        d ×ˢ (Finset.univ : Finset (Fin b)) := by
    intro p hp
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      Finset.mem_univ _⟩
    intro heq
    exact (Finset.mem_filter.mp hp).2 (congrFun (hpack heq) p.2)
  simpa [Finset.card_product, d] using Finset.card_le_card hsub

theorem eq_of_syndrome257 {m b T : ℕ} {pack : (Fin b → Bool) → ℤ}
    (hpack : Function.Injective pack) {x0 x1 : Fin m → Fin b → Bool}
    {y0 y1 : Fin m → ℤ}
    (hsynd : (Finset.univ.filter (fun p : Fin m × Fin b => x0 p.1 p.2 ≠ x1 p.1 p.2)).card
      ≤ 4 * T * b → x0 = x1)
    (hsum : ∀ i, pack (x0 i) + y0 i = pack (x1 i) + y1 i)
    (hnorm : norm257 (fun i => pack (x0 i)) = norm257 (fun i => pack (x1 i)))
    (hdot0 : |dot257 (fun i => pack (x0 i)) y0| ≤ (T : ℤ))
    (hdot1 : |dot257 (fun i => pack (x0 i)) y1| ≤ (T : ℤ)) :
    x0 = x1 :=
  hsynd <| (bit_distance_le257 hpack x0 x1).trans <|
    Nat.mul_le_mul_right b (digit_distance_le257 hsum hnorm hdot0 hdot1)


theorem triangle_eq257 {m b T : ℕ} {pack : (Fin b → Bool) → ℤ}
    (hpack : Function.Injective pack) {x0 x1 : Fin m → Fin b → Bool}
    {y0 y1 : Fin m → ℤ}
    (hsynd : (Finset.univ.filter (fun p : Fin m × Fin b => x0 p.1 p.2 ≠ x1 p.1 p.2)).card
      ≤ 4 * T * b → x0 = x1)
    (hsum : ∀ i, pack (x0 i) + y0 i = pack (x1 i) + y1 i)
    (hnorm : norm257 (fun i => pack (x0 i)) = norm257 (fun i => pack (x1 i)))
    (hdot0 : |dot257 (fun i => pack (x0 i)) y0| ≤ (T : ℤ))
    (hdot1 : |dot257 (fun i => pack (x0 i)) y1| ≤ (T : ℤ)) :
    x0 = x1 ∧ y0 = y1 := by
  have hx := eq_of_syndrome257 hpack hsynd hsum hnorm hdot0 hdot1
  refine ⟨hx, funext fun i => ?_⟩
  exact add_left_cancel (by simpa only [hx] using hsum i)

end Part4

section Part5

open scoped BigOperators

private def hadamardFactor (a b : Bool) : ℤ :=
  if a && b then -1 else 1

private def hadamardSign {l : ℕ} (u v : Fin l → Bool) : ℤ :=
  ∏ i, hadamardFactor (u i) (v i)

private theorem hadamardSign_vals {l : ℕ} (u v : Fin l → Bool) :
    hadamardSign u v = 1 ∨ hadamardSign u v = -1 := by
  unfold hadamardSign
  have h (s : Finset (Fin l)) :
      (∏ i ∈ s, hadamardFactor (u i) (v i)) = 1 ∨
      (∏ i ∈ s, hadamardFactor (u i) (v i)) = -1 := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      rcases ih with h | h <;> rw [h] <;> cases u i <;> cases v i <;>
        norm_num [hadamardFactor]
  exact h Finset.univ

private theorem hadamardBit_orthog (a b : Bool) :
    (∑ x : Bool, hadamardFactor x a * hadamardFactor x b) = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [hadamardFactor, Fintype.sum_bool]

private theorem hadamardSign_orthog {l : ℕ} (v w : Fin l → Bool) :
    (∑ u : Fin l → Bool, hadamardSign u v * hadamardSign u w) =
      if v = w then (2 : ℤ)^l else 0 := by
  classical
  simp only [hadamardSign, ← Finset.prod_mul_distrib]
  have hsum := Finset.sum_prod_piFinset Finset.univ
    (fun i x => hadamardFactor x (v i) * hadamardFactor x (w i))
  rw [Fintype.piFinset_univ] at hsum
  rw [hsum]
  simp only [hadamardBit_orthog]
  by_cases h : v = w
  · subst w
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ w i := by
      by_contra! h'
      exact h (funext h')
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

private theorem hadamard_secondMoment {m l : ℕ} (hm : m ≤ 2^l) :
    ∃ mask : Fin (2^l) → Fin m → Bool, ∀ f : Fin m → ℤ,
      (∑ s : Fin (2^l), (∑ i, if mask s i then -f i else f i)^2) =
        (2 : ℤ)^l * ∑ i, (f i)^2 := by
  classical
  let e : Fin (2^l) ≃ (Fin l → Bool) :=
    finFunctionFinEquiv.symm.trans (Equiv.piCongrRight fun _ => finTwoEquiv)
  let c (i : Fin m) : Fin l → Bool := e (Fin.castLE hm i)
  have hc : Function.Injective c := e.injective.comp (Fin.castLE_injective hm)
  let A (s : Fin (2^l)) (i : Fin m) := hadamardSign (e s) (c i)
  let mask (s : Fin (2^l)) (i : Fin m) : Bool := decide (A s i = -1)
  have hA (i j : Fin m) :
      (∑ s, A s i * A s j) = if i = j then (2 : ℤ)^l else 0 := by
    unfold A
    rw [Equiv.sum_comp e (fun u => hadamardSign u (c i) * hadamardSign u (c j))]
    simp [hadamardSign_orthog, hc.eq_iff]
  refine ⟨mask, fun f => ?_⟩
  have hmask (s : Fin (2^l)) (i : Fin m) :
      (if mask s i then -f i else f i) = A s i * f i := by
    rcases hadamardSign_vals (e s) (c i) with h | h <;>
      simp [mask, show A s i = _ from h]
  simp only [hmask]
  calc
    (∑ s, (∑ i, A s i * f i)^2) =
        ∑ s, ∑ i, ∑ j, (A s i * A s j) * (f i * f j) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, ∑ j, (∑ s, A s i * A s j) * (f i * f j) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = (2 : ℤ)^l * ∑ i, (f i)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hA, ite_mul, zero_mul]
      simp [pow_two]

theorem hadamard_balance_of_le {m l : ℕ} (hm : m ≤ 2^l) :
    ∃ mask : Fin (2^l) → Fin m → Bool,
      ∀ (f : Fin m → ℤ) (B T : ℤ), 0 ≤ T →
        (∀ i, |f i| ≤ B) → 2 * (m : ℤ) * B^2 ≤ T^2 →
        2 * (Finset.univ.filter fun s =>
          |∑ i, if mask s i then -f i else f i| ≤ T).card ≥ 2^l := by
  classical
  obtain ⟨mask, hmask⟩ := hadamard_secondMoment hm
  refine ⟨mask, fun f B T hT hf hBT => ?_⟩
  let S (s : Fin (2^l)) : ℤ := ∑ i, if mask s i then -f i else f i
  let good := Finset.univ.filter fun s => |S s| ≤ T
  let bad := Finset.univ.filter fun s => ¬ |S s| ≤ T
  change 2^l ≤ 2 * good.card
  have hc : good.card + bad.card = 2^l := by
    simpa [good, bad] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (2^l))))
        (fun s => |S s| ≤ T)
  have hF : (∑ i, (f i)^2) ≤ (m : ℤ) * B^2 := by
    calc
      (∑ i, (f i)^2) ≤ ∑ _ : Fin m, B^2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq_abs (f i)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hf i) 2
      _ = (m : ℤ) * B^2 := by simp
  have hEnergy : 2 * (∑ s, (S s)^2) ≤ (2 : ℤ)^l * T^2 := by
    change 2 * (∑ s : Fin (2^l), (∑ i, if mask s i then -f i else f i)^2) ≤ _
    rw [hmask]
    nlinarith [mul_le_mul_of_nonneg_left hF (show 0 ≤ (2 : ℤ)^l by positivity),
      mul_le_mul_of_nonneg_left hBT (show 0 ≤ (2 : ℤ)^l by positivity)]
  have hCard : (bad.card : ℤ) * (T+1)^2 ≤ ∑ s, (S s)^2 := by
    calc
      (bad.card : ℤ) * (T+1)^2 = ∑ _ ∈ bad, (T+1)^2 := by simp
      _ ≤ ∑ s ∈ bad, (S s)^2 := by
        refine Finset.sum_le_sum fun s hs => ?_
        have hs' : T + 1 ≤ |S s| := by
          have : ¬ |S s| ≤ T := (Finset.mem_filter.mp hs).2
          omega
        rw [← sq_abs (S s)]
        exact pow_le_pow_left₀ (by omega) hs' 2
      _ ≤ ∑ s, (S s)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bad) (fun s _ _ => sq_nonneg _)
  have hbad : 2 * (bad.card : ℤ) ≤ (2 : ℤ)^l := by
    have hq : 0 < (T+1)^2 := by positivity
    apply le_of_mul_le_mul_right (a := (T+1)^2) ?_ hq
    calc
      (2 * (bad.card : ℤ)) * (T+1)^2 ≤ 2 * (∑ s, (S s)^2) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hCard (by norm_num)
      _ ≤ (2 : ℤ)^l * T^2 := hEnergy
      _ ≤ (2 : ℤ)^l * (T+1)^2 := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT (by omega) 2) (by positivity)
  have hbad' : 2 * bad.card ≤ 2^l := by exact_mod_cast hbad
  omega

theorem hadamard_balance (m : ℕ) :
    ∃ mask : Fin (2^(Nat.clog 2 m)) → Fin m → Bool,
      ∀ (f : Fin m → ℤ) (B T : ℤ), 0 ≤ T →
        (∀ i, |f i| ≤ B) → 2 * (m : ℤ) * B^2 ≤ T^2 →
        2 * (Finset.univ.filter fun s =>
          |∑ i, if mask s i then -f i else f i| ≤ T).card ≥ 2^(Nat.clog 2 m) :=
  hadamard_balance_of_le (Nat.le_pow_clog (by decide) m)

end Part5

section Part6

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)
open PEqualNP.ProofComplexity
namespace AON

def Arity (o : GateOp) (l : ℕ) : Prop :=
  (o = .and ∧ l = 2) ∨ (o = .or ∧ l = 2) ∨ (o = .not ∧ l = 1)
def RightGates (C : Circuit) : Prop := ∀ g ∈ C.gates, Arity g.op g.inputs.length
namespace GateBridge

variable {α : Type*}

def Scheduled (n : Nat) (F : α → (Fin n → Bool) → Bool) (k : Nat) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ RightGates ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem start {n : Nat} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [RightGates]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

theorem restrict {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

theorem realizeDeps {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => F a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

theorem push {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k S) (op : GateOp) (deps : List α) (out : α)
    (hop : Arity op deps.length) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = g := List.mem_singleton.mp hg'
      subst g'
      change Arity op is.length
      rwa [his]
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

end GateBridge

variable {n : Nat}
abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B))

theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B) := H.2 HS hA

theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d, hd, K⟩ := H.run HS hA
  obtain ⟨e, he, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

theorem seqS {A B C D : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build D C c) (hsub : D ⊆ A ∪ B) : Build A (B ∪ C) (b + c) :=
  seq H (relax J hsub le_rfl le_rfl)

theorem stepSub {α : Type*} {A B_acc B_new D : Set α} (hD : D ⊆ A ∪ B_acc) :
    D ∪ B_new ⊆ A ∪ (B_acc ∪ B_new) :=
  Set.union_subset (hD.trans (Set.union_subset_union_right A Set.subset_union_left))
    (Set.subset_union_right.trans Set.subset_union_right)

theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : Arity op deps.length)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := GateBridge.push HS op deps f hop (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def an (f g : Sig n) : Sig n := fun x => f x && g x
def or (f g : Sig n) : Sig n := fun x => f x || g x
def nt (f : Sig n) : Sig n := fun x => !f x

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f, g] (by simp [Arity]) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f, g] (by simp [Arity]) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp [Arity]) (by simpa using hf) _ (by simp [GateOp.eval, nt])
theorem listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c : Nat) (H : ∀ a ∈ xs, Build A {F a} c) :
    Build A {f | ∃ a ∈ xs, f = F a} (xs.length * c) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ {F a}) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_
    · rintro f ⟨b, hb, rfl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hb, rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul xs.length, Nat.add_comm]
theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  have h := listBuild (List.finRange k) F c (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

theorem orListG {A : Set (Sig n)} (fs : List (Sig n))
    (hfs : ∀ f ∈ fs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => fs.any (fun f => f x)} fs.length := by
  induction fs with
  | nil =>
    have he : (fun x : Fin n → Bool => ([] : List (Sig n)).any (fun f => f x)) = (fun _ => false) := rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr hfalse)) le_rfl le_rfl (by simp)
  | cons f fs ih =>
    have h1 := ih (fun g hg => hfs g (List.mem_cons_of_mem f hg))
    have h2 := orG (A := A ∪ {fun x => fs.any (fun g => g x)})
      (Or.inl (hfs f List.mem_cons_self)) (Or.inr rfl)
    refine relax (seq h1 h2) le_rfl ?_ (by simp)
    rw [Set.singleton_subset_iff]
    exact Or.inr rfl

theorem Build.after {A B C : Set (Sig n)} {b c}
    (h : Build A B b) (j : Build (A ∪ B) C c) : Build A C (b + c) :=
  relax (seq h j) le_rfl Set.subset_union_right le_rfl

theorem Build.par {A B C : Set (Sig n)} {b c}
    (h : Build A B b) (j : Build A C c) : Build A (B ∪ C) (b + c) :=
  seq h (relax j Set.subset_union_left le_rfl le_rfl)

theorem allG {ι : Type*} [Fintype ι] {A : Set (Sig n)}
    (f : ι → Sig n) (c : ℕ) (h : ∀ i, Build A {f i} c) :
    Build A (Set.range f) (Fintype.card ι * c) := by
  classical
  have t := listBuild (Finset.univ : Finset ι).toList f c (fun i _ => h i)
  refine relax t le_rfl ?_ (by simp)
  rintro _ ⟨i, rfl⟩
  exact ⟨i, by simp, rfl⟩

def rawInputs (n : ℕ) : Set (Sig n) := Set.range (fun i x => x i)
def base (n : ℕ) : Set (Sig n) :=
  rawInputs n ∪ Set.range (fun (b : Bool) (_ : Fin n → Bool) => b)

theorem base_input (i : Fin n) : (fun x => x i) ∈ base n := Or.inl ⟨i, rfl⟩
theorem base_const (a : Bool) : (fun _ => a) ∈ base n := Or.inr ⟨a, rfl⟩

theorem buildBase (hn : 0 < n) : Build (rawInputs n) (base n) 3 := by
  let i : Fin n := ⟨0, hn⟩
  let t : Sig n := fun x => x i
  have ht : t ∈ rawInputs n := ⟨i, rfl⟩
  have h := notG ht
  let A := rawInputs n ∪ {nt t}
  have ht' : t ∈ A := Or.inl ht
  have hu' : nt t ∈ A := Or.inr rfl
  have j := Build.par (andG ht' hu') (orG ht' hu')
  have e₀ : an t (nt t) = (fun _ => false) := by funext x; simp [an, nt]
  have e₁ : or t (nt t) = (fun _ => true) := by funext x; simp [or, nt]
  have k := seq h j
  rw [e₀, e₁] at k
  refine relax ((idle (A := rawInputs n) le_rfl).par k) le_rfl ?_ le_rfl
  rintro f (hf | ⟨b, rfl⟩)
  · exact Or.inl hf
  · cases b with
    | false => exact Or.inr (Or.inr (Or.inl rfl))
    | true => exact Or.inr (Or.inr (Or.inr rfl))

noncomputable def bit {α : Type*} (f : (Fin n → Bool) → α) (a : α) : Sig n := by
  classical exact fun x => decide (f x = a)

def Small {α : Type*} (f : (Fin n → Bool) → α) (cost : ℕ) : Prop :=
  Build (base n) (Set.range (bit f)) cost

theorem Small.mono {α : Type*} {f : (Fin n → Bool) → α} {c d}
    (h : Small f c) (hle : c ≤ d) : Small f d := relax h le_rfl le_rfl hle

theorem Small.const {α : Type*} (a : α) : Small (n := n) (fun _ => a) 0 := by
  classical
  apply idle
  rintro _ ⟨i, rfl⟩
  exact base_const (decide (a = i))

theorem Small.input (i : Fin n) : Small (fun x => x i) 1 := by
  let f : Sig n := fun x => x i
  have h : f ∈ base n := base_input i
  have b := (idle (Set.singleton_subset_iff.mpr h)).par (notG h)
  refine relax b le_rfl ?_ le_rfl
  rintro _ ⟨j, rfl⟩
  cases j with
  | false =>
    apply Or.inr
    change bit f false = nt f
    funext x; simp [bit, nt]
  | true =>
    apply Or.inl
    change bit f true = f
    funext x; simp [bit]

private theorem table {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {f : (Fin n → Bool) → α} {g : (Fin n → Bool) → β}
    (op : α → β → γ) {A : Set (Sig n)} (hz : (fun _ => false) ∈ A)
    (hf : ∀ a, bit f a ∈ A) (hg : ∀ b, bit g b ∈ A) :
    Build A (Set.range (bit (fun x => op (f x) (g x))))
      (Fintype.card γ * (2 * (Fintype.card α * Fintype.card β))) := by
  classical
  apply allG
  intro k
  let t : α × β → Sig n := fun p =>
    if op p.1 p.2 = k then an (bit f p.1) (bit g p.2) else (fun _ => false)
  have ht : ∀ p, Build A {t p} 1 := by
    intro p
    by_cases h : op p.1 p.2 = k
    · simpa [t, h] using andG (hf p.1) (hg p.2)
    · simpa [t, h] using
        relax (idle (Set.singleton_subset_iff.mpr hz)) le_rfl le_rfl (Nat.zero_le 1)
  have hh := allG t 1 ht
  let ps := (Finset.univ : Finset (α × β)).toList
  have hlen : ps.length = Fintype.card α * Fintype.card β := by simp [ps]
  have hj := orListG (A := A ∪ Set.range t) (ps.map t)
    (by intro s hs; obtain ⟨p, _, rfl⟩ := List.mem_map.mp hs; exact Or.inr ⟨p, rfl⟩)
    (Or.inl hz)
  have he : (fun x => (ps.map t).any (fun q => q x)) = bit (fun x => op (f x) (g x)) k := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_map, bit, decide_eq_true_eq]
    constructor
    · rintro ⟨_, ⟨p, _, rfl⟩, hp⟩
      dsimp only [t] at hp
      split_ifs at hp with hk
      simp [an, bit] at hp
      simpa [hp.1, hp.2] using hk
    · intro hk
      refine ⟨t (f x, g x), ⟨(f x, g x), by simp [ps], rfl⟩, ?_⟩
      simp [t, hk, an, bit]
  rw [he] at hj
  exact relax (hh.after hj) le_rfl le_rfl (by simp [hlen, two_mul])

theorem Small.map₂ {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    {f : (Fin n → Bool) → α} {g : (Fin n → Bool) → β} {c d}
    (hf : Small f c) (hg : Small g d) (op : α → β → γ) :
    Small (fun x => op (f x) (g x))
      (c + d + Fintype.card γ * (2 * (Fintype.card α * Fintype.card β))) := by
  exact (Build.par hf hg).after (table op (Or.inl (base_const false))
    (fun a => Or.inr (Or.inl ⟨a, rfl⟩)) (fun b => Or.inr (Or.inr ⟨b, rfl⟩)))

theorem Small.map {α β : Type*} [Fintype α] [Fintype β]
    {f : (Fin n → Bool) → α} {c} (h : Small f c) (op : α → β) :
    Small (fun x => op (f x)) (c + Fintype.card β * (2 * Fintype.card α)) := by
  simpa using h.map₂ (Small.const ()) (fun a _ => op a)

theorem Small.foldl {ι α β : Type*} [Fintype α] [Fintype β]
    {init : (Fin n → Bool) → α} {c d}
    (xs : List ι) (f : ι → (Fin n → Bool) → β) (op : ι → α → β → α)
    (hi : Small init c) (hf : ∀ i ∈ xs, Small (f i) d) :
    Small (fun x => xs.foldl (fun a i => op i a (f i x)) (init x))
      (c + xs.length * (d + Fintype.card α * (2 * (Fintype.card α * Fintype.card β)))) := by
  induction xs generalizing init c with
  | nil => simpa using hi
  | cons i xs ih =>
    have t := ih (hi.map₂ (hf i List.mem_cons_self) (op i))
      (fun j hj => hf j (List.mem_cons_of_mem i hj))
    simpa only [List.foldl_cons, List.length_cons, Nat.succ_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using t

theorem Small.taps {ι : Type*} [Fintype ι] {c} (hn : 0 < n)
    (F : ι → (Fin n → Bool) → Bool) (h : ∀ i, Small (F i) c) :
    ∃ C : Circuit, C.size ≤ 3 + Fintype.card ι * c ∧ ReadsBack n C ∧ RightGates C ∧
      ∃ tap : ι → ℕ, ∀ i, tap i < n + C.size ∧
        ∀ x, (C.wires (List.ofFn x)).getD (tap i) false = F i x := by
  classical
  have hi : ∀ i, Build (base n) {F i} c := by
    intro i
    refine relax (h i) le_rfl (Set.singleton_subset_iff.mpr ⟨true, ?_⟩) le_rfl
    funext x; simp [bit]
  have t := allG F c hi
  have j := (buildBase hn).after (relax t Set.subset_union_right le_rfl le_rfl)
  have s : GateBridge.Scheduled n id 0 (rawInputs n) :=
    GateBridge.start (n := n) (F := id) (fun (i : Fin n) (x : Fin n → Bool) => x i)
      (fun _ _ => rfl)
  obtain ⟨d, hd, gs, hgs, hr, hgate, hw⟩ := j.run s le_rfl
  simp only [Nat.zero_add] at hgs hw
  have hwire (i : ι) := hw (F i) (Or.inr ⟨i, rfl⟩)
  choose tap hbound heval using hwire
  exact ⟨⟨gs, 0⟩, by simpa [Circuit.size, hgs] using hd, hr, hgate, tap,
    fun i => ⟨by simpa [Circuit.size, hgs] using hbound i, heval i⟩⟩

end AON
end Part6

section Part7


def Bound {I : Type*} (B x : I → ℕ) : Prop :=
  ∃ d : ℕ, ∀ i, x i ≤ B i ^ d

namespace Bound

variable {I J : Type*} {B x y : I → ℕ}

theorem mono (h : Bound B y) (hxy : ∀ i, x i ≤ y i) : Bound B x := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, fun i => (hxy i).trans (hd i)⟩

theorem reparam (h : Bound B x) (p : J → I) :
    Bound (fun j => B (p j)) (fun j => x (p j)) := by
  obtain ⟨d, hd⟩ := h
  exact ⟨d, fun j => hd (p j)⟩

theorem pow (d : ℕ) : Bound B (fun i => B i ^ d) := ⟨d, fun _ => le_rfl⟩

theorem base : Bound B B := ⟨1, by simp⟩

theorem const (hB : ∀ i, 2 ≤ B i) (k : ℕ) : Bound B (fun _ => k) :=
  ⟨k, fun i => (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_left (hB i) k)⟩

theorem mul (hx : Bound B x) (hy : Bound B y) : Bound B (fun i => x i * y i) := by
  obtain ⟨d, hd⟩ := hx
  obtain ⟨e, he⟩ := hy
  exact ⟨d + e, fun i => by rw [pow_add]; exact Nat.mul_le_mul (hd i) (he i)⟩

theorem add (hB : ∀ i, 2 ≤ B i) (hx : Bound B x) (hy : Bound B y) :
    Bound B (fun i => x i + y i) := by
  obtain ⟨d, hd⟩ := hx
  obtain ⟨e, he⟩ := hy
  refine ⟨max d e + 1, fun i => ?_⟩
  have h₁ : x i ≤ B i ^ max d e :=
    (hd i).trans (Nat.pow_le_pow_right (by have := hB i; omega) (le_max_left ..))
  have h₂ : y i ≤ B i ^ max d e :=
    (he i).trans (Nat.pow_le_pow_right (by have := hB i; omega) (le_max_right ..))
  calc
    x i + y i ≤ B i ^ max d e + B i ^ max d e := Nat.add_le_add h₁ h₂
    _ = B i ^ max d e * 2 := by omega
    _ ≤ _ := by rw [pow_succ]; exact Nat.mul_le_mul_left _ (hB i)

theorem card_fin (hx : Bound B x) : Bound B (fun i => Fintype.card (Fin (x i))) := by
  simpa using hx

theorem card_bool (hB : ∀ i, 2 ≤ B i) : Bound B (fun _ => Fintype.card Bool) := by
  simpa using const hB 2

theorem card_prod {α β : I → Type*} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (ha : Bound B (fun i => Fintype.card (α i))) (hb : Bound B (fun i => Fintype.card (β i))) :
    Bound B (fun i => Fintype.card (α i × β i)) := by
  simpa only [Fintype.card_prod] using ha.mul hb

theorem card_bits (hx : Bound B (fun i => 2 ^ x i)) :
    Bound B (fun i => Fintype.card (Fin (x i) → Bool)) := by simpa using hx

end Bound


def Poly {I : Type*} (B n : I → ℕ) {Out α : I → Type*}
    (f : ∀ i, Out i → (Fin (n i) → Bool) → α i) : Prop :=
  ∃ d : ℕ, ∀ i o, AON.Small (f i o) (B i ^ d)

namespace Poly

variable {I J : Type*} {B n k : I → ℕ} {Out Out' α β γ : I → Type*}
variable {f : ∀ i, Out i → (Fin (n i) → Bool) → α i}
variable {g : ∀ i, Out i → (Fin (n i) → Bool) → β i}

theorem ofBound {cost : I → ℕ} (hc : Bound B cost)
    (h : ∀ i o, AON.Small (f i o) (cost i)) : Poly B n f := by
  obtain ⟨d, hd⟩ := hc
  exact ⟨d, fun i o => (h i o).mono (hd i)⟩

theorem congr (hf : Poly B n f) {f' : ∀ i, Out i → (Fin (n i) → Bool) → α i}
    (he : ∀ i o x, f i o x = f' i o x) : Poly B n f' := by
  rwa [← show f = f' from funext fun i => funext fun o => funext (he i o)]

theorem reindex (hf : Poly B n f) (p : ∀ i, Out' i → Out i) :
    Poly B n (fun i o => f i (p i o)) := by
  obtain ⟨d, hd⟩ := hf
  exact ⟨d, fun i o => hd i (p i o)⟩

theorem reparam (hf : Poly B n f) (p : J → I) :
    Poly (fun j => B (p j)) (fun j => n (p j)) (fun j => f (p j)) := by
  obtain ⟨d, hd⟩ := hf
  exact ⟨d, fun j => hd (p j)⟩

theorem const (a : ∀ i, Out i → α i) : Poly B n (fun i o _ => a i o) :=
  ⟨0, fun i o => (AON.Small.const (a i o)).mono (Nat.zero_le _)⟩

theorem input (p : ∀ i, Out i → Fin (n i)) : Poly B n (fun i o x => x (p i o)) :=
  ⟨0, fun i o => (AON.Small.input (p i o)).mono (by simp)⟩

theorem either (hB : ∀ i, 2 ≤ B i) (hf : Poly B n f)
    {f' : ∀ i, Out' i → (Fin (n i) → Bool) → α i} (hf' : Poly B n f') :
    Poly B n (fun i => Sum.elim (f i) (f' i)) := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e, he⟩ := hf'
  apply ofBound (Bound.add hB (Bound.pow d) (Bound.pow e))
  rintro i (o | o)
  · exact (hd i o).mono (Nat.le_add_right ..)
  · exact (he i o).mono (Nat.le_add_left ..)

theorem byCases (hB : ∀ i, 2 ≤ B i) (hf : Poly B n f)
    {f' : ∀ i, Out i → (Fin (n i) → Bool) → α i} (hf' : Poly B n f')
    (p : ∀ i, Out i → Prop) [∀ i o, Decidable (p i o)] :
    Poly B n (fun i o => if p i o then f i o else f' i o) := by
  exact ((either hB hf hf').reindex (fun i o => if p i o then Sum.inl o else Sum.inr o)).congr
    (fun i o _ => by split_ifs <;> rfl)

theorem map [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (hB : ∀ i, 2 ≤ B i) (hf : Poly B n f)
    (ha : Bound B (fun i => Fintype.card (α i))) (hb : Bound B (fun i => Fintype.card (β i)))
    (op : ∀ i, Out i → α i → β i) : Poly B n (fun i o x => op i o (f i o x)) := by
  obtain ⟨d, hd⟩ := hf
  exact ofBound (Bound.add hB (Bound.pow d) (hb.mul ((Bound.const hB 2).mul ha)))
    (fun i o => (hd i o).map (op i o))

theorem map₂ [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]
    (hB : ∀ i, 2 ≤ B i) (hf : Poly B n f) (hg : Poly B n g)
    (ha : Bound B (fun i => Fintype.card (α i))) (hb : Bound B (fun i => Fintype.card (β i)))
    (hc : Bound B (fun i => Fintype.card (γ i))) (op : ∀ i, Out i → α i → β i → γ i) :
    Poly B n (fun i o x => op i o (f i o x) (g i o x)) := by
  obtain ⟨d, hd⟩ := hf
  obtain ⟨e, he⟩ := hg
  exact ofBound (Bound.add hB (Bound.add hB (Bound.pow d) (Bound.pow e))
    (hc.mul ((Bound.const hB 2).mul (ha.mul hb))))
    (fun i o => (hd i o).map₂ (he i o) (op i o))

theorem fold [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    (hB : ∀ i, 2 ≤ B i) (hk : Bound B k)
    (ha : Bound B (fun i => Fintype.card (α i))) (hb : Bound B (fun i => Fintype.card (β i)))
    {item : ∀ i, Out i × Fin (k i) → (Fin (n i) → Bool) → β i}
    (hinit : Poly B n f) (hitem : Poly B n item) (step : ∀ i, Out i → Fin (k i) → α i → β i → α i) :
    Poly B n (fun i o x => (List.finRange (k i)).foldl
      (fun a j => step i o j a (item i (o,j) x)) (f i o x)) := by
  obtain ⟨d, hd⟩ := hinit
  obtain ⟨e, he⟩ := hitem
  apply ofBound (Bound.add hB (Bound.pow d)
    (hk.mul (Bound.add hB (Bound.pow e) (ha.mul ((Bound.const hB 2).mul (ha.mul hb))))))
  intro i o
  simpa only [List.length_finRange] using AON.Small.foldl (List.finRange (k i))
    (fun j => item i (o,j)) (step i o) (hd i o) (fun j _ => he i (o,j))

private theorem foldUpdate {b : ℕ} (v z : Fin b → Bool) (xs : List (Fin b)) (t : Fin b) :
    (xs.foldl (fun a j => Function.update a j (v j)) z) t =
    if t ∈ xs then v t else z t := by
  induction xs generalizing z with
  | nil => simp
  | cons j xs ih =>
    rw [List.foldl_cons, ih]
    by_cases hx : t ∈ xs
    · simp [hx]
    · by_cases h : t = j <;> simp [hx, h]

theorem pack {b : I → ℕ}
    {bit : ∀ i, Out i × Fin (b i) → (Fin (n i) → Bool) → Bool}
    (hB : ∀ i, 2 ≤ B i) (hb : Bound B (fun i => 2 ^ b i)) (hf : Poly B n bit) :
    Poly B n (fun i o x j => bit i (o,j) x) := by
  have count : Bound B b := hb.mono (fun i => Nat.lt_two_pow_self.le)
  have h := fold hB count (Bound.card_bits hb) (Bound.card_bool hB)
    (const (fun i (_ : Out i) (_ : Fin (b i)) => false)) hf
    (fun _ _ j a v => Function.update a j v)
  apply h.congr
  intro i o x
  funext t
  simpa only [List.mem_finRange, ite_true] using
    foldUpdate (fun j => bit i (o,j) x) (fun _ => false) (List.finRange (b i)) t

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

theorem taps [∀ i, Fintype (Out i)] {F : ∀ i, Out i → (Fin (n i) → Bool) → Bool}
    (hB : ∀ i, 2 ≤ B i) (hn : ∀ i, 0 < n i) (ho : Bound B (fun i => Fintype.card (Out i)))
    (hF : Poly B n F) : ∃ d : ℕ, ∀ i, ∃ C : Circuit,
      C.size ≤ B i ^ d ∧ ReadsBack (n i) C ∧ AON.RightGates C ∧
      ∃ tap : Out i → ℕ, ∀ o, tap o < n i + C.size ∧
        ∀ x, (C.wires (List.ofFn x)).getD (tap o) false = F i o x := by
  obtain ⟨e, he⟩ := hF
  obtain ⟨d, hd⟩ := Bound.add hB (Bound.const hB 3) (ho.mul (Bound.pow e))
  refine ⟨d, fun i => ?_⟩
  obtain ⟨C, hc, rest⟩ := AON.Small.taps (hn i) (F i) (he i)
  exact ⟨C, hc.trans (hd i), rest⟩


theorem validTaps [∀ i, Fintype (Out i)] {F : ∀ i, Out i → (Fin (n i) → Bool) → Bool}
    (hB : ∀ i, 2 ≤ B i) (hn : ∀ i, 0 < n i) (ho : Bound B (fun i => Fintype.card (Out i)))
    (hF : Poly B n F) : ∃ d : ℕ, ∀ i, ∃ (C : Circuit) (tap : Out i → Fin (n i + C.size)),
      (ReadsBack (n i) C ∧ C.size ≤ B i ^ d ∧
        ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
          (g.op = .not ∧ g.inputs.length = 1)) ∧
      ∀ x o, (C.wires (List.ofFn x)).getD (tap o).val false = F i o x := by
  obtain ⟨d, hd⟩ := taps hB hn ho hF
  refine ⟨d, fun i => ?_⟩
  obtain ⟨C, hc, hr, hg, tap, ht⟩ := hd i
  refine ⟨C, fun o => ⟨tap o, (ht o).1⟩, ⟨hr, hc, ?_⟩, fun x o => (ht o).2 x⟩
  intro g h
  rcases hg g h with ⟨ha, hs⟩ | ⟨ho, hs⟩ | hnot
  · exact Or.inl ⟨Or.inl ha, hs⟩
  · exact Or.inl ⟨Or.inr ho, hs⟩
  · exact Or.inr hnot

end Poly

end Part7

namespace Poly

open scoped BigOperators

private theorem foldCapped {J : Type*} (c : ℕ) (f : J → ℕ) (l : List J)
    (a : Fin (c + 1)) :
    ((l.foldl (fun (v : Fin (c + 1)) j =>
      ⟨min c (v.val + f j), Nat.lt_succ_of_le (min_le_left ..)⟩) a).val) =
      min c (a.val + (l.map f).sum) := by
  induction l generalizing a with
  | nil => simp [min_eq_right (Nat.le_of_lt_succ a.isLt)]
  | cons j l ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    omega


theorem sumInt {I : Type*} {Out : I → Type*} {α β : I → Type*}
    [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]
    {B n k q : I → ℕ}
    {item : ∀ i, Out i × Fin (k i) → (Fin (n i) → Bool) → α i}
    (hB : ∀ i, 2 ≤ B i) (hk : Bound B k) (hq : Bound B q)
    (hα : Bound B (fun i => Fintype.card (α i)))
    (hβ : Bound B (fun i => Fintype.card (β i))) (hitem : Poly B n item)
    (term : ∀ i, Out i → Fin (k i) → α i → ℤ)
    (hterm : ∀ i o j a, (term i o j a).natAbs ≤ q i)
    (post : ∀ i, Out i → ℤ → β i) :
    Poly B n (fun i o x => post i o (∑ j, term i o j (item i (o, j) x))) := by
  classical
  let cap (i : I) := k i * (q i + q i)
  let inc (i : I) (o : Out i) (j : Fin (k i)) (a : α i) := (term i o j a + q i).toNat
  let step (i : I) (o : Out i) (j : Fin (k i)) (v : Fin (cap i + 1)) (a : α i) :
      Fin (cap i + 1) := ⟨min (cap i) (v.val + inc i o j a), Nat.lt_succ_of_le (min_le_left ..)⟩
  have hcap : Bound B (fun i => Fintype.card (Fin (cap i + 1))) :=
    Bound.card_fin (Bound.add hB (hk.mul (hq.add hB hq)) (Bound.const hB 1))
  have hf := Poly.fold hB hk hcap hα (Poly.const (n := n) (fun i (_ : Out i) =>
    (0 : Fin (cap i + 1)))) hitem step
  have hm := Poly.map hB hf hcap hβ (fun i o v => post i o ((v.val : ℤ) - (k i : ℤ) * q i))
  convert hm using 1
  funext i o x
  congr 1
  let f (j : Fin (k i)) := inc i o j (item i (o, j) x)
  let t (j : Fin (k i)) := term i o j (item i (o, j) x)
  have ht (j : Fin (k i)) : (t j).natAbs ≤ q i := hterm i o j _
  have he (j : Fin (k i)) : (f j : ℤ) = t j + q i := by
    change (((t j + q i).toNat : ℕ) : ℤ) = _
    have := ht j
    omega
  have hbound (j : Fin (k i)) : f j ≤ q i + q i := by
    have := he j
    have := ht j
    omega
  have hfit : ∑ j, f j ≤ cap i := by
    exact (Finset.sum_le_sum (fun j _ => hbound j)).trans_eq (by simp [cap])
  change (∑ j, t j) = ((_ : ℕ) : ℤ) - _
  dsimp only [step] at *
  rw [foldCapped]
  change (∑ j, t j) =
    ((min (cap i) (0 + ((List.finRange (k i)).map f).sum) : ℕ) : ℤ) - _
  rw [Nat.zero_add, ← List.ofFn_eq_map, List.sum_ofFn]
  rw [min_eq_right hfit, Nat.cast_sum]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

end Poly

section Part8

private def goodSeeds {s : ℕ} (good : Fin s → Bool) : Finset (Fin s) :=
  Finset.univ.filter fun j => good j = true


def seedCount {s : ℕ} (good : Fin s → Bool) : ℕ := (goodSeeds good).card

theorem seedCount_eq_card {s : ℕ} (good : Fin s → Bool) :
    seedCount good = (Finset.univ.filter fun j => good j = true).card := rfl

private def seedRankBit {s : ℕ} (j k : Fin s) (b : Bool) : Bool :=
  b && decide (k < j)

private def seedRankStep {s : ℕ} (a : Fin (s + 1)) (b : Bool) : Fin (s + 1) :=
  Fin.ofNat (s + 1) (a.val + b.toNat)

private def seedRankFinish {s : ℕ} (a : Fin (s + 1)) (j : Fin s) : Fin s :=
  if h : a.val < s then ⟨a.val, h⟩ else j


def seedRank {s : ℕ} (good : Fin s → Bool) (j : Fin s) : Fin s :=
  seedRankFinish ((List.finRange s).foldl
    (fun a k => seedRankStep a (seedRankBit j k (good k))) 0) j

private theorem seedRankStep_foldl {s : ℕ} {α : Type*} (p : α → Bool)
    (l : List α) (a : Fin (s + 1)) :
    ((l.foldl (fun a k => seedRankStep a (p k)) a : Fin (s + 1)) : ℕ) =
      (a.val + l.countP p) % (s + 1) := by
  induction l generalizing a with
  | nil => simpa using (Nat.mod_eq_of_lt a.isLt).symm
  | cons k l ih =>
    rw [List.foldl_cons, ih, List.countP_cons]
    simp only [seedRankStep, Fin.val_ofNat]
    rw [Nat.mod_add_mod]
    congr 1
    cases p k <;> simp [Nat.add_comm, Nat.add_left_comm]

private theorem seedRankBit_count {s : ℕ} (good : Fin s → Bool) (j : Fin s) :
    (List.finRange s).countP (fun k => seedRankBit j k (good k)) =
      ((Finset.Iio j).filter fun k => good k = true).card := by
  let p (k : Fin s) := seedRankBit j k (good k)
  change (List.finRange s).countP p = _
  rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup
    ((List.nodup_finRange s).filter p), List.toFinset_filter]
  congr 1
  ext k
  simp [p, seedRankBit, and_comm]

theorem seedRank_val {s : ℕ} (good : Fin s → Bool) (j : Fin s) :
    (seedRank good j).val = ((Finset.Iio j).filter fun k => good k = true).card := by
  have hle := Finset.card_filter_le (Finset.Iio j) (fun k => good k = true)
  rw [Fin.card_Iio] at hle
  have hlt : ((Finset.Iio j).filter fun k => good k = true).card < s :=
    hle.trans_lt j.isLt
  simp only [seedRank, seedRankFinish, seedRankStep_foldl, Fin.val_zero,
    Nat.zero_add, seedRankBit_count, Nat.mod_eq_of_lt (hlt.trans (Nat.lt_succ_self s)),
    hlt, dite_true]

theorem seedRank_lt_seedCount {s : ℕ} {good : Fin s → Bool}
    {j : Fin s} (hg : good j = true) : (seedRank good j).val < seedCount good := by
  rw [seedRank_val, seedCount]
  apply Finset.card_lt_card
  have hsub : (Finset.Iio j).filter (fun k => good k = true) ⊆ goodSeeds good := by
    intro k hk
    simp only [goodSeeds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hk).2
  apply (Finset.ssubset_iff_of_subset hsub).2
  exact ⟨j, by simp [goodSeeds, hg], by simp⟩

private theorem seedRank_strict {s : ℕ} {good : Fin s → Bool}
    {a b : Fin s} (ha : good a = true) (hab : a < b) :
    (seedRank good a).val < (seedRank good b).val := by
  rw [seedRank_val, seedRank_val]
  apply Finset.card_lt_card
  have hsub : (Finset.Iio a).filter (fun k => good k = true) ⊆
      (Finset.Iio b).filter (fun k => good k = true) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Iio] at hk ⊢
    exact ⟨hk.1.trans hab, hk.2⟩
  apply (Finset.ssubset_iff_of_subset hsub).2
  exact ⟨a, by simp [ha, hab], by simp⟩

private theorem seedRank_inj {s : ℕ} {good : Fin s → Bool}
    {a b : Fin s} (ha : good a = true) (hb : good b = true)
    (he : seedRank good a = seedRank good b) : a = b := by
  have hv := congrArg Fin.val he
  exact le_antisymm (le_of_not_gt fun h => (seedRank_strict hb h).ne hv.symm)
    (le_of_not_gt fun h => (seedRank_strict ha h).ne hv)

private theorem seedRank_exists {s : ℕ} (good : Fin s → Bool)
    (rank : Fin s) (h : rank.val < seedCount good) :
    ∃ j, good j = true ∧ seedRank good j = rank := by
  let f (a : goodSeeds good) : Fin (seedCount good) :=
    ⟨(seedRank good a.val).val,
      seedRank_lt_seedCount (Finset.mem_filter.mp a.property).2⟩
  have hf : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).2 ⟨
    fun a b he => Subtype.ext (seedRank_inj (Finset.mem_filter.mp a.property).2
      (Finset.mem_filter.mp b.property).2 (Fin.ext (congrArg (Fin.val (n := seedCount good)) he))),
    by rw [Fintype.card_coe, Fintype.card_fin]; rfl⟩
  obtain ⟨a, ha⟩ := hf.2 ⟨rank.val, h⟩
  exact ⟨a.val, (Finset.mem_filter.mp a.property).2,
    Fin.ext (congrArg (Fin.val (n := seedCount good)) ha)⟩

private def seedCandidate {s : ℕ} (good : Bool) (localRank rank : Fin s) : Bool :=
  good && decide (localRank = rank)

private def seedSelectStep {s : ℕ} (a k : Fin s) (b : Bool) : Fin s :=
  if b then k else a


def seedSelect {s : ℕ} (good : Fin s → Bool) (rank : Fin s) : Fin s :=
  (List.finRange s).foldl
    (fun a k => seedSelectStep a k (seedCandidate (good k) (seedRank good k) rank)) rank

private theorem seedSelectStep_foldl {s : ℕ} (p : Fin s → Bool) (j : Fin s)
    (hp : ∀ k, p k = true ↔ k = j) (l : List (Fin s)) (a : Fin s) :
    l.foldl (fun a k => seedSelectStep a k (p k)) a = if j ∈ l then j else a := by
  induction l generalizing a with
  | nil => simp
  | cons k l ih =>
    rw [List.foldl_cons, ih]
    by_cases hk : k = j
    · subst k
      simp [(hp j).2 rfl, seedSelectStep]
    · by_cases hj : j ∈ l <;> simp [seedSelectStep, hk, Ne.symm hk, hj, hp]

theorem seedSelect_seedRank {s : ℕ} (good : Fin s → Bool)
    (j : Fin s) (hj : good j = true) : seedSelect good (seedRank good j) = j := by
  have hp (k : Fin s) :
      seedCandidate (good k) (seedRank good k) (seedRank good j) = true ↔ k = j := by
    simp only [seedCandidate, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨hk, h⟩ => seedRank_inj hk hj h, fun h => by subst k; exact ⟨hj, rfl⟩⟩
  simp [seedSelect, seedSelectStep_foldl _ j hp]

theorem seedSelect_good {s : ℕ} (good : Fin s → Bool)
    (rank : Fin s) (h : rank.val < seedCount good) : good (seedSelect good rank) = true := by
  obtain ⟨j, hj, rfl⟩ := seedRank_exists good rank h
  rwa [seedSelect_seedRank good j hj]

theorem seedRank_seedSelect {s : ℕ} (good : Fin s → Bool)
    (rank : Fin s) (h : rank.val < seedCount good) : seedRank good (seedSelect good rank) = rank := by
  obtain ⟨j, hj, rfl⟩ := seedRank_exists good rank h
  rw [seedSelect_seedRank good j hj]

theorem seedSelect_of_count_le {s : ℕ} (good : Fin s → Bool)
    (rank : Fin s) (h : seedCount good ≤ rank.val) : seedSelect good rank = rank := by
  have hp (k : Fin s) : seedCandidate (good k) (seedRank good k) rank = false := by
    rw [← Bool.not_eq_true]
    simp only [seedCandidate, Bool.and_eq_true, decide_eq_true_eq]
    exact fun ⟨hk, he⟩ => (not_lt_of_ge h) (he ▸ seedRank_lt_seedCount hk)
  have hf (l : List (Fin s)) :
      l.foldl (fun a k => seedSelectStep a k
        (seedCandidate (good k) (seedRank good k) rank)) rank = rank := by
    induction l with
    | nil => rfl
    | cons k l ih => simp [List.foldl_cons, hp, seedSelectStep]
  exact hf _

namespace Poly

variable {I : Type*} {B n s : I → ℕ} {Out : I → Type*}

theorem seedRank
    {good : ∀ i, Out i × Fin (s i) → (Fin (n i) → Bool) → Bool}
    {j : ∀ i, Out i → (Fin (n i) → Bool) → Fin (s i)}
    (hB : ∀ i, 2 ≤ B i) (hs : Bound B s) (hgood : Poly B n good) (hj : Poly B n j) :
    Poly B n (fun i o x => PEqualNP.Outside.L_pcx_271_aux.seedRank
      (fun k => good i (o, k) x) (j i o x)) := by
  have hb := Bound.card_bool hB
  have hacc := (Bound.add hB hs (Bound.const hB 1)).card_fin
  have hj' := hj.reindex (fun i (ok : Out i × Fin (s i)) => ok.1)
  have hbit := map₂ hB hj' hgood hs.card_fin hb hb
    (fun _ ok j' b => seedRankBit j' ok.2 b)
  have hfold := fold hB hs hacc hb (const (B := B) (n := n)
    (fun i (_ : Out i) => (0 : Fin (s i + 1)))) hbit
    (fun _ _ _ a b => seedRankStep a b)
  exact map₂ hB hfold hj hacc hs.card_fin hs.card_fin (fun _ _ => seedRankFinish)

theorem seedSelect
    {good : ∀ i, Out i × Fin (s i) → (Fin (n i) → Bool) → Bool}
    {rank : ∀ i, Out i → (Fin (n i) → Bool) → Fin (s i)}
    (hB : ∀ i, 2 ≤ B i) (hs : Bound B s) (hgood : Poly B n good) (hrank : Poly B n rank) :
    Poly B n (fun i o x => PEqualNP.Outside.L_pcx_271_aux.seedSelect
      (fun k => good i (o, k) x) (rank i o x)) := by
  have hb := Bound.card_bool hB
  have hlocal := seedRank hB hs
    (hgood.reindex (fun i (okk : (Out i × Fin (s i)) × Fin (s i)) => (okk.1.1, okk.2)))
    (const (B := B) (n := n) (fun i (ok : Out i × Fin (s i)) => ok.2))
  have hrank' := hrank.reindex (fun i (ok : Out i × Fin (s i)) => ok.1)
  have heq := map₂ hB hlocal hrank' hs.card_fin hs.card_fin hb
    (fun _ _ j r => decide (j = r))
  have hcand := map₂ hB hgood heq hb hb hb (fun _ _ b e => b && e)
  exact fold hB hs hs.card_fin hb hrank hcand (fun _ _ k a b => seedSelectStep a k b)

end Poly

end Part8

section Part9

open scoped BigOperators

abbrev Digit257 (b : ℕ) := Fin (2^b)
def digitE257 (b : ℕ) : (Fin b → Bool) ≃ Digit257 b :=
  (Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv

variable {k : ℕ} (p : Params257 k)

abbrev Core257 := Fin p.m → Digit257 p.b
abbrev X257 := Core257 p × (Fin p.r → Bool)
abbrev Y257 := Core257 p × ((Fin (p.r-p.s) → Bool) × Fin (2^p.s))
abbrev R257 := Core257 p × ((Fin (p.r-p.s) → Bool) × Fin (2^(p.s-1)))
abbrev Src257 := X257 p × R257 p
abbrev Z257 := (Fin p.m → Digit257 (p.b+1)) ×
  ((Fin p.r → Bool) × ((Fin (p.r-p.s) → Bool) ×
    (Fin (2^p.s) × (Fin (2^p.lN) × (Fin p.L → Bool)))))
abbrev Mask257 := Fin (2^p.s) → Fin p.m → Bool
abbrev HMask257 := Fin p.L → Fin (p.m*p.b) → Bool

def center257 (d : Digit257 p.b) : ℤ := 2 * (d.val : ℤ) - ((p.q-1 : ℕ) : ℤ)

def reflectDigit257 (bit : Bool) (d : Digit257 p.b) : Digit257 p.b :=
  if bit then ⟨p.q - 1 - d.val, by
    change _ < p.q
    have hd : d.val < p.q := d.isLt
    omega⟩ else d

def reflect257 (mask : Mask257 p) (t : Fin (2^p.s)) (a : Core257 p) : Core257 p :=
  fun i => reflectDigit257 p (mask t i) (a i)

def good257 (mask : Mask257 p) (a c : Core257 p) (t : Fin (2^p.s)) : Bool :=
  decide (|∑ i, center257 p (a i) * center257 p (reflect257 p mask t c i)| ≤ (p.T : ℤ))

def ValidMask257 (mask : Mask257 p) : Prop :=
  ∀ a c, 2^(p.s-1) ≤ (Finset.univ.filter (fun t => good257 p mask a c t = true)).card

def ValidH257 (H : HMask257 p) : Prop :=
  ∀ x y : Fin (p.m*p.b) → Bool, (∀ j, syndromeBit (H j) x = syndromeBit (H j) y) →
    (Finset.univ.filter (fun i => x i ≠ y i)).card ≤ p.H → x = y

def coreBits257 (a : Core257 p) : Fin (p.m*p.b) → Bool :=
  fun i => (digitE257 p.b).symm (a (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

def normField257 (a : Core257 p) : Fin (2^p.lN) :=
  Fin.ofNat _ (∑ i, (center257 p (a i))^2).toNat

def sumField257 (a c : Core257 p) : Fin p.m → Digit257 (p.b+1) :=
  fun i => ⟨(a i).val + (c i).val, by
    have := (a i).isLt; have := (c i).isLt
    change _ < 2^(p.b+1)
    rw [pow_succ]; omega⟩

def subField257 (d : Fin p.m → Digit257 (p.b+1)) (a : Core257 p) : Core257 p :=
  fun i => Fin.ofNat _ ((d i).val - (a i).val)

def encX257 (w : Src257 p) : X257 p := w.1

def rankWide257 (u : Fin (2^(p.s-1))) : Fin (2^p.s) :=
  Fin.castLE (Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)) u

def encY257 (mask : Mask257 p) (w : Src257 p) : Y257 p :=
  let t := seedSelect (good257 p mask w.1.1 w.2.1) (rankWide257 p w.2.2.2)
  (reflect257 p mask t w.2.1, w.2.2.1, t)

def mkZ257 (H : HMask257 p) (x : X257 p) (y : Y257 p) : Z257 p :=
  (sumField257 p x.1 y.1, x.2, y.2.1, y.2.2, normField257 p x.1,
    fun j => syndromeBit (H j) (coreBits257 p x.1))

def encZ257 (mask : Mask257 p) (H : HMask257 p) (w : Src257 p) : Z257 p :=
  mkZ257 p H (encX257 p w) (encY257 p mask w)

def decXY257 (mask : Mask257 p) (x : X257 p) (y : Y257 p) : Src257 p :=
  let c := reflect257 p mask y.2.2 y.1
  let u := seedRank (good257 p mask x.1 c) y.2.2
  (x, c, y.2.1, Fin.ofNat _ u.val)

def decXZ257 (mask : Mask257 p) (x : X257 p) (z : Z257 p) : Src257 p :=
  decXY257 p mask x (subField257 p z.1 x.1, z.2.2.1, z.2.2.2.1)

def decYZ257 (mask : Mask257 p) (y : Y257 p) (z : Z257 p) : Src257 p :=
  decXY257 p mask (subField257 p z.1 y.1, z.2.1) y

end Part9

section Part10

open scoped BigOperators

variable {k : ℕ} (p : Params257 k)

theorem abs_center257_le (d : Digit257 p.b) : |center257 p d| ≤ (p.q : ℤ) := by
  have hd : d.val < p.q := d.isLt
  unfold center257
  apply abs_le.mpr
  omega

theorem center257_reflectDigit (bit : Bool) (d : Digit257 p.b) :
    center257 p (reflectDigit257 p bit d) =
      if bit then -center257 p d else center257 p d := by
  have hd : d.val < p.q := d.isLt
  cases bit with
  | false => rfl
  | true =>
    simp only [reflectDigit257, ite_true, center257]
    omega


theorem exists_validMask257 : ∃ mask : Mask257 p, ValidMask257 p mask := by
  obtain ⟨mask, hmask⟩ := hadamard_balance_of_le p.m_le_pow
  refine ⟨mask, fun a c => ?_⟩
  let f (i : Fin p.m) := center257 p (a i) * center257 p (c i)
  have hf (i) : |f i| ≤ (p.q : ℤ)^2 := by
    dsimp only [f]
    rw [abs_mul, sq]
    exact mul_le_mul (abs_center257_le p _) (abs_center257_le p _) (abs_nonneg _) (by positivity)
  have hT : 2 * (p.m : ℤ) * ((p.q : ℤ)^2)^2 ≤ (p.T : ℤ)^2 := by
    rw [← pow_mul]
    exact_mod_cast p.threshold
  have h := hmask f _ _ (Int.natCast_nonneg p.T) hf hT
  have hgood (t) : good257 p mask a c t = true ↔
      |∑ i, if mask t i then -f i else f i| ≤ (p.T : ℤ) := by
    simp only [good257, decide_eq_true_eq, reflect257, center257_reflectDigit]
    have he (i) : center257 p (a i) *
        (if mask t i then -center257 p (c i) else center257 p (c i)) =
          (if mask t i then -f i else f i) := by
      cases mask t i <;> simp [f]
    simp only [he]
  simp only [← hgood] at h
  have hs : 2 ^ p.s = 2 ^ (p.s-1) * 2 := by
    simpa only [Nat.sub_add_cancel p.s_pos] using (pow_succ (2 : ℕ) (p.s-1))
  omega


theorem exists_validH257 : ∃ H : HMask257 p, ValidH257 p H := by
  let a := p.H+1
  let b := Nat.log2 (p.m*p.b+1)+1
  have hrows : a*b ≤ p.L := by
    rw [p.L_eq]
    change a*b ≤ 2*a*(b+1)
    nlinarith
  obtain ⟨H, hH⟩ := exists_sparse_syndrome (p.m*p.b) p.H
  let H' : HMask257 p := fun j =>
    if h : j.val < a*b then H ⟨j.val, h⟩ else fun _ => false
  refine ⟨H', fun x y he hd => ?_⟩
  by_contra hxy
  obtain ⟨j, hj⟩ := hH x y hxy hd
  have hjlt : j.val < a*b := j.isLt
  exact hj (by simpa only [H', Fin.val_castLE, dite_eq_left hjlt] using he (Fin.castLE hrows j))

private theorem reflectDigit_twice257 (bit : Bool) (d : Digit257 p.b) :
    reflectDigit257 p bit (reflectDigit257 p bit d) = d := by
  cases bit
  · rfl
  · apply Fin.ext
    change p.q - 1 - (p.q - 1 - d.val) = d.val
    have hd : d.val < p.q := d.isLt
    omega

theorem reflect_twice257 (M : Mask257 p) (t : Fin (2^p.s)) (a : Core257 p) :
    reflect257 p M t (reflect257 p M t a) = a :=
  funext fun i => reflectDigit_twice257 p (M t i) (a i)

private theorem rank_lt_count257 (M : Mask257 p) (hM : ValidMask257 p M)
    (w : Src257 p) :
    (rankWide257 p w.2.2.2).val < seedCount (good257 p M w.1.1 w.2.1) := by
  rw [seedCount_eq_card]
  exact w.2.2.2.isLt.trans_le (hM _ _)

theorem encode_good257 (M : Mask257 p) (hM : ValidMask257 p M) (w : Src257 p) :
    |dot257 (fun i => center257 p ((encX257 p w).1 i))
      (fun i => center257 p ((encY257 p M w).1 i))| ≤ (p.T : ℤ) :=
  of_decide_eq_true (seedSelect_good _ _ (rank_lt_count257 p M hM w))

theorem decXY_enc257 (M : Mask257 p) (hM : ValidMask257 p M) (w : Src257 p) :
    decXY257 p M (encX257 p w) (encY257 p M w) = w := by
  rcases w with ⟨x,c,v,u⟩
  dsimp only [decXY257, encX257, encY257]
  rw [reflect_twice257, seedRank_seedSelect _ _ (rank_lt_count257 p M hM (x,c,v,u))]
  congr 3
  apply Fin.ext
  exact Nat.mod_eq_of_lt u.isLt

theorem subField_left257 (a c : Core257 p) :
    subField257 p (sumField257 p a c) a = c := by
  funext i
  apply Fin.ext
  simp [subField257, sumField257]

theorem subField_right257 (a c : Core257 p) :
    subField257 p (sumField257 p a c) c = a := by
  funext i
  apply Fin.ext
  simp [subField257, sumField257]

theorem decXZ_enc257 (M : Mask257 p) (hM : ValidMask257 p M) (H : HMask257 p) (w : Src257 p) :
    decXZ257 p M (encX257 p w) (encZ257 p M H w) = w := by
  dsimp only [decXZ257, encZ257, mkZ257]
  rw [subField_left257]
  exact decXY_enc257 p M hM w

theorem decYZ_enc257 (M : Mask257 p) (hM : ValidMask257 p M) (H : HMask257 p) (w : Src257 p) :
    decYZ257 p M (encY257 p M w) (encZ257 p M H w) = w := by
  dsimp only [decYZ257, encZ257, mkZ257]
  rw [subField_right257]
  exact decXY_enc257 p M hM w

theorem normField_val257 (a : Core257 p) :
    ((normField257 p a).val : ℤ) = norm257 (fun i => center257 p (a i)) := by
  let v : ℤ := ∑ i, (center257 p (a i))^2
  have hv0 : 0 ≤ v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hvle : v ≤ (p.m : ℤ) * (p.q : ℤ)^2 := calc
    v ≤ ∑ _i : Fin p.m, (p.q : ℤ)^2 := Finset.sum_le_sum fun i _ => by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_center257_le p _) 2
    _ = _ := by simp
  have hlen : (p.m : ℤ) * (p.q : ℤ)^2 < ((2^p.lN : ℕ) : ℤ) := by exact_mod_cast p.size_lt
  have hvlt : v.toNat < 2^p.lN := by
    have := hvle.trans_lt hlen
    omega
  change (((v.toNat % 2^p.lN : ℕ) : ℤ)) = _
  rw [Nat.mod_eq_of_lt hvlt, Int.toNat_of_nonneg hv0]
  simp [v, norm257, dot257, pow_two]

private theorem triCenterInj257 : Function.Injective (center257 p) := by
  intro a b h
  apply Fin.ext
  unfold center257 at h
  omega


private theorem triCoreEq257 (H : HMask257 p) (hH : ValidH257 p H)
    (x x' y y' : Core257 p)
    (hs : sumField257 p x y = sumField257 p x' y')
    (hn : normField257 p x = normField257 p x')
    (hh : ∀ j, syndromeBit (H j) (coreBits257 p x) =
      syndromeBit (H j) (coreBits257 p x'))
    (hd : |dot257 (fun i => center257 p (x i)) (fun i => center257 p (y i))| ≤ (p.T : ℤ))
    (hd' : |dot257 (fun i => center257 p (x i)) (fun i => center257 p (y' i))| ≤ (p.T : ℤ)) :
    x = x' ∧ y = y' := by
  let bits (v : Core257 p) (i : Fin p.m) := (digitE257 p.b).symm (v i)
  let pack (a : Fin p.b → Bool) := center257 p (digitE257 p.b a)
  have hp : Function.Injective pack := (triCenterInj257 p).comp (digitE257 p.b).injective
  have he (v : Core257 p) (i : Fin p.m) : pack (bits v i) = center257 p (v i) := by
    simp [pack, bits]
  have hdist := digit_distance_le257 (T := p.T) (x := fun i => center257 p (x i))
    (x' := fun i => center257 p (x' i)) (y := fun i => center257 p (y i))
    (y' := fun i => center257 p (y' i))
    (fun i => by
      have hi := congrArg Fin.val (congrFun hs i)
      change (x i).val + (y i).val = (x' i).val + (y' i).val at hi
      simp only [center257]; omega)
    (by rw [← normField_val257, hn, normField_val257]) hd hd'
  have hbits := bit_distance_le257 hp (bits x) (bits x')
  simp only [he] at hbits
  have hflat := hH _ _ hh (by
    refine le_trans ?_ (hbits.trans (Nat.mul_le_mul_right p.b hdist))
    apply le_of_eq
    exact Finset.card_equiv finProdFinEquiv.symm (fun i => by simp [coreBits257, bits]))
  have hx : x = x' := by
    funext i
    apply (digitE257 p.b).symm.injective
    funext j
    simpa [coreBits257] using congrFun hflat (finProdFinEquiv (i,j))
  refine ⟨hx, funext fun i => Fin.ext ?_⟩
  subst x'
  exact Nat.add_left_cancel (congrArg Fin.val (congrFun hs i))


theorem triangle257 (mask : Mask257 p) (H : HMask257 p)
    (hm : ValidMask257 p mask) (hH : ValidH257 p H) (a b c : Src257 p)
    (hx : encX257 p a = encX257 p b)
    (hy : encY257 p mask b = encY257 p mask c)
    (hz : encZ257 p mask H c = encZ257 p mask H a) : a = b ∧ a = c := by
  obtain ⟨hcore, hcore'⟩ := triCoreEq257 p H hH
    (encX257 p a).1 (encX257 p c).1 (encY257 p mask a).1 (encY257 p mask c).1
    (congrArg Prod.fst hz.symm) (congrArg (fun z => z.2.2.2.2.1) hz.symm)
    (fun j => congrArg (fun z => z.2.2.2.2.2 j) hz.symm)
    (encode_good257 p mask hm a)
    (by rw [hx, ← hy]; exact encode_good257 p mask hm b)
  have hxac : encX257 p a = encX257 p c :=
    Prod.ext hcore (congrArg (fun z => z.2.1) hz.symm)
  have hyac : encY257 p mask a = encY257 p mask c :=
    Prod.ext hcore' (Prod.ext (congrArg (fun z => z.2.2.1) hz.symm)
      (congrArg (fun z => z.2.2.2.1) hz.symm))
  have heq (v w : Src257 p) (h₁ : encX257 p v = encX257 p w)
      (h₂ : encY257 p mask v = encY257 p mask w) : v = w := by
    calc v = decXY257 p mask (encX257 p v) (encY257 p mask v) := (decXY_enc257 p mask hm v).symm
         _ = decXY257 p mask (encX257 p w) (encY257 p mask w) := by rw [h₁, h₂]
         _ = w := decXY_enc257 p mask hm w
  exact ⟨heq a b hx (hyac.trans hy.symm), heq a c hxac hyac⟩

end Part10

section Part11

variable {I : Type*} {k : I → ℕ}

structure CodecBounds (B : I → ℕ) (p : ∀ i, Params257 (k i)) : Prop where
  hB : ∀ i, 2 ≤ B i
  hk : Bound B k
  hq : Bound B (fun i => (p i).q)
  hs : Bound B (fun i => 2^(p i).s)
  hN : Bound B (fun i => 2^(p i).lN)
  hT : Bound B (fun i => (p i).T)
  hL : Bound B (fun i => (p i).L)

namespace CodecBounds
variable {B : I → ℕ} {p : ∀ i, Params257 (k i)} (h : CodecBounds B p)
include h

theorem hm : Bound B (fun i => (p i).m) := h.hs.mono fun i => (p i).m_le_pow
theorem hb : Bound B (fun i => (p i).b) := h.hq.mono fun _ => Nat.lt_two_pow_self.le
theorem hr : Bound B (fun i => (p i).r) := h.hk.mono fun i => by
  have := (p i).split
  omega
theorem hRank : Bound B (fun i => 2^((p i).s-1)) :=
  h.hs.mono fun _ => Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
theorem hSum : Bound B (fun i => 2^((p i).b+1)) := by
  simpa only [pow_succ, Params257.q] using h.hq.mul (Bound.const h.hB 2)

end CodecBounds

variable (B n : I → ℕ) (p : ∀ i, Params257 (k i))

def PolyCore (f : ∀ i, (Fin (n i) → Bool) → Core257 (p i)) : Prop :=
  Poly B n (fun i j x => f i x j)

def PolyX (f : ∀ i, (Fin (n i) → Bool) → X257 (p i)) : Prop :=
  PolyCore B n p (fun i x => (f i x).1) ∧
  Poly B n (fun i j x => (f i x).2 j)

def PolyR (f : ∀ i, (Fin (n i) → Bool) → R257 (p i)) : Prop :=
  PolyCore B n p (fun i x => (f i x).1) ∧
  Poly B n (fun i j x => (f i x).2.1 j) ∧
  Poly B n (fun i (_ : Unit) x => (f i x).2.2)

def PolyY (f : ∀ i, (Fin (n i) → Bool) → Y257 (p i)) : Prop :=
  PolyCore B n p (fun i x => (f i x).1) ∧
  Poly B n (fun i j x => (f i x).2.1 j) ∧
  Poly B n (fun i (_ : Unit) x => (f i x).2.2)

def PolySrc (f : ∀ i, (Fin (n i) → Bool) → Src257 (p i)) : Prop :=
  PolyX B n p (fun i x => (f i x).1) ∧ PolyR B n p (fun i x => (f i x).2)

def PolyZ (f : ∀ i, (Fin (n i) → Bool) → Z257 (p i)) : Prop :=
  Poly B n (fun i j x => (f i x).1 j) ∧
  Poly B n (fun i j x => (f i x).2.1 j) ∧
  Poly B n (fun i j x => (f i x).2.2.1 j) ∧
  Poly B n (fun i (_ : Unit) x => (f i x).2.2.2.1) ∧
  Poly B n (fun i (_ : Unit) x => (f i x).2.2.2.2.1) ∧
  Poly B n (fun i j x => (f i x).2.2.2.2.2 j)

end Part11

section Part12

open scoped BigOperators

private theorem center257_natAbs_le {k : ℕ} (p : Params257 k) (a : Digit257 p.b) :
    (center257 p a).natAbs ≤ p.q := by
  have ha : a.val < p.q := a.isLt
  unfold center257
  omega

section LocalPart1

variable {I : Type*} {k B n : I → ℕ} {p : ∀ i, Params257 (k i)}
variable {Out : I → Type*}
variable {a c : ∀ i, Out i → (Fin (n i) → Bool) → Core257 (p i)}


theorem poly_good257_family (h : CodecBounds B p)
    (mask : ∀ i, Mask257 (p i)) (t : ∀ i, Out i → Fin (2^(p i).s))
    (ha : Poly B n (fun i (oj : Out i × Fin (p i).m) x => a i oj.1 x oj.2))
    (hc : Poly B n (fun i (oj : Out i × Fin (p i).m) x => c i oj.1 x oj.2)) :
    Poly B n (fun i o x => good257 (p i) (mask i) (a i o x) (c i o x) (t i o)) := by
  have hd : Bound B (fun i => Fintype.card (Digit257 (p i).b)) := Bound.card_fin h.hq
  have hab := Bound.card_prod hd hd
  have hitem := Poly.map₂ h.hB ha hc hd hd hab (fun _ _ x y => (x, y))
  exact Poly.sumInt h.hB h.hm (h.hq.mul h.hq) hab (Bound.card_bool h.hB) hitem
    (fun i o j v =>
      center257 (p i) v.1 * center257 (p i) (reflectDigit257 (p i) (mask i (t i o) j) v.2))
    (fun i _ _ _ => by
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (center257_natAbs_le (p i) _) (center257_natAbs_le (p i) _))
    (fun i _ z => decide (|z| ≤ (p i).T))


theorem poly_normField257_family (h : CodecBounds B p)
    (ha : Poly B n (fun i (oj : Out i × Fin (p i).m) x => a i oj.1 x oj.2)) :
    Poly B n (fun i o x => normField257 (p i) (a i o x)) := by
  exact Poly.sumInt h.hB h.hm (h.hq.mul h.hq) (Bound.card_fin h.hq)
    (Bound.card_fin h.hN) ha
    (fun i _ _ z => (center257 (p i) z)^2)
    (fun i _ _ _ => by
      rw [pow_two, Int.natAbs_mul]
      exact Nat.mul_le_mul (center257_natAbs_le (p i) _) (center257_natAbs_le (p i) _))
    (fun _ _ z => Fin.ofNat _ z.toNat)


theorem poly_coreBits257_family (h : CodecBounds B p)
    (ha : Poly B n (fun i (oj : Out i × Fin (p i).m) x => a i oj.1 x oj.2)) :
    Poly B n (fun i (oj : Out i × Fin ((p i).m*(p i).b)) x =>
      coreBits257 (p i) (a i oj.1 x) oj.2) := by
  exact Poly.map h.hB (ha.reindex (fun i (oj : Out i × Fin ((p i).m*(p i).b)) =>
    (oj.1, (finProdFinEquiv.symm oj.2).1))) (Bound.card_fin h.hq) (Bound.card_bool h.hB)
    (fun i oj v => (digitE257 (p i).b).symm v (finProdFinEquiv.symm oj.2).2)

private theorem fold_xor_syndromeParity {m : ℕ} (v : Fin m → Bool) (z : Bool) :
    (List.finRange m).foldl (fun b j => Bool.xor b (v j)) z =
      Bool.xor z (syndromeParity v) := by
  induction m generalizing z with
  | zero => simp [syndromeParity]
  | succ m ih =>
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map, ih]
    exact Bool.xor_assoc ..


theorem poly_syndrome257_family (h : CodecBounds B p)
    (row : ∀ i, Out i → Fin ((p i).m*(p i).b) → Bool)
    (ha : Poly B n (fun i (oj : Out i × Fin (p i).m) x => a i oj.1 x oj.2)) :
    Poly B n (fun i o x => syndromeBit (row i o) (coreBits257 (p i) (a i o x))) := by
  have hfold := Poly.fold h.hB (h.hm.mul h.hb) (Bound.card_bool h.hB)
    (Bound.card_bool h.hB) (Poly.const (n := n) (fun i (_ : Out i) => false))
    (poly_coreBits257_family h ha) (fun i o j b v => Bool.xor b (row i o j && v))
  exact hfold.congr (fun i o x => by
    simpa only [Bool.false_xor, syndromeBit] using
      fold_xor_syndromeParity (fun j => row i o j && coreBits257 (p i) (a i o x) j) false)

end LocalPart1

section LocalPart2

variable {I : Type*} {k B n : I → ℕ} {p : ∀ i, Params257 (k i)}
variable {a c : ∀ i, (Fin (n i) → Bool) → Core257 (p i)}

theorem poly_good257 (h : CodecBounds B p) (mask : ∀ i, Mask257 (p i))
    (ha : Poly B n (fun i j x => a i x j)) (hc : Poly B n (fun i j x => c i x j)) :
    Poly B n (fun i t x => good257 (p i) (mask i) (a i x) (c i x) t) :=
  poly_good257_family (a := fun i _ => a i) (c := fun i _ => c i) h mask (fun _ t => t)
    (ha.reindex fun i (tj : Fin (2^(p i).s) × Fin (p i).m) => tj.2)
    (hc.reindex fun i (tj : Fin (2^(p i).s) × Fin (p i).m) => tj.2)

theorem poly_normField257 (h : CodecBounds B p)
    (ha : Poly B n (fun i j x => a i x j)) :
    Poly B n (fun i (_ : Unit) x => normField257 (p i) (a i x)) :=
  poly_normField257_family (a := fun i _ => a i) h
    (ha.reindex fun i (oj : Unit × Fin (p i).m) => oj.2)

theorem poly_coreBits257 (h : CodecBounds B p)
    (ha : Poly B n (fun i j x => a i x j)) :
    Poly B n (fun i j x => coreBits257 (p i) (a i x) j) :=
  (poly_coreBits257_family (a := fun i _ => a i) h
    (ha.reindex fun i (oj : Unit × Fin (p i).m) => oj.2)).reindex (fun _ j => ((), j))

theorem poly_syndrome257 (h : CodecBounds B p) (H : ∀ i, HMask257 (p i))
    (ha : Poly B n (fun i j x => a i x j)) :
    Poly B n (fun i j x => syndromeBit (H i j) (coreBits257 (p i) (a i x))) :=
  poly_syndrome257_family (a := fun i _ => a i) h H
    (ha.reindex fun i (oj : Fin (p i).L × Fin (p i).m) => oj.2)

end LocalPart2

end Part12

section Part13

variable {I : Type*} {B n k : I → ℕ} {p : ∀ i, Params257 (k i)}
variable {a c : ∀ i, (Fin (n i) → Bool) → Core257 (p i)}

theorem poly_reflect257 (h : CodecBounds B p) (mask : ∀ i, Mask257 (p i))
    {t : ∀ i, (Fin (n i) → Bool) → Fin (2^(p i).s)}
    (ht : Poly B n (fun i (_ : Unit) x => t i x))
    (ha : PolyCore B n p a) :
    PolyCore B n p (fun i x => reflect257 (p i) (mask i) (t i x) (a i x)) :=
  Poly.map₂ h.hB (ht.reindex (fun _ (_ : Fin _) => ())) ha
    (Bound.card_fin h.hs) (Bound.card_fin h.hq) (Bound.card_fin h.hq)
    (fun i j t d => reflectDigit257 (p i) (mask i t j) d)

theorem poly_digitE257 (h : CodecBounds B p) {Out : I → Type*}
    {bit : ∀ i, Out i × Fin (p i).b → (Fin (n i) → Bool) → Bool}
    (hb : Poly B n bit) :
    Poly B n (fun i o x => digitE257 (p i).b (fun j => bit i (o, j) x)) :=
  Poly.map h.hB (Poly.pack h.hB h.hq hb) (Bound.card_bits h.hq)
    (Bound.card_fin h.hq) (fun i _ => digitE257 (p i).b)

theorem poly_sumField257 (h : CodecBounds B p) (ha : PolyCore B n p a)
    (hc : PolyCore B n p c) :
    Poly B n (fun i j x => sumField257 (p i) (a i x) (c i x) j) :=
  Poly.map₂ h.hB ha hc (Bound.card_fin h.hq) (Bound.card_fin h.hq)
    (Bound.card_fin h.hSum)
    (fun i j d e => sumField257 (p i) (fun _ => d) (fun _ => e) j)

theorem poly_subField257 (h : CodecBounds B p)
    {d : ∀ i, (Fin (n i) → Bool) → Fin (p i).m → Digit257 ((p i).b+1)}
    (hd : Poly B n (fun i j x => d i x j)) (ha : PolyCore B n p a) :
    PolyCore B n p (fun i x => subField257 (p i) (d i x) (a i x)) :=
  Poly.map₂ h.hB hd ha (Bound.card_fin h.hSum) (Bound.card_fin h.hq)
    (Bound.card_fin h.hq)
    (fun i j e d => subField257 (p i) (fun _ => e) (fun _ => d) j)

theorem poly_encY257 (h : CodecBounds B p) (mask : ∀ i, Mask257 (p i))
    {w : ∀ i, (Fin (n i) → Bool) → Src257 (p i)} (hw : PolySrc B n p w) :
    PolyY B n p (fun i x => encY257 (p i) (mask i) (w i x)) := by
  obtain ⟨⟨ha, _⟩, hc, htail, hu⟩ := hw
  have hg := poly_good257 h mask ha hc
  have hu' := Poly.map h.hB hu (Bound.card_fin h.hRank) (Bound.card_fin h.hs)
    (fun i _ => rankWide257 (p i))
  have ht := Poly.seedSelect h.hB h.hs
    (hg.reindex (fun i (o : Unit × Fin (2^(p i).s)) => o.2)) hu'
  exact ⟨poly_reflect257 h mask ht hc, htail, ht⟩

theorem poly_decXY257 (h : CodecBounds B p) (mask : ∀ i, Mask257 (p i))
    {x : ∀ i, (Fin (n i) → Bool) → X257 (p i)}
    {y : ∀ i, (Fin (n i) → Bool) → Y257 (p i)}
    (hx : PolyX B n p x) (hy : PolyY B n p y) :
    PolySrc B n p (fun i v => decXY257 (p i) (mask i) (x i v) (y i v)) := by
  obtain ⟨hc', htail, ht⟩ := hy
  have hc := poly_reflect257 h mask ht hc'
  have hg := poly_good257 h mask hx.1 hc
  have hu := Poly.seedRank h.hB h.hs
    (hg.reindex (fun i (o : Unit × Fin (2^(p i).s)) => o.2)) ht
  exact ⟨hx, hc, htail, Poly.map h.hB hu (Bound.card_fin h.hs)
    (Bound.card_fin h.hRank) (fun _ _ u => Fin.ofNat _ u.val)⟩

end Part13

section Part14

variable {I : Type*} {k B n : I → ℕ} {p : ∀ i, Params257 (k i)}

variable {w : ∀ i, (Fin (n i) → Bool) → Src257 (p i)}
variable {X : ∀ i, (Fin (n i) → Bool) → X257 (p i)}
variable {Y : ∀ i, (Fin (n i) → Bool) → Y257 (p i)}
variable {Z : ∀ i, (Fin (n i) → Bool) → Z257 (p i)}

theorem poly_encX257 (hw : PolySrc B n p w) :
    PolyX B n p (fun i x => encX257 (p i) (w i x)) := hw.1

theorem poly_mkZ257 (h : CodecBounds B p) (H : ∀ i, HMask257 (p i))
    (hx : PolyX B n p X) (hy : PolyY B n p Y) :
    PolyZ B n p (fun i x => mkZ257 (p i) (H i) (X i x) (Y i x)) := by
  refine ⟨poly_sumField257 h hx.1 hy.1, hx.2, hy.2.1, hy.2.2, ?_, ?_⟩
  · exact poly_normField257 (a := fun i x => (X i x).1) h hx.1
  · exact poly_syndrome257 (a := fun i x => (X i x).1) h H hx.1

theorem poly_encZ257 (h : CodecBounds B p) (mask : ∀ i, Mask257 (p i))
    (H : ∀ i, HMask257 (p i)) (hw : PolySrc B n p w) :
    PolyZ B n p (fun i x => encZ257 (p i) (mask i) (H i) (w i x)) :=
  poly_mkZ257 h H (poly_encX257 hw) (poly_encY257 h mask hw)

theorem poly_decXZ257 (h : CodecBounds B p) (mask : ∀ i, Mask257 (p i))
    (hx : PolyX B n p X) (hz : PolyZ B n p Z) :
    PolySrc B n p (fun i x => decXZ257 (p i) (mask i) (X i x) (Z i x)) := by
  apply poly_decXY257 h mask hx (y := fun i x =>
    (subField257 (p i) (Z i x).1 (X i x).1, (Z i x).2.2.1, (Z i x).2.2.2.1))
  exact ⟨poly_subField257 h hz.1 hx.1, hz.2.2.1, hz.2.2.2.1⟩

theorem poly_decYZ257 (h : CodecBounds B p) (mask : ∀ i, Mask257 (p i))
    (hy : PolyY B n p Y) (hz : PolyZ B n p Z) :
    PolySrc B n p (fun i x => decYZ257 (p i) (mask i) (Y i x) (Z i x)) := by
  apply poly_decXY257 h mask (x := fun i x =>
    (subField257 (p i) (Z i x).1 (Y i x).1, (Z i x).2.1)) _ hy
  exact ⟨poly_subField257 h hz.1 hy.1, hz.2.1⟩

end Part14

section Part15



section LocalPart3
variable {k : ℕ} (p : Params257 k)

abbrev PortX := (Fin p.m × Fin p.b) ⊕ Fin p.r
abbrev PortY := (Fin p.m × Fin p.b) ⊕ (Fin (p.r-p.s) ⊕ Fin p.s)
abbrev PortR := (Fin p.m × Fin p.b) ⊕ (Fin (p.r-p.s) ⊕ Fin (p.s-1))
abbrev PortSrc := PortX p ⊕ PortR p
abbrev PortZ := (Fin p.m × Fin (p.b+1)) ⊕
  (Fin p.r ⊕ (Fin (p.r-p.s) ⊕ (Fin p.s ⊕ (Fin p.lN ⊕ Fin p.L))))

noncomputable def xPorts : Fin k ≃ PortX p := Fintype.equivOfCardEq (by
  simpa [PortX] using p.split)
noncomputable def yPorts : Fin k ≃ PortY p := Fintype.equivOfCardEq (by
  simp [PortY]
  have := p.split
  have := p.s_le_r
  omega)
noncomputable def rPorts : Fin (k-1) ≃ PortR p := Fintype.equivOfCardEq (by
  simp [PortR]
  have := p.split
  have := p.s_le_r
  have := p.s_pos
  omega)
noncomputable def srcPorts : Fin (k+(k-1)) ≃ PortSrc p :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (xPorts p) (rPorts p))
noncomputable def zPorts : Fin p.width ≃ PortZ p := Fintype.equivOfCardEq (by
  simp [PortZ, Params257.width]
  have := p.s_le_r
  omega)

private def permuteTape257 {α β : Type*} (e : α ≃ β) : (β → Bool) ≃ (α → Bool) where
  toFun f i := f (e i)
  invFun f i := f (e.symm i)
  left_inv f := by funext i; simp
  right_inv f := by funext i; simp

private def pairPort257 {A B α β : Type*} (e : A ≃ (α → Bool))
    (d : B ≃ (β → Bool)) : (A × B) ≃ ((α ⊕ β) → Bool) where
  toFun x := Sum.elim (e x.1) (d x.2)
  invFun f := (e.symm (fun i => f (.inl i)), d.symm (fun i => f (.inr i)))
  left_inv x := by simp
  right_inv f := by
    funext i
    cases i <;> simp

private noncomputable def blockPort257 (m b : ℕ) :
    (Fin m → Fin (2^b)) ≃ ((Fin m × Fin b) → Bool) where
  toFun v i := (digitE257 b).symm (v i.1) i.2
  invFun f i := digitE257 b (fun j => f (i,j))
  left_inv v := by funext i; simp
  right_inv f := by funext ⟨i,j⟩; simp

noncomputable def xPortEquiv257 : X257 p ≃ (PortX p → Bool) :=
  pairPort257 (blockPort257 p.m p.b) (Equiv.refl _)
noncomputable def yPortEquiv257 : Y257 p ≃ (PortY p → Bool) :=
  pairPort257 (blockPort257 p.m p.b)
    (pairPort257 (Equiv.refl _) (digitE257 p.s).symm)
noncomputable def rPortEquiv257 : R257 p ≃ (PortR p → Bool) :=
  pairPort257 (blockPort257 p.m p.b)
    (pairPort257 (Equiv.refl _) (digitE257 (p.s-1)).symm)
noncomputable def srcPortEquiv257 : Src257 p ≃ (PortSrc p → Bool) :=
  pairPort257 (xPortEquiv257 p) (rPortEquiv257 p)
noncomputable def zPortEquiv257 : Z257 p ≃ (PortZ p → Bool) :=
  pairPort257 (blockPort257 p.m (p.b+1))
    (pairPort257 (Equiv.refl _) (pairPort257 (Equiv.refl _)
      (pairPort257 (digitE257 p.s).symm (pairPort257 (digitE257 p.lN).symm (Equiv.refl _)))))

noncomputable abbrev xRead (v : X257 p) := xPortEquiv257 p v
noncomputable abbrev yRead (v : Y257 p) := yPortEquiv257 p v
noncomputable abbrev rRead (v : R257 p) := rPortEquiv257 p v
noncomputable abbrev srcRead (v : Src257 p) := srcPortEquiv257 p v
noncomputable abbrev zRead (v : Z257 p) := zPortEquiv257 p v

noncomputable def xBits : X257 p ≃ (Fin k → Bool) :=
  (xPortEquiv257 p).trans (permuteTape257 (xPorts p))
noncomputable def yBits : Y257 p ≃ (Fin k → Bool) :=
  (yPortEquiv257 p).trans (permuteTape257 (yPorts p))
noncomputable def rBits : R257 p ≃ (Fin (k-1) → Bool) :=
  (rPortEquiv257 p).trans (permuteTape257 (rPorts p))
noncomputable def srcBits : Src257 p ≃ (Fin (k+(k-1)) → Bool) :=
  (srcPortEquiv257 p).trans (permuteTape257 (srcPorts p))
noncomputable def zBits : Z257 p ≃ (Fin p.width → Bool) :=
  (zPortEquiv257 p).trans (permuteTape257 (zPorts p))
private theorem srcBits_left257 (a : Src257 p) (j : Fin k) :
    srcBits p a (Fin.castAdd (k-1) j) = xBits p a.1 j := by
  have h : finSumFinEquiv.symm (Fin.castAdd (k-1) j) = Sum.inl j := by
    apply finSumFinEquiv.injective
    simp
  simp [srcBits, xBits, permuteTape257, srcPorts, h, srcPortEquiv257, pairPort257]
end LocalPart3

def padBits257 {w c : ℕ} (_ : w ≤ c) (v : Fin w → Bool) (i : Fin c) : Bool :=
  if h : i.val < w then v ⟨i.val,h⟩ else false

def unpadBits257 {w c : ℕ} (h : w ≤ c) (v : Fin c → Bool) (i : Fin w) : Bool :=
  v (Fin.castLE h i)

@[simp] theorem unpad_padBits257 {w c : ℕ} (h : w ≤ c) (v : Fin w → Bool) :
    unpadBits257 h (padBits257 h v) = v := by
  funext i
  simp [unpadBits257, padBits257, Fin.castLE]

end Part15

section Part16

section LocalPart4

variable {I : Type*} {B n k b : I → ℕ} {p : ∀ i, Params257 (k i)}
variable {P Q : I → Type*}


private theorem portPoly257 (e : ∀ i, P i ≃ Q i)
    (v : ∀ i, Q i → (Fin (n i) → Bool) → Bool) :
    Poly B n (fun i j => v i (e i j)) ↔ Poly B n v := by
  constructor
  · intro h
    exact (h.reindex (fun i j => (e i).symm j)).congr (by intros; simp)
  · intro h
    exact h.reindex (fun i j => e i j)


private theorem portSumPoly257 (hB : ∀ i, 2 ≤ B i)
    (v : ∀ i, P i ⊕ Q i → (Fin (n i) → Bool) → Bool) :
    Poly B n v ↔ Poly B n (fun i j => v i (.inl j)) ∧
      Poly B n (fun i j => v i (.inr j)) := by
  constructor
  · intro h
    exact ⟨h.reindex (fun _ j => .inl j), h.reindex (fun _ j => .inr j)⟩
  · rintro ⟨hl, hr⟩
    exact (Poly.either hB hl hr).congr (by rintro i (j | j) x <;> rfl)


private theorem digitBlockPoly257 (hB : ∀ i, 2 ≤ B i) (hb : Bound B (fun i => 2 ^ b i))
    (f : ∀ i, P i → (Fin (n i) → Bool) → Digit257 (b i)) :
    Poly B n (fun i (j : P i × Fin (b i)) x => (digitE257 (b i)).symm (f i j.1 x) j.2) ↔
      Poly B n f := by
  constructor
  · intro h
    have h' := Poly.pack hB hb h
    exact (Poly.map hB h' (Bound.card_bits hb) (Bound.card_fin hb)
      (fun i _ v => digitE257 (b i) v)).congr (by intros; simp)
  · intro h
    exact Poly.map hB (h.reindex (fun i (j : P i × Fin (b i)) => j.1))
      (Bound.card_fin hb) (Bound.card_bool hB) (fun i j v => (digitE257 (b i)).symm v j.2)

private theorem digitScalarPoly257 (hB : ∀ i, 2 ≤ B i) (hb : Bound B (fun i => 2 ^ b i))
    (f : ∀ i, (Fin (n i) → Bool) → Digit257 (b i)) :
    Poly B n (fun i j x => (digitE257 (b i)).symm (f i x) j) ↔
      Poly B n (fun i (_ : Unit) x => f i x) := by
  have h := digitBlockPoly257 (n := n) (b := b) (P := fun _ => Unit)
    hB hb (fun i (_ : Unit) x => f i x)
  constructor
  · intro h'
    exact h.mp (h'.reindex (fun i (j : Unit × Fin (b i)) => j.2))
  · intro h'
    exact (h.mpr h').reindex (fun i (j : Fin (b i)) => ((), j))

private theorem xReadPoly257 (h : CodecBounds B p) (f : ∀ i, (Fin (n i) → Bool) → X257 (p i)) :
    Poly B n (fun i j x => xRead (p i) (f i x) j) ↔ PolyX B n p f := by
  rw [portSumPoly257 h.hB]
  exact and_congr (digitBlockPoly257 h.hB h.hq (fun i j x => (f i x).1 j)) Iff.rfl

private theorem rReadPoly257 (h : CodecBounds B p) (f : ∀ i, (Fin (n i) → Bool) → R257 (p i)) :
    Poly B n (fun i j x => rRead (p i) (f i x) j) ↔ PolyR B n p f := by
  rw [portSumPoly257 h.hB, portSumPoly257 h.hB]
  exact and_congr (digitBlockPoly257 h.hB h.hq (fun i j x => (f i x).1 j))
    (and_congr Iff.rfl (digitScalarPoly257 h.hB h.hRank (fun i x => (f i x).2.2)))

private theorem yReadPoly257 (h : CodecBounds B p) (f : ∀ i, (Fin (n i) → Bool) → Y257 (p i)) :
    Poly B n (fun i j x => yRead (p i) (f i x) j) ↔ PolyY B n p f := by
  rw [portSumPoly257 h.hB, portSumPoly257 h.hB]
  exact and_congr (digitBlockPoly257 h.hB h.hq (fun i j x => (f i x).1 j))
    (and_congr Iff.rfl (digitScalarPoly257 h.hB h.hs (fun i x => (f i x).2.2)))

private theorem srcReadPoly257 (h : CodecBounds B p) (f : ∀ i, (Fin (n i) → Bool) → Src257 (p i)) :
    Poly B n (fun i j x => srcRead (p i) (f i x) j) ↔ PolySrc B n p f := by
  rw [portSumPoly257 h.hB]
  exact and_congr (xReadPoly257 h (fun i x => (f i x).1)) (rReadPoly257 h (fun i x => (f i x).2))

private theorem zReadPoly257 (h : CodecBounds B p) (f : ∀ i, (Fin (n i) → Bool) → Z257 (p i)) :
    Poly B n (fun i j x => zRead (p i) (f i x) j) ↔ PolyZ B n p f := by
  rw [portSumPoly257 h.hB, portSumPoly257 h.hB, portSumPoly257 h.hB,
      portSumPoly257 h.hB, portSumPoly257 h.hB]
  exact and_congr (digitBlockPoly257 h.hB h.hSum (fun i j x => (f i x).1 j))
    (and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr (digitScalarPoly257 h.hB h.hs (fun i x => (f i x).2.2.2.1))
        (and_congr (digitScalarPoly257 h.hB h.hN (fun i x => (f i x).2.2.2.2.1)) Iff.rfl))))

theorem polyX_bits257 (h : CodecBounds B p) (f : ∀ i, (Fin (n i) → Bool) → X257 (p i)) :
    PolyX B n p f ↔ Poly B n (fun i j x => xBits (p i) (f i x) j) :=
  ((portPoly257 (fun i => xPorts (p i)) (fun i j x => xRead (p i) (f i x) j)).trans
    (xReadPoly257 h f)).symm

theorem polyY_bits257 (h : CodecBounds B p) (f : ∀ i, (Fin (n i) → Bool) → Y257 (p i)) :
    PolyY B n p f ↔ Poly B n (fun i j x => yBits (p i) (f i x) j) :=
  ((portPoly257 (fun i => yPorts (p i)) (fun i j x => yRead (p i) (f i x) j)).trans
    (yReadPoly257 h f)).symm

theorem polyR_bits257 (h : CodecBounds B p) (f : ∀ i, (Fin (n i) → Bool) → R257 (p i)) :
    PolyR B n p f ↔ Poly B n (fun i j x => rBits (p i) (f i x) j) :=
  ((portPoly257 (fun i => rPorts (p i)) (fun i j x => rRead (p i) (f i x) j)).trans
    (rReadPoly257 h f)).symm

theorem polySrc_bits257 (h : CodecBounds B p) (f : ∀ i, (Fin (n i) → Bool) → Src257 (p i)) :
    PolySrc B n p f ↔ Poly B n (fun i j x => srcBits (p i) (f i x) j) :=
  ((portPoly257 (fun i => srcPorts (p i)) (fun i j x => srcRead (p i) (f i x) j)).trans
    (srcReadPoly257 h f)).symm

theorem polyZ_bits257 (h : CodecBounds B p) (f : ∀ i, (Fin (n i) → Bool) → Z257 (p i)) :
    PolyZ B n p f ↔ Poly B n (fun i j x => zBits (p i) (f i x) j) :=
  ((portPoly257 (fun i => zPorts (p i)) (fun i j x => zRead (p i) (f i x) j)).trans
    (zReadPoly257 h f)).symm

end LocalPart4
end Part16

section Part17

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

abbrev Tape257 (w : ℕ) := Fin w → Bool

def port257 (k c : ℕ) : (e : Fin 3) → Fin (if e = 2 then c else k) →
    Fin k ⊕ Fin k ⊕ Fin c :=
  Fin.cons (α := fun e : Fin 3 => Fin (if e = 2 then c else k) → _) Sum.inl
    (Fin.cons (α := fun e : Fin 2 => Fin (if e.succ = (2 : Fin 3) then c else k) → _)
      (Sum.inr ∘ Sum.inl)
      (Fin.cons (α := fun e : Fin 1 =>
          Fin (if e.succ.succ = (2 : Fin 3) then c else k) → _)
        (Sum.inr ∘ Sum.inr) (fun e => Fin.elim0 e)))

def left257 {l r : ℕ} (u : Tape257 (l+r)) : Tape257 l := fun j => u (Fin.castAdd r j)
def right257 {l r : ℕ} (u : Tape257 (l+r)) : Tape257 r := fun j => u (Fin.natAdd l j)

theorem left_append257 {l r : ℕ} (x : Tape257 l) (y : Tape257 r) :
    left257 (Fin.append x y) = x := funext (Fin.append_left x y)
theorem right_append257 {l r : ℕ} (x : Tape257 l) (y : Tape257 r) :
    right257 (Fin.append x y) = y := funext (Fin.append_right x y)

def Valid257 (n t : ℕ) (C : Circuit) : Prop :=
  ReadsBack n C ∧ C.size ≤ t ∧
    ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)

private theorem valid257_of {n t : ℕ} {C : Circuit} (hr : ReadsBack n C)
    (hc : C.size ≤ t) (ha : AON.RightGates C) : Valid257 n t C := by
  refine ⟨hr, hc, ?_⟩
  intro g hg
  rcases ha g hg with h | h | h
  · exact .inl ⟨.inl h.1, h.2⟩
  · exact .inl ⟨.inr h.1, h.2⟩
  · exact .inr h

private theorem polyRealize257 {I : Type*} {B n : I → ℕ} {O : I → Type*}
    [∀ i, Fintype (O i)] {F : ∀ i, O i → Tape257 (n i) → Bool}
    (hB : ∀ i, 2 ≤ B i) (hn : ∀ i, 0 < n i) (hO : Bound B fun i => Fintype.card (O i))
    (hF : Poly B n F) : ∃ d : ℕ, ∀ i t, B i ^ d ≤ t →
      ∃ (C : Circuit) (tap : O i → Fin (n i + C.size)),
        Valid257 (n i) t C ∧
        ∀ o x, (C.wires (List.ofFn x)).getD (tap o).val false = F i o x := by
  obtain ⟨d, h⟩ := Poly.taps hB hn hO hF
  refine ⟨d, ?_⟩
  intro i t ht
  obtain ⟨C, hC, hr, hA, tap, ht'⟩ := h i
  exact ⟨C, fun o => ⟨tap o, (ht' o).1⟩, valid257_of hr (hC.trans ht) hA,
    fun o => (ht' o).2⟩

private theorem realizeDec257 {I : Type*} {B a b n : I → ℕ}
    {D : ∀ i, Tape257 (a i) → Tape257 (b i) → Tape257 (n i)}
    (hB : ∀ i, 2 ≤ B i) (hw : ∀ i, 0 < a i+b i) (hn : Bound B n)
    (hD : Poly B (fun i => a i + b i)
      (fun i j x => D i (left257 x) (right257 x) j)) :
    ∃ d : ℕ, ∀ i t, B i ^ d ≤ t → ∃ (C : Circuit)
      (out : Fin (n i) → Fin (a i + b i + C.size)),
      Valid257 (a i+b i) t C ∧ ∀ j x y,
        (C.wires (List.ofFn x ++ List.ofFn y)).getD (out j).val false = D i x y j := by
  obtain ⟨d, hd⟩ := polyRealize257 hB hw hn.card_fin hD
  refine ⟨d, fun i t ht => ?_⟩
  obtain ⟨C, tap, hc, h⟩ := hd i t ht
  exact ⟨C, tap, hc, fun j x y => by
    simpa only [List.ofFn_fin_append, left_append257, right_append257] using h j (Fin.append x y)⟩

theorem physical257 {I : Type*} {B n k c : I → ℕ}
    (hB : ∀ i, 2 ≤ B i) (hn : ∀ i, 0 < n i) (hk : ∀ i, 0 < k i)
    (bn : Bound B n) (bk : Bound B k) (bc : Bound B c)
    (X Y : ∀ i, Tape257 (n i) → Tape257 (k i)) (Z : ∀ i, Tape257 (n i) → Tape257 (c i))
    (D₀ : ∀ i, Tape257 (k i) → Tape257 (k i) → Tape257 (n i))
    (D₁ : ∀ i, Tape257 (k i) → Tape257 (c i) → Tape257 (n i))
    (D₂ : ∀ i, Tape257 (c i) → Tape257 (k i) → Tape257 (n i))
    (htri : ∀ i a b d, X i a = X i b → Y i b = Y i d → Z i d = Z i a → a = b ∧ a = d)
    (h₀ : ∀ i a, D₀ i (X i a) (Y i a) = a) (h₁ : ∀ i a, D₁ i (Y i a) (Z i a) = a)
    (h₂ : ∀ i a, D₂ i (Z i a) (X i a) = a)
    (pX : Poly B n (fun i j a => X i a j)) (pY : Poly B n (fun i j a => Y i a j))
    (pZ : Poly B n (fun i j a => Z i a j))
    (d₀ : Poly B (fun i => k i+k i) (fun i j x => D₀ i (left257 x) (right257 x) j))
    (d₁ : Poly B (fun i => k i+c i) (fun i j x => D₁ i (left257 x) (right257 x) j))
    (d₂ : Poly B (fun i => c i+k i) (fun i j x => D₂ i (left257 x) (right257 x) j)) :
    ∃ d : ℕ, ∀ i, Code257 (n i) (k i) (c i) (X i) (some (B i ^ d)) := by
  let mix := fun i => Sum.elim (fun j a => X i a j)
    (Sum.elim (fun j a => Y i a j) (fun j a => Z i a j))
  have pMix : Poly B n mix := Poly.either hB pX (Poly.either hB pY pZ)
  have hO : Bound B (fun i => Fintype.card (Fin (k i) ⊕ Fin (k i) ⊕ Fin (c i))) := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using Bound.add hB bk (Bound.add hB bk bc)
  obtain ⟨d, hd⟩ := polyRealize257 hB hn hO pMix
  obtain ⟨d₀, hd₀⟩ := realizeDec257 hB (fun i => by have := hk i; omega) bn d₀
  obtain ⟨d₁, hd₁⟩ := realizeDec257 hB (fun i => by have := hk i; omega) bn d₁
  obtain ⟨d₂, hd₂⟩ := realizeDec257 hB (fun i => by have := hk i; omega) bn d₂
  let D := d+d₀+d₁+d₂
  refine ⟨D, fun i => ?_⟩
  let code := fun a e j => mix i (port257 (k i) (c i) e j) a
  refine ⟨code, fun _ => rfl, ?_, ?_⟩
  · intro v he p
    have ⟨h01, h02⟩ := htri i (v 0) (v 1) (v 2) (he 0) (he 1) (he 2)
    fin_cases p
    · rfl
    · exact h01.symm
    · exact h02.symm
  · intro t ht
    cases ht
    have hpow (j : ℕ) (hj : j ≤ D) := Nat.pow_le_pow_right (by have := hB i; omega : 0 < B i) hj
    obtain ⟨enc, tap, hv, henc⟩ := hd i _ (hpow d (by dsimp [D]; omega))
    refine ⟨⟨enc, fun e j => tap (port257 (k i) (c i) e j), hv,
        fun a e j => henc (port257 (k i) (c i) e j) a⟩, ?_⟩
    intro e
    fin_cases e
    · obtain ⟨dec, out, hV, hc⟩ := hd₀ i _ (hpow d₀ (by dsimp [D]; omega))
      exact ⟨dec, out, hV, fun u j => (hc j (X i u) (Y i u)).trans (congrFun (h₀ i u) j)⟩
    · obtain ⟨dec, out, hV, hc⟩ := hd₁ i _ (hpow d₁ (by dsimp [D]; omega))
      exact ⟨dec, out, hV, fun u j => (hc j (Y i u) (Z i u)).trans (congrFun (h₁ i u) j)⟩
    · obtain ⟨dec, out, hV, hc⟩ := hd₂ i _ (hpow d₂ (by dsimp [D]; omega))
      exact ⟨dec, out, hV, fun u j => (hc j (Z i u) (X i u)).trans (congrFun (h₂ i u) j)⟩

end Part17

section Part18


theorem packedCode257 {I : Type*} {B k : I → ℕ} {p : ∀ i, Params257 (k i)}
    (h : CodecBounds B p) :
    ∃ d : ℕ, ∀ i, Code257 (k i + (k i-1)) (k i) (p i).width (left257 (r := k i-1)) (some (B i ^ d)) := by
  classical
  choose M hm using fun i => exists_validMask257 (p i)
  choose H hh using fun i => exists_validH257 (p i)
  let n := fun i => k i + (k i-1)
  let c := fun i => (p i).width
  let S (i : I) (a : Tape257 (n i)) := (srcBits (p i)).symm a
  let X (i : I) (a : Tape257 (n i)) := xBits (p i) (encX257 (p i) (S i a))
  let Y (i : I) (a : Tape257 (n i)) := yBits (p i) (encY257 (p i) (M i) (S i a))
  let Z (i : I) (a : Tape257 (n i)) := zBits (p i) (encZ257 (p i) (M i) (H i) (S i a))
  let D₀ (i : I) (x y : Tape257 (k i)) := srcBits (p i)
    (decXY257 (p i) (M i) ((xBits (p i)).symm x) ((yBits (p i)).symm y))
  let D₁ (i : I) (y : Tape257 (k i)) (z : Tape257 (c i)) := srcBits (p i)
    (decYZ257 (p i) (M i) ((yBits (p i)).symm y) ((zBits (p i)).symm z))
  let D₂ (i : I) (z : Tape257 (c i)) (x : Tape257 (k i)) := srcBits (p i)
    (decXZ257 (p i) (M i) ((xBits (p i)).symm x) ((zBits (p i)).symm z))
  have hn : ∀ i, 0 < n i := fun i => by dsimp [n]; have := (p i).k_pos; omega
  have bn : Bound B n := (Bound.add h.hB h.hk h.hk).mono
    (fun _ => Nat.add_le_add_left (Nat.sub_le ..) _)
  have bc : Bound B c :=
    Bound.add h.hB (Bound.add h.hB (Bound.add h.hB (h.hm.mul (Bound.add h.hB h.hb (Bound.const h.hB 1)))
      ((Bound.const h.hB 2).mul h.hr)) (h.hN.mono (fun _ => Nat.lt_two_pow_self.le))) h.hL
  have hs : PolySrc B n p S := by
    apply (polySrc_bits257 h S).mpr
    simpa only [S, Equiv.apply_symm_apply] using
      (Poly.input (B := B) (n := n) (fun i (j : Fin (n i)) => j))
  have hX (i : I) : X i = left257 (r := k i - 1) := by
    funext a j
    change xBits (p i) (S i a).1 j = a (Fin.castAdd (k i - 1) j)
    rw [← srcBits_left257]
    simp [S]
  suffices H : ∃ d : ℕ, ∀ i, Code257 (n i) (k i) (c i) (X i) (some (B i ^ d)) by
    obtain ⟨d, hd⟩ := H
    exact ⟨d, fun i => hX i ▸ hd i⟩
  refine physical257 h.hB hn (fun i => (p i).k_pos) bn h.hk bc X Y Z D₀ D₁ D₂
    ?_ ?_ ?_ ?_ ((polyX_bits257 h _).mp (poly_encX257 hs))
    ((polyY_bits257 h _).mp (poly_encY257 h M hs))
    ((polyZ_bits257 h _).mp (poly_encZ257 h M H hs)) ?_ ?_ ?_
  · intro i a b d hx hy hz
    obtain ⟨hab, had⟩ := triangle257 (p i) (M i) (H i) (hm i) (hh i) (S i a) (S i b) (S i d)
      ((xBits (p i)).injective hx) ((yBits (p i)).injective hy) ((zBits (p i)).injective hz)
    exact ⟨(srcBits (p i)).symm.injective hab, (srcBits (p i)).symm.injective had⟩
  · intro i a
    simp only [D₀, X, Y, Equiv.symm_apply_apply, decXY_enc257 _ _ (hm i), S, Equiv.apply_symm_apply]
  · intro i a
    simp only [D₁, Y, Z, Equiv.symm_apply_apply, decYZ_enc257 _ _ (hm i), S, Equiv.apply_symm_apply]
  · intro i a
    simp only [D₂, Z, X, Equiv.symm_apply_apply, decXZ_enc257 _ _ (hm i), S, Equiv.apply_symm_apply]
  · apply (polySrc_bits257 h _).mp
    apply poly_decXY257 h M
    · apply (polyX_bits257 h _).mpr
      simpa only [Equiv.apply_symm_apply, left257] using
        (Poly.input (B := B) (fun i => Fin.castAdd (k i) (n := k i)))
    · apply (polyY_bits257 h _).mpr
      simpa only [Equiv.apply_symm_apply, right257] using
        (Poly.input (B := B) (fun i => Fin.natAdd (k i) (m := k i)))
  · apply (polySrc_bits257 h _).mp
    apply poly_decYZ257 h M
    · apply (polyY_bits257 h _).mpr
      simpa only [Equiv.apply_symm_apply, left257, c] using
        (Poly.input (B := B) (fun i => Fin.castAdd (c i) (n := k i)))
    · apply (polyZ_bits257 h _).mpr
      simpa only [Equiv.apply_symm_apply, right257, c] using
        (Poly.input (B := B) (fun i => Fin.natAdd (k i) (m := c i)))
  · apply (polySrc_bits257 h _).mp
    apply poly_decXZ257 h M
    · apply (polyX_bits257 h _).mpr
      simpa only [Equiv.apply_symm_apply, right257, c] using
        (Poly.input (B := B) (fun i => Fin.natAdd (c i) (m := k i)))
    · apply (polyZ_bits257 h _).mpr
      simpa only [Equiv.apply_symm_apply, left257, c] using
        (Poly.input (B := B) (fun i => Fin.castAdd (k i) (n := c i)))

end Part18

section Part19

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

private def rewire257 {w w' : ℕ} (f : Fin w → Fin w') (i : ℕ) : ℕ :=
  if h : i < w then (f ⟨i, h⟩).val else w' + (i - w)

private theorem rewire257_lt {w w' : ℕ} (f : Fin w → Fin w') {i s : ℕ}
    (h : i < w + s) : rewire257 f i < w' + s := by
  unfold rewire257
  split
  next hi => exact lt_of_lt_of_le (f ⟨i, hi⟩).isLt (Nat.le_add_right _ _)
  next hi => omega

private def rewireGate257 {w w' : ℕ} (f : Fin w → Fin w') (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rewire257 f)⟩

private def gateStep257 (v : List Bool) (g : Gate) : List Bool :=
  v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))]

private theorem wiresMap257 {w w' : ℕ} (f : Fin w → Fin w') (gs : List Gate)
    (s : ℕ) (v v' : List Bool) (hv : v.length = w + s) (hv' : v'.length = w' + s)
    (hr : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < w + s + j)
    (agree : ∀ i < w + s, v'.getD (rewire257 f i) false = v.getD i false) :
    ∀ i < w + s + gs.length,
      ((gs.map (rewireGate257 f)).foldl gateStep257 v').getD (rewire257 f i) false =
      (gs.foldl gateStep257 v).getD i false := by
  induction gs generalizing s v v' with
  | nil => simpa using agree
  | cons g gs ih =>
    have hdep : ∀ i ∈ g.inputs, i < w + s := by
      intro i hi
      simpa using hr 0 (by simp) i hi
    have hvalue :
        (rewireGate257 f g).op.eval
          ((rewireGate257 f g).inputs.map (fun i => v'.getD i false)) =
        g.op.eval (g.inputs.map (fun i => v.getD i false)) := by
      simp only [rewireGate257, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact agree i (hdep i hi)
    have hr' : ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < w + (s+1) + j := by
      intro j hj i hi
      have h := hr (j+1) (by simpa using hj) i hi
      omega
    have hlen : (gateStep257 v g).length = w + (s+1) := by
      simp [gateStep257, hv, Nat.add_assoc]
    have hlen' : (gateStep257 v' (rewireGate257 f g)).length = w' + (s+1) := by
      simp [gateStep257, hv', Nat.add_assoc]
    have hagree : ∀ i < w + (s+1),
        (gateStep257 v' (rewireGate257 f g)).getD (rewire257 f i) false =
          (gateStep257 v g).getD i false := by
      intro i hi
      simp only [gateStep257, hvalue]
      by_cases h : i < w + s
      · rw [List.getD_append _ _ _ _ (by simpa [hv'] using rewire257_lt f h),
            List.getD_append _ _ _ _ (by simpa [hv] using h)]
        exact agree i h
      · have hi0 : i = w + s := by omega
        have heq : rewire257 f i = v'.length := by
          have hn : ¬i < w := by omega
          simp only [rewire257, dite_eq_right hn, hv']
          omega
        have heq' : i = v.length := by omega
        rw [heq, heq', List.getD_append_right _ _ _ _ (le_refl _),
          List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, Nat.sub_self]
    intro i hi
    simp only [List.map_cons, List.foldl_cons]
    exact ih (s+1) _ _ hlen hlen' hr' hagree i (by simp at hi; omega)

private def liftCircuit257 {w w' : ℕ} (f : Fin w → Fin w') (C : Circuit) : Circuit :=
  ⟨C.gates.map (rewireGate257 f), rewire257 f C.output⟩

@[simp] private theorem liftCircuit257_size {w w' : ℕ} (f : Fin w → Fin w') (C : Circuit) :
    (liftCircuit257 f C).size = C.size := by
  simp [liftCircuit257, Circuit.size]

private theorem liftCircuit257_reads {w w' : ℕ} (f : Fin w → Fin w') {C : Circuit}
    (h : ReadsBack w C) : ReadsBack w' (liftCircuit257 f C) := by
  intro j hj i hi
  change j < (C.gates.map _).length at hj
  have hj' : j < C.gates.length := by simpa using hj
  change i ∈ ((C.gates.map (rewireGate257 f)).getD j _).inputs at hi
  rw [List.getD_eq_getElem _ _ hj, List.getElem_map] at hi
  change i ∈ C.gates[j].inputs.map (rewire257 f) at hi
  obtain ⟨i₀, hi₀, rfl⟩ := List.mem_map.mp hi
  apply rewire257_lt f
  apply h j hj' i₀
  simpa only [gateAt, List.getD_eq_getElem _ _ hj'] using hi₀

private theorem liftCircuit257_arity {w w' : ℕ} (f : Fin w → Fin w') {C : Circuit}
    {P : GateOp → ℕ → Prop} (h : ∀ g ∈ C.gates, P g.op g.inputs.length) :
    ∀ g ∈ (liftCircuit257 f C).gates, P g.op g.inputs.length := by
  intro g hg
  change g ∈ C.gates.map (rewireGate257 f) at hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  simpa [rewireGate257] using h g₀ hg₀

private theorem liftCircuit257_wires {w w' : ℕ} (f : Fin w → Fin w') {C : Circuit}
    (hr : ReadsBack w C) (v v' : List Bool) (hv : v.length = w) (hv' : v'.length = w')
    (agree : ∀ i : Fin w, v'.getD (f i).val false = v.getD i.val false)
    (i : ℕ) (hi : i < w + C.size) :
    ((liftCircuit257 f C).wires v').getD (rewire257 f i) false = (C.wires v).getD i false := by
  exact wiresMap257 f C.gates 0 v v' (by simpa using hv) (by simpa using hv')
    (fun j hj i hi => by
      have hd := hr j hj i (by simpa only [gateAt, List.getD_eq_getElem _ _ hj] using hi)
      simpa using hd)
    (fun i hi => by
      have hl : i < w := by simpa using hi
      simpa only [rewire257, dite_eq_left hl] using agree ⟨i, hl⟩)
    i (by simpa [Circuit.size] using hi)

private theorem channelLe257 {k c c' : ℕ} (hc : c ≤ c') (e : Fin 3) :
    (if e = 2 then c else k) ≤ (if e = 2 then c' else k) := by
  by_cases he : e = 2 <;> simp [he, hc]

private def padPos257 {k c c' : ℕ} (hc0 : 0 < c) (e : Fin 3)
    (j : Fin (if e = 2 then c' else k)) : Fin (if e = 2 then c else k) :=
  if h : j.val < (if e = 2 then c else k) then ⟨j.val, h⟩ else
    ⟨0, by
      by_cases he : e = 2
      · simpa [he] using hc0
      · exact (h (by simpa [he] using j.isLt)).elim⟩

private theorem padPos257_castLE {k c c' : ℕ} (hc0 : 0 < c) (hc : c ≤ c') (e : Fin 3)
    (j : Fin (if e = 2 then c else k)) :
    padPos257 hc0 e (j.castLE (channelLe257 hc e)) = j := by
  simp [padPos257, j.isLt]

private def embedTape257 {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (i : Fin (a+b)) :
    Fin (a'+b') :=
  ⟨if i.val < a then i.val else a' + (i.val-a), by
    have hi := i.isLt
    split <;> omega⟩

private theorem tapeGet257 {m : ℕ} (x : Fin m → Bool) (i : Fin m) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

private theorem embedTape257_agree {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b')
    (x : Fin a → Bool) (y : Fin b → Bool) (x' : Fin a' → Bool) (y' : Fin b' → Bool)
    (hx : ∀ i, x' (i.castLE ha) = x i) (hy : ∀ i, y' (i.castLE hb) = y i)
    (i : Fin (a+b)) :
    (List.ofFn x' ++ List.ofFn y').getD (embedTape257 ha hb i).val false =
    (List.ofFn x ++ List.ofFn y).getD i.val false := by
  by_cases h : i.val < a
  · simp only [embedTape257, ite_eq_left h]
    rw [List.getD_append _ _ _ _ (by simpa using lt_of_lt_of_le h ha),
        List.getD_append _ _ _ _ (by simpa using h)]
    exact (tapeGet257 x' ((⟨i.val, h⟩ : Fin a).castLE ha)).trans
      ((hx ⟨i.val, h⟩).trans (tapeGet257 x ⟨i.val, h⟩).symm)
  · let j : Fin b := ⟨i.val-a, by have hi := i.isLt; omega⟩
    simp only [embedTape257, ite_eq_right h]
    rw [List.getD_append_right _ _ _ _ (by simp),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt h),
        List.length_ofFn, List.length_ofFn, Nat.add_sub_cancel_left]
    exact (tapeGet257 y' (j.castLE hb)).trans ((hy j).trans (tapeGet257 y j).symm)


theorem Code257.mono {n k c c' t t' : ℕ} (hc0 : 0 < c) (hc : c ≤ c') (ht : t ≤ t')
    {first : (Fin n → Bool) → Fin k → Bool}
    (h : Code257 n k c first (some t)) : Code257 n k c' first (some t') := by
  unfold Code257 at h ⊢
  dsimp only at h ⊢
  obtain ⟨code, hfirst, htri, hcircuits⟩ := h
  let pad (u : Fin n → Bool) (e : Fin 3) (j : Fin (if e = 2 then c' else k)) :=
    code u e (padPos257 hc0 e j)
  have hpad (u : Fin n → Bool) (e : Fin 3) (j : Fin (if e = 2 then c else k)) :
      pad u e (j.castLE (channelLe257 hc e)) = code u e j := by
    exact congrArg (code u e) (padPos257_castLE hc0 hc e j)
  refine ⟨pad, ?_, ?_, ?_⟩
  · intro u
    funext j
    exact (hpad u 0 j).trans (congrFun (hfirst u) j)
  · intro v hcycle
    apply htri v
    intro e
    funext j
    simpa only [hpad] using congrFun (hcycle e) (j.castLE (channelLe257 hc e))
  · intro limit hlimit
    cases hlimit
    obtain ⟨⟨enc, tap, ⟨hread, hsize, harity⟩, henc⟩, hdecs⟩ := hcircuits t rfl
    refine ⟨⟨enc, (fun e j => tap e (padPos257 hc0 e j)), ⟨hread, hsize.trans ht, harity⟩,
      (fun u e j => henc u e (padPos257 hc0 e j))⟩, ?_⟩
    intro e
    obtain ⟨dec, out, ⟨hdread, hdsize, hdarity⟩, hdec⟩ := hdecs e
    let f := embedTape257 (channelLe257 (k := k) hc e) (channelLe257 (k := k) hc (e+1))
    refine ⟨liftCircuit257 f dec, (fun j => ⟨rewire257 f (out j).val, ?_⟩), ?_, ?_⟩
    · simpa only [liftCircuit257_size] using rewire257_lt f (out j).isLt
    · exact ⟨liftCircuit257_reads f hdread,
        by simpa only [liftCircuit257_size] using hdsize.trans ht,
        liftCircuit257_arity f (C := dec)
          (P := fun op l => ((op = .and ∨ op = .or) ∧ l = 2) ∨ (op = .not ∧ l = 1))
          hdarity⟩
    · intro u j
      refine (liftCircuit257_wires f hdread
        (List.ofFn (code u e) ++ List.ofFn (code u (e+1)))
        (List.ofFn (pad u e) ++ List.ofFn (pad u (e+1))) (by simp) (by simp)
        (embedTape257_agree _ _ _ _ _ _ (hpad u e) (hpad u (e+1)))
        (out j).val (out j).isLt).trans (hdec u j)


open PEqualNP.CircuitLowerBounds

private theorem fixed257 : ∃ A K : ℕ, 0 < A ∧ ∀ k : ℕ, K ≤ k →
    Code257 (k+(k-1)) k (k+A*(k/(max 1 (Nat.log2 k))+1))
      (left257 (r := k-1)) (some ((k+1)^A)) := by
  classical
  obtain ⟨A₀, C, K, hK⟩ := params257_exists
  let I := {k : ℕ // K ≤ k}
  let B : I → ℕ := fun i => i.val+1
  choose p hp using fun i : I => hK i.val i.property
  have hB (i : I) : 2 ≤ B i := by
    have := (p i).k_pos
    dsimp [B]
    omega
  have bk : Bound B (fun i => i.val) := Bound.base.mono (fun i => Nat.le_succ _)
  have bwidth : Bound B (fun i => (p i).width) := by
    refine (Bound.add hB bk ((Bound.const hB A₀).mul (Bound.add hB bk (Bound.const hB 1)))).mono
      (fun i => (hp i).1.trans ?_)
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.div_le_self ..) _)) _
  have hBound : CodecBounds B p :=
    ⟨hB, bk, ⟨C, fun i => (hp i).2.1⟩, ⟨C, fun i => (hp i).2.2.1⟩,
      ⟨C, fun i => (hp i).2.2.2.1⟩, ⟨C, fun i => (hp i).2.2.2.2⟩,
      bwidth.mono (fun i => Nat.le_add_left ..)⟩
  obtain ⟨d, hd⟩ := packedCode257 hBound
  refine ⟨A₀+d+1, K, by omega, fun k hk => ?_⟩
  let i : I := ⟨k, hk⟩
  have hc : 0 < (p i).width := by
    unfold Params257.width Params257.lN
    omega
  apply Code257.mono hc _ _ (hd i)
  · exact (hp i).1.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : A₀ ≤ A₀+d+1)) _)
  · exact Nat.pow_le_pow_right (Nat.succ_pos k) (by omega)

end Part19
end PEqualNP.Outside.L_pcx_271_aux

open PEqualNP.Outside.L_pcx_271_aux

theorem PEqualNP.Outside.L_pcx_271 :
∃ A K : ℕ, 0 < A ∧ ∀ k : ℕ, K ≤ k →
  let c := k+A*(k/(max 1 (Nat.log2 k))+1)
  let X := Fin k → Bool
  let W := X × (Fin (k-1) → Bool)
  let raw := fun w : W => List.ofFn w.1 ++ List.ofFn w.2
  let len := fun e : Fin 3 => if e = 2 then c else k
  let valid := fun (inputs : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧ C.size ≤ (k+1)^A ∧
    ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)
  ∃ (send : W → X) (tag : W → Fin c → Bool)
    (enc : PEqualNP.CircuitLowerBounds.Circuit)
    (second : Fin k → Fin (k+(k-1)+enc.size)) (third : Fin c → Fin (k+(k-1)+enc.size)),
    valid (k+(k-1)) enc ∧
    (∀ w : W, (∀ j, (enc.wires (raw w)).getD (second j).val false = send w j) ∧
      ∀ j, (enc.wires (raw w)).getD (third j).val false = tag w j) ∧
    (∀ a b t : W, a.1 = b.1 → send b = send t → tag t = tag a → a = b ∧ b = t) ∧
    ∀ e : Fin 3,
      let port := fun (i : Fin 3) (w : W) =>
        if i = 0 then List.ofFn w.1 else if i = 1 then List.ofFn (send w) else List.ofFn (tag w)
      let width := len e + len (e+1)
      ∃ (dec : PEqualNP.CircuitLowerBounds.Circuit) (out : Fin (k+(k-1)) → Fin (width+dec.size)),
        valid width dec ∧ ∀ (w : W) (j : Fin (k+(k-1))),
          (dec.wires (port e w ++ port (e+1) w)).getD (out j).val false = (raw w).getD j.val false := by
  obtain ⟨A, K, hA, hK⟩ := fixed257
  refine ⟨A, K, hA, ?_⟩
  intro k hk
  dsimp only
  obtain ⟨code, hfirst, htri, hc⟩ := hK k hk
  obtain ⟨⟨enc, tap, henc, hev⟩, hd⟩ := hc _ rfl
  let tape (w : (Fin k → Bool) × (Fin (k-1) → Bool)) := Fin.append w.1 w.2
  have hleft (w) : code (tape w) 0 = w.1 := (hfirst _).trans (left_append257 _ _)
  have hinj : Function.Injective tape := by
    intro a b h
    exact Prod.ext ((left_append257 a.1 a.2).symm.trans
      ((congrArg left257 h).trans (left_append257 b.1 b.2)))
      ((right_append257 a.1 a.2).symm.trans
      ((congrArg right257 h).trans (right_append257 b.1 b.2)))
  have hport (e : Fin 3) (w : (Fin k → Bool) × (Fin (k-1) → Bool)) :
      (if e = 0 then List.ofFn w.1 else if e = 1 then List.ofFn (code (tape w) 1)
       else List.ofFn (code (tape w) 2)) = List.ofFn (code (tape w) e) := by
    fin_cases e
    · exact congrArg List.ofFn (hleft w).symm
    · rfl
    · rfl
  refine ⟨fun w => code (tape w) 1, fun w => code (tape w) 2,
    enc, tap 1, tap 2, henc, ?_, ?_, ?_⟩
  · intro w
    exact ⟨fun j => by simpa only [tape, List.ofFn_fin_append] using hev (tape w) 1 j,
      fun j => by simpa only [tape, List.ofFn_fin_append] using hev (tape w) 2 j⟩
  · intro a b t hab hbt hta
    let v : Fin 3 → Fin (k+(k-1)) → Bool := ![tape a, tape b, tape t]
    have hv : ∀ e : Fin 3, code (v e) e = code (v (e+1)) e := by
      intro e
      fin_cases e
      · exact (hleft a).trans (hab.trans (hleft b).symm)
      · exact hbt
      · exact hta
    exact ⟨hinj (htri v hv 1).symm, hinj ((htri v hv 1).trans (htri v hv 2).symm)⟩
  · intro e
    obtain ⟨dec, out, hvalid, hdec⟩ := hd e
    refine ⟨dec, out, hvalid, ?_⟩
    intro w j
    rw [hport e w, hport (e+1) w, ← List.ofFn_fin_append w.1 w.2, tapeGet257]
    exact hdec (tape w) j
