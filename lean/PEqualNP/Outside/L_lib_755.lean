import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_755

private def nxt {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

private def prv {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + k - 1) % k, Nat.mod_lt _ hk⟩

private lemma nxt_prv {k : ℕ} (hk : 0 < k) (i : Fin k) : nxt hk (prv hk i) = i := by
  ext
  simp only [nxt, prv]
  by_cases hi : i.val = 0
  · rw [hi]
    have h1 : (0 + k - 1) % k = k - 1 := by simp only [zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [h1, show k - 1 + 1 = k by omega, Nat.mod_self]
  · have h1 : (i.val + k - 1) % k = i.val - 1 := by
      have h2 : i.val + k - 1 = (i.val - 1) + k := by omega
      have hilt := i.isLt
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1, show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt i.isLt]

private lemma prv_nxt {k : ℕ} (hk : 0 < k) (i : Fin k) : prv hk (nxt hk i) = i := by
  ext
  simp only [nxt, prv]
  by_cases hi : i.val + 1 = k
  · rw [hi, Nat.mod_self]
    have h1 : (0 + k - 1) % k = k - 1 := by simp only [zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    omega
  · have hlt : i.val + 1 < k := by have := i.isLt; omega
    rw [Nat.mod_eq_of_lt hlt]
    have h2 : i.val + 1 + k - 1 = i.val + k := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

private def nxtEquiv {k : ℕ} (hk : 0 < k) : Fin k ≃ Fin k where
  toFun := nxt hk
  invFun := prv hk
  left_inv := prv_nxt hk
  right_inv := nxt_prv hk

private def rot {k : ℕ} (hk : 0 < k) (p i : Fin k) : Fin k :=
  ⟨(p.val + i.val) % k, Nat.mod_lt _ hk⟩

private def rotInv {k : ℕ} (hk : 0 < k) (p i : Fin k) : Fin k :=
  ⟨(i.val + k - p.val) % k, Nat.mod_lt _ hk⟩

private lemma rot_rotInv {k : ℕ} (hk : 0 < k) (p i : Fin k) : rot hk p (rotInv hk p i) = i := by
  ext
  simp only [rot, rotInv]
  have hi := i.isLt
  have hp := p.isLt
  by_cases h : p.val ≤ i.val
  · have h1 : i.val + k - p.val = (i.val - p.val) + k := by omega
    have hlt : i.val - p.val < k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hlt,
      show p.val + (i.val - p.val) = i.val by omega, Nat.mod_eq_of_lt hi]
  · have h1 : i.val + k - p.val < k := by omega
    rw [Nat.mod_eq_of_lt h1, show p.val + (i.val + k - p.val) = i.val + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hi]

private lemma rotInv_rot {k : ℕ} (hk : 0 < k) (p i : Fin k) : rotInv hk p (rot hk p i) = i := by
  ext
  simp only [rot, rotInv]
  have hi := i.isLt
  have hp := p.isLt
  by_cases h : p.val + i.val < k
  · rw [Nat.mod_eq_of_lt h]
    have h1 : p.val + i.val + k - p.val = i.val + k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have h1 : (p.val + i.val) % k = p.val + i.val - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h1, show p.val + i.val - k + k - p.val = i.val by omega, Nat.mod_eq_of_lt hi]

private lemma rot_nxt {k : ℕ} (hk : 0 < k) (p i : Fin k) :
    rot hk p (nxt hk i) = nxt hk (rot hk p i) := by
  ext
  simp only [rot, nxt]
  rw [Nat.add_mod p.val, Nat.mod_mod, ← Nat.add_mod, Nat.add_mod _ 1, Nat.mod_mod, ← Nat.add_mod, add_assoc]

private lemma rot_prv {k : ℕ} (hk : 0 < k) (p i : Fin k) :
    rot hk p (prv hk i) = prv hk (rot hk p i) := by
  apply (nxtEquiv hk).injective
  change nxt hk (rot hk p (prv hk i)) = nxt hk (prv hk (rot hk p i))
  rw [← rot_nxt hk p (prv hk i), nxt_prv hk, nxt_prv hk]

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

private lemma zmod2_ne_one_iff (x : ZMod 2) : x ≠ 1 ↔ x = 0 := by
  rcases zmod2_cases x with rfl | rfl
  · exact ⟨fun _ => rfl, fun _ => zero_ne_one⟩
  · exact ⟨fun h => absurd rfl h, fun h => absurd h one_ne_zero⟩

private lemma zmod2_ne_zero_iff (x : ZMod 2) : x ≠ 0 ↔ x = 1 := by
  rcases zmod2_cases x with rfl | rfl
  · exact ⟨fun h => absurd rfl h, fun h => absurd h zero_ne_one⟩
  · exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩

private def ones {k : ℕ} (m : Fin k → ZMod 2) : Finset (Fin k) :=
  Finset.univ.filter (fun i => m i = 1)

private def zeros {k : ℕ} (m : Fin k → ZMod 2) : Finset (Fin k) :=
  Finset.univ.filter (fun i => m i = 0)

private def S1 {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2) : Finset (Fin k) :=
  Finset.univ.filter (fun i => m i = 1 ∧ m (prv hk i) = 0)

private def E1 {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2) : Finset (Fin k) :=
  Finset.univ.filter (fun i => m i = 1 ∧ m (nxt hk i) = 0)

private def Left0 {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2) : Finset (Fin k) :=
  Finset.univ.filter (fun i => m i = 0 ∧ m (prv hk i) = 1)

private def Right0 {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2) : Finset (Fin k) :=
  Finset.univ.filter (fun i => m i = 0 ∧ m (nxt hk i) = 1)

private def Free0 {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2) : Finset (Fin k) :=
  Finset.univ.filter (fun i => m i = 0 ∧ m (prv hk i) = 0 ∧ m (nxt hk i) = 0)

private def fiberSet {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter (fun u => ∀ i, m i * u (nxt hk i) = u i * m (nxt hk i))

private lemma ones_add_zeros {k : ℕ} (m : Fin k → ZMod 2) :
    (ones m).card + (zeros m).card = k := by
  have h1 : zeros m = Finset.univ.filter (fun i => ¬ m i = 1) := by
    ext i; simp [zeros, zmod2_ne_one_iff]
  rw [h1]
  simpa [ones] using Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun i : Fin k => m i = 1)

private lemma card_E1_eq_card_S1 {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2) :
    (E1 hk m).card = (S1 hk m).card := by
  let Bprv := Finset.univ.filter (fun i : Fin k => m i = 1 ∧ m (prv hk i) = 1)
  let Bnxt := Finset.univ.filter (fun i : Fin k => m i = 1 ∧ m (nxt hk i) = 1)
  have hB : Bnxt.card = Bprv.card := by
    refine Finset.card_bij (fun i _ => nxt hk i) ?_ ?_ ?_
    · intro i hi
      simp only [Bnxt, Bprv, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨hi.2, by rw [prv_nxt]; exact hi.1⟩
    · intro i1 _ i2 _ heq
      exact (nxtEquiv hk).injective heq
    · intro j hj
      refine ⟨prv hk j, ?_, nxt_prv hk j⟩
      simp only [Bnxt, Bprv, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ⟨hj.2, by rw [nxt_prv]; exact hj.1⟩
  have hsum1 : (S1 hk m).card + Bprv.card = (ones m).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext i; simp only [S1, Bprv, ones, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases zmod2_cases (m (prv hk i)) with h | h <;> simp [h]
    · rw [Finset.disjoint_left]; intro i hi1 hi2
      simp only [S1, Bprv, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
      rw [hi1.2] at hi2; exact zero_ne_one hi2.2
  have hsum2 : (E1 hk m).card + Bnxt.card = (ones m).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext i; simp only [E1, Bnxt, ones, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases zmod2_cases (m (nxt hk i)) with h | h <;> simp [h]
    · rw [Finset.disjoint_left]; intro i hi1 hi2
      simp only [E1, Bnxt, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
      rw [hi1.2] at hi2; exact zero_ne_one hi2.2
  omega

private lemma card_Left0_eq_card_S1 {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2) :
    (Left0 hk m).card = (S1 hk m).card := by
  rw [← card_E1_eq_card_S1 hk m]
  refine Finset.card_bij (fun i _ => prv hk i) ?_ ?_ ?_
  · intro i hi
    simp only [Left0, E1, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.2, by rw [nxt_prv]; exact hi.1⟩
  · intro i1 _ i2 _ heq
    exact (nxtEquiv hk).symm.injective heq
  · intro j hj
    refine ⟨nxt hk j, ?_, prv_nxt hk j⟩
    simp only [Left0, E1, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.2, by rw [prv_nxt]; exact hj.1⟩

private lemma card_Right0_eq_card_S1 {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2) :
    (Right0 hk m).card = (S1 hk m).card := by
  refine Finset.card_bij (fun i _ => nxt hk i) ?_ ?_ ?_
  · intro i hi
    simp only [Right0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨hi.2, by rw [prv_nxt]; exact hi.1⟩
  · intro i1 _ i2 _ heq
    exact (nxtEquiv hk).injective heq
  · intro j hj
    refine ⟨prv hk j, ?_, nxt_prv hk j⟩
    simp only [Right0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj.2, by rw [nxt_prv]; exact hj.1⟩

private lemma eq_of_add_mod_eq {k a b d : ℕ} (ha : a < k) (hb : b < k) (hd : d < k)
    (h : (a + d) % k = (b + d) % k) : a = b := by
  by_cases c1 : a + d < k <;> by_cases c2 : b + d < k
  · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at h; omega
  · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega
  · rw [Nat.mod_eq_of_lt c2, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h; omega

private lemma card_S1_pos {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2)
    (h1 : 0 < (ones m).card) (h0 : 0 < (zeros m).card) :
    1 ≤ (S1 hk m).card := by
  obtain ⟨i1, hi1⟩ := Finset.card_pos.1 h1
  obtain ⟨i0, hi0⟩ := Finset.card_pos.1 h0
  simp only [ones, Finset.mem_filter, Finset.mem_univ, true_and] at hi1
  simp only [zeros, Finset.mem_filter, Finset.mem_univ, true_and] at hi0
  have hreach : ∀ s : ℕ, ∃ j : Fin k, j = (prv hk)^[s] i1 := fun s => ⟨_, rfl⟩
  have hex : ∃ s : ℕ, m ((prv hk)^[s] i1) = 0 := by
    let d := (i1.val + k - i0.val) % k
    refine ⟨d, ?_⟩
    have hiter : ∀ t : ℕ, ((prv hk)^[t] i1).val = (i1.val + t * (k - 1)) % k := by
      intro t
      induction t with
      | zero => simp [Nat.mod_eq_of_lt i1.isLt]
      | succ t ih =>
        rw [Function.iterate_succ_apply']
        simp only [prv, ih]
        have hstep : ((i1.val + t * (k - 1)) % k + k - 1) % k =
            (i1.val + (t + 1) * (k - 1)) % k := by
          have ha : (i1.val + t * (k - 1)) % k + k - 1 = (i1.val + t * (k - 1)) % k + (k - 1) := by omega
          rw [ha, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          congr 1; ring
        exact hstep
    have heq : (prv hk)^[d] i1 = i0 := by
      ext
      rw [hiter d]
      have hdk : (i1.val + d * (k - 1)) + d = i1.val + d * k := by
        have : d * (k - 1) + d = d * k := by
          calc d * (k - 1) + d = d * (k - 1 + 1) := by ring
            _ = d * k := by rw [Nat.sub_add_cancel (by omega)]
        omega
      have hmod : (i1.val + d * (k - 1)) % k = i0.val := by
        have hd_lt : d < k := Nat.mod_lt _ hk
        have hsum : (i1.val + k - i0.val) % k = d := rfl
        have hcong : (i0.val + d) % k = i1.val := by
          by_cases hle : i0.val ≤ i1.val
          · have hdv : d = i1.val - i0.val := by
              change (i1.val + k - i0.val) % k = i1.val - i0.val
              rw [show i1.val + k - i0.val = (i1.val - i0.val) + k by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [hdv, show i0.val + (i1.val - i0.val) = i1.val by omega, Nat.mod_eq_of_lt i1.isLt]
          · have hdv : d = i1.val + k - i0.val := Nat.mod_eq_of_lt (by omega)
            rw [hdv, show i0.val + (i1.val + k - i0.val) = i1.val + k by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt i1.isLt]
        have hmul : (i1.val + d * (k - 1)) + (i0.val + d) = i0.val + i1.val + d * k := by omega
        have hq : i1.val + d * (k - 1) + d = i1.val + d * k := hdk
        have hstep2 : (i1.val + d * (k - 1) + d) % k = i1.val := by
          rw [hq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i1.isLt]
        have hmod2 : ((i1.val + d * (k - 1)) % k + d) % k = (i0.val + d) % k := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hstep2, hcong]
        have hlt1 : (i1.val + d * (k - 1)) % k < k := Nat.mod_lt _ hk
        have hlt2 : i0.val < k := i0.isLt
        exact eq_of_add_mod_eq hlt1 hlt2 hd_lt hmod2
      exact hmod
    rw [heq]
    exact hi0
  classical
  let s0 := Nat.find hex
  have hs0_spec : m ((prv hk)^[s0] i1) = 0 := Nat.find_spec hex
  have hs0_pos : 0 < s0 := by
    by_contra hle
    have hs0 : s0 = 0 := by omega
    rw [hs0, Function.iterate_zero_apply] at hs0_spec
    rw [hi1] at hs0_spec
    exact one_ne_zero hs0_spec
  have hprev_one : m ((prv hk)^[s0 - 1] i1) = 1 := by
    have hne : m ((prv hk)^[s0 - 1] i1) ≠ 0 := Nat.find_min hex (by omega)
    exact (zmod2_ne_zero_iff _).1 hne
  have hmem : (prv hk)^[s0 - 1] i1 ∈ S1 hk m := by
    simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hprev_one, ?_⟩
    have hsucc : (s0 - 1).succ = s0 := by omega
    rw [← Function.iterate_succ_apply' (prv hk) (s0 - 1) i1, hsucc]
    exact hs0_spec
  exact Finset.one_le_card.2 ⟨_, hmem⟩

private lemma card_fiber_of_mixed {k : ℕ} (hk : 0 < k) (m : Fin k → ZMod 2)
    (_h1 : 0 < (ones m).card) (h0 : 0 < (zeros m).card) :
    (S1 hk m).card + (Right0 hk m \ Left0 hk m).card ≤ (zeros m).card ∧
    (fiberSet hk m).card = 2 ^ ((zeros m).card - (Right0 hk m \ Left0 hk m).card) := by
  set r := (S1 hk m).card
  set t := (Right0 hk m \ Left0 hk m).card
  have hLR_sub : Left0 hk m ∪ Right0 hk m ⊆ zeros m := by
    intro i hi
    simp only [Left0, Right0, zeros, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rcases hi with h | h <;> exact h.1
  have hLR_eq : Left0 hk m ∪ Right0 hk m = Left0 hk m ∪ (Right0 hk m \ Left0 hk m) := by
    ext i; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  have hLR_card : (Left0 hk m ∪ Right0 hk m).card = r + t := by
    rw [hLR_eq, Finset.card_union_of_disjoint Finset.disjoint_sdiff, card_Left0_eq_card_S1 hk m]
  have hrt_le : r + t ≤ (zeros m).card := by
    rw [← hLR_card]
    exact Finset.card_le_card hLR_sub
  have hFree_eq : Free0 hk m = zeros m \ (Left0 hk m ∪ Right0 hk m) := by
    ext i
    simp only [Free0, zeros, Left0, Right0, Finset.mem_sdiff, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_and]
    constructor
    · rintro ⟨h0i, hp, hn⟩
      refine ⟨h0i, ?_, ?_⟩
      · intro _; rw [hp]; exact zero_ne_one
      · intro _; rw [hn]; exact zero_ne_one
    · rintro ⟨h0i, hL, hR⟩
      exact ⟨h0i, (zmod2_ne_one_iff _).1 (hL h0i), (zmod2_ne_one_iff _).1 (hR h0i)⟩
  have hFree_card : (Free0 hk m).card = (zeros m).card - (r + t) := by
    rw [hFree_eq, Finset.card_sdiff, Finset.inter_eq_left.2 hLR_sub, hLR_card]
  have hdisj_SF : Disjoint (S1 hk m) (Free0 hk m) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [S1, Free0, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    rw [hi1.1] at hi2
    exact one_ne_zero hi2.1
  have hSF_card : (S1 hk m ∪ Free0 hk m).card = (zeros m).card - t := by
    rw [Finset.card_union_of_disjoint hdisj_SF, hFree_card]
    omega
  refine ⟨hrt_le, ?_⟩
  have hex_zero : ∀ i : Fin k, ∃ s : ℕ, m ((prv hk)^[s + 1] i) = 0 := by
    intro i
    obtain ⟨i0, hi0⟩ := Finset.card_pos.1 h0
    simp only [zeros, Finset.mem_filter, Finset.mem_univ, true_and] at hi0
    let j := prv hk i
    let d := (j.val + k - i0.val) % k
    refine ⟨d, ?_⟩
    have hiter : ∀ t : ℕ, ((prv hk)^[t] j).val = (j.val + t * (k - 1)) % k := by
      intro n
      induction n with
      | zero => simp [Nat.mod_eq_of_lt j.isLt]
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        simp only [prv, ih]
        have ha : (j.val + n * (k - 1)) % k + k - 1 = (j.val + n * (k - 1)) % k + (k - 1) := by omega
        rw [ha, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        congr 1; ring
    have heq : (prv hk)^[d] j = i0 := by
      ext
      rw [hiter d]
      have hd_lt : d < k := Nat.mod_lt _ hk
      have hcong : (i0.val + d) % k = j.val := by
        by_cases hle : i0.val ≤ j.val
        · have hdv : d = j.val - i0.val := by
            change (j.val + k - i0.val) % k = j.val - i0.val
            rw [show j.val + k - i0.val = (j.val - i0.val) + k by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hdv, show i0.val + (j.val - i0.val) = j.val by omega, Nat.mod_eq_of_lt j.isLt]
        · have hdv : d = j.val + k - i0.val := Nat.mod_eq_of_lt (by omega)
          rw [hdv, show i0.val + (j.val + k - i0.val) = j.val + k by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
      have hdk : j.val + d * (k - 1) + d = j.val + d * k := by
        have : d * (k - 1) + d = d * k := by
          calc d * (k - 1) + d = d * (k - 1 + 1) := by ring
            _ = d * k := by rw [Nat.sub_add_cancel (by omega)]
        omega
      have hstep2 : (j.val + d * (k - 1) + d) % k = j.val := by
        rw [hdk, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
      have hmod2 : ((j.val + d * (k - 1)) % k + d) % k = (i0.val + d) % k := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hstep2, hcong]
      have hlt1 : (j.val + d * (k - 1)) % k < k := Nat.mod_lt _ hk
      have hlt2 : i0.val < k := i0.isLt
      exact eq_of_add_mod_eq hlt1 hlt2 hd_lt hmod2
    rw [Function.iterate_succ_apply]
    change m ((prv hk)^[d] j) = 0
    rw [heq]
    exact hi0
  classical
  let rdist : Fin k → ℕ := fun i => Nat.find (hex_zero i)
  let rstart : Fin k → Fin k := fun i => (prv hk)^[rdist i] i
  have hrstart_prv0 : ∀ i, m (prv hk (rstart i)) = 0 := by
    intro i
    change m (prv hk ((prv hk)^[rdist i] i)) = 0
    rw [← Function.iterate_succ_apply' (prv hk) (rdist i) i]
    exact Nat.find_spec (hex_zero i)
  have hrstart_all1 : ∀ i, m i = 1 → ∀ s ≤ rdist i, m ((prv hk)^[s] i) = 1 := by
    intro i hi s hs
    cases s with
    | zero => simpa using hi
    | succ s' =>
      have hlt : s' < Nat.find (hex_zero i) := by dsimp only [rdist] at hs; omega
      have hne : m ((prv hk)^[s' + 1] i) ≠ 0 := Nat.find_min (hex_zero i) hlt
      exact (zmod2_ne_zero_iff _).1 hne
  have hrstart_mem : ∀ i, m i = 1 → rstart i ∈ S1 hk m := by
    intro i hi
    simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hrstart_all1 i hi (rdist i) le_rfl, hrstart_prv0 i⟩
  have hrstart_of_S1 : ∀ i ∈ S1 hk m, rstart i = i := by
    intro i hi
    simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hd0 : rdist i = 0 := (Nat.find_eq_zero (hex_zero i)).2 (by simpa using hi.2)
    simp [rstart, hd0]
  have hrstart_nxt : ∀ i, m i = 1 → m (nxt hk i) = 1 → rstart (nxt hk i) = rstart i := by
    intro i hi hni
    have hd : rdist (nxt hk i) = rdist i + 1 := by
      apply le_antisymm
      · apply Nat.find_min'
        rw [Function.iterate_succ_apply (prv hk) (rdist i + 1) (nxt hk i), prv_nxt]
        exact Nat.find_spec (hex_zero i)
      · by_contra hlt
        have hlt' : rdist (nxt hk i) ≤ rdist i := by omega
        cases hcase : rdist (nxt hk i) with
        | zero =>
          have hsp : m ((prv hk)^[rdist (nxt hk i) + 1] (nxt hk i)) = 0 := Nat.find_spec (hex_zero (nxt hk i))
          rw [hcase, zero_add, Function.iterate_one, prv_nxt] at hsp
          rw [hi] at hsp; exact one_ne_zero hsp
        | succ d' =>
          have hsp : m ((prv hk)^[rdist (nxt hk i) + 1] (nxt hk i)) = 0 := Nat.find_spec (hex_zero (nxt hk i))
          rw [hcase, Function.iterate_succ_apply (prv hk) (d' + 1) (nxt hk i), prv_nxt] at hsp
          have hmin := Nat.find_min (hex_zero i) (show d' < Nat.find (hex_zero i) by dsimp only [rdist] at hlt' hcase; omega)
          exact hmin hsp
    dsimp only [rstart]
    rw [hd, Function.iterate_succ_apply (prv hk) (rdist i) (nxt hk i), prv_nxt]
  let B := S1 hk m ∪ Free0 hk m
  have hcardB : Fintype.card (B → ZMod 2) = 2 ^ ((zeros m).card - t) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_coe, hSF_card]
  rw [← hcardB]
  refine Finset.card_bij (fun (u : Fin k → ZMod 2) _ => fun (x : B) => u x.1) ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro u1 hu1 u2 hu2 heq
    simp only [fiberSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu1 hu2
    have hconst : ∀ (u : Fin k → ZMod 2),
        (∀ i, m i * u (nxt hk i) = u i * m (nxt hk i)) →
        ∀ i, m i = 1 → u i = u (rstart i) := by
      intro u hu i hi
      have hind : ∀ s ≤ rdist i, u ((prv hk)^[s] i) = u i := by
        intro s
        induction s with
        | zero => intro _; rfl
        | succ s ih =>
          intro hs
          have h1s : m ((prv hk)^[s + 1] i) = 1 := hrstart_all1 i hi (s + 1) hs
          have h1p : m ((prv hk)^[s] i) = 1 := hrstart_all1 i hi s (by omega)
          have hstep := hu ((prv hk)^[s + 1] i)
          have hnxt_eq : nxt hk ((prv hk)^[s + 1] i) = (prv hk)^[s] i := by
            rw [Function.iterate_succ_apply', nxt_prv]
          rw [hnxt_eq, h1s, h1p, one_mul, mul_one] at hstep
          rw [← hstep, ih (by omega)]
      exact (hind (rdist i) le_rfl).symm
    have hzero_adj : ∀ (u : Fin k → ZMod 2),
        (∀ i, m i * u (nxt hk i) = u i * m (nxt hk i)) →
        ∀ i, m i = 0 → i ∉ Free0 hk m → u i = 0 := by
      intro u hu i hi0 hnf
      simp only [Free0, Finset.mem_filter, Finset.mem_univ, true_and, hi0, not_and] at hnf
      by_cases hp : m (prv hk i) = 0
      · have hn : m (nxt hk i) = 1 := (zmod2_ne_zero_iff _).1 (hnf hp)
        have hstep := hu i
        rw [hi0, hn, zero_mul, mul_one] at hstep
        exact hstep.symm
      · have hp1 : m (prv hk i) = 1 := (zmod2_ne_zero_iff _).1 hp
        have hstep := hu (prv hk i)
        rw [nxt_prv, hp1, hi0, one_mul, mul_zero] at hstep
        exact hstep
    funext i
    rcases zmod2_cases (m i) with hi0 | hi1
    · by_cases hfi : i ∈ Free0 hk m
      · exact congrFun heq ⟨i, Finset.mem_union_right _ hfi⟩
      · rw [hzero_adj u1 hu1 i hi0 hfi, hzero_adj u2 hu2 i hi0 hfi]
    · rw [hconst u1 hu1 i hi1, hconst u2 hu2 i hi1]
      exact congrFun heq ⟨rstart i, Finset.mem_union_left _ (hrstart_mem i hi1)⟩
  · intro g _
    let u : Fin k → ZMod 2 := fun i =>
      if hi1 : m i = 1 then g ⟨rstart i, Finset.mem_union_left _ (hrstart_mem i hi1)⟩
      else if hfi : i ∈ Free0 hk m then g ⟨i, Finset.mem_union_right _ hfi⟩
      else 0
    refine ⟨u, ?_, ?_⟩
    · simp only [fiberSet, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      rcases zmod2_cases (m i) with hi0 | hi1 <;> rcases zmod2_cases (m (nxt hk i)) with hn0 | hn1
      · simp [hi0, hn0]
      · have hni : i ∉ Free0 hk m := by
          simp only [Free0, Finset.mem_filter, Finset.mem_univ, true_and, hn1]
          intro h; exact one_ne_zero h.2.2
        have hui : u i = 0 := by simp [u, hi0, hni]
        simp [hi0, hn1, hui]
      · have hnn : nxt hk i ∉ Free0 hk m := by
          simp only [Free0, Finset.mem_filter, Finset.mem_univ, true_and, prv_nxt, hi1]
          intro h; exact one_ne_zero h.2.1
        have huni : u (nxt hk i) = 0 := by simp [u, hn0, hnn]
        simp [hi1, hn0, huni]
      · have hreq : rstart (nxt hk i) = rstart i := hrstart_nxt i hi1 hn1
        simp only [hi1, hn1, one_mul, mul_one, u, dite_true]
        congr 1
        exact Subtype.ext hreq
    · funext ⟨i, hiB⟩
      rcases Finset.mem_union.1 hiB with hiS | hiF
      · have hi1 : m i = 1 := (Finset.mem_filter.1 hiS).2.1
        have hreq : rstart i = i := hrstart_of_S1 i hiS
        simp only [u, hi1, dite_true]
        congr 1
        exact Subtype.ext hreq
      · have hi0 : m i = 0 := (Finset.mem_filter.1 hiF).2.1
        simp [u, hi0, hiF]

private def posComps (n m : ℕ) : Finset (Fin m → Fin (n + 1)) :=
  Finset.univ.filter (fun x => (∀ j, 1 ≤ (x j).val) ∧ ∑ j : Fin m, (x j).val = n)

private lemma card_posComps {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (posComps n m).card = Nat.choose (n - 1) (m - 1) := by
  have hchoose : ((Finset.univ : Finset (Fin (n - 1))).powersetCard (m - 1)).card =
      Nat.choose (n - 1) (m - 1) := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hchoose]
  let pref : (Fin m → Fin (n + 1)) → Fin (m - 1) → ℕ :=
    fun x j => (Finset.univ.filter (fun i : Fin m => i.val ≤ j.val)).sum (fun i => (x i).val)
  have hpref_mono : ∀ x ∈ posComps n m, StrictMono (pref x) := by
    intro x hx j1 j2 hlt
    simp only [posComps, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    let s1 := Finset.univ.filter (fun i : Fin m => i.val ≤ j1.val)
    let s2 := Finset.univ.filter (fun i : Fin m => i.val ≤ j2.val)
    have hsub : s1 ⊆ s2 := by
      intro i hi
      simp only [s1, s2, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      omega
    have hmem : (⟨j2.val, by omega⟩ : Fin m) ∈ s2 \ s1 := by
      simp only [s1, s2, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hpos : 0 < (s2 \ s1).sum (fun i => (x i).val) := by
      have hle := Finset.single_le_sum (f := fun i : Fin m => (x i).val)
        (fun _ _ => Nat.zero_le _) hmem
      have h1 := hx.1 ⟨j2.val, by omega⟩
      omega
    have hsplit : (s2 \ s1).sum (fun i => (x i).val) + s1.sum (fun i => (x i).val) =
        s2.sum (fun i => (x i).val) := Finset.sum_sdiff hsub
    change s1.sum (fun i => (x i).val) < s2.sum (fun i => (x i).val)
    omega
  have hpref_bounds : ∀ x ∈ posComps n m, ∀ j : Fin (m - 1), 1 ≤ pref x j ∧ pref x j ≤ n - 1 := by
    intro x hx j
    simp only [posComps, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    let s := Finset.univ.filter (fun i : Fin m => i.val ≤ j.val)
    have hmem0 : (⟨0, by omega⟩ : Fin m) ∈ s := by simp [s]
    have hlo : 1 ≤ s.sum (fun i => (x i).val) :=
      (hx.1 ⟨0, by omega⟩).trans (Finset.single_le_sum (f := fun i : Fin m => (x i).val) (fun _ _ => Nat.zero_le _) hmem0)
    have hmemlast : (⟨m - 1, by omega⟩ : Fin m) ∈ Finset.univ \ s := by
      simp only [s, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter]
      omega
    have htail : 1 ≤ (Finset.univ \ s).sum (fun i => (x i).val) :=
      (hx.1 ⟨m - 1, by omega⟩).trans (Finset.single_le_sum (f := fun i : Fin m => (x i).val) (fun _ _ => Nat.zero_le _) hmemlast)
    have htot : (Finset.univ \ s).sum (fun i => (x i).val) + s.sum (fun i => (x i).val) = n := by
      rw [Finset.sum_sdiff (Finset.subset_univ s), hx.2]
    exact ⟨hlo, by change s.sum (fun i => (x i).val) ≤ n - 1; omega⟩
  refine Finset.card_bij
    (fun x hx => (Finset.univ : Finset (Fin (m - 1))).image
      (fun j => (⟨pref x j - 1, by have := hpref_bounds x hx j; omega⟩ : Fin (n - 1))))
    ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    rw [Finset.card_image_of_injective]
    · simp
    · intro j1 j2 heq
      have hv : pref x j1 - 1 = pref x j2 - 1 := congrArg Fin.val heq
      have h1 := (hpref_bounds x hx j1).1
      have h2 := (hpref_bounds x hx j2).1
      exact (hpref_mono x hx).injective (by omega)
  · intro x1 hx1 x2 hx2 heq
    have hf1 : StrictMono (fun j : Fin (m - 1) =>
        (⟨pref x1 j - 1, by have := hpref_bounds x1 hx1 j; omega⟩ : Fin (n - 1))) := by
      intro j1 j2 hlt
      change pref x1 j1 - 1 < pref x1 j2 - 1
      have h1 := (hpref_bounds x1 hx1 j1).1
      have hlt' := hpref_mono x1 hx1 hlt
      omega
    have hf2 : StrictMono (fun j : Fin (m - 1) =>
        (⟨pref x2 j - 1, by have := hpref_bounds x2 hx2 j; omega⟩ : Fin (n - 1))) := by
      intro j1 j2 hlt
      change pref x2 j1 - 1 < pref x2 j2 - 1
      have h1 := (hpref_bounds x2 hx2 j1).1
      have hlt' := hpref_mono x2 hx2 hlt
      omega
    have hrange : Set.range (fun j : Fin (m - 1) =>
          (⟨pref x1 j - 1, by have := hpref_bounds x1 hx1 j; omega⟩ : Fin (n - 1))) =
        Set.range (fun j : Fin (m - 1) =>
          (⟨pref x2 j - 1, by have := hpref_bounds x2 hx2 j; omega⟩ : Fin (n - 1))) := by
      ext y
      have hmem := Finset.ext_iff.1 heq y
      simpa [Finset.mem_image, Set.mem_range] using hmem
    have hfun : (fun j : Fin (m - 1) => pref x1 j) = fun j => pref x2 j := by
      have he1 : OrderEmbedding.ofStrictMono _ hf1 =
          OrderEmbedding.ofStrictMono _ hf2 := by
        have hcard1 : (Finset.univ.image (fun j : Fin (m - 1) =>
            (⟨pref x1 j - 1, by have := hpref_bounds x1 hx1 j; omega⟩ : Fin (n - 1)))).card = m - 1 := by
          rw [Finset.card_image_of_injective _ hf1.injective]; simp
        have hEq := Finset.orderEmbOfFin_unique' hcard1 (f := OrderEmbedding.ofStrictMono _ hf1)
          (by intro j; simp)
        have hEq2 := Finset.orderEmbOfFin_unique' (heq ▸ hcard1) (f := OrderEmbedding.ofStrictMono _ hf2)
          (by intro j; simp)
        have hord : ∀ (A B : Finset (Fin (n - 1))) (hAB : A = B) (hA : A.card = m - 1),
            A.orderEmbOfFin hA = B.orderEmbOfFin (hAB ▸ hA) := by
          rintro A _ rfl _; rfl
        rw [hEq, hEq2]
        exact hord _ _ heq hcard1
      funext j
      have hv := congrArg (fun e => (e j).val) he1
      dsimp at hv
      have h1 := (hpref_bounds x1 hx1 j).1
      have h2 := (hpref_bounds x2 hx2 j).1
      omega
    have hsum1 := (Finset.mem_filter.1 hx1).2.2
    have hsum2 := (Finset.mem_filter.1 hx2).2.2
    have hall : ∀ r : ℕ, (hr : r < m) →
        (Finset.univ.filter (fun i : Fin m => i.val ≤ r)).sum (fun i => (x1 i).val) =
        (Finset.univ.filter (fun i : Fin m => i.val ≤ r)).sum (fun i => (x2 i).val) := by
      intro r hr
      by_cases hlast : r < m - 1
      · exact congrFun hfun ⟨r, hlast⟩
      · have heqr : r = m - 1 := by omega
        have hfil : Finset.univ.filter (fun i : Fin m => i.val ≤ r) = Finset.univ := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; have := i.isLt; omega
        rw [hfil, hsum1, hsum2]
    funext i
    ext
    by_cases hi0 : i.val = 0
    · have h0 := hall 0 (by omega)
      have hfil : Finset.univ.filter (fun j : Fin m => j.val ≤ 0) = {i} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
        omega
      rw [hfil, Finset.sum_singleton, Finset.sum_singleton] at h0
      exact h0
    · have hcur := hall i.val i.isLt
      have hprev := hall (i.val - 1) (by omega)
      have hsplit : ∀ (x : Fin m → Fin (n + 1)),
          (Finset.univ.filter (fun j : Fin m => j.val ≤ i.val)).sum (fun j => (x j).val) =
          (Finset.univ.filter (fun j : Fin m => j.val ≤ i.val - 1)).sum (fun j => (x j).val) + (x i).val := by
        intro x
        have hsub : Finset.univ.filter (fun j : Fin m => j.val ≤ i.val) =
            insert i (Finset.univ.filter (fun j : Fin m => j.val ≤ i.val - 1)) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        have hni : i ∉ Finset.univ.filter (fun j : Fin m => j.val ≤ i.val - 1) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
        rw [hsub, Finset.sum_insert hni, add_comm]
      rw [hsplit x1, hsplit x2, hprev] at hcur
      omega
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hcard : S.card = m - 1 := hS.2
    let e := S.orderEmbOfFin hcard
    let bp : ℕ → ℕ := fun idx =>
      if h0 : idx = 0 then 0
      else if hlt : idx < m then (e ⟨idx - 1, by omega⟩).val + 1
      else n
    have hbp_strict : ∀ j : Fin m, bp j.val < bp (j.val + 1) := by
      intro j
      by_cases hj0 : j.val = 0
      · simp only [bp, hj0, dite_true, show ¬ (0 + 1 = 0) by omega, dite_false]
        split_ifs with hlt
        · omega
        · omega
      · by_cases hlast : j.val + 1 < m
        · have hjlt : j.val < m := by omega
          simp only [bp, hj0, hjlt, hlast, show ¬ (j.val + 1 = 0) by omega, dite_false, dite_true]
          have hst : e ⟨j.val - 1, by omega⟩ < e ⟨j.val, by omega⟩ :=
            e.strictMono (show (⟨j.val - 1, by omega⟩ : Fin (m - 1)) < ⟨j.val, by omega⟩ from by
              change j.val - 1 < j.val; omega)
          have hval : (e ⟨j.val - 1, by omega⟩).val < (e ⟨j.val, by omega⟩).val := hst
          have hidx : (⟨j.val + 1 - 1, by omega⟩ : Fin (m - 1)) = ⟨j.val, by omega⟩ := by ext; simp
          rw [hidx]
          omega
        · have hjlt : j.val < m := j.isLt
          simp only [bp, hj0, hjlt, hlast, show ¬ (j.val + 1 = 0) by omega, dite_false, dite_true]
          have hlt2 := (e ⟨j.val - 1, by omega⟩).isLt
          omega
    have hbp_le : ∀ j : Fin m, bp (j.val + 1) ≤ n := by
      intro j
      simp only [bp, show ¬ (j.val + 1 = 0) by omega, dite_false]
      split_ifs with hlt
      · have := (e ⟨j.val, by omega⟩).isLt; omega
      · exact le_rfl
    let x : Fin m → Fin (n + 1) := fun j =>
      ⟨bp (j.val + 1) - bp j.val, by have := hbp_le j; omega⟩
    have hpref_x : ∀ r : ℕ, (hr : r ≤ m) →
        (Finset.univ.filter (fun i : Fin m => i.val < r)).sum (fun i => (x i).val) = bp r := by
      intro r
      induction r with
      | zero =>
        intro _
        have h0 : Finset.univ.filter (fun i : Fin m => i.val < 0) = ∅ := by ext i; simp
        simp [bp]
      | succ r ih =>
        intro hr
        have hsub : Finset.univ.filter (fun i : Fin m => i.val < r + 1) =
            insert ⟨r, by omega⟩ (Finset.univ.filter (fun i : Fin m => i.val < r)) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        have hni : (⟨r, by omega⟩ : Fin m) ∉ Finset.univ.filter (fun i : Fin m => i.val < r) := by
          simp
        rw [hsub, Finset.sum_insert hni, ih (by omega)]
        have hlt := hbp_strict ⟨r, by omega⟩
        dsimp at hlt
        change bp (r + 1) - bp r + bp r = bp (r + 1)
        omega
    have hx_mem : x ∈ posComps n m := by
      simp only [posComps, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun j => by have := hbp_strict j; change 1 ≤ bp (j.val + 1) - bp j.val; omega, ?_⟩
      have hm_eq := hpref_x m le_rfl
      have hall : Finset.univ.filter (fun i : Fin m => i.val < m) = Finset.univ := by
        ext i; simp
      rw [hall] at hm_eq
      rw [hm_eq]
      simp [bp, show ¬ m = 0 by omega]
    refine ⟨x, hx_mem, ?_⟩
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      have hfil : Finset.univ.filter (fun i : Fin m => i.val ≤ j.val) =
          Finset.univ.filter (fun i : Fin m => i.val < j.val + 1) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have hpj : pref x j = bp (j.val + 1) := by
        dsimp only [pref]; rw [hfil]; exact hpref_x (j.val + 1) (by omega)
      have heq_y : (⟨pref x j - 1, by have := hpref_bounds x hx_mem j; omega⟩ : Fin (n - 1)) = e j := by
        ext
        simp only [hpj, bp, show ¬ j.val + 1 = 0 by omega, show j.val + 1 < m by omega, dite_false, dite_true]
        simp
      rw [heq_y]
      exact Finset.orderEmbOfFin_mem S hcard j
    · intro hy
      have hmem_range : y ∈ Set.range e := by
        rw [Finset.range_orderEmbOfFin S hcard]
        exact hy
      obtain ⟨j, rfl⟩ := hmem_range
      refine ⟨j, ?_⟩
      have hfil : Finset.univ.filter (fun i : Fin m => i.val ≤ j.val) =
          Finset.univ.filter (fun i : Fin m => i.val < j.val + 1) := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have hpj : pref x j = bp (j.val + 1) := by
        dsimp only [pref]; rw [hfil]; exact hpref_x (j.val + 1) (by omega)
      ext
      simp only [hpj, bp, show ¬ j.val + 1 = 0 by omega, show j.val + 1 < m by omega, dite_false, dite_true]
      simp

private def zeroComps (b r t : ℕ) : Finset (Fin r → Fin (b + 1)) :=
  (posComps b r).filter (fun y => (Finset.univ.filter (fun j : Fin r => 2 ≤ (y j).val)).card = t)

private lemma card_zeroComps {b r t : ℕ} (hr : 1 ≤ r) (htr : t ≤ r) (hrt : r + t ≤ b) :
    (zeroComps b r t).card =
      Nat.choose r t * (if t = 0 then (if r = b then 1 else 0) else Nat.choose (b - r - 1) (t - 1)) := by
  let extVal := if t = 0 then (if r = b then 1 else 0) else Nat.choose (b - r - 1) (t - 1)
  have hpart : (zeroComps b r t).card =
      ∑ T ∈ (Finset.univ : Finset (Fin r)).powersetCard t,
        ((zeroComps b r t).filter (fun y => Finset.univ.filter (fun j : Fin r => 2 ≤ (y j).val) = T)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext y
      simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ, true_and,
        Finset.mem_filter]
      constructor
      · intro hy
        exact ⟨Finset.univ.filter (fun j : Fin r => 2 ≤ (y j).val), (Finset.mem_filter.1 hy).2, hy, rfl⟩
      · rintro ⟨_, _, hy, _⟩; exact hy
    · intro T1 _ T2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro y h1 h2
      rw [Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  rw [hpart]
  have heach : ∀ T ∈ (Finset.univ : Finset (Fin r)).powersetCard t,
      ((zeroComps b r t).filter (fun y => Finset.univ.filter (fun j : Fin r => 2 ≤ (y j).val) = T)).card = extVal := by
    intro T hT
    rw [Finset.mem_powersetCard] at hT
    have hTcard : T.card = t := hT.2
    by_cases ht0 : t = 0
    · subst ht0
      have hTempty : T = ∅ := Finset.card_eq_zero.1 hTcard
      simp only [extVal, ite_true]
      by_cases hrb : r = b
      · simp only [hrb, ite_true]
        let y1 : Fin r → Fin (b + 1) := fun _ => ⟨1, by omega⟩
        have hsing : (zeroComps b r 0).filter (fun y => Finset.univ.filter (fun j : Fin r => 2 ≤ (y j).val) = T) = {y1} := by
          ext y
          simp only [zeroComps, posComps, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, hTempty]
          constructor
          · rintro ⟨⟨⟨hge, _⟩, _⟩, hemp⟩
            funext j
            ext
            have hnot : ¬ 2 ≤ (y j).val := by
              intro h2
              have hmem : j ∈ Finset.univ.filter (fun j : Fin r => 2 ≤ (y j).val) := by simp [h2]
              rw [hemp] at hmem; exact Finset.notMem_empty j hmem
            have h1 := hge j
            change (y j).val = 1; omega
          · rintro rfl
            refine ⟨⟨⟨fun _ => le_rfl, by simp [y1, hrb]⟩, ?_⟩, ?_⟩
            · have : Finset.univ.filter (fun j : Fin r => 2 ≤ (y1 j).val) = ∅ := by ext j; simp [y1]
              simp [this]
            · ext j; simp [y1]
        rw [hsing, Finset.card_singleton]
      · simp only [hrb, ite_false]
        apply Finset.card_eq_zero.2
        rw [Finset.eq_empty_iff_forall_notMem]
        intro y hy
        simp only [zeroComps, posComps, Finset.mem_filter, Finset.mem_univ, true_and, hTempty] at hy
        have hall1 : ∀ j : Fin r, (y j).val = 1 := by
          intro j
          have hnot : ¬ 2 ≤ (y j).val := by
            intro h2
            have hmem : j ∈ Finset.univ.filter (fun j : Fin r => 2 ≤ (y j).val) := by simp [h2]
            rw [hy.2] at hmem; exact Finset.notMem_empty j hmem
          have h1 := hy.1.1.1 j
          omega
        have hsum : ∑ j : Fin r, (y j).val = r := by
          calc ∑ j : Fin r, (y j).val = ∑ _j : Fin r, 1 := Finset.sum_congr rfl (fun j _ => hall1 j)
            _ = r := by simp
        exact hrb (hsum.symm.trans hy.1.1.2)
    · simp only [extVal, ht0, ite_false]
      rw [← card_posComps (show 1 ≤ t by omega) (show t ≤ b - r by omega)]
      let eT := T.orderEmbOfFin hTcard
      refine Finset.card_bij
        (fun y hy => fun u : Fin t =>
          (⟨(y (eT u)).val - 1, by
            have hy' := (Finset.mem_filter.1 hy).1
            have hsum := (Finset.mem_filter.1 (Finset.mem_filter.1 hy').1).2.2
            have hge := (Finset.mem_filter.1 (Finset.mem_filter.1 hy').1).2.1
            have hsingle : (y (eT u)).val + (Finset.univ.erase (eT u)).sum (fun j => (y j).val) = b := by
              rw [Finset.add_sum_erase Finset.univ (fun j : Fin r => (y j).val) (Finset.mem_univ (eT u)), hsum]
            have hrest : r - 1 ≤ (Finset.univ.erase (eT u)).sum (fun j => (y j).val) := by
              calc r - 1 = (Finset.univ.erase (eT u)).card := by simp
                _ = ∑ _j ∈ Finset.univ.erase (eT u), 1 := by simp
                _ ≤ ∑ j ∈ Finset.univ.erase (eT u), (y j).val := Finset.sum_le_sum (fun j _ => hge j)
            omega⟩ : Fin (b - r + 1)))
        ?_ ?_ ?_
      · intro y hy
        simp only [zeroComps, posComps, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        refine ⟨?_, ?_⟩
        · intro u
          have hmem : eT u ∈ T := Finset.orderEmbOfFin_mem T hTcard u
          rw [← hy.2] at hmem
          have h2 : 2 ≤ (y (eT u)).val := (Finset.mem_filter.1 hmem).2
          omega
        · have hsplit : ∑ j ∈ Finset.univ \ T, (y j).val + ∑ j ∈ T, (y j).val = ∑ j : Fin r, (y j).val :=
            Finset.sum_sdiff (Finset.subset_univ T)
          have hout : ∑ j ∈ Finset.univ \ T, (y j).val = r - t := by
            have hall1 : ∀ j ∈ Finset.univ \ T, (y j).val = 1 := by
              intro j hj
              have hnt : j ∉ T := (Finset.mem_sdiff.1 hj).2
              rw [← hy.2] at hnt
              have hnot2 : ¬ 2 ≤ (y j).val := by simpa using hnt
              have h1 := hy.1.1.1 j
              omega
            rw [Finset.sum_congr rfl hall1, Finset.sum_const, smul_eq_mul, mul_one,
              Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.subset_univ T),
              Finset.card_univ, Fintype.card_fin, hTcard]
          have hin : ∑ u : Fin t, ((y (eT u)).val - 1) + t = ∑ j ∈ T, (y j).val := by
            have hbij : ∑ u : Fin t, (y (eT u)).val = ∑ j ∈ T, (y j).val := by
              refine Finset.sum_bij (fun u _ => eT u) ?_ ?_ ?_ ?_
              · intro u _; exact Finset.orderEmbOfFin_mem T hTcard u
              · intro u1 _ u2 _ h; exact eT.injective h
              · intro j hj
                have : j ∈ Set.range eT := by rw [Finset.range_orderEmbOfFin T hTcard]; exact hj
                obtain ⟨u, rfl⟩ := this
                exact ⟨u, Finset.mem_univ u, rfl⟩
              · intro _ _; rfl
            rw [← hbij]
            have hge1 : ∀ u : Fin t, 1 ≤ (y (eT u)).val := fun u => hy.1.1.1 (eT u)
            calc ∑ u : Fin t, ((y (eT u)).val - 1) + t
                = ∑ u : Fin t, ((y (eT u)).val - 1) + ∑ _u : Fin t, 1 := by simp
              _ = ∑ u : Fin t, (((y (eT u)).val - 1) + 1) := by rw [← Finset.sum_add_distrib]
              _ = ∑ u : Fin t, (y (eT u)).val := Finset.sum_congr rfl (fun u _ => Nat.sub_add_cancel (hge1 u))
          have hsum := hy.1.1.2
          omega
      · intro y1 hy1 y2 hy2 heq
        simp only [zeroComps, posComps, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
        funext j
        ext
        by_cases hjT : j ∈ T
        · have : j ∈ Set.range eT := by rw [Finset.range_orderEmbOfFin T hTcard]; exact hjT
          obtain ⟨u, rfl⟩ := this
          have hv := congrArg Fin.val (congrFun heq u)
          dsimp at hv
          have h1 := hy1.1.1.1 (eT u)
          have h2 := hy2.1.1.1 (eT u)
          omega
        · have hnot1 : ¬ 2 ≤ (y1 j).val := by
            have h := hjT; rw [← hy1.2] at h; simpa using h
          have hnot2 : ¬ 2 ≤ (y2 j).val := by
            have h := hjT; rw [← hy2.2] at h; simpa using h
          have h1 := hy1.1.1.1 j
          have h2 := hy2.1.1.1 j
          omega
      · intro z hz
        simp only [posComps, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        classical
        let bijT : Fin t ≃ T := Equiv.ofBijective
          (fun u : Fin t => (⟨eT u, Finset.orderEmbOfFin_mem T hTcard u⟩ : T))
          ⟨fun u1 u2 h => eT.injective (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
            have : x ∈ Set.range eT := by rw [Finset.range_orderEmbOfFin T hTcard]; exact hx
            obtain ⟨u, rfl⟩ := this; exact ⟨u, rfl⟩⟩
        let y : Fin r → Fin (b + 1) := fun j =>
          if hj : j ∈ T then
            let u : Fin t := bijT.symm ⟨j, hj⟩
            ⟨(z u).val + 1, by
              have hle : (z u).val ≤ b - r := by
                have := Finset.single_le_sum (f := fun v : Fin t => (z v).val)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
                omega
              omega⟩
          else ⟨1, by omega⟩
        have hy_eT : ∀ u : Fin t, (y (eT u)).val = (z u).val + 1 := by
          intro u
          have hmem : eT u ∈ T := Finset.orderEmbOfFin_mem T hTcard u
          simp only [y, hmem, dite_true]
          have hequ : bijT.symm ⟨eT u, hmem⟩ = u := bijT.symm_apply_apply u
          rw [hequ]
        have hy_out : ∀ j, j ∉ T → (y j).val = 1 := by
          intro j hj; simp [y, hj]
        have hy_fil : Finset.univ.filter (fun j : Fin r => 2 ≤ (y j).val) = T := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hj : j ∈ T
          · have : j ∈ Set.range eT := by rw [Finset.range_orderEmbOfFin T hTcard]; exact hj
            obtain ⟨u, rfl⟩ := this
            rw [hy_eT u]
            have := hz.1 u
            simp [hj, show 2 ≤ (z u).val + 1 by omega]
          · rw [hy_out j hj]; simp [hj]
        have hy_sum : ∑ j : Fin r, (y j).val = b := by
          have hsplit : ∑ j ∈ Finset.univ \ T, (y j).val + ∑ j ∈ T, (y j).val = ∑ j : Fin r, (y j).val :=
            Finset.sum_sdiff (Finset.subset_univ T)
          have hout : ∑ j ∈ Finset.univ \ T, (y j).val = r - t := by
            rw [Finset.sum_congr rfl (fun j hj => hy_out j (Finset.mem_sdiff.1 hj).2),
              Finset.sum_const, smul_eq_mul, mul_one,
              Finset.card_sdiff, Finset.inter_eq_left.2 (Finset.subset_univ T),
              Finset.card_univ, Fintype.card_fin, hTcard]
          have hin : ∑ j ∈ T, (y j).val = b - r + t := by
            have hbij : ∑ j ∈ T, (y j).val = ∑ u : Fin t, (y (eT u)).val := by
              symm
              refine Finset.sum_bij (fun u _ => eT u) ?_ ?_ ?_ ?_
              · intro u _; exact Finset.orderEmbOfFin_mem T hTcard u
              · intro u1 _ u2 _ h; exact eT.injective h
              · intro j hj
                have : j ∈ Set.range eT := by rw [Finset.range_orderEmbOfFin T hTcard]; exact hj
                obtain ⟨u, rfl⟩ := this; exact ⟨u, Finset.mem_univ u, rfl⟩
              · intro _ _; rfl
            rw [hbij, Finset.sum_congr rfl (fun u _ => hy_eT u), Finset.sum_add_distrib, hz.2]
            simp
          omega
        refine ⟨y, ?_, ?_⟩
        · simp only [zeroComps, posComps, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨⟨⟨?_, hy_sum⟩, by rw [hy_fil, hTcard]⟩, hy_fil⟩
          intro j
          by_cases hj : j ∈ T
          · have : j ∈ Set.range eT := by rw [Finset.range_orderEmbOfFin T hTcard]; exact hj
            obtain ⟨u, rfl⟩ := this; rw [hy_eT u]; omega
          · rw [hy_out j hj]
        · funext u
          ext
          dsimp
          rw [hy_eT u]
          omega
  rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private def linWords {k : ℕ} (hk : 0 < k) (a r t : ℕ) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter (fun w =>
    w ⟨0, hk⟩ = 1 ∧ w ⟨k - 1, by omega⟩ = 0 ∧
    (ones w).card = a ∧ (S1 hk w).card = r ∧ (Right0 hk w \ Left0 hk w).card = t)

private lemma card_linWords {k : ℕ} (hk : 0 < k) {a r t : ℕ}
    (ha0 : 0 < a) (hak : a < k) (hr1 : 1 ≤ r) (hra : r ≤ a)
    (htr : t ≤ r) (hrt : r + t ≤ k - a) :
    (linWords hk a r t).card =
      (posComps a r).card * (zeroComps (k - a) r t).card := by
  set b := k - a
  rw [← Finset.card_product]
  let prefXY : (Fin r → Fin (a + 1)) → (Fin r → Fin (b + 1)) → ℕ → ℕ :=
    fun x y j => (Finset.univ.filter (fun u : Fin r => u.val < j)).sum (fun u => (x u).val + (y u).val)
  let mkW : (Fin r → Fin (a + 1)) × (Fin r → Fin (b + 1)) → Fin k → ZMod 2 :=
    fun xy i =>
      if ∃ j : Fin r, prefXY xy.1 xy.2 j.val ≤ i.val ∧ i.val < prefXY xy.1 xy.2 j.val + (xy.1 j).val
      then 1 else 0
  have hpref_step : ∀ (x : Fin r → Fin (a + 1)) (y : Fin r → Fin (b + 1)) (j : Fin r),
      prefXY x y (j.val + 1) = prefXY x y j.val + (x j).val + (y j).val := by
    intro x y j
    dsimp only [prefXY]
    have hsub : Finset.univ.filter (fun u : Fin r => u.val < j.val + 1) =
        insert j (Finset.univ.filter (fun u : Fin r => u.val < j.val)) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnj : j ∉ Finset.univ.filter (fun u : Fin r => u.val < j.val) := by simp
    rw [hsub, Finset.sum_insert hnj]
    omega
  have hpref_zero : ∀ x y, prefXY x y 0 = 0 := by
    intro x y
    simp [prefXY]
  have hpref_top : ∀ x y, x ∈ posComps a r → y ∈ zeroComps b r t → prefXY x y r = k := by
    intro x y hx hy
    simp only [zeroComps, posComps, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    have hall : Finset.univ.filter (fun u : Fin r => u.val < r) = Finset.univ := by ext u; simp
    dsimp only [prefXY]
    rw [hall, Finset.sum_add_distrib, hx.2, hy.1.2]
    omega
  have hpref_mono : ∀ x y, x ∈ posComps a r → y ∈ zeroComps b r t →
      ∀ j1 j2 : ℕ, j1 ≤ j2 → j2 ≤ r → prefXY x y j1 ≤ prefXY x y j2 := by
    intro x y _ _ j1 j2 hle _
    dsimp only [prefXY]
    refine Finset.sum_le_sum_of_subset ?_
    intro u hu; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢; omega
  have hpref_strict : ∀ x y, x ∈ posComps a r → y ∈ zeroComps b r t →
      ∀ j1 j2 : ℕ, j1 < j2 → j2 ≤ r → prefXY x y j1 < prefXY x y j2 := by
    intro x y hx hy j1 j2 hlt hle
    have h1 := hpref_step x y ⟨j1, by omega⟩
    dsimp only at h1
    have h2 := hpref_mono x y hx hy (j1 + 1) j2 (by omega) hle
    have hx1 := (Finset.mem_filter.1 hx).2.1 ⟨j1, by omega⟩
    omega
  have hinterval_cover : ∀ x y, x ∈ posComps a r → y ∈ zeroComps b r t →
      ∀ i : Fin k, ∃! j : Fin r, prefXY x y j.val ≤ i.val ∧ i.val < prefXY x y (j.val + 1) := by
    intro x y hx hy i
    have hex : ∃ m : ℕ, m < r ∧ i.val < prefXY x y (m + 1) := by
      refine ⟨r - 1, by omega, ?_⟩
      rw [Nat.sub_add_cancel hr1, hpref_top x y hx hy]
      exact i.isLt
    classical
    let m0 := Nat.find hex
    have hm0 : m0 < r ∧ i.val < prefXY x y (m0 + 1) := Nat.find_spec hex
    have hlo : prefXY x y m0 ≤ i.val := by
      by_cases hm0_eq : m0 = 0
      · rw [hm0_eq, hpref_zero]; exact Nat.zero_le _
      · have hmin := Nat.find_min hex (show m0 - 1 < Nat.find hex by dsimp only [m0]; omega)
        push Not at hmin
        have h := hmin (by omega)
        rwa [Nat.sub_add_cancel (by omega)] at h
    refine ⟨⟨m0, hm0.1⟩, ⟨hlo, hm0.2⟩, ?_⟩
    rintro j ⟨hjlo, hjhi⟩
    ext
    dsimp only
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle := hpref_mono x y hx hy (j.val + 1) m0 (by omega) (by omega)
      omega
    · have hle := hpref_mono x y hx hy (m0 + 1) j.val (by omega) (by omega)
      omega
  have hmkW_prop : ∀ (xy : (Fin r → Fin (a + 1)) × (Fin r → Fin (b + 1)))
      (hxy : xy ∈ posComps a r ×ˢ zeroComps b r t),
      let x := xy.1
      let y := xy.2
      let w := mkW xy
      w ∈ linWords hk a r t ∧
      S1 hk w = Finset.univ.image (fun j : Fin r =>
        ⟨prefXY x y j.val, by
          have := hpref_strict x y (Finset.mem_product.1 hxy).1 (Finset.mem_product.1 hxy).2 j.val r j.isLt le_rfl
          rw [hpref_top x y (Finset.mem_product.1 hxy).1 (Finset.mem_product.1 hxy).2] at this
          exact this⟩) ∧
      Left0 hk w = Finset.univ.image (fun j : Fin r =>
        ⟨prefXY x y j.val + (x j).val, by
          have hst := hpref_step x y j
          have hy1 : 1 ≤ (y j).val := (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_product.1 hxy).2).1).2.1 j
          have hle := hpref_mono x y (Finset.mem_product.1 hxy).1 (Finset.mem_product.1 hxy).2 (j.val + 1) r (by omega) le_rfl
          rw [hpref_top x y (Finset.mem_product.1 hxy).1 (Finset.mem_product.1 hxy).2] at hle
          omega⟩) := by
    intro xy hxy
    rcases Finset.mem_product.1 hxy with ⟨hx, hy⟩
    set x := xy.1
    set y := xy.2
    set w := mkW xy
    have hx_ge : ∀ j, 1 ≤ (x j).val := (Finset.mem_filter.1 hx).2.1
    have hx_sum : ∑ j : Fin r, (x j).val = a := (Finset.mem_filter.1 hx).2.2
    have hy_ge : ∀ j, 1 ≤ (y j).val := (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2.1
    have hy_sum : ∑ j : Fin r, (y j).val = b := (Finset.mem_filter.1 (Finset.mem_filter.1 hy).1).2.2
    have hy_t : (Finset.univ.filter (fun j : Fin r => 2 ≤ (y j).val)).card = t := (Finset.mem_filter.1 hy).2
    have htop := hpref_top x y hx hy
    have hw_iff : ∀ i : Fin k, w i = 1 ↔ ∃ j : Fin r, prefXY x y j.val ≤ i.val ∧ i.val < prefXY x y j.val + (x j).val := by
      intro i
      dsimp only [w, mkW]
      split_ifs with h <;> simp [x, y, h]
    have hw0_iff : ∀ i : Fin k, w i = 0 ↔ ∀ j : Fin r, ¬ (prefXY x y j.val ≤ i.val ∧ i.val < prefXY x y j.val + (x j).val) := by
      intro i
      rw [← zmod2_ne_one_iff, ne_eq, hw_iff]
      simp
    have hw_0 : w ⟨0, hk⟩ = 1 := by
      rw [hw_iff]
      refine ⟨⟨0, hr1⟩, ?_, ?_⟩
      · dsimp only; rw [hpref_zero]
      · dsimp only; rw [hpref_zero]; have := hx_ge ⟨0, hr1⟩; omega
    have hw_last : w ⟨k - 1, by omega⟩ = 0 := by
      rw [hw0_iff]
      intro j ⟨_, hhi⟩
      dsimp only at hhi
      have hst := hpref_step x y j
      have hle := hpref_mono x y hx hy (j.val + 1) r (by omega) le_rfl
      have hy1 := hy_ge j
      omega
    have hS1_eq : S1 hk w = Finset.univ.image (fun j : Fin r =>
        ⟨prefXY x y j.val, by
          have := hpref_strict x y hx hy j.val r j.isLt le_rfl
          rw [htop] at this; exact this⟩) := by
      ext i
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Fin.ext_iff]
      constructor
      · rintro ⟨hi1, hip0⟩
        obtain ⟨j, hjlo, hjhi⟩ := (hw_iff i).1 hi1
        refine ⟨j, ?_⟩
        by_contra hne
        have hlt : prefXY x y j.val < i.val := by omega
        have hipos : 0 < i.val := by omega
        have hprv_val : (prv hk i).val = i.val - 1 := by
          simp only [prv]
          have hilt := i.isLt
          rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hp1 : w (prv hk i) = 1 := by
          rw [hw_iff]
          exact ⟨j, by omega, by omega⟩
        rw [hp1] at hip0
        exact one_ne_zero hip0
      · rintro ⟨j, hj⟩
        refine ⟨?_, ?_⟩
        · rw [hw_iff]
          exact ⟨j, by omega, by have := hx_ge j; omega⟩
        · by_cases hj0 : j.val = 0
          · have hi0 : i.val = 0 := by rw [← hj, hj0, hpref_zero]
            have hprv : prv hk i = ⟨k - 1, by omega⟩ := by
              ext; simp only [prv, hi0, zero_add]; exact Nat.mod_eq_of_lt (by omega)
            rw [hprv]
            exact hw_last
          · have hpos : 0 < i.val := by
              have := hpref_strict x y hx hy 0 j.val (by omega) (by omega)
              rw [hpref_zero] at this; omega
            have hprv_val : (prv hk i).val = i.val - 1 := by
              simp only [prv]
              have hilt := i.isLt
              rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [hw0_iff]
            intro j' ⟨hlo', hhi'⟩
            have hst_prev := hpref_step x y ⟨j.val - 1, by omega⟩
            dsimp only at hst_prev
            have hy_prev := hy_ge ⟨j.val - 1, by omega⟩
            have hjj : j.val - 1 + 1 = j.val := by omega
            rw [hjj] at hst_prev
            rcases lt_or_ge j'.val j.val with hlt | hge
            · by_cases heq' : j'.val = j.val - 1
              · have hje : j' = ⟨j.val - 1, by omega⟩ := Fin.ext heq'
                rw [hje] at hhi'
                dsimp only at hhi'
                omega
              · have hst' := hpref_step x y j'
                have hle2 := hpref_mono x y hx hy (j'.val + 1) (j.val - 1) (by omega) (by omega)
                omega
            · have hle := hpref_mono x y hx hy j.val j'.val hge (by omega)
              omega
    have hL0_eq : Left0 hk w = Finset.univ.image (fun j : Fin r =>
        ⟨prefXY x y j.val + (x j).val, by
          have hst := hpref_step x y j
          have hle := hpref_mono x y hx hy (j.val + 1) r (by omega) le_rfl
          have hy1 := hy_ge j
          omega⟩) := by
      ext i
      simp only [Left0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Fin.ext_iff]
      constructor
      · rintro ⟨hi0, hip1⟩
        obtain ⟨j, hjlo, hjhi⟩ := (hw_iff (prv hk i)).1 hip1
        have hipos : 0 < i.val := by
          by_contra h0
          have hi0v : i.val = 0 := by omega
          have h0e : i = ⟨0, hk⟩ := Fin.ext hi0v
          rw [h0e, hw_0] at hi0; exact one_ne_zero hi0
        have hprv_val : (prv hk i).val = i.val - 1 := by
          simp only [prv]
          rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        refine ⟨j, ?_⟩
        by_contra hne
        have hlt : i.val < prefXY x y j.val + (x j).val := by omega
        have hi1 : w i = 1 := (hw_iff i).2 ⟨j, by omega, hlt⟩
        rw [hi1] at hi0; exact one_ne_zero hi0
      · rintro ⟨j, hj⟩
        refine ⟨?_, ?_⟩
        · rw [hw0_iff]
          intro j' ⟨hlo', hhi'⟩
          rcases lt_or_ge j'.val j.val with hlt | hge
          · have hst' := hpref_step x y j'
            have hle := hpref_mono x y hx hy (j'.val + 1) j.val (by omega) (by omega)
            omega
          · by_cases heq' : j'.val = j.val
            · have : j' = j := Fin.ext heq'; rw [this] at hhi'; omega
            · have hst := hpref_step x y j
              have hle := hpref_mono x y hx hy (j.val + 1) j'.val (by omega) (by omega)
              have hy1 := hy_ge j
              omega
        · have hx1 := hx_ge j
          have hprv_val : (prv hk i).val = i.val - 1 := by
            simp only [prv]
            rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hw_iff]
          exact ⟨j, by omega, by omega⟩
    have hS1_card : (S1 hk w).card = r := by
      rw [hS1_eq, Finset.card_image_of_injective]
      · simp
      · intro j1 j2 heq
        have hv : prefXY x y j1.val = prefXY x y j2.val := congrArg Fin.val heq
        ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ne_of_lt (hpref_strict x y hx hy j1.val j2.val hlt (by omega)) hv
        · exact ne_of_gt (hpref_strict x y hx hy j2.val j1.val hgt (by omega)) hv
    have hones_card : (ones w).card = a := by
      have hbi : ones w = Finset.univ.biUnion (fun j : Fin r =>
          Finset.univ.filter (fun i : Fin k => prefXY x y j.val ≤ i.val ∧ i.val < prefXY x y j.val + (x j).val)) := by
        ext i
        simp only [ones, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hw_iff]
      rw [hbi, Finset.card_biUnion]
      · calc ∑ j : Fin r, (Finset.univ.filter (fun i : Fin k =>
              prefXY x y j.val ≤ i.val ∧ i.val < prefXY x y j.val + (x j).val)).card
            = ∑ j : Fin r, (x j).val := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              have hhi_le : prefXY x y j.val + (x j).val ≤ k := by
                have hst := hpref_step x y j
                have hle := hpref_mono x y hx hy (j.val + 1) r (by omega) le_rfl
                omega
              have hcard_f : (Finset.univ : Finset (Fin (x j).val)).card = (x j).val := by simp
              rw [← hcard_f]
              refine Finset.card_bij (fun i hi => (⟨i.val - prefXY x y j.val, by
                have := (Finset.mem_filter.1 hi).2; omega⟩ : Fin (x j).val)) ?_ ?_ ?_
              · intro _ _; exact Finset.mem_univ _
              · intro i1 hi1 i2 hi2 heq
                have h1 := (Finset.mem_filter.1 hi1).2
                have h2 := (Finset.mem_filter.1 hi2).2
                have hv := congrArg Fin.val heq; dsimp at hv
                ext; omega
              · intro d _
                refine ⟨⟨prefXY x y j.val + d.val, by have := d.isLt; omega⟩, ?_, ?_⟩
                · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have := d.isLt; omega
                · ext; simp
          _ = a := hx_sum
      · intro j1 _ j2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have h1 := (Finset.mem_filter.1 hi1).2
        have h2 := (Finset.mem_filter.1 hi2).2
        have hne' : j1.val ≠ j2.val := fun h => hne (Fin.ext h)
        rcases lt_or_gt_of_ne hne' with hlt | hgt
        · have hst := hpref_step x y j1
          have hle := hpref_mono x y hx hy (j1.val + 1) j2.val (by omega) (by omega)
          omega
        · have hst := hpref_step x y j2
          have hle := hpref_mono x y hx hy (j2.val + 1) j1.val (by omega) (by omega)
          omega
    have ht_card : (Right0 hk w \ Left0 hk w).card = t := by
      rw [← hy_t]
      have hnxtS_of_mem : ∀ i ∈ Right0 hk w \ Left0 hk w, nxt hk i ∈ S1 hk w := by
        intro i hi
        have hiR : i ∈ Right0 hk w := (Finset.mem_sdiff.1 hi).1
        simp only [Right0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hiR ⊢
        exact ⟨hiR.2, by rw [prv_nxt]; exact hiR.1⟩
      have hfindS1 : ∀ i : Fin k, nxt hk i ∈ S1 hk w → ∃ j : Fin r, prefXY x y j.val = (nxt hk i).val := by
        intro i hiS
        rw [hS1_eq, Finset.mem_image] at hiS
        obtain ⟨j, _, hj⟩ := hiS
        exact ⟨j, congrArg Fin.val hj⟩
      classical
      let findJ1 : (i : Fin k) → nxt hk i ∈ S1 hk w → Fin r := fun i hiS => Classical.choose (hfindS1 i hiS)
      have hfindJ1_spec : ∀ (i : Fin k) (hiS : nxt hk i ∈ S1 hk w), prefXY x y (findJ1 i hiS).val = (nxt hk i).val :=
        fun i hiS => Classical.choose_spec (hfindS1 i hiS)
      have hfindJ1_uniq : ∀ (i : Fin k) (hiS : nxt hk i ∈ S1 hk w) (j : Fin r),
          prefXY x y j.val = (nxt hk i).val → findJ1 i hiS = j := by
        intro i hiS j hj
        have hEq : prefXY x y (findJ1 i hiS).val = prefXY x y j.val := (hfindJ1_spec i hiS).trans hj.symm
        ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact ne_of_lt (hpref_strict x y hx hy _ _ hlt (by omega)) hEq
        · exact ne_of_gt (hpref_strict x y hx hy _ _ hgt (by omega)) hEq
      let toJ0 : Fin r → Fin r := fun j1 => ⟨if j1.val = 0 then r - 1 else j1.val - 1, by split_ifs <;> omega⟩
      have htoJ0_inj : Function.Injective toJ0 := by
        intro j1 j2 h
        have hv : (if j1.val = 0 then r - 1 else j1.val - 1) = (if j2.val = 0 then r - 1 else j2.val - 1) :=
          congrArg Fin.val h
        ext
        split_ifs at hv with c1 c2 c2 <;> omega
      refine Finset.card_bij (fun i hi => toJ0 (findJ1 i (hnxtS_of_mem i hi))) ?_ ?_ ?_
      · intro i hi
        have hiNL : i ∉ Left0 hk w := (Finset.mem_sdiff.1 hi).2
        have hnxtS := hnxtS_of_mem i hi
        set j1 := findJ1 i hnxtS
        have h2 : (nxt hk i).val = prefXY x y j1.val := (hfindJ1_spec i hnxtS).symm
        set j0 := toJ0 j1
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hi_val : i.val = prefXY x y (j0.val + 1) - 1 := by
          have h1 : prv hk (nxt hk i) = i := prv_nxt hk i
          by_cases hj10 : j1.val = 0
          · have hnxt0 : (nxt hk i).val = 0 := by rw [h2, hj10, hpref_zero]
            have hprv0 : (prv hk (nxt hk i)).val = k - 1 := by
              simp only [prv, hnxt0, zero_add]; exact Nat.mod_eq_of_lt (by omega)
            rw [h1] at hprv0
            have hj0v : j0.val + 1 = r := by dsimp [j0, toJ0]; simp [hj10]; omega
            rw [hprv0, hj0v, htop]
          · have hpos : 0 < (nxt hk i).val := by
              rw [h2]
              have := hpref_strict x y hx hy 0 j1.val (by omega) (by omega)
              rw [hpref_zero] at this; exact this
            have hprv1 : (prv hk (nxt hk i)).val = (nxt hk i).val - 1 := by
              simp only [prv]
              have hlt := (nxt hk i).isLt
              rw [show (nxt hk i).val + k - 1 = ((nxt hk i).val - 1) + k by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [h1] at hprv1
            have hj0v : j0.val + 1 = j1.val := by dsimp [j0, toJ0]; simp [hj10]; omega
            rw [hprv1, h2, hj0v]
        have hst0 := hpref_step x y j0
        have hneL : i.val ≠ prefXY x y j0.val + (x j0).val := by
          intro heq
          apply hiNL
          rw [hL0_eq, Finset.mem_image]
          exact ⟨j0, Finset.mem_univ j0, Fin.ext heq.symm⟩
        have hy1 := hy_ge j0
        omega
      · intro i1 hi1 i2 hi2 heq
        have hj12 : findJ1 i1 (hnxtS_of_mem i1 hi1) = findJ1 i2 (hnxtS_of_mem i2 hi2) := htoJ0_inj heq
        apply (nxtEquiv hk).injective
        change nxt hk i1 = nxt hk i2
        ext
        rw [← hfindJ1_spec i1 (hnxtS_of_mem i1 hi1), ← hfindJ1_spec i2 (hnxtS_of_mem i2 hi2), hj12]
      · intro j0 hj0
        have hy2 : 2 ≤ (y j0).val := (Finset.mem_filter.1 hj0).2
        have hst0 := hpref_step x y j0
        have hle0 := hpref_mono x y hx hy (j0.val + 1) r (by omega) le_rfl
        have hpos0 : 0 < prefXY x y (j0.val + 1) := by have := hx_ge j0; omega
        let i : Fin k := ⟨prefXY x y (j0.val + 1) - 1, by omega⟩
        let j1 : Fin r := ⟨if j0.val + 1 < r then j0.val + 1 else 0, by split_ifs <;> omega⟩
        have hnxt_eq : (nxt hk i).val = prefXY x y j1.val := by
          simp only [nxt, i]
          by_cases hlt : j0.val + 1 < r
          · have hlt_k : prefXY x y (j0.val + 1) < k := by
              have := hpref_strict x y hx hy (j0.val + 1) r hlt le_rfl
              rw [htop] at this; exact this
            rw [Nat.sub_add_cancel hpos0, Nat.mod_eq_of_lt hlt_k]
            simp [j1, hlt]
          · have heqr : j0.val + 1 = r := by omega
            rw [Nat.sub_add_cancel hpos0, heqr, htop, Nat.mod_self]
            simp [j1, hlt, hpref_zero]
        have hnxtS : nxt hk i ∈ S1 hk w := by
          rw [hS1_eq, Finset.mem_image]
          exact ⟨j1, Finset.mem_univ j1, Fin.ext hnxt_eq.symm⟩
        have hiR : i ∈ Right0 hk w := by
          simp only [S1, Right0, Finset.mem_filter, Finset.mem_univ, true_and] at hnxtS ⊢
          exact ⟨by rw [← prv_nxt hk i]; exact hnxtS.2, hnxtS.1⟩
        have hiNL : i ∉ Left0 hk w := by
          rw [hL0_eq, Finset.mem_image]
          rintro ⟨j', _, hj'⟩
          have hv : prefXY x y j'.val + (x j').val = prefXY x y (j0.val + 1) - 1 := congrArg Fin.val hj'
          rcases lt_or_ge j'.val j0.val with hlt | hge
          · have hst' := hpref_step x y j'
            have hle' := hpref_mono x y hx hy (j'.val + 1) j0.val (by omega) (by omega)
            have hx0 := hx_ge j0
            omega
          · by_cases heq' : j'.val = j0.val
            · have : j' = j0 := Fin.ext heq'; rw [this] at hv; omega
            · have hle' := hpref_mono x y hx hy (j0.val + 1) j'.val (by omega) (by omega)
              have hx' := hx_ge j'
              omega
        have hi_mem : i ∈ Right0 hk w \ Left0 hk w := Finset.mem_sdiff.2 ⟨hiR, hiNL⟩
        refine ⟨i, hi_mem, ?_⟩
        have hj1_eq : findJ1 i (hnxtS_of_mem i hi_mem) = j1 := hfindJ1_uniq i (hnxtS_of_mem i hi_mem) j1 hnxt_eq.symm
        rw [hj1_eq]
        apply Fin.ext
        change (if j1.val = 0 then r - 1 else j1.val - 1) = j0.val
        have hj0lt := j0.isLt
        by_cases hlt : j0.val + 1 < r
        · have hj1v : j1.val = j0.val + 1 := by simp [j1, hlt]
          simp only [hj1v, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
          omega
        · have hj1v : j1.val = 0 := by simp [j1, hlt]
          simp only [hj1v, ite_true]
          omega
    refine ⟨?_, hS1_eq, hL0_eq⟩
    simp only [linWords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hw_0, hw_last, hones_card, hS1_card, ht_card⟩
  symm
  refine Finset.card_bij (fun xy _ => mkW xy) ?_ ?_ ?_
  · intro xy hxy; exact (hmkW_prop xy hxy).1
  · intro xy1 hxy1 xy2 hxy2 heq
    have hp1 := hmkW_prop xy1 hxy1
    have hp2 := hmkW_prop xy2 hxy2
    have hS_eq : S1 hk (mkW xy1) = S1 hk (mkW xy2) := by rw [heq]
    have hL_eq : Left0 hk (mkW xy1) = Left0 hk (mkW xy2) := by rw [heq]
    rw [hp1.2.1, hp2.2.1] at hS_eq
    rw [hp1.2.2, hp2.2.2] at hL_eq
    rcases Finset.mem_product.1 hxy1 with ⟨hx1, hy1⟩
    rcases Finset.mem_product.1 hxy2 with ⟨hx2, hy2⟩
    have hfS1 : StrictMono (fun j : Fin r =>
        (⟨prefXY xy1.1 xy1.2 j.val, by
          have := hpref_strict xy1.1 xy1.2 hx1 hy1 j.val r j.isLt le_rfl
          rw [hpref_top xy1.1 xy1.2 hx1 hy1] at this; exact this⟩ : Fin k)) :=
      fun j1 j2 hlt => hpref_strict xy1.1 xy1.2 hx1 hy1 j1.val j2.val hlt (by omega)
    have hfS2 : StrictMono (fun j : Fin r =>
        (⟨prefXY xy2.1 xy2.2 j.val, by
          have := hpref_strict xy2.1 xy2.2 hx2 hy2 j.val r j.isLt le_rfl
          rw [hpref_top xy2.1 xy2.2 hx2 hy2] at this; exact this⟩ : Fin k)) :=
      fun j1 j2 hlt => hpref_strict xy2.1 xy2.2 hx2 hy2 j1.val j2.val hlt (by omega)
    have hS_fun : ∀ j : Fin r, prefXY xy1.1 xy1.2 j.val = prefXY xy2.1 xy2.2 j.val := by
      have hcardS : (Finset.univ.image (fun j : Fin r =>
          (⟨prefXY xy1.1 xy1.2 j.val, by
            have := hpref_strict xy1.1 xy1.2 hx1 hy1 j.val r j.isLt le_rfl
            rw [hpref_top xy1.1 xy1.2 hx1 hy1] at this; exact this⟩ : Fin k))).card = r := by
        rw [Finset.card_image_of_injective _ hfS1.injective]; simp
      have he1 := Finset.orderEmbOfFin_unique' hcardS (f := OrderEmbedding.ofStrictMono _ hfS1)
        (by intro j; simp)
      have he2 := Finset.orderEmbOfFin_unique' (hS_eq ▸ hcardS) (f := OrderEmbedding.ofStrictMono _ hfS2)
        (by intro j; simp)
      have hord : ∀ (A B : Finset (Fin k)) (hAB : A = B) (hA : A.card = r) (j : Fin r),
          (A.orderEmbOfFin hA j).val = (B.orderEmbOfFin (hAB ▸ hA) j).val := by
        rintro A _ rfl _ _; rfl
      intro j
      have ha := congrArg (fun e => (e j).val) he1
      have hb := congrArg (fun e => (e j).val) he2
      dsimp at ha hb
      rw [ha, hb]
      exact hord _ _ hS_eq hcardS j
    have hfL1 : StrictMono (fun j : Fin r =>
        (⟨prefXY xy1.1 xy1.2 j.val + (xy1.1 j).val, by
          have hst := hpref_step xy1.1 xy1.2 j
          have hy1g := (Finset.mem_filter.1 (Finset.mem_filter.1 hy1).1).2.1 j
          have hle := hpref_mono xy1.1 xy1.2 hx1 hy1 (j.val + 1) r (by omega) le_rfl
          rw [hpref_top xy1.1 xy1.2 hx1 hy1] at hle; omega⟩ : Fin k)) := by
      intro j1 j2 hlt
      change prefXY xy1.1 xy1.2 j1.val + (xy1.1 j1).val < prefXY xy1.1 xy1.2 j2.val + (xy1.1 j2).val
      have hst := hpref_step xy1.1 xy1.2 j1
      have hle := hpref_mono xy1.1 xy1.2 hx1 hy1 (j1.val + 1) j2.val (by omega) (by omega)
      have hy1g := (Finset.mem_filter.1 (Finset.mem_filter.1 hy1).1).2.1 j1
      have hx2g := (Finset.mem_filter.1 hx1).2.1 j2
      omega
    have hfL2 : StrictMono (fun j : Fin r =>
        (⟨prefXY xy2.1 xy2.2 j.val + (xy2.1 j).val, by
          have hst := hpref_step xy2.1 xy2.2 j
          have hy2g := (Finset.mem_filter.1 (Finset.mem_filter.1 hy2).1).2.1 j
          have hle := hpref_mono xy2.1 xy2.2 hx2 hy2 (j.val + 1) r (by omega) le_rfl
          rw [hpref_top xy2.1 xy2.2 hx2 hy2] at hle; omega⟩ : Fin k)) := by
      intro j1 j2 hlt
      change prefXY xy2.1 xy2.2 j1.val + (xy2.1 j1).val < prefXY xy2.1 xy2.2 j2.val + (xy2.1 j2).val
      have hst := hpref_step xy2.1 xy2.2 j1
      have hle := hpref_mono xy2.1 xy2.2 hx2 hy2 (j1.val + 1) j2.val (by omega) (by omega)
      have hy2g := (Finset.mem_filter.1 (Finset.mem_filter.1 hy2).1).2.1 j1
      have hx2g := (Finset.mem_filter.1 hx2).2.1 j2
      omega
    have hL_fun : ∀ j : Fin r, prefXY xy1.1 xy1.2 j.val + (xy1.1 j).val = prefXY xy2.1 xy2.2 j.val + (xy2.1 j).val := by
      have hcardL : (Finset.univ.image (fun j : Fin r =>
          (⟨prefXY xy1.1 xy1.2 j.val + (xy1.1 j).val, by
            have hst := hpref_step xy1.1 xy1.2 j
            have hy1g := (Finset.mem_filter.1 (Finset.mem_filter.1 hy1).1).2.1 j
            have hle := hpref_mono xy1.1 xy1.2 hx1 hy1 (j.val + 1) r (by omega) le_rfl
            rw [hpref_top xy1.1 xy1.2 hx1 hy1] at hle; omega⟩ : Fin k))).card = r := by
        rw [Finset.card_image_of_injective _ hfL1.injective]; simp
      have he1 := Finset.orderEmbOfFin_unique' hcardL (f := OrderEmbedding.ofStrictMono _ hfL1)
        (by intro j; simp)
      have he2 := Finset.orderEmbOfFin_unique' (hL_eq ▸ hcardL) (f := OrderEmbedding.ofStrictMono _ hfL2)
        (by intro j; simp)
      have hord : ∀ (A B : Finset (Fin k)) (hAB : A = B) (hA : A.card = r) (j : Fin r),
          (A.orderEmbOfFin hA j).val = (B.orderEmbOfFin (hAB ▸ hA) j).val := by
        rintro A _ rfl _ _; rfl
      intro j
      have ha := congrArg (fun e => (e j).val) he1
      have hb := congrArg (fun e => (e j).val) he2
      dsimp at ha hb
      rw [ha, hb]
      exact hord _ _ hL_eq hcardL j
    ext j
    · have hS := hS_fun j; have hL := hL_fun j; omega
    · have hS := hS_fun j; have hL := hL_fun j
      have hst1 := hpref_step xy1.1 xy1.2 j
      have hst2 := hpref_step xy2.1 xy2.2 j
      by_cases hlt : j.val + 1 < r
      · have hSn := hS_fun ⟨j.val + 1, hlt⟩; dsimp only at hSn; omega
      · have heqr : j.val + 1 = r := by omega
        rw [heqr, hpref_top xy1.1 xy1.2 hx1 hy1] at hst1
        rw [heqr, hpref_top xy2.1 xy2.2 hx2 hy2] at hst2
        omega
  · intro w hw
    simp only [linWords, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rcases hw with ⟨hw0, hwlast, hones, hS1c, htc⟩
    have hL0c : (Left0 hk w).card = r := by rw [card_Left0_eq_card_S1 hk w, hS1c]
    let eS := (S1 hk w).orderEmbOfFin hS1c
    let eL := (Left0 hk w).orderEmbOfFin hL0c
    have h0_S1 : (⟨0, hk⟩ : Fin k) ∈ S1 hk w := by
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, hw0, true_and]
      have hprv0 : prv hk ⟨0, hk⟩ = ⟨k - 1, by omega⟩ := by
        ext; simp only [prv, zero_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [hprv0]; exact hwlast
    have heS0 : (eS ⟨0, hr1⟩).val = 0 := by
      have hmem : (⟨0, hk⟩ : Fin k) ∈ Set.range eS := by rw [Finset.range_orderEmbOfFin _ hS1c]; exact h0_S1
      obtain ⟨j, hj⟩ := hmem
      have hle : eS ⟨0, hr1⟩ ≤ eS j := eS.monotone (show (⟨0, hr1⟩ : Fin r) ≤ j from Nat.zero_le j.val)
      have hv : (eS ⟨0, hr1⟩).val ≤ (eS j).val := hle
      rw [hj] at hv; dsimp only at hv; omega
    have hbetween_SL : ∀ u v : Fin k, u.val < v.val → w u = 1 → w v = 0 →
        ∃ z ∈ Left0 hk w, u.val < z.val ∧ z.val ≤ v.val := by
      intro u v hlt hu hv
      have hex : ∃ d : ℕ, ∃ hd : d < k, u.val < d ∧ w ⟨d, hd⟩ = 0 := ⟨v.val, v.isLt, hlt, hv⟩
      classical
      let d0 := Nat.find hex
      have hd0 : ∃ hd : d0 < k, u.val < d0 ∧ w ⟨d0, hd⟩ = 0 := Nat.find_spec hex
      rcases hd0 with ⟨hd0_lt, hd0_gt, hd0_w⟩
      have hd0_le : d0 ≤ v.val := Nat.find_min' hex ⟨v.isLt, hlt, hv⟩
      have hprev1 : w ⟨d0 - 1, by omega⟩ = 1 := by
        by_cases heq : d0 - 1 = u.val
        · have : (⟨d0 - 1, by omega⟩ : Fin k) = u := Fin.ext heq
          rw [this]; exact hu
        · have hmin := Nat.find_min hex (show d0 - 1 < Nat.find hex by dsimp only [d0]; omega)
          push Not at hmin
          exact (zmod2_ne_zero_iff _).1 (hmin (by omega) (by omega))
      refine ⟨⟨d0, hd0_lt⟩, ?_, hd0_gt, hd0_le⟩
      simp only [Left0, Finset.mem_filter, Finset.mem_univ, true_and, hd0_w, true_and]
      have hprv_eq : prv hk ⟨d0, hd0_lt⟩ = ⟨d0 - 1, by omega⟩ := by
        ext; simp only [prv]
        rw [show d0 + k - 1 = (d0 - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hprv_eq]; exact hprev1
    have hbetween_LS : ∀ u v : Fin k, u.val < v.val → w u = 0 → w v = 1 →
        ∃ s ∈ S1 hk w, u.val < s.val ∧ s.val ≤ v.val := by
      intro u v hlt hu hv
      have hex : ∃ d : ℕ, ∃ hd : d < k, u.val < d ∧ w ⟨d, hd⟩ = 1 := ⟨v.val, v.isLt, hlt, hv⟩
      classical
      let d0 := Nat.find hex
      have hd0 : ∃ hd : d0 < k, u.val < d0 ∧ w ⟨d0, hd⟩ = 1 := Nat.find_spec hex
      rcases hd0 with ⟨hd0_lt, hd0_gt, hd0_w⟩
      have hd0_le : d0 ≤ v.val := Nat.find_min' hex ⟨v.isLt, hlt, hv⟩
      have hprev0 : w ⟨d0 - 1, by omega⟩ = 0 := by
        by_cases heq : d0 - 1 = u.val
        · have : (⟨d0 - 1, by omega⟩ : Fin k) = u := Fin.ext heq
          rw [this]; exact hu
        · have hmin := Nat.find_min hex (show d0 - 1 < Nat.find hex by dsimp only [d0]; omega)
          push Not at hmin
          exact (zmod2_ne_one_iff _).1 (hmin (by omega) (by omega))
      refine ⟨⟨d0, hd0_lt⟩, ?_, hd0_gt, hd0_le⟩
      simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, hd0_w, true_and]
      have hprv_eq : prv hk ⟨d0, hd0_lt⟩ = ⟨d0 - 1, by omega⟩ := by
        ext; simp only [prv]
        rw [show d0 + k - 1 = (d0 - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hprv_eq]; exact hprev0
    have hinterleave : ∀ j : Fin r,
        (eS j).val < (eL j).val ∧ ∀ (hj : j.val + 1 < r), (eL j).val < (eS ⟨j.val + 1, hj⟩).val := by
      have hSL : ∀ j : Fin r, (eS j).val < (eL j).val := by
        intro j
        by_contra hge
        have hle : (eL j).val ≤ (eS j).val := by omega
        have hlt : (eL j).val < (eS j).val := by
          have hne : eL j ≠ eS j := by
            intro heq
            have h1 := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hS1c j)).2.1
            have h0 := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hL0c j)).2.1
            rw [heq, h1] at h0; exact one_ne_zero h0
          have : (eL j).val ≠ (eS j).val := fun h => hne (Fin.ext h)
          omega
        have hcard_lt : (Finset.univ.filter (fun u : Fin r => u.val ≤ j.val)).card ≤
            (Finset.univ.filter (fun u : Fin r => (eS u).val < (eL j).val)).card := by
          have hmap : ∀ u : Fin r, u.val ≤ j.val → ∃ s ∈ S1 hk w,
              (if u.val = 0 then (0 : ℕ) ≤ s.val ∧ s.val < (eL u).val
               else (eL ⟨u.val - 1, by omega⟩).val < s.val ∧ s.val < (eL u).val) := by
            intro u _
            by_cases hu0 : u.val = 0
            · refine ⟨⟨0, hk⟩, h0_S1, ?_⟩
              simp only [hu0, ite_true, zero_le, true_and]
              have hne : eL u ≠ ⟨0, hk⟩ := by
                intro h; have h0 := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hL0c u)).2.1
                rw [h, hw0] at h0; exact one_ne_zero h0
              have : (eL u).val ≠ 0 := fun h => hne (Fin.ext h)
              omega
            · simp only [hu0, ite_false]
              have huL := Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hL0c u)
              have hpL := Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hL0c ⟨u.val - 1, by omega⟩)
              have hltL : (eL ⟨u.val - 1, by omega⟩).val < (eL u).val :=
                eL.strictMono (show (⟨u.val - 1, by omega⟩ : Fin r) < u from by change u.val - 1 < u.val; omega)
              have hposL : 0 < (eL u).val := by omega
              have hprv_eq : prv hk (eL u) = ⟨(eL u).val - 1, by omega⟩ := by
                ext; simp only [prv]
                rw [show (eL u).val + k - 1 = ((eL u).val - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              have hprv1 : w ⟨(eL u).val - 1, by omega⟩ = 1 := by rw [← hprv_eq]; exact huL.2.2
              have hlt2 : (eL ⟨u.val - 1, by omega⟩).val < (eL u).val - 1 := by
                have hne : (eL ⟨u.val - 1, by omega⟩).val ≠ (eL u).val - 1 := by
                  intro h
                  have : eL ⟨u.val - 1, by omega⟩ = ⟨(eL u).val - 1, by omega⟩ := Fin.ext h
                  rw [← this, hpL.2.1] at hprv1; exact zero_ne_one hprv1
                omega
              obtain ⟨s, hsS, hlo, hhi⟩ := hbetween_LS (eL ⟨u.val - 1, by omega⟩) ⟨(eL u).val - 1, by omega⟩ hlt2 hpL.2.1 hprv1
              dsimp only at hhi
              exact ⟨s, hsS, hlo, by omega⟩
          classical
          let pickS : (u : Fin r) → u.val ≤ j.val → Fin k := fun u hu => Classical.choose (hmap u hu)
          have hpickS_spec : ∀ (u : Fin r) (hu : u.val ≤ j.val),
              pickS u hu ∈ S1 hk w ∧
              (if u.val = 0 then (0 : ℕ) ≤ (pickS u hu).val ∧ (pickS u hu).val < (eL u).val
               else (eL ⟨u.val - 1, by omega⟩).val < (pickS u hu).val ∧ (pickS u hu).val < (eL u).val) :=
            fun u hu => Classical.choose_spec (hmap u hu)
          let idxS : (s : Fin k) → s ∈ S1 hk w → Fin r := fun s hs =>
            Classical.choose (show s ∈ Set.range eS by rw [Finset.range_orderEmbOfFin _ hS1c]; exact hs)
          have hidxS_spec : ∀ (s : Fin k) (hs : s ∈ S1 hk w), eS (idxS s hs) = s := fun s hs =>
            Classical.choose_spec (show s ∈ Set.range eS by rw [Finset.range_orderEmbOfFin _ hS1c]; exact hs)
          let f : Fin r → Fin r := fun u =>
            if hu : u.val ≤ j.val then idxS (pickS u hu) (hpickS_spec u hu).1 else ⟨0, hr1⟩
          refine Finset.card_le_card_of_injOn f ?_ ?_
          · intro u hu
            have huj : u.val ≤ j.val := (Finset.mem_filter.1 hu).2
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, f, huj, dite_true]
            rw [hidxS_spec (pickS u huj) (hpickS_spec u huj).1]
            have hlt_u : (pickS u huj).val < (eL u).val := by
              have h2 := (hpickS_spec u huj).2
              split_ifs at h2 <;> exact h2.2
            have hle_uj : (eL u).val ≤ (eL j).val := eL.monotone (show u ≤ j from huj)
            omega
          · intro u1 hu1 u2 hu2 hfeq
            have h1j : u1.val ≤ j.val := (Finset.mem_filter.1 hu1).2
            have h2j : u2.val ≤ j.val := (Finset.mem_filter.1 hu2).2
            simp only [f, h1j, h2j, dite_true] at hfeq
            have hs_eq : pickS u1 h1j = pickS u2 h2j := by
              rw [← hidxS_spec (pickS u1 h1j) (hpickS_spec u1 h1j).1,
                ← hidxS_spec (pickS u2 h2j) (hpickS_spec u2 h2j).1, hfeq]
            ext
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt12 | hlt21
            · have h2p := (hpickS_spec u2 h2j).2
              simp only [show ¬ u2.val = 0 by omega, ite_false] at h2p
              have h1p := (hpickS_spec u1 h1j).2
              have hs1_lt : (pickS u1 h1j).val < (eL u1).val := by split_ifs at h1p <;> exact h1p.2
              have hleL : (eL u1).val ≤ (eL ⟨u2.val - 1, by omega⟩).val :=
                eL.monotone (show u1 ≤ ⟨u2.val - 1, by omega⟩ from by change u1.val ≤ u2.val - 1; omega)
              rw [hs_eq] at hs1_lt
              omega
            · have h1p := (hpickS_spec u1 h1j).2
              simp only [show ¬ u1.val = 0 by omega, ite_false] at h1p
              have h2p := (hpickS_spec u2 h2j).2
              have hs2_lt : (pickS u2 h2j).val < (eL u2).val := by split_ifs at h2p <;> exact h2p.2
              have hleL : (eL u2).val ≤ (eL ⟨u1.val - 1, by omega⟩).val :=
                eL.monotone (show u2 ≤ ⟨u1.val - 1, by omega⟩ from by change u2.val ≤ u1.val - 1; omega)
              rw [← hs_eq] at hs2_lt
              omega
        have hsub : Finset.univ.filter (fun u : Fin r => (eS u).val < (eL j).val) ⊆
            Finset.univ.filter (fun u : Fin r => u.val < j.val) := by
          intro u hu
          have hlt_u : (eS u).val < (eL j).val := (Finset.mem_filter.1 hu).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_contra hge_u
          have hle_ju : (eS j).val ≤ (eS u).val := eS.monotone (show j ≤ u from by omega)
          omega
        have hc1 : (Finset.univ.filter (fun u : Fin r => u.val ≤ j.val)).card = j.val + 1 := by
          have : (Finset.univ.filter (fun u : Fin r => u.val ≤ j.val)).card = (Finset.univ : Finset (Fin (j.val + 1))).card := by
            refine Finset.card_bij (fun (u : Fin r) hu => (⟨u.val, by have := (Finset.mem_filter.1 hu).2; omega⟩ : Fin (j.val + 1)))
              (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
              (fun v _ => ⟨⟨v.val, by have := v.isLt; omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have := v.isLt; omega, by ext; simp⟩)
          simpa using this
        have hc2 : (Finset.univ.filter (fun u : Fin r => u.val < j.val)).card = j.val := by
          have : (Finset.univ.filter (fun u : Fin r => u.val < j.val)).card = (Finset.univ : Finset (Fin j.val)).card := by
            refine Finset.card_bij (fun (u : Fin r) hu => (⟨u.val, (Finset.mem_filter.1 hu).2⟩ : Fin j.val))
              (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
              (fun v _ => ⟨⟨v.val, by have := v.isLt; omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact v.isLt, by ext; simp⟩)
          simpa using this
        have hle_cards := hcard_lt.trans (Finset.card_le_card hsub)
        omega
      have hLS : ∀ (j : Fin r) (hj : j.val + 1 < r), (eL j).val < (eS ⟨j.val + 1, hj⟩).val := by
        intro j hj
        by_contra hge
        have hle : (eS ⟨j.val + 1, hj⟩).val ≤ (eL j).val := by omega
        have hlt : (eS ⟨j.val + 1, hj⟩).val < (eL j).val := by
          have hne : eS ⟨j.val + 1, hj⟩ ≠ eL j := by
            intro heq
            have h1 := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hS1c ⟨j.val + 1, hj⟩)).2.1
            have h0 := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hL0c j)).2.1
            rw [heq, h0] at h1; exact zero_ne_one h1
          have : (eS ⟨j.val + 1, hj⟩).val ≠ (eL j).val := fun h => hne (Fin.ext h)
          omega
        have hmap : ∀ u : Fin r, u.val ≤ j.val + 1 → ∃ z ∈ Left0 hk w,
            (eS u).val < z.val ∧ (∀ (hu : u.val + 1 < r), z.val < (eS ⟨u.val + 1, hu⟩).val) := by
          intro u _
          have huS := Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hS1c u)
          by_cases hlast : u.val + 1 < r
          · have hnS := Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hS1c ⟨u.val + 1, hlast⟩)
            have hltS : (eS u).val < (eS ⟨u.val + 1, hlast⟩).val :=
              eS.strictMono (show u < ⟨u.val + 1, hlast⟩ from by change u.val < u.val + 1; omega)
            have hposS : 0 < (eS ⟨u.val + 1, hlast⟩).val := by omega
            have hprv_eq : prv hk (eS ⟨u.val + 1, hlast⟩) = ⟨(eS ⟨u.val + 1, hlast⟩).val - 1, by omega⟩ := by
              ext; simp only [prv]
              have hlt' := (eS ⟨u.val + 1, hlast⟩).isLt
              rw [show (eS ⟨u.val + 1, hlast⟩).val + k - 1 = ((eS ⟨u.val + 1, hlast⟩).val - 1) + k by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            have hprv0 : w ⟨(eS ⟨u.val + 1, hlast⟩).val - 1, by omega⟩ = 0 := by rw [← hprv_eq]; exact hnS.2.2
            have hlt2 : (eS u).val < (eS ⟨u.val + 1, hlast⟩).val - 1 := by
              have hne : (eS u).val ≠ (eS ⟨u.val + 1, hlast⟩).val - 1 := by
                intro h
                have : eS u = ⟨(eS ⟨u.val + 1, hlast⟩).val - 1, by omega⟩ := Fin.ext h
                rw [← this, huS.2.1] at hprv0; exact one_ne_zero hprv0
              omega
            obtain ⟨z, hzL, hlo, hhi⟩ := hbetween_SL (eS u) ⟨(eS ⟨u.val + 1, hlast⟩).val - 1, by omega⟩ hlt2 huS.2.1 hprv0
            dsimp only at hhi
            exact ⟨z, hzL, hlo, fun _ => by omega⟩
          · have hlt2 : (eS u).val < k - 1 := by
              have hne : (eS u).val ≠ k - 1 := by
                intro h
                have : eS u = ⟨k - 1, by omega⟩ := Fin.ext h
                rw [this, hwlast] at huS; exact zero_ne_one huS.2.1
              have := (eS u).isLt; omega
            obtain ⟨z, hzL, hlo, _⟩ := hbetween_SL (eS u) ⟨k - 1, by omega⟩ hlt2 huS.2.1 hwlast
            exact ⟨z, hzL, hlo, fun hbad => absurd hbad hlast⟩
        classical
        let pickZ : (u : Fin r) → u.val ≤ j.val → Fin k := fun u hu => Classical.choose (hmap u (by omega))
        have hpickZ_spec : ∀ (u : Fin r) (hu : u.val ≤ j.val),
            pickZ u hu ∈ Left0 hk w ∧
            (eS u).val < (pickZ u hu).val ∧
            (∀ (hu' : u.val + 1 < r), (pickZ u hu).val < (eS ⟨u.val + 1, hu'⟩).val) :=
          fun u hu => Classical.choose_spec (hmap u (by omega))
        let idxL : (z : Fin k) → z ∈ Left0 hk w → Fin r := fun z hz =>
          Classical.choose (show z ∈ Set.range eL by rw [Finset.range_orderEmbOfFin _ hL0c]; exact hz)
        have hidxL_spec : ∀ (z : Fin k) (hz : z ∈ Left0 hk w), eL (idxL z hz) = z := fun z hz =>
          Classical.choose_spec (show z ∈ Set.range eL by rw [Finset.range_orderEmbOfFin _ hL0c]; exact hz)
        let f : Fin r → Fin r := fun u =>
          if hu : u.val ≤ j.val then idxL (pickZ u hu) (hpickZ_spec u hu).1 else ⟨0, hr1⟩
        have hcard_lt : (Finset.univ.filter (fun u : Fin r => u.val ≤ j.val)).card ≤
            (Finset.univ.filter (fun u : Fin r => (eL u).val < (eS ⟨j.val + 1, hj⟩).val)).card := by
          refine Finset.card_le_card_of_injOn f ?_ ?_
          · intro u hu
            have huj : u.val ≤ j.val := (Finset.mem_filter.1 hu).2
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, f, huj, dite_true]
            rw [hidxL_spec (pickZ u huj) (hpickZ_spec u huj).1]
            have hlt_u : (pickZ u huj).val < (eS ⟨u.val + 1, by omega⟩).val := (hpickZ_spec u huj).2.2 (by omega)
            have hle_uj : (eS ⟨u.val + 1, by omega⟩).val ≤ (eS ⟨j.val + 1, hj⟩).val :=
              eS.monotone (show (⟨u.val + 1, by omega⟩ : Fin r) ≤ ⟨j.val + 1, hj⟩ from by change u.val + 1 ≤ j.val + 1; omega)
            omega
          · intro u1 hu1 u2 hu2 hfeq
            have h1j : u1.val ≤ j.val := (Finset.mem_filter.1 hu1).2
            have h2j : u2.val ≤ j.val := (Finset.mem_filter.1 hu2).2
            simp only [f, h1j, h2j, dite_true] at hfeq
            have hz_eq : pickZ u1 h1j = pickZ u2 h2j := by
              rw [← hidxL_spec (pickZ u1 h1j) (hpickZ_spec u1 h1j).1,
                ← hidxL_spec (pickZ u2 h2j) (hpickZ_spec u2 h2j).1, hfeq]
            ext
            by_contra hne
            rcases lt_or_gt_of_ne hne with hlt12 | hlt21
            · have hz1_lt := (hpickZ_spec u1 h1j).2.2 (show u1.val + 1 < r by omega)
              have hleS : (eS ⟨u1.val + 1, by omega⟩).val ≤ (eS u2).val :=
                eS.monotone (show (⟨u1.val + 1, by omega⟩ : Fin r) ≤ u2 from by change u1.val + 1 ≤ u2.val; omega)
              have hz2_gt := (hpickZ_spec u2 h2j).2.1
              rw [hz_eq] at hz1_lt
              omega
            · have hz2_lt := (hpickZ_spec u2 h2j).2.2 (show u2.val + 1 < r by omega)
              have hleS : (eS ⟨u2.val + 1, by omega⟩).val ≤ (eS u1).val :=
                eS.monotone (show (⟨u2.val + 1, by omega⟩ : Fin r) ≤ u1 from by change u2.val + 1 ≤ u1.val; omega)
              have hz1_gt := (hpickZ_spec u1 h1j).2.1
              rw [← hz_eq] at hz2_lt
              omega
        have hsub : Finset.univ.filter (fun u : Fin r => (eL u).val < (eS ⟨j.val + 1, hj⟩).val) ⊆
            Finset.univ.filter (fun u : Fin r => u.val < j.val) := by
          intro u hu
          have hlt_u : (eL u).val < (eS ⟨j.val + 1, hj⟩).val := (Finset.mem_filter.1 hu).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          by_contra hge_u
          have hle_ju : (eL j).val ≤ (eL u).val := eL.monotone (show j ≤ u from by omega)
          omega
        have hc1 : (Finset.univ.filter (fun u : Fin r => u.val ≤ j.val)).card = j.val + 1 := by
          have : (Finset.univ.filter (fun u : Fin r => u.val ≤ j.val)).card = (Finset.univ : Finset (Fin (j.val + 1))).card := by
            refine Finset.card_bij (fun (u : Fin r) hu => (⟨u.val, by have := (Finset.mem_filter.1 hu).2; omega⟩ : Fin (j.val + 1)))
              (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
              (fun v _ => ⟨⟨v.val, by have := v.isLt; omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have := v.isLt; omega, by ext; simp⟩)
          simpa using this
        have hc2 : (Finset.univ.filter (fun u : Fin r => u.val < j.val)).card = j.val := by
          have : (Finset.univ.filter (fun u : Fin r => u.val < j.val)).card = (Finset.univ : Finset (Fin j.val)).card := by
            refine Finset.card_bij (fun (u : Fin r) hu => (⟨u.val, (Finset.mem_filter.1 hu).2⟩ : Fin j.val))
              (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => Fin.ext (by simpa using congrArg Fin.val h))
              (fun v _ => ⟨⟨v.val, by have := v.isLt; omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact v.isLt, by ext; simp⟩)
          simpa using this
        have hle_cards := hcard_lt.trans (Finset.card_le_card hsub)
        omega
      exact fun j => ⟨hSL j, hLS j⟩
    have hconst1 : ∀ (j : Fin r) (i : Fin k), (eS j).val ≤ i.val → i.val < (eL j).val → w i = 1 := by
      intro j i hlo hhi
      by_contra h0
      have hi0 : w i = 0 := (zmod2_ne_one_iff _).1 h0
      have hlt : (eS j).val < i.val := by
        have hne : eS j ≠ i := by
          intro heq
          have h1 := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hS1c j)).2.1
          rw [heq, hi0] at h1; exact zero_ne_one h1
        have : (eS j).val ≠ i.val := fun h => hne (Fin.ext h)
        omega
      have h1S := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hS1c j)).2.1
      obtain ⟨z, hzL, hloz, hhiz⟩ := hbetween_SL (eS j) i hlt h1S hi0
      have hz_range : z ∈ Set.range eL := by rw [Finset.range_orderEmbOfFin _ hL0c]; exact hzL
      obtain ⟨j', rfl⟩ := hz_range
      rcases lt_or_ge j'.val j.val with hlt' | hge'
      · have hLS := (hinterleave j').2 (by omega)
        have hleS : (eS ⟨j'.val + 1, by omega⟩).val ≤ (eS j).val :=
          eS.monotone (show (⟨j'.val + 1, by omega⟩ : Fin r) ≤ j from by change j'.val + 1 ≤ j.val; omega)
        omega
      · have hleL : (eL j).val ≤ (eL j').val := eL.monotone (show j ≤ j' from hge')
        omega
    have hconst0 : ∀ (j : Fin r) (i : Fin k), (eL j).val ≤ i.val →
        (∀ hj : j.val + 1 < r, i.val < (eS ⟨j.val + 1, hj⟩).val) → w i = 0 := by
      intro j i hlo hhi
      by_contra h1
      have hi1 : w i = 1 := (zmod2_ne_zero_iff _).1 h1
      have hlt : (eL j).val < i.val := by
        have hne : eL j ≠ i := by
          intro heq
          have h0 := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hL0c j)).2.1
          rw [heq, hi1] at h0; exact one_ne_zero h0
        have : (eL j).val ≠ i.val := fun h => hne (Fin.ext h)
        omega
      have h0L := (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem _ hL0c j)).2.1
      obtain ⟨s, hsS, hlos, hhis⟩ := hbetween_LS (eL j) i hlt h0L hi1
      have hs_range : s ∈ Set.range eS := by rw [Finset.range_orderEmbOfFin _ hS1c]; exact hsS
      obtain ⟨j', rfl⟩ := hs_range
      rcases le_or_gt j'.val j.val with hle' | hgt'
      · have hleS : (eS j').val ≤ (eS j).val := eS.monotone (show j' ≤ j from hle')
        have hSL := (hinterleave j).1
        omega
      · have hj : j.val + 1 < r := by omega
        have hleS : (eS ⟨j.val + 1, hj⟩).val ≤ (eS j').val :=
          eS.monotone (show (⟨j.val + 1, hj⟩ : Fin r) ≤ j' from by change j.val + 1 ≤ j'.val; omega)
        have := hhi hj
        omega
    let xval : Fin r → ℕ := fun j => (eL j).val - (eS j).val
    let yval : Fin r → ℕ := fun j => (if hj : j.val + 1 < r then (eS ⟨j.val + 1, hj⟩).val else k) - (eL j).val
    have hpref_eS : ∀ m : ℕ, (hm : m ≤ r) →
        (Finset.univ.filter (fun u : Fin r => u.val < m)).sum (fun u => xval u + yval u) =
        (if hlt : m < r then (eS ⟨m, hlt⟩).val else k) := by
      intro m
      induction m with
      | zero =>
        intro _
        have h0r : 0 < r := hr1
        simp [h0r, heS0]
      | succ m ih =>
        intro hm
        have hsub : Finset.univ.filter (fun u : Fin r => u.val < m + 1) =
            insert ⟨m, by omega⟩ (Finset.univ.filter (fun u : Fin r => u.val < m)) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        have hnm : (⟨m, by omega⟩ : Fin r) ∉ Finset.univ.filter (fun u : Fin r => u.val < m) := by simp
        rw [hsub, Finset.sum_insert hnm, ih (by omega)]
        simp only [show m < r by omega, dite_true]
        dsimp only [xval, yval]
        have hSL := (hinterleave ⟨m, by omega⟩).1
        by_cases hlt : m + 1 < r
        · have hLS := (hinterleave ⟨m, by omega⟩).2 hlt
          dsimp only at hLS
          simp only [hlt, dite_true]; omega
        · simp only [hlt, dite_false]
          have := (eL ⟨m, by omega⟩).isLt; omega
    have hones_part : ones w = Finset.univ.biUnion (fun j : Fin r =>
        Finset.univ.filter (fun i : Fin k => (eS j).val ≤ i.val ∧ i.val < (eL j).val)) := by
      ext i
      simp only [ones, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hi1
        have hex : ∃ m : ℕ, m < r ∧ i.val < (if hlt : m + 1 < r then (eS ⟨m + 1, hlt⟩).val else k) := by
          refine ⟨r - 1, by omega, ?_⟩
          have hnot : ¬ (r - 1 + 1 < r) := by omega
          simp only [hnot, dite_false]; exact i.isLt
        classical
        let m0 := Nat.find hex
        have hm0 : m0 < r ∧ i.val < (if hlt : m0 + 1 < r then (eS ⟨m0 + 1, hlt⟩).val else k) := Nat.find_spec hex
        have hlo : (eS ⟨m0, hm0.1⟩).val ≤ i.val := by
          by_cases hm0_eq : m0 = 0
          · have h0e : (⟨m0, hm0.1⟩ : Fin r) = ⟨0, hr1⟩ := Fin.ext hm0_eq
            rw [h0e, heS0]; exact Nat.zero_le _
          · have hmin := Nat.find_min hex (show m0 - 1 < Nat.find hex by dsimp only [m0]; omega)
            push Not at hmin
            have h := hmin (by omega)
            have hlt' : m0 - 1 + 1 < r := by omega
            simp only [hlt', dite_true] at h
            have hfe : (⟨m0 - 1 + 1, hlt'⟩ : Fin r) = ⟨m0, hm0.1⟩ := by ext; simp; omega
            rwa [hfe] at h
        refine ⟨⟨m0, hm0.1⟩, hlo, ?_⟩
        by_contra hge
        have h0 := hconst0 ⟨m0, hm0.1⟩ i (by omega) (fun hj => by
          have h2 := hm0.2
          simp only [hj, dite_true] at h2
          exact h2)
        rw [h0] at hi1; exact zero_ne_one hi1
      · rintro ⟨j, hlo, hhi⟩; exact hconst1 j i hlo hhi
    have hx_sum : ∑ j : Fin r, xval j = a := by
      rw [← hones, hones_part, Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        have hSL := (hinterleave j).1
        have hLt := (eL j).isLt
        have hcard_f : (Finset.univ : Finset (Fin (xval j))).card = xval j := by simp
        rw [← hcard_f]
        symm
        refine Finset.card_bij (fun (i : Fin k) hi => (⟨i.val - (eS j).val, by
          have := (Finset.mem_filter.1 hi).2; dsimp [xval]; omega⟩ : Fin (xval j)))
          (fun _ _ => Finset.mem_univ _)
          (fun i1 hi1 i2 hi2 h => by
            have h1 := (Finset.mem_filter.1 hi1).2; have h2 := (Finset.mem_filter.1 hi2).2
            have hv := congrArg Fin.val h; dsimp at hv; ext; omega)
          (fun d _ => ⟨⟨(eS j).val + d.val, by have := d.isLt; dsimp [xval] at this; omega⟩,
            by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have := d.isLt; dsimp [xval] at this; omega,
            by ext; simp⟩)
      · intro j1 _ j2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have h1 := (Finset.mem_filter.1 hi1).2; have h2 := (Finset.mem_filter.1 hi2).2
        have hne' : j1.val ≠ j2.val := fun h => hne (Fin.ext h)
        rcases lt_or_gt_of_ne hne' with hlt | hgt
        · have hLS := (hinterleave j1).2 (by omega)
          have hleS : (eS ⟨j1.val + 1, by omega⟩).val ≤ (eS j2).val :=
            eS.monotone (show (⟨j1.val + 1, by omega⟩ : Fin r) ≤ j2 from by change j1.val + 1 ≤ j2.val; omega)
          omega
        · have hLS := (hinterleave j2).2 (by omega)
          have hleS : (eS ⟨j2.val + 1, by omega⟩).val ≤ (eS j1).val :=
            eS.monotone (show (⟨j2.val + 1, by omega⟩ : Fin r) ≤ j1 from by change j2.val + 1 ≤ j1.val; omega)
          omega
    have hy_sum : ∑ j : Fin r, yval j = b := by
      have htot := hpref_eS r le_rfl
      have hall : Finset.univ.filter (fun u : Fin r => u.val < r) = Finset.univ := by ext u; simp
      rw [hall, Finset.sum_add_distrib, hx_sum] at htot
      simp only [lt_irrefl r, dite_false] at htot
      omega
    have hx_le : ∀ j : Fin r, xval j ≤ a := fun j => by
      have := Finset.single_le_sum (f := xval) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j); omega
    have hy_le : ∀ j : Fin r, yval j ≤ b := fun j => by
      have := Finset.single_le_sum (f := yval) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j); omega
    let x : Fin r → Fin (a + 1) := fun j => ⟨xval j, by have := hx_le j; omega⟩
    let y : Fin r → Fin (b + 1) := fun j => ⟨yval j, by have := hy_le j; omega⟩
    have hx_mem : x ∈ posComps a r := by
      simp only [posComps, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun j => by have := (hinterleave j).1; dsimp [x, xval]; omega, hx_sum⟩
    have hy_t_eq : (Finset.univ.filter (fun j : Fin r => 2 ≤ (y j).val)).card = t := by
      rw [← htc]
      symm
      have hnxtS_of_mem : ∀ i ∈ Right0 hk w \ Left0 hk w, nxt hk i ∈ S1 hk w := by
        intro i hi
        have hiR := (Finset.mem_sdiff.1 hi).1
        simp only [Right0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hiR ⊢
        exact ⟨hiR.2, by rw [prv_nxt]; exact hiR.1⟩
      have hfindS : ∀ i : Fin k, nxt hk i ∈ S1 hk w → ∃ j : Fin r, eS j = nxt hk i := by
        intro i hiS
        have : nxt hk i ∈ Set.range eS := by rw [Finset.range_orderEmbOfFin _ hS1c]; exact hiS
        exact this
      classical
      let findJ1 : (i : Fin k) → nxt hk i ∈ S1 hk w → Fin r := fun i hiS => Classical.choose (hfindS i hiS)
      have hfindJ1_spec : ∀ (i : Fin k) (hiS : nxt hk i ∈ S1 hk w), eS (findJ1 i hiS) = nxt hk i :=
        fun i hiS => Classical.choose_spec (hfindS i hiS)
      let toJ0 : Fin r → Fin r := fun j1 => ⟨if j1.val = 0 then r - 1 else j1.val - 1, by split_ifs <;> omega⟩
      have htoJ0_inj : Function.Injective toJ0 := by
        intro j1 j2 h
        have hv : (if j1.val = 0 then r - 1 else j1.val - 1) = (if j2.val = 0 then r - 1 else j2.val - 1) :=
          congrArg Fin.val h
        ext; split_ifs at hv with c1 c2 c2 <;> omega
      refine Finset.card_bij (fun i hi => toJ0 (findJ1 i (hnxtS_of_mem i hi))) ?_ ?_ ?_
      · intro i hi
        have hiNL := (Finset.mem_sdiff.1 hi).2
        have hnxtS := hnxtS_of_mem i hi
        set j1 := findJ1 i hnxtS
        have hj1 : eS j1 = nxt hk i := hfindJ1_spec i hnxtS
        set j0 := toJ0 j1
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hi_val : i.val = (if hj : j0.val + 1 < r then (eS ⟨j0.val + 1, hj⟩).val else k) - 1 := by
          have h1 : prv hk (nxt hk i) = i := prv_nxt hk i
          by_cases hj10 : j1.val = 0
          · have hnxt0 : (nxt hk i).val = 0 := by
              rw [← hj1, show j1 = ⟨0, hr1⟩ from Fin.ext hj10, heS0]
            have hprv0 : (prv hk (nxt hk i)).val = k - 1 := by
              simp only [prv, hnxt0, zero_add]; exact Nat.mod_eq_of_lt (by omega)
            rw [h1] at hprv0
            have hnot : ¬ (j0.val + 1 < r) := by dsimp [j0, toJ0]; simp [hj10]; omega
            simp only [hprv0, hnot, dite_false]
          · have hlt : j0.val + 1 < r := by dsimp [j0, toJ0]; simp [hj10]; omega
            have hjeq : (⟨j0.val + 1, hlt⟩ : Fin r) = j1 := by ext; dsimp [j0, toJ0]; simp [hj10]; omega
            have hpos : 0 < (nxt hk i).val := by
              rw [← hj1]
              have := eS.strictMono (show (⟨0, hr1⟩ : Fin r) < j1 from by change 0 < j1.val; omega)
              have hv : (eS ⟨0, hr1⟩).val < (eS j1).val := this
              rw [heS0] at hv; exact hv
            have hprv1 : (prv hk (nxt hk i)).val = (nxt hk i).val - 1 := by
              simp only [prv]
              have hlt' := (nxt hk i).isLt
              rw [show (nxt hk i).val + k - 1 = ((nxt hk i).val - 1) + k by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [h1] at hprv1
            simp only [hprv1, ← hj1, hlt, dite_true, hjeq]
        have hneL : i ≠ eL j0 := fun heq => hiNL (heq ▸ Finset.orderEmbOfFin_mem _ hL0c j0)
        have hneLv : i.val ≠ (eL j0).val := fun h => hneL (Fin.ext h)
        dsimp only [y, yval]
        by_cases hj : j0.val + 1 < r
        · have hLS := (hinterleave j0).2 hj
          simp only [hj, dite_true] at hi_val ⊢
          omega
        · simp only [hj, dite_false] at hi_val ⊢
          have := (eL j0).isLt
          omega
      · intro i1 hi1 i2 hi2 heq
        have hj12 : findJ1 i1 (hnxtS_of_mem i1 hi1) = findJ1 i2 (hnxtS_of_mem i2 hi2) := htoJ0_inj heq
        apply (nxtEquiv hk).injective
        change nxt hk i1 = nxt hk i2
        rw [← hfindJ1_spec i1 (hnxtS_of_mem i1 hi1), ← hfindJ1_spec i2 (hnxtS_of_mem i2 hi2), hj12]
      · intro j0 hj0
        have hy2 : 2 ≤ yval j0 := (Finset.mem_filter.1 hj0).2
        let j1 : Fin r := ⟨if j0.val + 1 < r then j0.val + 1 else 0, by split_ifs <;> omega⟩
        let i : Fin k := prv hk (eS j1)
        have hnxtS : nxt hk i ∈ S1 hk w := by
          rw [nxt_prv]; exact Finset.orderEmbOfFin_mem _ hS1c j1
        have hiR : i ∈ Right0 hk w := by
          simp only [S1, Right0, Finset.mem_filter, Finset.mem_univ, true_and] at hnxtS ⊢
          exact ⟨by rw [← prv_nxt hk i]; exact hnxtS.2, hnxtS.1⟩
        have hi_val : i.val = (if hj : j0.val + 1 < r then (eS ⟨j0.val + 1, hj⟩).val else k) - 1 := by
          by_cases hlt : j0.val + 1 < r
          · have hje : j1 = ⟨j0.val + 1, hlt⟩ := by ext; simp [j1, hlt]
            have hpos : 0 < (eS ⟨j0.val + 1, hlt⟩).val := by
              have := eS.strictMono (show (⟨0, hr1⟩ : Fin r) < ⟨j0.val + 1, hlt⟩ from by change 0 < j0.val + 1; omega)
              have hv : (eS ⟨0, hr1⟩).val < (eS ⟨j0.val + 1, hlt⟩).val := this
              rw [heS0] at hv; exact hv
            have hlt' := (eS ⟨j0.val + 1, hlt⟩).isLt
            simp only [i, prv, hlt, dite_true, hje]
            rw [show (eS ⟨j0.val + 1, hlt⟩).val + k - 1 = ((eS ⟨j0.val + 1, hlt⟩).val - 1) + k by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          · have hje : j1 = ⟨0, hr1⟩ := by ext; simp [j1, hlt]
            simp only [i, prv, hlt, dite_false, hje, heS0, zero_add]
            exact Nat.mod_eq_of_lt (by omega)
        have hiNL : i ∉ Left0 hk w := by
          intro hiL
          have : i ∈ Set.range eL := by rw [Finset.range_orderEmbOfFin _ hL0c]; exact hiL
          obtain ⟨j', hj'⟩ := this
          have hv : (eL j').val = i.val := congrArg Fin.val hj'
          dsimp only [yval] at hy2
          rcases lt_or_ge j'.val j0.val with hlt | hge
          · have hLS := (hinterleave j').2 (by omega)
            have hleS : (eS ⟨j'.val + 1, by omega⟩).val ≤ (eS j0).val :=
              eS.monotone (show (⟨j'.val + 1, by omega⟩ : Fin r) ≤ j0 from by change j'.val + 1 ≤ j0.val; omega)
            have hSL := (hinterleave j0).1
            by_cases h0lt : j0.val + 1 < r
            · simp only [h0lt, dite_true] at hi_val hy2; omega
            · simp only [h0lt, dite_false] at hi_val hy2; omega
          · by_cases heq' : j'.val = j0.val
            · have : j' = j0 := Fin.ext heq'; rw [this] at hv
              by_cases h0lt : j0.val + 1 < r
              · simp only [h0lt, dite_true] at hi_val hy2; omega
              · simp only [h0lt, dite_false] at hi_val hy2; omega
            · have h0lt : j0.val + 1 < r := by omega
              have hleS : (eS ⟨j0.val + 1, h0lt⟩).val ≤ (eS j').val :=
                eS.monotone (show (⟨j0.val + 1, h0lt⟩ : Fin r) ≤ j' from by change j0.val + 1 ≤ j'.val; omega)
              have hSL := (hinterleave j').1
              simp only [h0lt, dite_true] at hi_val
              omega
        have hi_mem : i ∈ Right0 hk w \ Left0 hk w := Finset.mem_sdiff.2 ⟨hiR, hiNL⟩
        refine ⟨i, hi_mem, ?_⟩
        have hj1_eq : findJ1 i (hnxtS_of_mem i hi_mem) = j1 :=
          eS.injective ((hfindJ1_spec i (hnxtS_of_mem i hi_mem)).trans (nxt_prv hk (eS j1)))
        rw [hj1_eq]
        apply Fin.ext
        change (if j1.val = 0 then r - 1 else j1.val - 1) = j0.val
        have hj0lt := j0.isLt
        by_cases hlt : j0.val + 1 < r
        · have hj1v : j1.val = j0.val + 1 := by simp [j1, hlt]
          simp only [hj1v, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
          omega
        · have hj1v : j1.val = 0 := by simp [j1, hlt]
          simp only [hj1v, ite_true]
          omega
    have hy_mem : y ∈ zeroComps b r t := by
      simp only [zeroComps, posComps, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨?_, hy_sum⟩, hy_t_eq⟩
      intro j
      dsimp only [y, yval]
      by_cases hlt : j.val + 1 < r
      · have hLS := (hinterleave j).2 hlt; simp only [hlt, dite_true]; omega
      · simp only [hlt, dite_false]; have := (eL j).isLt; omega
    refine ⟨(x, y), Finset.mem_product.2 ⟨hx_mem, hy_mem⟩, ?_⟩
    funext i
    have hpref_eq : ∀ j : Fin r, prefXY x y j.val = (eS j).val := by
      intro j
      have h := hpref_eS j.val (le_of_lt j.isLt)
      simpa [prefXY, x, y, j.isLt] using h
    have hmk_iff : mkW (x, y) i = 1 ↔ ∃ j : Fin r, (eS j).val ≤ i.val ∧ i.val < (eL j).val := by
      dsimp only [mkW]
      split_ifs with h
      · simp only [true_iff]
        obtain ⟨j, hlo, hhi⟩ := h
        rw [hpref_eq j] at hlo hhi
        have hSL := (hinterleave j).1
        refine ⟨j, hlo, ?_⟩
        dsimp [x, xval] at hhi; omega
      · simp only [zero_ne_one, false_iff]
        rintro ⟨j, hlo, hhi⟩
        apply h
        refine ⟨j, ?_, ?_⟩
        · rw [hpref_eq j]; exact hlo
        · rw [hpref_eq j]; dsimp [x, xval]; omega
    have hw_iff2 : w i = 1 ↔ ∃ j : Fin r, (eS j).val ≤ i.val ∧ i.val < (eL j).val := by
      have hmem := Finset.ext_iff.1 hones_part i
      simpa [ones, Finset.mem_filter, Finset.mem_biUnion] using hmem
    rcases zmod2_cases (mkW (x, y) i) with h0 | h1 <;> rcases zmod2_cases (w i) with h0' | h1'
    · rw [h0, h0']
    · exact absurd (hmk_iff.2 (hw_iff2.1 h1')) (by rw [h0]; exact zero_ne_one)
    · exact absurd (hw_iff2.2 (hmk_iff.1 h1)) (by rw [h0']; exact zero_ne_one)
    · rw [h1, h1']

private def cycWords {k : ℕ} (hk : 0 < k) (a r t : ℕ) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter (fun m =>
    (ones m).card = a ∧ (S1 hk m).card = r ∧ (Right0 hk m \ Left0 hk m).card = t)

private lemma card_cycWords_mul {k : ℕ} (hk : 0 < k) (a r t : ℕ) :
    r * (cycWords hk a r t).card = k * (linWords hk a r t).card := by
  let M : Finset ((Fin k → ZMod 2) × Fin k) :=
    (cycWords hk a r t).sigma (fun m => S1 hk m) |>.map
      ⟨fun x => (x.1, x.2), fun a b h => by
        rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
        simp only [Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩; rfl⟩
  have hM1 : M.card = r * (cycWords hk a r t).card := by
    rw [Finset.card_map, Finset.card_sigma]
    have hconst : ∀ m ∈ cycWords hk a r t, (S1 hk m).card = r :=
      fun m hm => (Finset.mem_filter.1 hm).2.2.1
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
  have hM2 : M.card = k * (linWords hk a r t).card := by
    have hprod : (Finset.univ ×ˢ linWords hk a r t : Finset (Fin k × (Fin k → ZMod 2))).card =
        k * (linWords hk a r t).card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
    rw [← hprod]
    refine Finset.card_bij
      (fun mp _ => (mp.2, fun i => mp.1 (rot hk mp.2 i)))
      ?_ ?_ ?_
    · intro mp hmp
      rcases mp with ⟨m, p⟩
      simp only [M, Finset.mem_map, Finset.mem_sigma] at hmp
      obtain ⟨⟨m0, p0⟩, ⟨hm, hp⟩, hEq⟩ := hmp
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      have hm' : (ones m0).card = a ∧ (S1 hk m0).card = r ∧ (Right0 hk m0 \ Left0 hk m0).card = t :=
        (Finset.mem_filter.1 hm).2
      have hp' : m0 p0 = 1 ∧ m0 (prv hk p0) = 0 :=
        (Finset.mem_filter.1 hp).2
      set w : Fin k → ZMod 2 := fun i => m0 (rot hk p0 i)
      have hrot_ones : (ones w).card = (ones m0).card := by
        refine Finset.card_bij (fun i _ => rot hk p0 i) ?_ ?_ ?_
        · intro i hi; simpa [ones, w] using hi
        · intro i1 _ i2 _ h; have := congrArg (rotInv hk p0) h; simpa [rotInv_rot] using this
        · intro j hj; refine ⟨rotInv hk p0 j, ?_, rot_rotInv hk p0 j⟩; simpa [ones, w, rot_rotInv] using hj
      have hrot_S1 : (S1 hk w).card = (S1 hk m0).card := by
        refine Finset.card_bij (fun i _ => rot hk p0 i) ?_ ?_ ?_
        · intro i hi; simpa [S1, w, rot_prv] using hi
        · intro i1 _ i2 _ h; have := congrArg (rotInv hk p0) h; simpa [rotInv_rot] using this
        · intro j hj; refine ⟨rotInv hk p0 j, ?_, rot_rotInv hk p0 j⟩; simpa [S1, w, rot_prv, rot_rotInv] using hj
      have hrot_RL : (Right0 hk w \ Left0 hk w).card = (Right0 hk m0 \ Left0 hk m0).card := by
        refine Finset.card_bij (fun i _ => rot hk p0 i) ?_ ?_ ?_
        · intro i hi; simpa [Right0, Left0, w, rot_nxt, rot_prv] using hi
        · intro i1 _ i2 _ h; have := congrArg (rotInv hk p0) h; simpa [rotInv_rot] using this
        · intro j hj; refine ⟨rotInv hk p0 j, ?_, rot_rotInv hk p0 j⟩
          simpa [Right0, Left0, w, rot_nxt, rot_prv, rot_rotInv] using hj
      simp only [Finset.mem_product, Finset.mem_univ, true_and, linWords, Finset.mem_filter]
      have hw0 : w ⟨0, hk⟩ = 1 := by
        have hrot0 : rot hk p0 ⟨0, hk⟩ = p0 := by ext; simp [rot, Nat.mod_eq_of_lt p0.isLt]
        change m0 (rot hk p0 ⟨0, hk⟩) = 1
        rw [hrot0]; exact hp'.1
      have hwlast : w ⟨k - 1, by omega⟩ = 0 := by
        have hrotl : rot hk p0 ⟨k - 1, by omega⟩ = prv hk p0 := by
          ext; simp only [rot, prv]; congr 1; omega
        change m0 (rot hk p0 ⟨k - 1, by omega⟩) = 0
        rw [hrotl]; exact hp'.2
      exact ⟨hw0, hwlast, hrot_ones.trans hm'.1, hrot_S1.trans hm'.2.1, hrot_RL.trans hm'.2.2⟩
    · intro mp1 _ mp2 _ heq
      rcases Prod.mk.inj heq with ⟨hp, hw⟩
      apply Prod.ext
      · funext j
        have := congrFun hw (rotInv hk mp1.2 j)
        rw [hp] at this
        simpa [rot_rotInv] using this
      · exact hp
    · intro pw hpw
      rcases Finset.mem_product.1 hpw with ⟨_, hw⟩
      rcases pw with ⟨p, w⟩
      simp only [linWords, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      let m : Fin k → ZMod 2 := fun j => w (rotInv hk p j)
      have hm_rot : (fun i => m (rot hk p i)) = w := by
        funext i; dsimp [m]; rw [rotInv_rot]
      have hpS1 : p ∈ S1 hk m := by
        simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, m]
        have h0 : rotInv hk p p = ⟨0, hk⟩ := by
          ext; simp only [rotInv]; rw [show p.val + k - p.val = k by omega, Nat.mod_self]
        have h1 : rotInv hk p (prv hk p) = ⟨k - 1, by omega⟩ := by
          have : rot hk p ⟨k - 1, by omega⟩ = prv hk p := by ext; simp only [rot, prv]; congr 1; omega
          rw [← this, rotInv_rot]
        rw [h0, h1]; exact ⟨hw.1, hw.2.1⟩
      have hrot_ones : (ones m).card = (ones w).card := by
        refine Finset.card_bij (fun j _ => rotInv hk p j) ?_ ?_ ?_
        · intro j hj; simpa [ones, m] using hj
        · intro j1 _ j2 _ h; have := congrArg (rot hk p) h; simpa [rot_rotInv] using this
        · intro i hi; refine ⟨rot hk p i, ?_, rotInv_rot hk p i⟩; simpa [ones, m, rotInv_rot] using hi
      have hrot_S1 : (S1 hk m).card = (S1 hk w).card := by
        refine Finset.card_bij (fun j _ => rotInv hk p j) ?_ ?_ ?_
        · intro j hj
          have hprv : rotInv hk p (prv hk j) = prv hk (rotInv hk p j) := by
            have := rot_prv hk p (rotInv hk p j)
            rw [rot_rotInv] at this
            rw [← this, rotInv_rot]
          simpa [S1, m, hprv] using hj
        · intro j1 _ j2 _ h; have := congrArg (rot hk p) h; simpa [rot_rotInv] using this
        · intro i hi
          have hprv : rotInv hk p (prv hk (rot hk p i)) = prv hk i := by
            rw [← rot_prv, rotInv_rot]
          refine ⟨rot hk p i, ?_, rotInv_rot hk p i⟩
          simpa [S1, m, rotInv_rot, hprv] using hi
      have hrot_RL : (Right0 hk m \ Left0 hk m).card = (Right0 hk w \ Left0 hk w).card := by
        refine Finset.card_bij (fun j _ => rotInv hk p j) ?_ ?_ ?_
        · intro j hj
          have hprv : rotInv hk p (prv hk j) = prv hk (rotInv hk p j) := by
            have := rot_prv hk p (rotInv hk p j); rw [rot_rotInv] at this; rw [← this, rotInv_rot]
          have hnxt : rotInv hk p (nxt hk j) = nxt hk (rotInv hk p j) := by
            have := rot_nxt hk p (rotInv hk p j); rw [rot_rotInv] at this; rw [← this, rotInv_rot]
          simpa [Right0, Left0, m, hprv, hnxt] using hj
        · intro j1 _ j2 _ h; have := congrArg (rot hk p) h; simpa [rot_rotInv] using this
        · intro i hi
          have hprv : rotInv hk p (prv hk (rot hk p i)) = prv hk i := by rw [← rot_prv, rotInv_rot]
          have hnxt : rotInv hk p (nxt hk (rot hk p i)) = nxt hk i := by rw [← rot_nxt, rotInv_rot]
          refine ⟨rot hk p i, ?_, rotInv_rot hk p i⟩
          simpa [Right0, Left0, m, rotInv_rot, hprv, hnxt] using hi
      refine ⟨(m, p), ?_, Prod.ext rfl hm_rot⟩
      simp only [M, Finset.mem_map, Finset.mem_sigma]
      refine ⟨⟨m, p⟩, ⟨?_, hpS1⟩, rfl⟩
      simp only [cycWords, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hrot_ones.trans hw.2.2.1, hrot_S1.trans hw.2.2.2.1, hrot_RL.trans hw.2.2.2.2⟩
  omega

end PEqualNP.Outside.L_lib_755

theorem PEqualNP.Outside.L_lib_755 : ∀ (k : ℕ) (hk : 0 < k) (a f : ℕ), a ≤ k →
  let F := ZMod 2
  let W := Fin k → F
  let next := fun (i : Fin k) => (⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k)
  let fiber := fun (m : W) => (Finset.univ : Finset W).filter (fun u =>
    ∀ i, m i * u (next i) = u i * m (next i))
  let words := (Finset.univ : Finset W).filter (fun m =>
    (Finset.univ.filter (fun i : Fin k => m i = 1)).card = a ∧ (fiber m).card = 2^f)
  let b := k-a
  words.card =
    if a = 0 then (if f = k then 1 else 0)
    else if a = k then (if f = 1 then 1 else 0)
    else ∑ r ∈ Finset.Icc 1 (min a b), ∑ t ∈ Finset.Icc 0 r,
      if r+t ≤ b ∧ f = b-t then
        let extras := if t = 0 then (if r = b then 1 else 0)
          else Nat.choose (b-r-1) (t-1)
        (k * Nat.choose (a-1) (r-1) * Nat.choose r t * extras) / r
      else 0 := by
  intro k hk a f hak F W next fiber words b
  by_cases ha0 : a = 0
  · subst ha0
    simp only [ite_true]
    let m0 : W := fun _ => 0
    have hfib0 : (fiber m0).card = 2 ^ k := by
      have hall : fiber m0 = Finset.univ := by ext u; simp [fiber, m0]
      rw [hall, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hpow_inj : (2 ^ k = 2 ^ f) ↔ f = k := by
      constructor
      · intro h; exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
      · intro h; rw [h]
    by_cases hfk : f = k
    · simp only [hfk, ite_true]
      have hsing : words = {m0} := by
        ext m
        simp only [words, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hc, _⟩
          funext i
          have hnot : m i ≠ 1 := by
            intro h1
            have : i ∈ Finset.univ.filter (fun i : Fin k => m i = 1) := by simp [h1]
            rw [Finset.card_eq_zero.1 hc] at this
            exact Finset.notMem_empty i this
          exact (PEqualNP.Outside.L_lib_755.zmod2_ne_one_iff (m i)).1 hnot
        · rintro rfl
          refine ⟨by simp [m0], ?_⟩
          rw [hfib0, hfk]
      rw [hsing, Finset.card_singleton]
    · simp only [hfk, ite_false]
      apply Finset.card_eq_zero.2
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      simp only [words, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      have hm0 : m = m0 := by
        funext i
        have hnot : m i ≠ 1 := by
          intro h1
          have : i ∈ Finset.univ.filter (fun i : Fin k => m i = 1) := by simp [h1]
          rw [Finset.card_eq_zero.1 hm.1] at this
          exact Finset.notMem_empty i this
        exact (PEqualNP.Outside.L_lib_755.zmod2_ne_one_iff (m i)).1 hnot
      rw [hm0, hfib0] at hm
      exact hfk (hpow_inj.1 hm.2)
  · simp only [ha0, ite_false]
    by_cases haeq : a = k
    · simp only [haeq, ite_true]
      let m1 : W := fun _ => 1
      have hfib1 : (fiber m1).card = 2 ^ 1 := by
        have heq : fiber m1 = {fun _ => 0, fun _ => 1} := by
          ext u
          simp only [fiber, m1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton, one_mul, mul_one]
          constructor
          · intro hconst
            have hall : ∀ n : ℕ, (hn : n < k) → u ⟨n, hn⟩ = u ⟨0, hk⟩ := by
              intro n
              induction n with
              | zero => intro _; rfl
              | succ n ih =>
                intro hn
                have hstep := hconst ⟨n, by omega⟩
                have hnxt : next ⟨n, by omega⟩ = ⟨n + 1, hn⟩ := by
                  ext; simp only [next]; exact Nat.mod_eq_of_lt hn
                rw [hnxt] at hstep
                rw [hstep, ih (by omega)]
            rcases PEqualNP.Outside.L_lib_755.zmod2_cases (u ⟨0, hk⟩) with h0 | h1
            · left; funext i; rw [hall i.val i.isLt, h0]
            · right; funext i; rw [hall i.val i.isLt, h1]
          · rintro (rfl | rfl) <;> intro i <;> rfl
        rw [heq, Finset.card_pair (fun h => zero_ne_one (congrFun h ⟨0, hk⟩))]
        norm_num
      have hpow_inj : (2 ^ 1 = 2 ^ f) ↔ f = 1 := by
        constructor
        · intro h; exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
        · intro h; rw [h]
      by_cases hf1 : f = 1
      · simp only [hf1, ite_true]
        have hsing : words = {m1} := by
          ext m
          simp only [words, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hc, _⟩
            have hall : Finset.univ.filter (fun i : Fin k => m i = 1) = Finset.univ :=
              Finset.eq_univ_of_card _ (by simpa [haeq] using hc)
            funext i
            have hi : i ∈ Finset.univ.filter (fun i : Fin k => m i = 1) := by rw [hall]; exact Finset.mem_univ i
            exact (Finset.mem_filter.1 hi).2
          · rintro rfl
            refine ⟨by simp [m1, haeq], ?_⟩
            rw [hfib1, hf1]
        rw [hsing, Finset.card_singleton]
      · simp only [hf1, ite_false]
        apply Finset.card_eq_zero.2
        rw [Finset.eq_empty_iff_forall_notMem]
        intro m hm
        simp only [words, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        have hall : Finset.univ.filter (fun i : Fin k => m i = 1) = Finset.univ :=
          Finset.eq_univ_of_card _ (by simpa [haeq] using hm.1)
        have hmeq : m = m1 := by
          funext i
          have hi : i ∈ Finset.univ.filter (fun i : Fin k => m i = 1) := by rw [hall]; exact Finset.mem_univ i
          exact (Finset.mem_filter.1 hi).2
        rw [hmeq, hfib1] at hm
        exact hf1 (hpow_inj.1 hm.2)
    · simp only [haeq, ite_false]
      have ha_pos : 0 < a := by omega
      have ha_lt : a < k := by omega
      have hb_pos : 0 < b := by omega
      have hpart : words = (Finset.Icc 1 (min a b)).biUnion (fun r =>
          (Finset.Icc 0 r).biUnion (fun t =>
            if r + t ≤ b ∧ f = b - t then PEqualNP.Outside.L_lib_755.cycWords hk a r t else ∅)) := by
        ext m
        simp only [words, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
          Finset.mem_Icc]
        constructor
        · rintro ⟨hones, hfib⟩
          have hzcard : (PEqualNP.Outside.L_lib_755.zeros m).card = b := by
            have := PEqualNP.Outside.L_lib_755.ones_add_zeros m
            change (Finset.univ.filter (fun i : Fin k => m i = 1)).card + _ = k at this
            omega
          have hones_pos : 0 < (PEqualNP.Outside.L_lib_755.ones m).card := by
            change 0 < (Finset.univ.filter (fun i : Fin k => m i = 1)).card; omega
          have hmix := PEqualNP.Outside.L_lib_755.card_fiber_of_mixed hk m hones_pos (by omega)
          rw [hzcard] at hmix
          set r := (PEqualNP.Outside.L_lib_755.S1 hk m).card
          set t := (PEqualNP.Outside.L_lib_755.Right0 hk m \ PEqualNP.Outside.L_lib_755.Left0 hk m).card
          have hr1 : 1 ≤ r := PEqualNP.Outside.L_lib_755.card_S1_pos hk m hones_pos (by omega)
          have hra : r ≤ a := by
            have hsub : PEqualNP.Outside.L_lib_755.S1 hk m ⊆ PEqualNP.Outside.L_lib_755.ones m := by
              intro i hi; simp only [PEqualNP.Outside.L_lib_755.S1, PEqualNP.Outside.L_lib_755.ones,
                Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1
            have := Finset.card_le_card hsub
            change r ≤ (Finset.univ.filter (fun i : Fin k => m i = 1)).card at this
            omega
          have hrb : r ≤ b := by omega
          have htr : t ≤ r := by
            have hle : t ≤ (PEqualNP.Outside.L_lib_755.Right0 hk m).card :=
              Finset.card_le_card Finset.sdiff_subset
            rwa [PEqualNP.Outside.L_lib_755.card_Right0_eq_card_S1 hk m] at hle
          have hfeq : f = b - t := by
            have h2 : (2 : ℕ) ^ f = 2 ^ (b - t) := by
              rw [← hfib]
              exact hmix.2
            exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
          refine ⟨r, ⟨hr1, le_min hra hrb⟩, t, ⟨Nat.zero_le _, htr⟩, ?_⟩
          simp only [hmix.1, hfeq, and_self, ite_true]
          simp only [PEqualNP.Outside.L_lib_755.cycWords, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hones, rfl, rfl⟩
        · rintro ⟨r, ⟨hr1, hrmax⟩, t, ⟨_, htr⟩, hm⟩
          split_ifs at hm with hcond
          · simp only [PEqualNP.Outside.L_lib_755.cycWords, Finset.mem_filter, Finset.mem_univ, true_and] at hm
            have hzcard : (PEqualNP.Outside.L_lib_755.zeros m).card = b := by
              have := PEqualNP.Outside.L_lib_755.ones_add_zeros m
              rw [hm.1] at this; omega
            have hmix := PEqualNP.Outside.L_lib_755.card_fiber_of_mixed hk m
              (by rw [hm.1]; exact ha_pos) (by rw [hzcard]; exact hb_pos)
            rw [hzcard, hm.2.2] at hmix
            refine ⟨hm.1, ?_⟩
            change (PEqualNP.Outside.L_lib_755.fiberSet hk m).card = 2 ^ f
            rw [hmix.2, hcond.2]
          · exact absurd hm (Finset.notMem_empty m)
      rw [hpart, Finset.card_biUnion]
      · refine Finset.sum_congr rfl (fun r hr => ?_)
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl (fun t ht => ?_)
          by_cases hcond : r + t ≤ b ∧ f = b - t
          · simp only [hcond, and_self, ite_true]
            simp only [Finset.mem_Icc] at hr ht
            have hr1 : 1 ≤ r := hr.1
            have hra : r ≤ a := le_trans hr.2 (min_le_left _ _)
            have htr : t ≤ r := ht.2
            have hmul := PEqualNP.Outside.L_lib_755.card_cycWords_mul hk a r t
            rw [PEqualNP.Outside.L_lib_755.card_linWords hk ha_pos ha_lt hr1 hra htr hcond.1,
              PEqualNP.Outside.L_lib_755.card_posComps hr1 hra,
              PEqualNP.Outside.L_lib_755.card_zeroComps hr1 htr hcond.1] at hmul
            have hmul' : r * (PEqualNP.Outside.L_lib_755.cycWords hk a r t).card =
                k * Nat.choose (a - 1) (r - 1) * Nat.choose r t *
                  (if t = 0 then (if r = b then 1 else 0) else Nat.choose (b - r - 1) (t - 1)) := by
              rw [hmul]; ring
            rw [← hmul', Nat.mul_div_cancel_left _ (by omega)]
          · simp only [hcond, ite_false, Finset.card_empty]
        · intro t1 _ t2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro m h1 h2
          dsimp only at h1 h2
          split_ifs at h1 with c1 <;> split_ifs at h2 with c2
          · simp only [PEqualNP.Outside.L_lib_755.cycWords, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
            exact hne (h1.2.2.symm.trans h2.2.2)
          · exact Finset.notMem_empty m h2
          · exact Finset.notMem_empty m h1
          · exact Finset.notMem_empty m h1
      · intro r1 _ r2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro m h1 h2
        dsimp only at h1 h2
        simp only [Finset.mem_biUnion] at h1 h2
        obtain ⟨t1, _, hm1⟩ := h1
        obtain ⟨t2, _, hm2⟩ := h2
        split_ifs at hm1 with c1 <;> split_ifs at hm2 with c2
        · simp only [PEqualNP.Outside.L_lib_755.cycWords, Finset.mem_filter, Finset.mem_univ, true_and] at hm1 hm2
          exact hne (hm1.2.1.symm.trans hm2.2.1)
        · exact Finset.notMem_empty m hm2
        · exact Finset.notMem_empty m hm1
        · exact Finset.notMem_empty m hm1
