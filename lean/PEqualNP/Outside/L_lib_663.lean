import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_663_aux

abbrev F := ZMod 2
abbrev W (k : ℕ) := Fin k → F

def ix {k : ℕ} (hk : 0 < k) (a : ℕ) : Fin k :=
  ⟨a % k, Nat.mod_lt _ hk⟩

def pt {k : ℕ} (hk : 0 < k) (c : Fin k) (left offset : ℕ) : Fin k :=
  ix hk (c.val + k - left % k + offset)

def mixFn {k : ℕ} (hk : 0 < k) (d : ℕ) (v : W k) (j : Fin k) : F :=
  v j + v (ix hk (j.val + d)) + v (ix hk (j.val + k - d % k))

def polarFn {k : ℕ} (hk : 0 < k) (z p : W k) (j : Fin k) : F :=
  z (ix hk (j.val + 1)) * p (ix hk (j.val + 2)) +
  z (ix hk (j.val + 2)) * p (ix hk (j.val + 1))

def stepSub {k : ℕ} (hk : 0 < k) (d : ℕ) (S : Submodule F (W k)) : Submodule F (W k) :=
  Submodule.span F {w : W k | ∃ v ∈ S, ∃ p : W k, w = polarFn hk (mixFn hk d v) p}

def unitVec {k : ℕ} (i j : Fin k) : F :=
  if i = j then (1 : F) else 0

lemma ix_eq_iff {k : ℕ} (hk : 0 < k) (a b : ℕ) : ix hk a = ix hk b ↔ a % k = b % k := by
  simp [ix, Fin.ext_iff]

lemma pt_val_mod {k : ℕ} (hk : 0 < k) (c : Fin k) (left offset : ℕ) :
    ((pt hk c left offset).val + left) % k = (c.val + offset) % k := by
  simp only [pt, ix]
  have hl : left % k < k := Nat.mod_lt left hk
  have hdiv : left = k * (left / k) + left % k := (Nat.div_add_mod left k).symm
  rw [Nat.mod_add_mod]
  have hrew : c.val + k - left % k + offset + left = c.val + offset + k * (left / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [hrew, Nat.add_mul_mod_self_left]

lemma pt_eq_iff_mod {k : ℕ} (hk : 0 < k) (c : Fin k) (l1 r1 l2 r2 : ℕ) :
    pt hk c l1 r1 = pt hk c l2 r2 ↔ (r1 + l2) % k = (r2 + l1) % k := by
  have h1 := pt_val_mod hk c l1 r1
  have h2 := pt_val_mod hk c l2 r2
  have hlt1 : (pt hk c l1 r1).val < k := (pt hk c l1 r1).isLt
  have hlt2 : (pt hk c l2 r2).val < k := (pt hk c l2 r2).isLt
  constructor
  · intro heq
    have hmod1 : ((pt hk c l1 r1).val + l1 + l2) % k = (c.val + r1 + l2) % k := by
      rw [← Nat.mod_add_mod, h1, Nat.mod_add_mod]
    have hmod2 : ((pt hk c l2 r2).val + l2 + l1) % k = (c.val + r2 + l1) % k := by
      rw [← Nat.mod_add_mod, h2, Nat.mod_add_mod]
    have hEq : (c.val + (r1 + l2)) % k = (c.val + (r2 + l1)) % k := by
      have hcomm : (pt hk c l1 r1).val + l1 + l2 = (pt hk c l2 r2).val + l2 + l1 := by
        rw [heq]; omega
      have h1' : (c.val + r1 + l2) % k = (c.val + r2 + l1) % k := by
        rw [← hmod1, ← hmod2, hcomm]
      simpa only [Nat.add_assoc] using h1'
    have hadd := congrArg (fun x => (x + (k - c.val)) % k) hEq
    simp only [Nat.mod_add_mod] at hadd
    have hc : c.val < k := c.isLt
    have ha1 : c.val + (r1 + l2) + (k - c.val) = (r1 + l2) + k := by omega
    have ha2 : c.val + (r2 + l1) + (k - c.val) = (r2 + l1) + k := by omega
    rw [ha1, ha2, Nat.add_mod_right, Nat.add_mod_right] at hadd
    exact hadd
  · intro hmod
    have hEq : ((pt hk c l1 r1).val + (l1 + l2)) % k = ((pt hk c l2 r2).val + (l1 + l2)) % k := by
      have ha1 : ((pt hk c l1 r1).val + (l1 + l2)) % k = (c.val + (r1 + l2)) % k := by
        rw [← Nat.add_assoc, ← Nat.mod_add_mod, h1, Nat.mod_add_mod, Nat.add_assoc]
      have ha2 : ((pt hk c l2 r2).val + (l1 + l2)) % k = (c.val + (r2 + l1)) % k := by
        have hcomm : (pt hk c l2 r2).val + (l1 + l2) = (pt hk c l2 r2).val + l2 + l1 := by omega
        rw [hcomm, ← Nat.mod_add_mod, h2, Nat.mod_add_mod, Nat.add_assoc]
      rw [ha1, ha2, Nat.add_mod, hmod, ← Nat.add_mod]
    have hsub := congrArg (fun x => (x + (k - (l1 + l2) % k)) % k) hEq
    simp only [Nat.mod_add_mod] at hsub
    have hlm : (l1 + l2) % k < k := Nat.mod_lt _ hk
    have hdiv : l1 + l2 = k * ((l1 + l2) / k) + (l1 + l2) % k := (Nat.div_add_mod _ k).symm
    have hs1 : (pt hk c l1 r1).val + (l1 + l2) + (k - (l1 + l2) % k) =
        (pt hk c l1 r1).val + k * ((l1 + l2) / k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    have hs2 : (pt hk c l2 r2).val + (l1 + l2) + (k - (l1 + l2) % k) =
        (pt hk c l2 r2).val + k * ((l1 + l2) / k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [hs1, hs2, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hsub
    exact Fin.ext hsub

lemma pt_zero_zero {k : ℕ} (hk : 0 < k) (c : Fin k) : pt hk c 0 0 = c := by
  apply Fin.ext
  simp [pt, ix, Nat.mod_eq_of_lt c.isLt]

lemma pt_add {k : ℕ} (hk : 0 < k) (c : Fin k) (l r a : ℕ) :
    ix hk ((pt hk c l r).val + a) = pt hk c l (r + a) := by
  apply Fin.ext
  simp only [pt, ix]
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma pt_sub {k : ℕ} (hk : 0 < k) (c : Fin k) (l r a : ℕ) :
    ix hk ((pt hk c l r).val + k - a % k) = pt hk c (l + a) r := by
  have h1 : ix hk ((pt hk c l r).val + k - a % k) = pt hk (pt hk c l r) a 0 := by
    simp [pt]
  rw [h1]
  have hmod : ((pt hk (pt hk c l r) a 0).val + (l + a)) % k = (c.val + r) % k := by
    have ha := pt_val_mod hk (pt hk c l r) a 0
    have hb := pt_val_mod hk c l r
    have hcomm : (pt hk (pt hk c l r) a 0).val + (l + a) =
        (pt hk (pt hk c l r) a 0).val + a + l := by omega
    rw [hcomm, ← Nat.mod_add_mod, ha, Nat.add_zero, Nat.mod_add_mod, hb]
  have hmod2 := pt_val_mod hk c (l + a) r
  have hEq : ((pt hk (pt hk c l r) a 0).val + (l + a)) % k =
      ((pt hk c (l + a) r).val + (l + a)) % k := by
    rw [hmod, hmod2]
  have hsub := congrArg (fun x => (x + (k - (l + a) % k)) % k) hEq
  simp only [Nat.mod_add_mod] at hsub
  have hlm : (l + a) % k < k := Nat.mod_lt _ hk
  have hdiv : l + a = k * ((l + a) / k) + (l + a) % k := (Nat.div_add_mod _ k).symm
  have hs1 : (pt hk (pt hk c l r) a 0).val + (l + a) + (k - (l + a) % k) =
      (pt hk (pt hk c l r) a 0).val + k * ((l + a) / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hs2 : (pt hk c (l + a) r).val + (l + a) + (k - (l + a) % k) =
      (pt hk c (l + a) r).val + k * ((l + a) / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [hs1, hs2, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (pt hk (pt hk c l r) a 0).isLt,
    Nat.mod_eq_of_lt (pt hk c (l + a) r).isLt] at hsub
  exact Fin.ext hsub

lemma ix_add_eq_pt {k : ℕ} (hk : 0 < k) (j : Fin k) (a : ℕ) :
    ix hk (j.val + a) = pt hk j 0 a := by
  apply Fin.ext
  simp only [pt, ix, Nat.zero_mod, Nat.sub_zero]
  have h : j.val + k + a = j.val + a + k := by omega
  rw [h, Nat.add_mod_right]

lemma pt_pt {k : ℕ} (hk : 0 < k) (c : Fin k) (l1 r1 l2 r2 : ℕ) :
    pt hk (pt hk c l1 r1) l2 r2 = pt hk c (l1 + l2) (r1 + r2) := by
  have h1 : pt hk (pt hk c l1 r1) l2 r2 = ix hk ((pt hk (pt hk c l1 r1) l2 0).val + r2) := by
    apply Fin.ext
    simp only [pt, ix]
    rw [Nat.add_zero, Nat.mod_add_mod]
  have h2 : pt hk (pt hk c l1 r1) l2 0 = ix hk ((pt hk c l1 r1).val + k - l2 % k) := by
    simp [pt]
  rw [h1, h2, pt_sub, pt_add]

lemma pt_cancel {k : ℕ} (hk : 0 < k) (c : Fin k) (l r m : ℕ) :
    pt hk c (l + m) (r + m) = pt hk c l r := by
  rw [pt_eq_iff_mod]
  have : r + m + l = r + (l + m) := by omega
  rw [this]

lemma pt_self_cancel {k : ℕ} (hk : 0 < k) (c : Fin k) (m : ℕ) :
    pt hk c m m = c := by
  simpa only [Nat.zero_add] using (pt_cancel hk c 0 0 m).trans (pt_zero_zero hk c)

lemma pt_ne_of_lt {k : ℕ} (hk : 0 < k) (c : Fin k) {l1 r1 l2 r2 : ℕ}
    (h1 : r1 + l2 ≠ r2 + l1)
    (h2 : r1 + l2 < r2 + l1 + k) (h3 : r2 + l1 < r1 + l2 + k) :
    pt hk c l1 r1 ≠ pt hk c l2 r2 := by
  intro heq
  rw [pt_eq_iff_mod] at heq
  have hmod : ∀ a b : ℕ, a < b → b < a + k → a % k ≠ b % k := by
    intro a b hab hbk h
    have h1' : b = a + (b - a) := by omega
    have h2' : 0 < b - a := by omega
    have h3' : b - a < k := by omega
    have h4' : (a % k + (b - a) % k) % k = a % k := by
      rw [← Nat.add_mod, ← h1', ← h]
    have h5' : (b - a) % k = b - a := Nat.mod_eq_of_lt h3'
    rw [h5'] at h4'
    have h6' : a % k < k := Nat.mod_lt a hk
    by_cases hlt : a % k + (b - a) < k
    · rw [Nat.mod_eq_of_lt hlt] at h4'
      omega
    · have hsub : a % k + (b - a) = (a % k + (b - a) - k) + k := by omega
      have hlt2 : a % k + (b - a) - k < k := by omega
      rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2] at h4'
      omega
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · exact hmod _ _ hlt h3 heq
  · exact hmod _ _ hgt h2 heq.symm

lemma mixFn_add {k : ℕ} (hk : 0 < k) (d : ℕ) (v1 v2 : W k) :
    mixFn hk d (v1 + v2) = mixFn hk d v1 + mixFn hk d v2 := by
  funext j
  simp only [mixFn, Pi.add_apply]
  ring

lemma mixFn_smul {k : ℕ} (hk : 0 < k) (d : ℕ) (a : F) (v : W k) :
    mixFn hk d (a • v) = a • mixFn hk d v := by
  funext j
  simp only [mixFn, Pi.smul_apply, smul_eq_mul]
  ring

lemma polarFn_add_left {k : ℕ} (hk : 0 < k) (z1 z2 p : W k) :
    polarFn hk (z1 + z2) p = polarFn hk z1 p + polarFn hk z2 p := by
  funext j
  simp only [polarFn, Pi.add_apply]
  ring

lemma polarFn_smul_left {k : ℕ} (hk : 0 < k) (a : F) (z p : W k) :
    polarFn hk (a • z) p = a • polarFn hk z p := by
  funext j
  simp only [polarFn, Pi.smul_apply, smul_eq_mul]
  ring

lemma polarFn_add_right {k : ℕ} (hk : 0 < k) (z p1 p2 : W k) :
    polarFn hk z (p1 + p2) = polarFn hk z p1 + polarFn hk z p2 := by
  funext j
  simp only [polarFn, Pi.add_apply]
  ring

lemma polarFn_smul_right {k : ℕ} (hk : 0 < k) (a : F) (z p : W k) :
    polarFn hk z (a • p) = a • polarFn hk z p := by
  funext j
  simp only [polarFn, Pi.smul_apply, smul_eq_mul]
  ring

lemma polarFn_unit {k : ℕ} (hk : 0 < k) (hk3 : 3 ≤ k) (z : W k) (q : Fin k) :
    polarFn hk z (unitVec q) =
      z (pt hk q 1 0) • unitVec (pt hk q 2 0) + z (pt hk q 0 1) • unitVec (pt hk q 1 0) := by
  funext j
  simp only [polarFn, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hj2 : q = ix hk (j.val + 2) ↔ pt hk q 2 0 = j := by
    constructor
    · intro h
      have h1 := congrArg (fun x => pt hk x 2 0) h
      have h2 : pt hk (ix hk (j.val + 2)) 2 0 = j := by
        simp only [ix_add_eq_pt, pt_pt, Nat.zero_add, Nat.add_zero, pt_self_cancel]
      rw [h2] at h1
      exact h1
    · intro h
      rw [← h, pt_add, Nat.zero_add, pt_self_cancel]
  have hj1 : q = ix hk (j.val + 1) ↔ pt hk q 1 0 = j := by
    constructor
    · intro h
      have h1 := congrArg (fun x => pt hk x 1 0) h
      have h2 : pt hk (ix hk (j.val + 1)) 1 0 = j := by
        simp only [ix_add_eq_pt, pt_pt, Nat.zero_add, Nat.add_zero, pt_self_cancel]
      rw [h2] at h1
      exact h1
    · intro h
      rw [← h, pt_add, Nat.zero_add, pt_self_cancel]
  have hne : pt hk q 2 0 ≠ pt hk q 1 0 :=
    pt_ne_of_lt hk q (by omega) (by omega) (by omega)
  by_cases h1 : pt hk q 2 0 = j
  · subst h1
    have h1' : q = ix hk ((pt hk q 2 0).val + 2) := hj2.mpr rfl
    have h2' : q ≠ ix hk ((pt hk q 2 0).val + 1) := fun h => hne (hj1.mp h).symm
    have hx1 : ix hk ((pt hk q 2 0).val + 1) = pt hk q 1 0 := by
      rw [pt_add]
      exact pt_cancel hk q 1 0 1
    have u1 : unitVec q (ix hk ((pt hk q 2 0).val + 2)) = 1 := by
      dsimp only [unitVec]; rw [ite_eq_left_iff]; intro h; exact absurd h1' h
    have u2 : unitVec q (ix hk ((pt hk q 2 0).val + 1)) = 0 := by
      dsimp only [unitVec]; rw [ite_eq_right_iff]; intro h; exact absurd h h2'
    have u3 : unitVec (pt hk q 2 0) (pt hk q 2 0) = 1 := by
      dsimp only [unitVec]; rw [ite_eq_left_iff]; intro h; exact absurd rfl h
    have u4 : unitVec (pt hk q 1 0) (pt hk q 2 0) = 0 := by
      dsimp only [unitVec]; rw [ite_eq_right_iff]; intro h; exact absurd h hne.symm
    rw [u1, u2, u3, u4, hx1]
    ring
  · by_cases h2 : pt hk q 1 0 = j
    · subst h2
      have h2' : q = ix hk ((pt hk q 1 0).val + 1) := hj1.mpr rfl
      have h1' : q ≠ ix hk ((pt hk q 1 0).val + 2) := fun h => hne (hj2.mp h)
      have hx2 : ix hk ((pt hk q 1 0).val + 2) = pt hk q 0 1 := by
        rw [pt_add]
        exact pt_cancel hk q 0 1 1
      have u1 : unitVec q (ix hk ((pt hk q 1 0).val + 2)) = 0 := by
        dsimp only [unitVec]; rw [ite_eq_right_iff]; intro h; exact absurd h h1'
      have u2 : unitVec q (ix hk ((pt hk q 1 0).val + 1)) = 1 := by
        dsimp only [unitVec]; rw [ite_eq_left_iff]; intro h; exact absurd h2' h
      have u3 : unitVec (pt hk q 2 0) (pt hk q 1 0) = 0 := by
        dsimp only [unitVec]; rw [ite_eq_right_iff]; intro h; exact absurd h hne
      have u4 : unitVec (pt hk q 1 0) (pt hk q 1 0) = 1 := by
        dsimp only [unitVec]; rw [ite_eq_left_iff]; intro h; exact absurd rfl h
      rw [u1, u2, u3, u4, hx2]
      ring
    · have h1' : q ≠ ix hk (j.val + 2) := fun h => h1 (hj2.mp h)
      have h2' : q ≠ ix hk (j.val + 1) := fun h => h2 (hj1.mp h)
      have u1 : unitVec q (ix hk (j.val + 2)) = 0 := by
        dsimp only [unitVec]; rw [ite_eq_right_iff]; intro h; exact absurd h h1'
      have u2 : unitVec q (ix hk (j.val + 1)) = 0 := by
        dsimp only [unitVec]; rw [ite_eq_right_iff]; intro h; exact absurd h h2'
      have u3 : unitVec (pt hk q 2 0) j = 0 := by
        dsimp only [unitVec]; rw [ite_eq_right_iff]; intro h; exact absurd h h1
      have u4 : unitVec (pt hk q 1 0) j = 0 := by
        dsimp only [unitVec]; rw [ite_eq_right_iff]; intro h; exact absurd h h2
      rw [u1, u2, u3, u4]
      ring

lemma mixFn_unit {k : ℕ} (hk : 0 < k) (d : ℕ) (c : Fin k) :
    mixFn hk d (unitVec c) =
      unitVec (pt hk c d 0) + unitVec c + unitVec (pt hk c 0 d) := by
  funext j
  simp only [mixFn, Pi.add_apply]
  have hpos : c = ix hk (j.val + d) ↔ pt hk c d 0 = j := by
    constructor
    · intro h
      have h1 := congrArg (fun x => pt hk x d 0) h
      have h2 : pt hk (ix hk (j.val + d)) d 0 = j := by
        rw [ix_add_eq_pt, pt_pt, Nat.zero_add, Nat.add_zero, pt_self_cancel]
      rw [h2] at h1
      exact h1
    · intro h
      rw [← h, pt_add, Nat.zero_add, pt_self_cancel]
  have hneg : c = ix hk (j.val + k - d % k) ↔ pt hk c 0 d = j := by
    constructor
    · intro h
      have h1 := congrArg (fun x => pt hk x 0 d) h
      have h2 : pt hk (ix hk (j.val + k - d % k)) 0 d = j := by
        have : ix hk (j.val + k - d % k) = pt hk j d 0 := by simp [pt]
        rw [this, pt_pt, Nat.add_zero, Nat.zero_add, pt_self_cancel]
      rw [h2] at h1
      exact h1
    · intro h
      rw [← h, pt_sub, Nat.zero_add, pt_self_cancel]
  have e1 : unitVec c (ix hk (j.val + d)) = unitVec (pt hk c d 0) j := by
    simp only [unitVec, hpos]
  have e2 : unitVec c (ix hk (j.val + k - d % k)) = unitVec (pt hk c 0 d) j := by
    simp only [unitVec, hneg]
  rw [e1, e2]
  ring

lemma stepSub_mono {k : ℕ} (hk : 0 < k) (d : ℕ) {S1 S2 : Submodule F (W k)} (h : S1 ≤ S2) :
    stepSub hk d S1 ≤ stepSub hk d S2 := by
  refine Submodule.span_mono ?_
  rintro w ⟨v, hv, p, rfl⟩
  exact ⟨v, h hv, p, rfl⟩

lemma mem_stepSub_of_mem {k : ℕ} (hk : 0 < k) (d : ℕ) {S : Submodule F (W k)}
    {v : W k} (hv : v ∈ S) (p : W k) :
    polarFn hk (mixFn hk d v) p ∈ stepSub hk d S :=
  Submodule.subset_span ⟨v, hv, p, rfl⟩

lemma vec_eq_sum_unit {k : ℕ} (w : W k) : w = ∑ j : Fin k, w j • unitVec j := by
  funext i
  simp [Finset.sum_apply, unitVec]

lemma span_eq_supp {k : ℕ} (S : Submodule F (W k)) (P : Fin k → Prop)
    (hupper : ∀ w ∈ S, ∀ j, ¬ P j → w j = 0)
    (hlower : ∀ j, P j → unitVec j ∈ S) :
    ∀ w : W k, w ∈ S ↔ ∀ j : Fin k, ¬ P j → w j = 0 := by
  intro w
  constructor
  · exact hupper w
  · intro hw
    rw [vec_eq_sum_unit w]
    refine Submodule.sum_mem S ?_
    intro j _
    by_cases hj : P j
    · exact S.smul_mem (w j) (hlower j hj)
    · rw [hw j hj, zero_smul]
      exact S.zero_mem

lemma stepSub_locality {k : ℕ} (hk : 0 < k) (d : ℕ) (start : Fin k) (L M : ℕ)
    {S : Submodule F (W k)}
    (hS : ∀ v ∈ S, ∀ j : Fin k, (¬ ∃ b ≤ M, pt hk start L b = j) → v j = 0) :
    ∀ w ∈ stepSub hk d S, ∀ j : Fin k,
      (¬ ∃ b ≤ M + (2 * d + 1), pt hk start (L + (d + 2)) b = j) → w j = 0 := by
  let U : Submodule F (W k) :=
    ⟨⟨⟨{w | ∀ j : Fin k, (¬ ∃ b ≤ M + (2 * d + 1), pt hk start (L + (d + 2)) b = j) → w j = 0},
      fun ha hb j hj => by simp [ha j hj, hb j hj]⟩,
      fun _ _ => rfl⟩,
      fun c _ hx j hj => by simp [hx j hj]⟩
  have hle : stepSub hk d S ≤ U := by
    rw [stepSub, Submodule.span_le]
    rintro w ⟨v, hv, p, rfl⟩ j hj
    have hz : ∀ t, 1 ≤ t → t ≤ 2 → mixFn hk d v (ix hk (j.val + t)) = 0 := by
      intro t ht1 ht2
      simp only [mixFn]
      have h0 : v (ix hk (j.val + t)) = 0 := by
        apply hS v hv
        rintro ⟨b, hbM, hbe⟩
        apply hj
        refine ⟨b + d + 2 - t, by omega, ?_⟩
        rw [ix_add_eq_pt] at hbe
        have h2 := congrArg (fun x => pt hk x t 0) hbe
        simp only [pt_pt, Nat.zero_add, Nat.add_zero, pt_self_cancel] at h2
        rw [← h2, pt_eq_iff_mod]
        have : b + d + 2 - t + (L + t) = b + (L + (d + 2)) := by omega
        rw [this]
      have hplus : v (ix hk ((ix hk (j.val + t)).val + d)) = 0 := by
        apply hS v hv
        rintro ⟨b, hbM, hbe⟩
        apply hj
        refine ⟨b + 2 + 2 * d - t - 2 * d, by omega, ?_⟩
        have h1 : ix hk ((ix hk (j.val + t)).val + d) = pt hk j 0 (t + d) := by
          rw [ix_add_eq_pt hk j t, pt_add]
        rw [h1] at hbe
        have h2 := congrArg (fun x => pt hk x (t + d) 0) hbe
        simp only [pt_pt, Nat.zero_add, Nat.add_zero, pt_self_cancel] at h2
        rw [← h2, pt_eq_iff_mod]
        have : b + 2 + 2 * d - t - 2 * d + (L + (t + d)) = b + (L + (d + 2)) := by omega
        rw [this]
      have hminus : v (ix hk ((ix hk (j.val + t)).val + k - d % k)) = 0 := by
        apply hS v hv
        rintro ⟨b, hbM, hbe⟩
        apply hj
        refine ⟨b + 2 * d + 2 - t, by omega, ?_⟩
        have h1 : ix hk ((ix hk (j.val + t)).val + k - d % k) = pt hk j d t := by
          rw [ix_add_eq_pt, pt_sub, Nat.zero_add]
        rw [h1] at hbe
        have h2 := congrArg (fun x => pt hk x t d) hbe
        simp only [pt_pt] at h2
        have h3 : pt hk j (d + t) (t + d) = j := by
          rw [Nat.add_comm t d, pt_self_cancel]
        rw [h3] at h2
        rw [← h2, pt_eq_iff_mod]
        have : b + 2 * d + 2 - t + (L + t) = b + d + (L + (d + 2)) := by omega
        rw [this]
      rw [h0, hplus, hminus]
      simp
    simp only [polarFn, hz 1 (by omega) (by omega), hz 2 (by omega) (by omega), zero_mul, add_zero]
  exact fun w hw => hle hw

lemma iter_locality {k : ℕ} (hk : 0 < k) (d : ℕ) (start : Fin k) :
    ∀ h : ℕ, ∀ w ∈ (stepSub hk d)^[h] (Submodule.span F ({unitVec start} : Set (W k))),
      ∀ j : Fin k, (¬ ∃ b ≤ (2 * d + 1) * h, pt hk start ((d + 2) * h) b = j) → w j = 0 := by
  intro h
  induction h with
  | zero =>
    intro w hw j hj
    simp only [Function.iterate_zero, id_eq] at hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
    have hne : start ≠ j := by
      intro heq
      apply hj
      exact ⟨0, by omega, by rw [Nat.mul_zero, pt_zero_zero, heq]⟩
    simp [unitVec, hne]
  | succ h ih =>
    rw [Function.iterate_succ_apply']
    have hloc := stepSub_locality hk d start ((d + 2) * h) ((2 * d + 1) * h) ih
    intro w hw j hj
    apply hloc w hw j
    intro hex
    apply hj
    rcases hex with ⟨b, hb, heq⟩
    refine ⟨b, by rw [Nat.mul_succ]; omega, ?_⟩
    simpa [Nat.mul_succ] using heq

lemma d1_step_unit {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (c : Fin k) (S : Submodule F (W k))
    (hc : unitVec c ∈ S) :
    ∀ a ≤ 3, unitVec (pt hk c 3 a) ∈ stepSub hk 1 S := by
  have hz : mixFn hk 1 (unitVec c) =
      unitVec (pt hk c 1 0) + unitVec c + unitVec (pt hk c 0 1) :=
    mixFn_unit hk 1 c
  have hval : ∀ l r, mixFn hk 1 (unitVec c) (pt hk c l r) =
      unitVec (pt hk c 1 0) (pt hk c l r) + unitVec (pt hk c 0 0) (pt hk c l r) +
      unitVec (pt hk c 0 1) (pt hk c l r) := by
    intro l r; rw [hz, pt_zero_zero]; rfl
  have hmem : ∀ q : Fin k,
      mixFn hk 1 (unitVec c) (pt hk q 1 0) • unitVec (pt hk q 2 0) +
      mixFn hk 1 (unitVec c) (pt hk q 0 1) • unitVec (pt hk q 1 0) ∈ stepSub hk 1 S := by
    intro q
    rw [← polarFn_unit hk (by omega)]
    exact mem_stepSub_of_mem hk 1 hc (unitVec q)
  have h_eval : ∀ l1 r1 l2 r2,
      unitVec (pt hk c l1 r1) (pt hk c l2 r2) = if pt hk c l1 r1 = pt hk c l2 r2 then 1 else 0 :=
    fun _ _ _ _ => rfl
  have h0 : unitVec (pt hk c 3 0) ∈ stepSub hk 1 S := by
    have hm := hmem (pt hk c 2 0)
    simp only [pt_pt] at hm
    have hneq1 : pt hk c 1 0 ≠ pt hk c 3 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq2 : pt hk c 0 0 ≠ pt hk c 3 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq3 : pt hk c 0 1 ≠ pt hk c 3 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq4 : pt hk c 0 0 ≠ pt hk c 2 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq5 : pt hk c 0 1 ≠ pt hk c 2 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have heq1 : pt hk c 1 0 = pt hk c 2 1 := (pt_cancel hk c 1 0 1).symm
    have hleft : mixFn hk 1 (unitVec c) (pt hk c (2 + 1) (0 + 0)) = 0 := by
      rw [hval]; simp only [unitVec, hneq1, hneq2, hneq3]; simp
    have hright : mixFn hk 1 (unitVec c) (pt hk c (2 + 0) (0 + 1)) = 1 := by
      rw [hval]; simp only [unitVec, heq1, hneq4, hneq5]; simp
    rw [hleft, hright, zero_smul, one_smul, zero_add] at hm
    exact hm
  have h1 : unitVec (pt hk c 3 1) ∈ stepSub hk 1 S := by
    have hm := hmem (pt hk c 1 0)
    simp only [pt_pt] at hm
    have hneq1 : pt hk c 1 0 ≠ pt hk c 2 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq2 : pt hk c 0 0 ≠ pt hk c 2 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq3 : pt hk c 0 1 ≠ pt hk c 2 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq4 : pt hk c 1 0 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq5 : pt hk c 0 1 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have heq2 : pt hk c 0 0 = pt hk c 1 1 := (pt_cancel hk c 0 0 1).symm
    have hleft : mixFn hk 1 (unitVec c) (pt hk c (1 + 1) (0 + 0)) = 0 := by
      rw [hval]; simp only [unitVec, hneq1, hneq2, hneq3]; simp
    have hright : mixFn hk 1 (unitVec c) (pt hk c (1 + 0) (0 + 1)) = 1 := by
      rw [hval]; simp only [unitVec, hneq4, heq2, hneq5]; simp
    rw [hleft, hright, zero_smul, one_smul, zero_add] at hm
    have heq_out : pt hk c (1 + 1) (0 + 0) = pt hk c 3 1 := (pt_cancel hk c 2 0 1).symm
    rwa [heq_out] at hm
  have h2 : unitVec (pt hk c 3 2) ∈ stepSub hk 1 S := by
    have hm := hmem (pt hk c 0 1)
    simp only [pt_pt] at hm
    have hneq1 : pt hk c 1 0 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq2 : pt hk c 0 1 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have heq1 : pt hk c 0 0 = pt hk c 1 1 := (pt_cancel hk c 0 0 1).symm
    have hneq3 : pt hk c 1 0 ≠ pt hk c 0 2 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq4 : pt hk c 0 0 ≠ pt hk c 0 2 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq5 : pt hk c 0 1 ≠ pt hk c 0 2 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hleft : mixFn hk 1 (unitVec c) (pt hk c (0 + 1) (1 + 0)) = 1 := by
      rw [hval]; simp only [unitVec, hneq1, heq1, hneq2]; simp
    have hright : mixFn hk 1 (unitVec c) (pt hk c (0 + 0) (1 + 1)) = 0 := by
      rw [hval]; simp only [unitVec, hneq3, hneq4, hneq5]; simp
    rw [hleft, hright, one_smul, zero_smul, add_zero] at hm
    have heq_out : pt hk c (0 + 2) (1 + 0) = pt hk c 3 2 := (pt_cancel hk c 2 1 1).symm
    rwa [heq_out] at hm
  have h3 : unitVec (pt hk c 3 3) ∈ stepSub hk 1 S := by
    have hm := hmem (pt hk c 0 2)
    simp only [pt_pt] at hm
    have hneq1 : pt hk c 1 0 ≠ pt hk c 1 2 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq2 : pt hk c 0 0 ≠ pt hk c 1 2 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have heq1 : pt hk c 0 1 = pt hk c 1 2 := (pt_cancel hk c 0 1 1).symm
    have hneq3 : pt hk c 1 0 ≠ pt hk c 0 3 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq4 : pt hk c 0 0 ≠ pt hk c 0 3 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hneq5 : pt hk c 0 1 ≠ pt hk c 0 3 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have hleft : mixFn hk 1 (unitVec c) (pt hk c (0 + 1) (2 + 0)) = 1 := by
      rw [hval]; simp only [unitVec, hneq1, hneq2, heq1]; simp
    have hright : mixFn hk 1 (unitVec c) (pt hk c (0 + 0) (2 + 1)) = 0 := by
      rw [hval]; simp only [unitVec, hneq3, hneq4, hneq5]; simp
    rw [hleft, hright, one_smul, zero_smul, add_zero] at hm
    have heq_out : pt hk c (0 + 2) (2 + 0) = pt hk c 3 3 := (pt_cancel hk c 2 2 1).symm
    rwa [heq_out] at hm
  intro a ha
  interval_cases a
  · exact h0
  · exact h1
  · exact h2
  · exact h3

lemma d2_step_unit_eq {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (c : Fin k) :
    stepSub hk 2 (Submodule.span F ({unitVec c} : Set (W k))) =
      Submodule.span F ({unitVec (pt hk c 4 0), unitVec (pt hk c 4 5),
        unitVec (pt hk c 4 1) + unitVec (pt hk c 4 2),
        unitVec (pt hk c 4 3) + unitVec (pt hk c 4 4)} : Set (W k)) := by
  set G : Set (W k) := {unitVec (pt hk c 4 0), unitVec (pt hk c 4 5),
    unitVec (pt hk c 4 1) + unitVec (pt hk c 4 2),
    unitVec (pt hk c 4 3) + unitVec (pt hk c 4 4)}
  have hz : mixFn hk 2 (unitVec c) =
      unitVec (pt hk c 2 0) + unitVec c + unitVec (pt hk c 0 2) :=
    mixFn_unit hk 2 c
  have hval : ∀ x : Fin k, mixFn hk 2 (unitVec c) x =
      unitVec (pt hk c 2 0) x + unitVec (pt hk c 0 0) x + unitVec (pt hk c 0 2) x := by
    intro x; rw [hz, pt_zero_zero]; rfl
  have hq_form : ∀ q : Fin k,
      polarFn hk (mixFn hk 2 (unitVec c)) (unitVec q) ∈ Submodule.span F G := by
    intro q
    rw [polarFn_unit hk (by omega)]
    by_cases hq1 : q = pt hk c 3 0
    · subst hq1
      simp only [pt_pt]
      have hl : mixFn hk 2 (unitVec c) (pt hk c (3 + 1) (0 + 0)) = 0 := by
        rw [hval]
        have n1 : pt hk c 2 0 ≠ pt hk c 4 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n2 : pt hk c 0 0 ≠ pt hk c 4 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n3 : pt hk c 0 2 ≠ pt hk c 4 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        simp only [unitVec, n1, n2, n3]; simp
      have hr : mixFn hk 2 (unitVec c) (pt hk c (3 + 0) (0 + 1)) = 1 := by
        rw [hval]
        have e1 : pt hk c 2 0 = pt hk c 3 1 := (pt_cancel hk c 2 0 1).symm
        have n2 : pt hk c 0 0 ≠ pt hk c 3 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n3 : pt hk c 0 2 ≠ pt hk c 3 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        simp only [unitVec, e1, n2, n3]; simp
      rw [hl, hr, zero_smul, one_smul, zero_add]
      exact Submodule.subset_span (by simp [G])
    · by_cases hq2 : q = pt hk c 1 0
      · subst hq2
        simp only [pt_pt]
        have hl : mixFn hk 2 (unitVec c) (pt hk c (1 + 1) (0 + 0)) = 1 := by
          rw [hval]
          have n2 : pt hk c 0 0 ≠ pt hk c 2 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
          have n3 : pt hk c 0 2 ≠ pt hk c 2 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
          simp only [unitVec, n2, n3]; simp
        have hr : mixFn hk 2 (unitVec c) (pt hk c (1 + 0) (0 + 1)) = 1 := by
          rw [hval]
          have n1 : pt hk c 2 0 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
          have e2 : pt hk c 0 0 = pt hk c 1 1 := (pt_cancel hk c 0 0 1).symm
          have n3 : pt hk c 0 2 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
          simp only [unitVec, n1, e2, n3]; simp
        rw [hl, hr, one_smul, one_smul]
        have e1 : pt hk c (1 + 2) (0 + 0) = pt hk c 4 1 := (pt_cancel hk c 3 0 1).symm
        have e2 : pt hk c (1 + 1) (0 + 0) = pt hk c 4 2 := (pt_cancel hk c 2 0 2).symm
        rw [e1, e2]
        exact Submodule.subset_span (by simp [G])
      · by_cases hq3 : q = pt hk c 0 1
        · subst hq3
          simp only [pt_pt]
          have hl : mixFn hk 2 (unitVec c) (pt hk c (0 + 1) (1 + 0)) = 1 := by
            rw [hval]
            have n1 : pt hk c 2 0 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
            have e2 : pt hk c 0 0 = pt hk c 1 1 := (pt_cancel hk c 0 0 1).symm
            have n3 : pt hk c 0 2 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
            simp only [unitVec, n1, e2, n3]; simp
          have hr : mixFn hk 2 (unitVec c) (pt hk c (0 + 0) (1 + 1)) = 1 := by
            rw [hval]
            have n1 : pt hk c 2 0 ≠ pt hk c 0 2 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
            have n2 : pt hk c 0 0 ≠ pt hk c 0 2 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
            simp only [unitVec, n1, n2]; simp
          rw [hl, hr, one_smul, one_smul]
          have e1 : pt hk c (0 + 2) (1 + 0) = pt hk c 4 3 := (pt_cancel hk c 2 1 2).symm
          have e2 : pt hk c (0 + 1) (1 + 0) = pt hk c 4 4 := (pt_cancel hk c 1 1 3).symm
          rw [e1, e2]
          exact Submodule.subset_span (by simp [G])
        · by_cases hq4 : q = pt hk c 0 3
          · subst hq4
            simp only [pt_pt]
            have hl : mixFn hk 2 (unitVec c) (pt hk c (0 + 1) (3 + 0)) = 1 := by
              rw [hval]
              have n1 : pt hk c 2 0 ≠ pt hk c 1 3 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
              have n2 : pt hk c 0 0 ≠ pt hk c 1 3 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
              have e3 : pt hk c 0 2 = pt hk c 1 3 := (pt_cancel hk c 0 2 1).symm
              simp only [unitVec, n1, n2, e3]; simp
            have hr : mixFn hk 2 (unitVec c) (pt hk c (0 + 0) (3 + 1)) = 0 := by
              rw [hval]
              have n1 : pt hk c 2 0 ≠ pt hk c 0 4 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
              have n2 : pt hk c 0 0 ≠ pt hk c 0 4 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
              have n3 : pt hk c 0 2 ≠ pt hk c 0 4 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
              simp only [unitVec, n1, n2, n3]; simp
            rw [hl, hr, one_smul, zero_smul, add_zero]
            have e1 : pt hk c (0 + 2) (3 + 0) = pt hk c 4 5 := (pt_cancel hk c 2 3 2).symm
            rw [e1]
            exact Submodule.subset_span (by simp [G])
          · have hleft0 : mixFn hk 2 (unitVec c) (pt hk q 1 0) = 0 := by
              rw [hval]
              have n1 : pt hk c 2 0 ≠ pt hk q 1 0 := by
                intro h
                apply hq2
                have h1 := congrArg (fun x => pt hk x 0 1) h
                rw [pt_pt, pt_pt, Nat.add_zero, Nat.zero_add,
                  pt_cancel hk q 0 0 1, pt_zero_zero, pt_cancel hk c 1 0 1] at h1
                exact h1.symm
              have n2 : pt hk c 0 0 ≠ pt hk q 1 0 := by
                intro h
                rw [pt_zero_zero] at h
                apply hq3
                have h1 := congrArg (fun x => pt hk x 0 1) h
                rw [pt_pt, Nat.add_zero, pt_cancel hk q 0 0 1, pt_zero_zero] at h1
                exact h1.symm
              have n3 : pt hk c 0 2 ≠ pt hk q 1 0 := by
                intro h
                apply hq4
                have h1 := congrArg (fun x => pt hk x 0 1) h
                rw [pt_pt, pt_pt, Nat.add_zero, pt_cancel hk q 0 0 1, pt_zero_zero] at h1
                exact h1.symm
              simp only [unitVec, n1, n2, n3]; simp
            have hright0 : mixFn hk 2 (unitVec c) (pt hk q 0 1) = 0 := by
              rw [hval]
              have n1 : pt hk c 2 0 ≠ pt hk q 0 1 := by
                intro h
                apply hq1
                have h1 := congrArg (fun x => pt hk x 1 0) h
                rw [pt_pt, pt_pt, Nat.add_zero, pt_cancel hk q 0 0 1, pt_zero_zero] at h1
                exact h1.symm
              have n2 : pt hk c 0 0 ≠ pt hk q 0 1 := by
                intro h
                rw [pt_zero_zero] at h
                apply hq2
                have h1 := congrArg (fun x => pt hk x 1 0) h
                rw [pt_pt, Nat.zero_add, pt_cancel hk q 0 0 1, pt_zero_zero] at h1
                exact h1.symm
              have n3 : pt hk c 0 2 ≠ pt hk q 0 1 := by
                intro h
                apply hq3
                have h1 := congrArg (fun x => pt hk x 1 0) h
                rw [pt_pt, pt_pt, Nat.zero_add, pt_cancel hk q 0 0 1, pt_zero_zero,
                  pt_cancel hk c 0 1 1] at h1
                exact h1.symm
              simp only [unitVec, n1, n2, n3]; simp
            rw [hleft0, hright0, zero_smul, zero_smul, add_zero]
            exact Submodule.zero_mem _
  apply le_antisymm
  · rw [stepSub, Submodule.span_le]
    rintro w ⟨v, hv, p, rfl⟩
    rcases Submodule.mem_span_singleton.mp hv with ⟨a, rfl⟩
    rw [mixFn_smul, polarFn_smul_left]
    apply Submodule.smul_mem
    rw [vec_eq_sum_unit p]
    have hsum : ∀ s : Finset (Fin k),
        polarFn hk (mixFn hk 2 (unitVec c)) (∑ j ∈ s, p j • unitVec j) =
          ∑ j ∈ s, p j • polarFn hk (mixFn hk 2 (unitVec c)) (unitVec j) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        funext j; simp [polarFn]
      | @insert x s hx ih =>
        rw [Finset.sum_insert hx, polarFn_add_right, polarFn_smul_right, ih, Finset.sum_insert hx]
    rw [hsum]
    exact Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (hq_form q))
  · rw [Submodule.span_le]
    have huc : unitVec c ∈ Submodule.span F ({unitVec c} : Set (W k)) :=
      Submodule.subset_span (Set.mem_singleton _)
    have hmem : ∀ q : Fin k,
        mixFn hk 2 (unitVec c) (pt hk q 1 0) • unitVec (pt hk q 2 0) +
        mixFn hk 2 (unitVec c) (pt hk q 0 1) • unitVec (pt hk q 1 0) ∈
          stepSub hk 2 (Submodule.span F ({unitVec c} : Set (W k))) := by
      intro q
      rw [← polarFn_unit hk (by omega)]
      exact mem_stepSub_of_mem hk 2 huc (unitVec q)
    rintro w hw
    simp only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · have hm := hmem (pt hk c 3 0)
      simp only [pt_pt] at hm
      have hl : mixFn hk 2 (unitVec c) (pt hk c (3 + 1) (0 + 0)) = 0 := by
        rw [hval]
        have n1 : pt hk c 2 0 ≠ pt hk c 4 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n2 : pt hk c 0 0 ≠ pt hk c 4 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n3 : pt hk c 0 2 ≠ pt hk c 4 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        simp only [unitVec, n1, n2, n3]; simp
      have hr : mixFn hk 2 (unitVec c) (pt hk c (3 + 0) (0 + 1)) = 1 := by
        rw [hval]
        have e1 : pt hk c 2 0 = pt hk c 3 1 := (pt_cancel hk c 2 0 1).symm
        have n2 : pt hk c 0 0 ≠ pt hk c 3 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n3 : pt hk c 0 2 ≠ pt hk c 3 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        simp only [unitVec, e1, n2, n3]; simp
      rw [hl, hr, zero_smul, one_smul, zero_add] at hm
      exact hm
    · have hm := hmem (pt hk c 0 3)
      simp only [pt_pt] at hm
      have hl : mixFn hk 2 (unitVec c) (pt hk c (0 + 1) (3 + 0)) = 1 := by
        rw [hval]
        have n1 : pt hk c 2 0 ≠ pt hk c 1 3 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n2 : pt hk c 0 0 ≠ pt hk c 1 3 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have e3 : pt hk c 0 2 = pt hk c 1 3 := (pt_cancel hk c 0 2 1).symm
        simp only [unitVec, n1, n2, e3]; simp
      have hr : mixFn hk 2 (unitVec c) (pt hk c (0 + 0) (3 + 1)) = 0 := by
        rw [hval]
        have n1 : pt hk c 2 0 ≠ pt hk c 0 4 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n2 : pt hk c 0 0 ≠ pt hk c 0 4 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n3 : pt hk c 0 2 ≠ pt hk c 0 4 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        simp only [unitVec, n1, n2, n3]; simp
      rw [hl, hr, one_smul, zero_smul, add_zero] at hm
      have e1 : pt hk c (0 + 2) (3 + 0) = pt hk c 4 5 := (pt_cancel hk c 2 3 2).symm
      rwa [e1] at hm
    · have hm := hmem (pt hk c 1 0)
      simp only [pt_pt] at hm
      have hl : mixFn hk 2 (unitVec c) (pt hk c (1 + 1) (0 + 0)) = 1 := by
        rw [hval]
        have n2 : pt hk c 0 0 ≠ pt hk c 2 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n3 : pt hk c 0 2 ≠ pt hk c 2 0 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        simp only [unitVec, n2, n3]; simp
      have hr : mixFn hk 2 (unitVec c) (pt hk c (1 + 0) (0 + 1)) = 1 := by
        rw [hval]
        have n1 : pt hk c 2 0 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have e2 : pt hk c 0 0 = pt hk c 1 1 := (pt_cancel hk c 0 0 1).symm
        have n3 : pt hk c 0 2 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        simp only [unitVec, n1, e2, n3]; simp
      rw [hl, hr, one_smul, one_smul] at hm
      have e1 : pt hk c (1 + 2) (0 + 0) = pt hk c 4 1 := (pt_cancel hk c 3 0 1).symm
      have e2 : pt hk c (1 + 1) (0 + 0) = pt hk c 4 2 := (pt_cancel hk c 2 0 2).symm
      rwa [e1, e2] at hm
    · have hm := hmem (pt hk c 0 1)
      simp only [pt_pt] at hm
      have hl : mixFn hk 2 (unitVec c) (pt hk c (0 + 1) (1 + 0)) = 1 := by
        rw [hval]
        have n1 : pt hk c 2 0 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have e2 : pt hk c 0 0 = pt hk c 1 1 := (pt_cancel hk c 0 0 1).symm
        have n3 : pt hk c 0 2 ≠ pt hk c 1 1 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        simp only [unitVec, n1, e2, n3]; simp
      have hr : mixFn hk 2 (unitVec c) (pt hk c (0 + 0) (1 + 1)) = 1 := by
        rw [hval]
        have n1 : pt hk c 2 0 ≠ pt hk c 0 2 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        have n2 : pt hk c 0 0 ≠ pt hk c 0 2 := pt_ne_of_lt hk c (by omega) (by omega) (by omega)
        simp only [unitVec, n1, n2]; simp
      rw [hl, hr, one_smul, one_smul] at hm
      have e1 : pt hk c (0 + 2) (1 + 0) = pt hk c 4 3 := (pt_cancel hk c 2 1 2).symm
      have e2 : pt hk c (0 + 1) (1 + 0) = pt hk c 4 4 := (pt_cancel hk c 1 1 3).symm
      rwa [e1, e2] at hm

lemma d2_step_extremes {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (c : Fin k)
    {S : Submodule F (W k)} (hc : unitVec c ∈ S) :
    unitVec (pt hk c 4 0) ∈ stepSub hk 2 S ∧ unitVec (pt hk c 4 5) ∈ stepSub hk 2 S := by
  have hle : Submodule.span F ({unitVec c} : Set (W k)) ≤ S := by
    rw [Submodule.span_le]
    rintro _ rfl
    exact hc
  have hst := stepSub_mono hk 2 hle
  rw [d2_step_unit_eq hk hk11 c] at hst
  exact ⟨hst (Submodule.subset_span (by simp)), hst (Submodule.subset_span (by simp))⟩

lemma d2_pair_step {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (c : Fin k)
    {S : Submodule F (W k)} (hp : unitVec c + unitVec (pt hk c 0 1) ∈ S) :
    unitVec (pt hk c 4 0) ∈ stepSub hk 2 S ∧
    unitVec (pt hk c 4 1) ∈ stepSub hk 2 S ∧
    unitVec (pt hk c 4 5) ∈ stepSub hk 2 S ∧
    unitVec (pt hk c 4 6) ∈ stepSub hk 2 S := by
  have hz : mixFn hk 2 (unitVec c + unitVec (pt hk c 0 1)) =
      unitVec (pt hk c 2 0) + unitVec (pt hk c 2 1) + unitVec (pt hk c 2 2) +
      unitVec (pt hk c 2 3) + unitVec (pt hk c 2 4) + unitVec (pt hk c 2 5) := by
    rw [mixFn_add, mixFn_unit, mixFn_unit, pt_pt, pt_pt]
    have e1 : pt hk c (0 + 2) (1 + 0) = pt hk c 2 1 := rfl
    have e2' : unitVec c = unitVec (pt hk c 2 2) := congrArg unitVec (pt_self_cancel hk c 2).symm
    have e3 : pt hk c 0 1 = pt hk c 2 3 := (pt_cancel hk c 0 1 2).symm
    have e4 : pt hk c 0 2 = pt hk c 2 4 := (pt_cancel hk c 0 2 2).symm
    have e5 : pt hk c (0 + 0) (1 + 2) = pt hk c 2 5 := (pt_cancel hk c 0 3 2).symm
    rw [e1, e3, e4, e5, e2']
    abel
  have hval : ∀ a : ℕ, mixFn hk 2 (unitVec c + unitVec (pt hk c 0 1)) (pt hk c 4 a) =
      unitVec (pt hk c 4 2) (pt hk c 4 a) + unitVec (pt hk c 4 3) (pt hk c 4 a) +
      unitVec (pt hk c 4 4) (pt hk c 4 a) + unitVec (pt hk c 4 5) (pt hk c 4 a) +
      unitVec (pt hk c 4 6) (pt hk c 4 a) + unitVec (pt hk c 4 7) (pt hk c 4 a) := by
    intro a
    rw [hz]
    have c0 : pt hk c 2 0 = pt hk c 4 2 := (pt_cancel hk c 2 0 2).symm
    have c1 : pt hk c 2 1 = pt hk c 4 3 := (pt_cancel hk c 2 1 2).symm
    have c2 : pt hk c 2 2 = pt hk c 4 4 := (pt_cancel hk c 2 2 2).symm
    have c3 : pt hk c 2 3 = pt hk c 4 5 := (pt_cancel hk c 2 3 2).symm
    have c4 : pt hk c 2 4 = pt hk c 4 6 := (pt_cancel hk c 2 4 2).symm
    have c5 : pt hk c 2 5 = pt hk c 4 7 := (pt_cancel hk c 2 5 2).symm
    rw [c0, c1, c2, c3, c4, c5]
    rfl
  have hmem : ∀ q : Fin k,
      mixFn hk 2 (unitVec c + unitVec (pt hk c 0 1)) (pt hk q 1 0) • unitVec (pt hk q 2 0) +
      mixFn hk 2 (unitVec c + unitVec (pt hk c 0 1)) (pt hk q 0 1) • unitVec (pt hk q 1 0) ∈
        stepSub hk 2 S := by
    intro q
    rw [← polarFn_unit hk (by omega)]
    exact mem_stepSub_of_mem hk 2 hp (unitVec q)
  have h_out : ∀ a : ℕ, a ∈ ({0, 1, 8, 9} : Finset ℕ) →
      mixFn hk 2 (unitVec c + unitVec (pt hk c 0 1)) (pt hk c 4 a) = 0 := by
    intro a ha
    rw [hval]
    have ha_cases : a = 0 ∨ a = 1 ∨ a = 8 ∨ a = 9 := by simpa using ha
    have hn : ∀ b, 2 ≤ b → b ≤ 7 → pt hk c 4 b ≠ pt hk c 4 a := by
      intro b hb1 hb2
      rcases ha_cases with rfl | rfl | rfl | rfl <;>
        exact pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    simp only [unitVec, hn 2 (by omega) (by omega), hn 3 (by omega) (by omega),
      hn 4 (by omega) (by omega), hn 5 (by omega) (by omega),
      hn 6 (by omega) (by omega), hn 7 (by omega) (by omega)]
    simp
  have h_in : ∀ a : ℕ, 2 ≤ a → a ≤ 7 →
      mixFn hk 2 (unitVec c + unitVec (pt hk c 0 1)) (pt hk c 4 a) = 1 := by
    intro a ha1 ha2
    rw [hval]
    have hne : ∀ b1 b2, b1 ≠ b2 → b1 ≤ 9 → b2 ≤ 9 → pt hk c 4 b1 ≠ pt hk c 4 b2 := by
      intro b1 b2 h1 h2 h3
      exact pt_ne_of_lt hk c (by omega) (by omega) (by omega)
    have heq_u : ∀ b, b ≤ 9 →
        unitVec (pt hk c 4 b) (pt hk c 4 a) = if b = a then (1 : F) else 0 := by
      intro b hb
      by_cases hba : b = a
      · subst hba; simp [unitVec]
      · simp [unitVec, hba, hne b a hba hb (by omega)]
    rw [heq_u 2 (by omega), heq_u 3 (by omega), heq_u 4 (by omega),
      heq_u 5 (by omega), heq_u 6 (by omega), heq_u 7 (by omega)]
    interval_cases a <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hm := hmem (pt hk c 4 1)
    simp only [pt_pt] at hm
    have eL : pt hk c (4 + 1) (1 + 0) = pt hk c 4 0 := pt_cancel hk c 4 0 1
    have eR : pt hk c (4 + 0) (1 + 1) = pt hk c 4 2 := rfl
    have eO : pt hk c (4 + 1) (1 + 0) = pt hk c 4 0 := pt_cancel hk c 4 0 1
    rw [eL, eR, h_out 0 (by simp), h_in 2 (by omega) (by omega), zero_smul, one_smul, zero_add] at hm
    exact hm
  · have hm := hmem (pt hk c 4 2)
    simp only [pt_pt] at hm
    have eL : pt hk c (4 + 1) (2 + 0) = pt hk c 4 1 := pt_cancel hk c 4 1 1
    have eR : pt hk c (4 + 0) (2 + 1) = pt hk c 4 3 := rfl
    rw [eL, eR, h_out 1 (by simp), h_in 3 (by omega) (by omega), zero_smul, one_smul, zero_add] at hm
    exact hm
  · have hm := hmem (pt hk c 4 7)
    simp only [pt_pt] at hm
    have eL : pt hk c (4 + 1) (7 + 0) = pt hk c 4 6 := pt_cancel hk c 4 6 1
    have eR : pt hk c (4 + 0) (7 + 1) = pt hk c 4 8 := rfl
    have eO : pt hk c (4 + 2) (7 + 0) = pt hk c 4 5 := pt_cancel hk c 4 5 2
    rw [eL, eR, eO, h_in 6 (by omega) (by omega), h_out 8 (by simp), one_smul, zero_smul, add_zero] at hm
    exact hm
  · have hm := hmem (pt hk c 4 8)
    simp only [pt_pt] at hm
    have eL : pt hk c (4 + 1) (8 + 0) = pt hk c 4 7 := pt_cancel hk c 4 7 1
    have eR : pt hk c (4 + 0) (8 + 1) = pt hk c 4 9 := rfl
    have eO : pt hk c (4 + 2) (8 + 0) = pt hk c 4 6 := pt_cancel hk c 4 6 2
    rw [eL, eR, eO, h_in 7 (by omega) (by omega), h_out 9 (by simp), one_smul, zero_smul, add_zero] at hm
    exact hm

lemma d2_step2_units {k : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (start : Fin k) :
    ∀ b ≤ 10, unitVec (pt hk start 8 b) ∈
      (stepSub hk 2)^[2] (Submodule.span F ({unitVec start} : Set (W k))) := by
  set S1 := stepSub hk 2 (Submodule.span F ({unitVec start} : Set (W k)))
  have hS1_eq : S1 =
      Submodule.span F ({unitVec (pt hk start 4 0), unitVec (pt hk start 4 5),
        unitVec (pt hk start 4 1) + unitVec (pt hk start 4 2),
        unitVec (pt hk start 4 3) + unitVec (pt hk start 4 4)} : Set (W k)) :=
    d2_step_unit_eq hk hk11 start
  have hg0 : unitVec (pt hk start 4 0) ∈ S1 := by
    rw [hS1_eq]; exact Submodule.subset_span (by simp)
  have hg5 : unitVec (pt hk start 4 5) ∈ S1 := by
    rw [hS1_eq]; exact Submodule.subset_span (by simp)
  have hg12 : unitVec (pt hk start 4 1) + unitVec (pt hk (pt hk start 4 1) 0 1) ∈ S1 := by
    rw [pt_pt, hS1_eq]; exact Submodule.subset_span (by simp)
  have hg34 : unitVec (pt hk start 4 3) + unitVec (pt hk (pt hk start 4 3) 0 1) ∈ S1 := by
    rw [pt_pt, hS1_eq]; exact Submodule.subset_span (by simp)
  have h2_eq : (stepSub hk 2)^[2] (Submodule.span F ({unitVec start} : Set (W k))) =
      stepSub hk 2 S1 := rfl
  rw [h2_eq]
  have ⟨u0, u5⟩ := d2_step_extremes hk hk11 (pt hk start 4 0) hg0
  have ⟨_, u10⟩ := d2_step_extremes hk hk11 (pt hk start 4 5) hg5
  have ⟨u1, u2, u6, u7⟩ := d2_pair_step hk hk11 (pt hk start 4 1) hg12
  have ⟨u3, u4, u8, u9⟩ := d2_pair_step hk hk11 (pt hk start 4 3) hg34
  rw [pt_pt] at u0 u5 u10 u1 u2 u6 u7 u3 u4 u8 u9
  intro b hb
  interval_cases b
  · exact u0
  · exact u1
  · exact u2
  · exact u3
  · exact u4
  · exact u5
  · exact u6
  · exact u7
  · exact u8
  · exact u9
  · exact u10

lemma iter_units {k d : ℕ} (hk : 0 < k) (hk11 : 11 ≤ k) (hd : d = 1 ∨ d = 2) (start : Fin k) :
    ∀ h : ℕ, (d = 1 ∨ h ≠ 1) →
      ∀ b ≤ (2 * d + 1) * h,
        unitVec (pt hk start ((d + 2) * h) b) ∈
          (stepSub hk d)^[h] (Submodule.span F ({unitVec start} : Set (W k))) := by
  rcases hd with rfl | rfl
  · intro h _
    suffices ∀ m, ∀ b ≤ 3 * m,
        unitVec (pt hk start (3 * m) b) ∈
          (stepSub hk 1)^[m] (Submodule.span F ({unitVec start} : Set (W k))) from this h
    intro m
    induction m with
    | zero =>
      intro b hb
      have hb0 : b = 0 := by omega
      subst hb0
      simp only [Nat.mul_zero, pt_zero_zero, Function.iterate_zero, id_eq]
      exact Submodule.subset_span (Set.mem_singleton _)
    | succ m ih =>
      intro b hb
      rw [Function.iterate_succ_apply']
      have ha_exists : ∃ b0 a, b0 ≤ 3 * m ∧ a ≤ 3 ∧ b = b0 + a := by
        by_cases hle : b ≤ 3 * m
        · exact ⟨b, 0, hle, by omega, by omega⟩
        · exact ⟨3 * m, b - 3 * m, le_refl _, by omega, by omega⟩
      rcases ha_exists with ⟨b0, a, hb0, ha, rfl⟩
      have hu := d1_step_unit hk hk11 (pt hk start (3 * m) b0) _ (ih b0 hb0) a ha
      rw [pt_pt] at hu
      have hL : 3 * m + 3 = 3 * (m + 1) := by omega
      rwa [hL] at hu
  · intro h hh
    rcases hh with h1 | hne1
    · omega
    · cases h with
      | zero =>
        intro b hb
        have hb0 : b = 0 := by omega
        subst hb0
        simp only [Nat.mul_zero, pt_zero_zero, Function.iterate_zero, id_eq]
        exact Submodule.subset_span (Set.mem_singleton _)
      | succ h =>
        cases h with
        | zero => exact absurd rfl hne1
        | succ h =>
          clear hne1
          induction h with
          | zero =>
            intro b hb
            exact d2_step2_units hk hk11 start b hb
          | succ h ih =>
            intro b hb
            rw [Function.iterate_succ_apply']
            by_cases hle : b ≤ 5 * (h + 2)
            · have hu := (d2_step_extremes hk hk11 (pt hk start (4 * (h + 2)) b) (ih b hle)).1
              rw [pt_pt, Nat.add_zero] at hu
              have hL : 4 * (h + 2) + 4 = 4 * (h + 3) := by omega
              rwa [hL] at hu
            · have hb5 : b - 5 ≤ 5 * (h + 2) := by omega
              have hu := (d2_step_extremes hk hk11 (pt hk start (4 * (h + 2)) (b - 5))
                (ih (b - 5) hb5)).2
              rw [pt_pt] at hu
              have hL : 4 * (h + 2) + 4 = 4 * (h + 3) := by omega
              have hR : b - 5 + 5 = b := by omega
              rwa [hL, hR] at hu

theorem main :
    (∀ (k d : ℕ) (hk : 0 < k), 11 ≤ k → (d = 1 ∨ d = 2) →
      let F := ZMod 2
      let W := Fin k → F
      let ix := fun a : ℕ => (⟨a % k, Nat.mod_lt _ hk⟩ : Fin k)
      let mix := fun (v : W) (j : Fin k) =>
        v j + v (ix (j.val+d)) + v (ix (j.val+k-d % k))
      let polar := fun (z p : W) (j : Fin k) =>
        z (ix (j.val+1))*p (ix (j.val+2)) + z (ix (j.val+2))*p (ix (j.val+1))
      let step := fun S : Submodule F W =>
        Submodule.span F {w : W | ∃ v ∈ S, ∃ p : W, w = polar (mix v) p}
      ∀ start : Fin k,
        let e := fun (i j : Fin k) => if i = j then (1:F) else 0
        let seed := Submodule.span F ({e start} : Set W)
        let loc := fun (left offset : ℕ) => ix (start.val+k-left % k+offset)
        (∀ h : ℕ, (d = 1 ∨ h ≠ 1) → ∀ w : W,
          w ∈ (step^[h]) seed ↔ ∀ j : Fin k,
            (¬ ∃ b : ℕ, b ≤ (2*d+1)*h ∧ loc ((d+2)*h) b = j) → w j = 0) ∧
        (d = 2 → step seed =
          Submodule.span F ({e (loc 4 0), e (loc 4 5),
            e (loc 4 1) + e (loc 4 2), e (loc 4 3) + e (loc 4 4)} : Set W))) := by
  intro k d hk hk11 hd
  dsimp only
  intro start
  constructor
  · intro h hh
    refine span_eq_supp _ (fun j => ∃ b ≤ (2 * d + 1) * h, pt hk start ((d + 2) * h) b = j)
      (iter_locality hk d start h) ?_
    rintro j ⟨b, hb, rfl⟩
    exact iter_units hk hk11 hd start h hh b hb
  · intro hd2
    subst hd2
    exact d2_step_unit_eq hk hk11 start

end PEqualNP.Outside.L_lib_663_aux

theorem PEqualNP.Outside.L_lib_663 : (∀ (k d : ℕ) (hk : 0 < k), 11 ≤ k → (d = 1 ∨ d = 2) →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun a : ℕ => (⟨a % k, Nat.mod_lt _ hk⟩ : Fin k)
  let mix := fun (v : W) (j : Fin k) =>
    v j + v (ix (j.val+d)) + v (ix (j.val+k-d % k))
  let polar := fun (z p : W) (j : Fin k) =>
    z (ix (j.val+1))*p (ix (j.val+2)) + z (ix (j.val+2))*p (ix (j.val+1))
  let step := fun S : Submodule F W =>
    Submodule.span F {w : W | ∃ v ∈ S, ∃ p : W, w = polar (mix v) p}
  ∀ start : Fin k,
    let e := fun (i j : Fin k) => if i = j then (1:F) else 0
    let seed := Submodule.span F ({e start} : Set W)
    let loc := fun (left offset : ℕ) => ix (start.val+k-left % k+offset)
    (∀ h : ℕ, (d = 1 ∨ h ≠ 1) → ∀ w : W,
      w ∈ (step^[h]) seed ↔ ∀ j : Fin k,
        (¬ ∃ b : ℕ, b ≤ (2*d+1)*h ∧ loc ((d+2)*h) b = j) → w j = 0) ∧
    (d = 2 → step seed =
      Submodule.span F ({e (loc 4 0), e (loc 4 5),
        e (loc 4 1) + e (loc 4 2), e (loc 4 3) + e (loc 4 4)} : Set W))) := by
  exact PEqualNP.Outside.L_lib_663_aux.main
