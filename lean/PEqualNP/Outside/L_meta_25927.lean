import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25927

open Finset

variable {k : ℕ} (hk : 0 < k)

def ix (t : ℕ) : Fin k := ⟨t % k, Nat.mod_lt t hk⟩

lemma ix_val (t : ℕ) : (ix hk t).val = t % k := rfl

lemma ix_add_mul (t m : ℕ) : ix hk (t + m * k) = ix hk t := by
  simp [ix, Nat.add_mul_mod_self_right]

lemma ix_mod (t : ℕ) : ix hk (t % k) = ix hk t := by
  simp [ix]

lemma ix_val' (j : Fin k) : ix hk j.val = j := by
  simp [ix, Nat.mod_eq_of_lt j.isLt]

lemma ix_add_k (t : ℕ) : ix hk (t + k) = ix hk t := by
  simpa using ix_add_mul hk t 1

def mix (gap : ℕ) (x : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  x j + x (ix hk (j.val + gap)) + x (ix hk (j.val + k - gap % k))

lemma mix_linear (gap : ℕ) (x y : Fin k → ZMod 2) :
    mix hk gap (x + y) = mix hk gap x + mix hk gap y := by
  ext j
  simp [mix, Pi.add_apply]
  ring

lemma mix_zero (gap : ℕ) : mix hk gap (0 : Fin k → ZMod 2) = 0 := by
  ext j
  simp [mix]

lemma mix_smul (gap : ℕ) (c : ZMod 2) (x : Fin k → ZMod 2) :
    mix hk gap (c • x) = c • mix hk gap x := by
  ext j
  simp [mix, Pi.smul_apply, smul_eq_mul]
  ring

def mixLM (gap : ℕ) : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun := mix hk gap
  map_add' := mix_linear hk gap
  map_smul' := mix_smul hk gap

lemma gcd_dvd_k (gap : ℕ) : Nat.gcd k gap ∣ k := Nat.gcd_dvd_left k gap

lemma three_dvd_k_div_gcd {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    3 ∣ k / Nat.gcd k gap := by
  rcases hgap with rfl | rfl
  · simpa [Nat.gcd_one_right] using h3
  · have hle : Nat.gcd k 2 ≤ 2 :=
      Nat.le_of_dvd (by decide : (0 : ℕ) < 2) (Nat.gcd_dvd_right k 2)
    have hpos : 0 < Nat.gcd k 2 := Nat.gcd_pos_of_pos_right k (by decide)
    have hg : Nat.gcd k 2 = 1 ∨ Nat.gcd k 2 = 2 := by
      omega
    rcases hg with hg | hg
    · simpa [hg] using h3
    · have h2 : 2 ∣ k := by
        have := Nat.gcd_dvd_left k 2
        simpa [hg] using this
      have hlcm : Nat.lcm 2 3 = 6 := by decide
      have h6 : 6 ∣ k := by
        rw [← hlcm]
        exact Nat.lcm_dvd h2 h3
      obtain ⟨m, hm⟩ := h6
      have hkfact : k = 2 * (3 * m) := by
        rw [hm]; ring
      have hdiv : k / 2 = 3 * m := by
        rw [hkfact, Nat.mul_div_cancel_left _ (by decide : (0 : ℕ) < 2)]
      have : 3 ∣ k / 2 := ⟨m, hdiv⟩
      simpa [hg] using this

def residue (gap : ℕ) (j : Fin k) : ℕ := j.val % Nat.gcd k gap

def syndrome (gap : ℕ) (x : Fin k → ZMod 2) (a : Fin (Nat.gcd k gap) × Fin 2) : ZMod 2 :=
  ∑ t ∈ Finset.range (k / Nat.gcd k gap),
    (if t % 3 = a.2.val ∨ t % 3 = 2 then x (ix hk (a.1.val + t * gap)) else 0)

lemma syndrome_add (gap : ℕ) (x y : Fin k → ZMod 2) (a : Fin (Nat.gcd k gap) × Fin 2) :
    syndrome hk gap (x + y) a = syndrome hk gap x a + syndrome hk gap y a := by
  simp only [syndrome, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro t ht
  split_ifs <;> ring

lemma syndrome_zero (gap : ℕ) (a : Fin (Nat.gcd k gap) × Fin 2) :
    syndrome hk gap (0 : Fin k → ZMod 2) a = 0 := by
  simp [syndrome]

lemma syndrome_smul (gap : ℕ) (c : ZMod 2) (x : Fin k → ZMod 2)
    (a : Fin (Nat.gcd k gap) × Fin 2) :
    syndrome hk gap (c • x) a = c * syndrome hk gap x a := by
  simp only [syndrome, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t ht
  split_ifs <;> ring

def syndromeLM (gap : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin (Nat.gcd k gap) × Fin 2 → ZMod 2) where
  toFun x := syndrome hk gap x
  map_add' x y := by
    ext a
    exact syndrome_add hk gap x y a
  map_smul' c x := by
    ext a
    simpa [RingHom.id, Pi.smul_apply, smul_eq_mul] using syndrome_smul hk gap c x a

def chi (x : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  x j + (1 + x (ix hk (j.val + 1))) * x (ix hk (j.val + 2))

def out (x d : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  chi hk (x + d) j - chi hk x j

lemma out_formula (x d : Fin k → ZMod 2) (j : Fin k) :
    out hk x d j =
      d j + d (ix hk (j.val + 2)) +
        x (ix hk (j.val + 1)) * d (ix hk (j.val + 2)) +
        d (ix hk (j.val + 1)) * x (ix hk (j.val + 2)) +
        d (ix hk (j.val + 1)) * d (ix hk (j.val + 2)) := by
  simp only [out, chi, Pi.add_apply]
  ring

lemma out_diff (x a d : Fin k → ZMod 2) (j : Fin k) :
    out hk x d j + out hk a d j =
      (x (ix hk (j.val + 1)) + a (ix hk (j.val + 1))) * d (ix hk (j.val + 2)) +
      d (ix hk (j.val + 1)) * (x (ix hk (j.val + 2)) + a (ix hk (j.val + 2))) := by
  have hx := out_formula hk x d j
  have ha := out_formula hk a d j

  rw [hx, ha]
  ring_nf
  have : (2 : ZMod 2) = 0 := by decide
  simp [this]

lemma out_eq_iff (x a d : Fin k → ZMod 2) (j : Fin k) :
    out hk x d j = out hk a d j ↔
      (x (ix hk (j.val + 1)) + a (ix hk (j.val + 1))) * d (ix hk (j.val + 2)) +
        d (ix hk (j.val + 1)) * (x (ix hk (j.val + 2)) + a (ix hk (j.val + 2))) = 0 := by
  have h := out_diff hk x a d j
  constructor
  · intro heq

    have : out hk x d j + out hk a d j = 0 := by
      rw [heq, add_comm, CharTwo.add_self_eq_zero]
    exact h ▸ this
  · intro hz
    have : out hk x d j + out hk a d j = 0 := h.trans hz

    have := congrArg (fun z => z + out hk a d j) this
    simpa [add_assoc, CharTwo.add_self_eq_zero] using this

lemma eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma eq_one_of_ne_zero (x : ZMod 2) (h : x ≠ 0) : x = 1 :=
  (eq_zero_or_one x).resolve_left h

lemma exists_coord_one {s : ℕ} {c : Fin s → ZMod 2} (h : c ≠ 0) :
    ∃ p, c p = 1 := by
  have : ∃ p, c p ≠ 0 := by
    contrapose! h
    ext p
    exact h p
  obtain ⟨p, hp⟩ := this
  exact ⟨p, eq_one_of_ne_zero _ hp⟩

lemma constraint_same {s : ℕ} (delta : Fin k → ZMod 2)
    (D : Fin s → Fin k → ZMod 2) (u v : Fin k)
    (hsame : (fun p : Fin s => D p u) = fun p => D p v)
    (hnez : (fun p : Fin s => D p u) ≠ 0) :
    (∀ p : Fin s, delta u * D p v + D p u * delta v = 0) ↔ delta u = delta v := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := exists_coord_one hnez
    have hv : D p v = D p u := (congrFun hsame p).symm
    have := h p
    rw [hv, hp] at this
    have : delta u + delta v = 0 := by simpa using this
    exact CharTwo.add_eq_zero.mp this
  · intro hde p
    have hv : D p v = D p u := (congrFun hsame p).symm
    rw [hde, hv, mul_comm (delta v)]
    exact CharTwo.add_self_eq_zero _

lemma constraint_pin_right {s : ℕ} (delta : Fin k → ZMod 2)
    (D : Fin s → Fin k → ZMod 2) (u v : Fin k)
    (hdiff : (fun p : Fin s => D p u) ≠ (fun p => D p v))
    (hu : (fun p : Fin s => D p u) ≠ 0)
    (h : ∀ p : Fin s, delta u * D p v + D p u * delta v = 0) :
    delta v = 0 := by
  obtain ⟨p, hp⟩ := exists_coord_one hu
  have hp' := h p
  rw [hp] at hp'
  have hrel : delta v = delta u * D p v := by
    have : delta u * D p v + delta v = 0 := by simpa using hp'
    exact (CharTwo.add_eq_zero.mp this).symm
  rcases eq_zero_or_one (delta u) with hu0 | hu1
  · simp [hrel, hu0]
  · have hcoord : ∀ q, D q v = D q u * D p v := by
      intro q
      have hq := h q
      have : D q v + D q u * delta v = 0 := by

        rw [hu1] at hq
        convert hq using 1
        ring
      have : D q v = D q u * delta v := CharTwo.add_eq_zero.mp this
      simpa [hrel, hu1] using this
    rcases eq_zero_or_one (D p v) with hv0 | hv1
    · simp [hrel, hu1, hv0]
    · have : (fun q : Fin s => D q u) = fun q => D q v := by
        ext q
        have := hcoord q
        simpa [hv1] using this.symm
      exact (hdiff this).elim

lemma constraint_pin_left {s : ℕ} (delta : Fin k → ZMod 2)
    (D : Fin s → Fin k → ZMod 2) (u v : Fin k)
    (hdiff : (fun p : Fin s => D p u) ≠ (fun p => D p v))
    (hv : (fun p : Fin s => D p v) ≠ 0)
    (h : ∀ p : Fin s, delta u * D p v + D p u * delta v = 0) :
    delta u = 0 := by

  have h' : ∀ p, delta v * D p u + D p v * delta u = 0 := by
    intro p
    have := h p
    convert this using 1
    ring
  exact constraint_pin_right delta D v u (Ne.symm hdiff) hv h'

lemma ix_add_gap (gap t : ℕ) :
    ix hk (t + gap) = ix hk ((ix hk t).val + gap) := by
  simp [ix, Nat.add_mod]

include hk

lemma ix_modEq {a b : ℕ} (h : a ≡ b [MOD k]) : ix hk a = ix hk b := by
  simp [ix]
  exact h

lemma ix_cast_eq {a b : ℕ} (h : (a : ZMod k) = (b : ZMod k)) : ix hk a = ix hk b := by
  have : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk⟩
  exact ix_modEq hk ((ZMod.natCast_eq_natCast_iff a b k).mp h)

lemma gcd_pos (gap : ℕ) : 0 < Nat.gcd k gap :=
  Nat.gcd_pos_of_pos_left gap hk

lemma orbit_len_pos (gap : ℕ) : 0 < k / Nat.gcd k gap :=
  Nat.div_pos (Nat.le_of_dvd hk (Nat.gcd_dvd_left k gap)) (gcd_pos hk gap)

omit hk in
lemma orbit_len_mul_gap (gap : ℕ) :
    (k / Nat.gcd k gap) * gap = k * (gap / Nat.gcd k gap) := by
  set g := Nat.gcd k gap
  have hkdiv : g * (k / g) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k gap)
  have hgapdiv : g * (gap / g) = gap := Nat.mul_div_cancel' (Nat.gcd_dvd_right k gap)
  calc
    (k / g) * gap = (k / g) * (g * (gap / g)) := by rw [hgapdiv]
    _ = (k / g * g) * (gap / g) := by ring
    _ = (g * (k / g)) * (gap / g) := by ring
    _ = k * (gap / g) := by rw [hkdiv]

omit hk in
lemma n_mul_gap_cast (gap : ℕ) :
    ((k / Nat.gcd k gap * gap : ℕ) : ZMod k) = 0 := by
  rw [orbit_len_mul_gap gap, Nat.cast_mul, ZMod.natCast_self, zero_mul]

lemma ix_orbit_period (r gap : ℕ) :
    ix hk (r + (k / Nat.gcd k gap) * gap) = ix hk r := by
  apply ix_cast_eq hk
  simp [n_mul_gap_cast gap]

lemma ix_succ_orbit (r gap t : ℕ) :
    ix hk ((ix hk (r + t * gap)).val + gap) = ix hk (r + (t + 1) * gap) := by
  apply ix_cast_eq hk
  simp [ix_val, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  ring

lemma gap_lt_of_three {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    gap < k := by
  have : 3 ≤ k := Nat.le_of_dvd hk h3
  rcases hgap with rfl | rfl <;> omega

lemma gap_mod_eq {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    gap % k = gap :=
  Nat.mod_eq_of_lt (gap_lt_of_three hk hgap h3)

lemma gap_div_gcd_pos {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) :
    1 ≤ gap / Nat.gcd k gap := by
  have hg : Nat.gcd k gap ∣ gap := Nat.gcd_dvd_right k gap
  have hgp : 0 < gap := by rcases hgap with rfl | rfl <;> decide
  exact Nat.div_pos (Nat.le_of_dvd hgp hg) (gcd_pos hk gap)

omit hk in
lemma mod_n_mul_gap (gap t : ℕ) :
    (((t % (k / Nat.gcd k gap)) : ℕ) : ZMod k) * (gap : ZMod k) =
      (t : ZMod k) * gap := by
  set g := Nat.gcd k gap
  set n := k / g
  have hdiv : n * (t / n) + t % n = t := Nat.div_add_mod t n
  have hteq : (t : ZMod k) = ((n * (t / n) + t % n : ℕ) : ZMod k) := by
    rw [hdiv]
  rw [hteq, Nat.cast_add, Nat.cast_mul, add_mul]
  have hng : (n : ZMod k) * gap = 0 := by
    rw [← Nat.cast_mul]
    dsimp [n, g]
    exact n_mul_gap_cast gap
  have : (n : ZMod k) * (t / n : ℕ) * gap = 0 := by
    calc
      (n : ZMod k) * (t / n : ℕ) * gap = (t / n : ℕ) * ((n : ZMod k) * gap) := by ring
      _ = (t / n : ℕ) * 0 := by rw [hng]
      _ = 0 := by ring
  simp [this]

lemma ix_orbit_reduce (r gap t : ℕ) :
    ix hk (r + t * gap) = ix hk (r + (t % (k / Nat.gcd k gap)) * gap) := by
  apply ix_cast_eq hk
  have ht : (t : ZMod k) * gap = (((t % (k / Nat.gcd k gap)) : ℕ) : ZMod k) * gap :=
    (mod_n_mul_gap (k := k) gap t).symm
  simp [Nat.cast_add, Nat.cast_mul, ht]

lemma ix_pred_index (x gap : ℕ) :
    ix hk ((ix hk x).val + k - gap % k) = ix hk (x + k - gap % k) := by
  apply ix_cast_eq hk
  have hle1 : gap % k ≤ (ix hk x).val + k := by
    have : gap % k < k := Nat.mod_lt gap hk
    have : (ix hk x).val < k := (ix hk x).isLt
    omega
  have hle2 : gap % k ≤ x + k := by
    have : gap % k < k := Nat.mod_lt gap hk
    omega
  have hle1' : gap % k ≤ x % k + k := by
    have := hle1
    rw [ix_val] at this
    exact this
  rw [ix_val, Nat.cast_sub hle1', Nat.cast_sub hle2, Nat.cast_add, Nat.cast_add,
    ZMod.natCast_self, ZMod.natCast_mod]

lemma ix_pred_orbit {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (r t : ℕ) :
    ix hk ((ix hk (r + t * gap)).val + k - gap % k) =
      ix hk (r + ((t + k / Nat.gcd k gap - 1) % (k / Nat.gcd k gap)) * gap) := by
  rw [ix_pred_index hk, gap_mod_eq hk hgap h3]
  apply ix_cast_eq hk
  set g := Nat.gcd k gap
  set n := k / g
  have hn : 0 < n := orbit_len_pos hk gap
  have hgaplt : gap < k := gap_lt_of_three hk hgap h3
  have hle : gap ≤ r + t * gap + k := by omega
  have hle' : 1 ≤ n := hn

  have hcastn : (n : ZMod k) * gap = 0 := by
    rw [← Nat.cast_mul]
    dsimp [n, g]
    exact n_mul_gap_cast gap
  have hle_sub : gap ≤ r + t * gap + k := hle
  rw [Nat.cast_sub hle_sub, Nat.cast_add, Nat.cast_add, ZMod.natCast_self, add_zero]
  have hmod : (((t + n - 1) % n : ℕ) : ZMod k) * gap =
      ((t + n - 1 : ℕ) : ZMod k) * gap :=
    mod_n_mul_gap (k := k) gap (t + n - 1)
  have hn1 : 1 ≤ t + n := by omega
  have hrhs : ((r + (t + n - 1) % n * gap : ℕ) : ZMod k) =
      (r : ZMod k) + (((t + n - 1) % n : ℕ) : ZMod k) * gap := by
    simp [Nat.cast_add, Nat.cast_mul]
  rw [hrhs, hmod, Nat.cast_sub hn1, Nat.cast_add, Nat.cast_one]
  simp only [Nat.cast_mul]
  rw [sub_mul, add_mul, hcastn]
  ring

lemma mix_at_orbit {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (x : Fin k → ZMod 2) (r t : ℕ) :
    mix hk gap x (ix hk (r + t * gap)) =
      x (ix hk (r + t * gap)) +
      x (ix hk (r + ((t + 1) % (k / Nat.gcd k gap)) * gap)) +
      x (ix hk (r + ((t + k / Nat.gcd k gap - 1) % (k / Nat.gcd k gap)) * gap)) := by
  have hs : ix hk ((ix hk (r + t * gap)).val + gap) =
      ix hk (r + ((t + 1) % (k / Nat.gcd k gap)) * gap) := by
    rw [ix_succ_orbit hk, ix_orbit_reduce hk]
  have hp := ix_pred_orbit hk hgap h3 r t
  simp only [mix]
  rw [hs, hp]

omit hk in
lemma syn_mask_coeff (b r : ℕ) (hb : b < 2) :
    (if r % 3 = b ∨ r % 3 = 2 then (1 : ZMod 2) else 0) +
      (if (r + 2) % 3 = b ∨ (r + 2) % 3 = 2 then 1 else 0) +
      (if (r + 1) % 3 = b ∨ (r + 1) % 3 = 2 then 1 else 0) = 0 := by
  have hr : r % 3 < 3 := Nat.mod_lt r (by decide)
  have hb' : b = 0 ∨ b = 1 := by omega
  have hmod (s : ℕ) : (r + s) % 3 = (r % 3 + s % 3) % 3 := Nat.add_mod r s 3
  rcases hb' with rfl | rfl
  · interval_cases r % 3 <;> simp [hmod, CharTwo.add_self_eq_zero]
  · interval_cases r % 3 <;> simp [hmod, CharTwo.add_self_eq_zero]

omit hk in
lemma pred_succ_mod {n t : ℕ} (hn : 0 < n) (ht : t < n) :
    ((t + 1) % n + n - 1) % n = t := by
  have hle : 1 ≤ n := hn
  by_cases h : t + 1 = n
  · have hmod : (t + 1) % n = 0 := by rw [h, Nat.mod_self]
    have ht' : t = n - 1 := by omega
    rw [hmod, ht']
    have : 0 + n - 1 = n - 1 := by omega
    rw [this]
    exact Nat.mod_eq_of_lt (Nat.sub_lt hn (by decide))
  · have hlt : t + 1 < n := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt ht) h
    have hmod : (t + 1) % n = t + 1 := Nat.mod_eq_of_lt hlt
    rw [hmod]
    have : t + 1 + n - 1 = t + n := by omega
    rw [this, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt ht]

omit hk in
lemma succ_pred_mod {n t : ℕ} (hn : 0 < n) (ht : t < n) :
    ((t + n - 1) % n + 1) % n = t := by
  have hle : 1 ≤ n := hn
  by_cases ht0 : t = 0
  · subst t
    have hmod : (n - 1) % n = n - 1 :=
      Nat.mod_eq_of_lt (Nat.sub_lt hn (by decide))
    have hsum : n - 1 + 1 = n := Nat.sub_add_cancel hle
    have : (0 + n - 1) % n = n - 1 := by
      have : 0 + n - 1 = n - 1 := by omega
      rw [this, hmod]
    rw [this, hsum, Nat.mod_self]
  · have htpos : 1 ≤ t := Nat.pos_of_ne_zero ht0
    have : t + n - 1 = t - 1 + n := by omega
    rw [this]
    have ht1 : t - 1 < n := by omega
    have hmod : (t - 1 + n) % n = t - 1 := by
      rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt ht1]
    rw [hmod, Nat.sub_add_cancel htpos, Nat.mod_eq_of_lt ht]

omit hk in
lemma add_one_mod_mod_three {t n : ℕ} (h3 : 3 ∣ n) :
    ((t + 1) % n) % 3 = (t + 1) % 3 :=
  Nat.mod_mod_of_dvd (t + 1) h3

omit hk in
lemma pred_mod_mod_three {t n : ℕ} (hn : 0 < n) (h3 : 3 ∣ n) :
    ((t + n - 1) % n) % 3 = (t + 2) % 3 := by
  have hle : 1 ≤ n := hn
  have hdecomp : t + n - 1 = t + (n - 1) := by omega
  rw [hdecomp, Nat.mod_mod_of_dvd _ h3]
  have hn0 : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
  have hn2 : (n - 1) % 3 = 2 := by omega
  rw [Nat.add_mod, hn2]
  exact (Nat.add_mod t 2 3).symm

omit hk in
lemma ite_eq_mask_mul (b t : ℕ) (y : ZMod 2) :
    (if t % 3 = b ∨ t % 3 = 2 then y else (0 : ZMod 2)) =
      (if t % 3 = b ∨ t % 3 = 2 then (1 : ZMod 2) else 0) * y := by
  split_ifs <;> ring

lemma syndrome_mix_zero {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (x : Fin k → ZMod 2) (a : Fin (Nat.gcd k gap) × Fin 2) :
    syndrome hk gap (mix hk gap x) a = 0 := by
  let n := k / Nat.gcd k gap
  have hn : 0 < n := orbit_len_pos hk gap
  have h3n : 3 ∣ n := three_dvd_k_div_gcd hgap h3
  let b := a.2.val
  have hb : b < 2 := a.2.isLt
  let mask : ℕ → ZMod 2 := fun t => if t % 3 = b ∨ t % 3 = 2 then 1 else 0
  let f : ℕ → ZMod 2 := fun t => x (ix hk (a.1.val + t * gap))
  have hmix : ∀ t, mix hk gap x (ix hk (a.1.val + t * gap)) =
      f t + f ((t + 1) % n) + f ((t + n - 1) % n) := by
    intro t
    simpa [f, n] using mix_at_orbit hk hgap h3 x a.1.val t
  have hsum :
      syndrome hk gap (mix hk gap x) a =
        ∑ t ∈ range n, mask t * (f t + f ((t + 1) % n) + f ((t + n - 1) % n)) := by
    simp only [syndrome, mask, f, n, b]
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [hmix t]
    exact ite_eq_mask_mul a.2.val t _
  rw [hsum]
  have hdistrib :
      ∑ t ∈ range n, mask t * (f t + f ((t + 1) % n) + f ((t + n - 1) % n)) =
        (∑ t ∈ range n, mask t * f t) +
          (∑ t ∈ range n, mask t * f ((t + 1) % n)) +
            (∑ t ∈ range n, mask t * f ((t + n - 1) % n)) := by
    simp only [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hdistrib]
  have hsucc :
      ∑ t ∈ range n, mask t * f ((t + 1) % n) =
        ∑ t ∈ range n, mask ((t + n - 1) % n) * f t := by
    refine Finset.sum_nbij' (fun t => (t + 1) % n) (fun t => (t + n - 1) % n) ?_ ?_ ?_ ?_ ?_
    · intro t ht; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
    · intro t ht; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
    · intro t ht; exact pred_succ_mod hn (Finset.mem_range.mp ht)
    · intro t ht; exact succ_pred_mod hn (Finset.mem_range.mp ht)
    · intro t ht
      have ht' := Finset.mem_range.mp ht
      rw [pred_succ_mod hn ht']
  have hpred :
      ∑ t ∈ range n, mask t * f ((t + n - 1) % n) =
        ∑ t ∈ range n, mask ((t + 1) % n) * f t := by
    refine Finset.sum_nbij' (fun t => (t + n - 1) % n) (fun t => (t + 1) % n) ?_ ?_ ?_ ?_ ?_
    · intro t ht; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
    · intro t ht; exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
    · intro t ht; exact succ_pred_mod hn (Finset.mem_range.mp ht)
    · intro t ht; exact pred_succ_mod hn (Finset.mem_range.mp ht)
    · intro t ht
      have ht' := Finset.mem_range.mp ht
      rw [succ_pred_mod hn ht']
  rw [hsucc, hpred, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hcoeff : ∀ t ∈ range n, mask t + mask ((t + n - 1) % n) + mask ((t + 1) % n) = 0 := by
    intro t ht
    have h1 : mask ((t + 1) % n) =
        if (t + 1) % 3 = b ∨ (t + 1) % 3 = 2 then (1 : ZMod 2) else 0 := by
      simp only [mask]
      simp [add_one_mod_mod_three h3n]
    have h2 : mask ((t + n - 1) % n) =
        if (t + 2) % 3 = b ∨ (t + 2) % 3 = 2 then (1 : ZMod 2) else 0 := by
      simp only [mask]
      simp [pred_mod_mod_three hn h3n]
    simp only [mask, h1, h2]
    exact syn_mask_coeff b t hb
  have : ∑ t ∈ range n,
      (mask t + mask ((t + n - 1) % n) + mask ((t + 1) % n)) * f t = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t ht
    rw [hcoeff t ht, zero_mul]
  convert this using 1
  refine Finset.sum_congr rfl ?_
  intro t ht
  ring

lemma mix_mem_ker_syndrome {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (x : Fin k → ZMod 2) :
    syndromeLM hk gap (mixLM hk gap x) = 0 := by
  ext a
  exact syndrome_mix_zero hk hgap h3 x a

lemma orbit_len_ge_three {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    3 ≤ k / Nat.gcd k gap :=
  Nat.le_of_dvd (orbit_len_pos hk gap) (three_dvd_k_div_gcd hgap h3)

lemma orbit_eq {gap : ℕ} {r₁ r₂ t₁ t₂ : ℕ}
    (hr₁ : r₁ < Nat.gcd k gap) (hr₂ : r₂ < Nat.gcd k gap)
    (ht₁ : t₁ < k / Nat.gcd k gap) (ht₂ : t₂ < k / Nat.gcd k gap)
    (h : ix hk (r₁ + t₁ * gap) = ix hk (r₂ + t₂ * gap)) :
    r₁ = r₂ ∧ t₁ = t₂ := by
  set g := Nat.gcd k gap
  set n := k / g
  have hgpos : 0 < g := gcd_pos hk gap
  have hval : (r₁ + t₁ * gap) % k = (r₂ + t₂ * gap) % k := by
    simpa [ix] using congrArg Fin.val h
  have hvalg : (r₁ + t₁ * gap) % g = (r₂ + t₂ * gap) % g := by
    rw [← Nat.mod_mod_of_dvd (r₁ + t₁ * gap) (Nat.gcd_dvd_left k gap),
        ← Nat.mod_mod_of_dvd (r₂ + t₂ * gap) (Nat.gcd_dvd_left k gap), hval]
  have hr1 : (r₁ + t₁ * gap) % g = r₁ := by
    have hgap0 : gap % g = 0 := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right k gap)
    rw [Nat.add_mod, Nat.mul_mod, hgap0, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
      Nat.mod_mod, Nat.mod_eq_of_lt hr₁]
  have hr2 : (r₂ + t₂ * gap) % g = r₂ := by
    have hgap0 : gap % g = 0 := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right k gap)
    rw [Nat.add_mod, Nat.mul_mod, hgap0, Nat.mul_zero, Nat.zero_mod, Nat.add_zero,
      Nat.mod_mod, Nat.mod_eq_of_lt hr₂]
  have hr : r₁ = r₂ := by
    rw [hr1, hr2] at hvalg
    exact hvalg
  refine ⟨hr, ?_⟩
  subst hr
  have htg : t₁ * gap ≡ t₂ * gap [MOD k] := by
    have : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk⟩
    have hZ : ((r₁ + t₁ * gap : ℕ) : ZMod k) = (r₁ + t₂ * gap : ℕ) :=
      (ZMod.natCast_eq_natCast_iff _ _ k).mpr hval
    simp only [Nat.cast_add] at hZ
    have hZ' : ((t₁ * gap : ℕ) : ZMod k) = (t₂ * gap : ℕ) := add_left_cancel hZ
    exact (ZMod.natCast_eq_natCast_iff _ _ k).mp hZ'
  have hgs : g * (gap / g) = gap := Nat.mul_div_cancel' (Nat.gcd_dvd_right k gap)
  have hkn : g * n = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k gap)
  have hcong : t₁ * (gap / g) ≡ t₂ * (gap / g) [MOD n] := by
    have h1 : t₁ * gap = g * (t₁ * (gap / g)) := by
      conv_lhs => rw [← hgs]
      rw [← mul_assoc, mul_comm t₁ g, mul_assoc]
    have h2 : t₂ * gap = g * (t₂ * (gap / g)) := by
      conv_lhs => rw [← hgs]
      rw [← mul_assoc, mul_comm t₂ g, mul_assoc]
    have : (g * (t₁ * (gap / g))) % (g * n) = (g * (t₂ * (gap / g))) % (g * n) := by
      have htg' : (t₁ * gap) % k = (t₂ * gap) % k := htg
      simpa [h1, h2, hkn] using htg'
    rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at this
    exact Nat.mul_left_cancel hgpos this
  have hcop : Nat.Coprime n (gap / g) := by
    simpa [n, g] using Nat.coprime_div_gcd_div_gcd hgpos
  have htt : t₁ ≡ t₂ [MOD n] := Nat.ModEq.cancel_right_of_coprime hcop.gcd_eq_one hcong
  have htt' : t₁ % n = t₂ % n := htt
  rw [Nat.mod_eq_of_lt ht₁, Nat.mod_eq_of_lt ht₂] at htt'
  exact htt'

def pulse (gap : ℕ) (r t0 : ℕ) : Fin k → ZMod 2 :=
  fun j => if j = ix hk (r + t0 * gap) then 1 else 0

lemma syndrome_pulse {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (r : Fin (Nat.gcd k gap)) (t0 : ℕ) (ht0 : t0 < k / Nat.gcd k gap)
    (a : Fin (Nat.gcd k gap) × Fin 2) :
    syndrome hk gap (pulse hk gap r.val t0) a =
      if a.1 = r ∧ (t0 % 3 = a.2.val ∨ t0 % 3 = 2) then (1 : ZMod 2) else 0 := by
  let n := k / Nat.gcd k gap
  simp only [syndrome, pulse]
  have hterm : ∀ t ∈ Finset.range n,
      (if t % 3 = a.2.val ∨ t % 3 = 2 then
        (if ix hk (a.1.val + t * gap) = ix hk (r.val + t0 * gap) then (1 : ZMod 2) else 0)
      else 0) =
      if a.1 = r ∧ t = t0 ∧ (t0 % 3 = a.2.val ∨ t0 % 3 = 2) then (1 : ZMod 2) else 0 := by
    intro t ht
    have htlt : t < n := Finset.mem_range.mp ht
    by_cases hmask : t % 3 = a.2.val ∨ t % 3 = 2
    · by_cases hix : ix hk (a.1.val + t * gap) = ix hk (r.val + t0 * gap)
      · have heq := orbit_eq hk a.1.isLt r.isLt htlt ht0 hix
        have har : a.1 = r := Fin.ext heq.1
        have htt : t = t0 := heq.2
        simp [hmask, hix, har, htt]
      · have hnot : ¬ (a.1 = r ∧ t = t0) := by
          rintro ⟨h1, h2⟩
          apply hix
          rw [h1, h2]
        split_ifs with hcond
        · exact (hnot ⟨hcond.1, hcond.2.1⟩).elim
        · rfl
    · have hnot : ¬ (a.1 = r ∧ t = t0 ∧ (t0 % 3 = a.2.val ∨ t0 % 3 = 2)) := by
        rintro ⟨_, htt, hm⟩
        apply hmask
        simpa [htt] using hm
      simp [hmask, hnot]
  refine (Finset.sum_congr rfl hterm).trans ?_
  by_cases hr : a.1 = r
  · by_cases hm : t0 % 3 = a.2.val ∨ t0 % 3 = 2
    · simp only [hr, hm, true_and, and_true]
      rw [Finset.sum_ite_eq']
      simp [Finset.mem_range, ht0, n]
    · simp only [hr, hm, and_false, ite_false]
      exact Finset.sum_eq_zero (fun t ht => by simp [hm])
  · simp only [hr, false_and, ite_false]
    exact Finset.sum_eq_zero (fun t ht => by simp [hr])

lemma syndrome_pulse_zero {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (r : Fin (Nat.gcd k gap)) (a : Fin (Nat.gcd k gap) × Fin 2) :
    syndrome hk gap (pulse hk gap r.val 0) a =
      if a.1 = r ∧ a.2.val = 0 then (1 : ZMod 2) else 0 := by
  have ht0 : 0 < k / Nat.gcd k gap := orbit_len_pos hk gap
  have h := syndrome_pulse hk hgap h3 r 0 ht0 a
  simpa [eq_comm] using h

lemma syndrome_pulse_one {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (r : Fin (Nat.gcd k gap)) (a : Fin (Nat.gcd k gap) × Fin 2) :
    syndrome hk gap (pulse hk gap r.val 1) a =
      if a.1 = r ∧ a.2.val = 1 then (1 : ZMod 2) else 0 := by
  have ht0 : 1 < k / Nat.gcd k gap := Nat.lt_of_lt_of_le (by decide) (orbit_len_ge_three hk hgap h3)
  have h := syndrome_pulse hk hgap h3 r 1 ht0 a
  simpa [eq_comm] using h

lemma syndromeLM_apply (gap : ℕ) (x : Fin k → ZMod 2)
    (a : Fin (Nat.gcd k gap) × Fin 2) :
    syndromeLM hk gap x a = syndrome hk gap x a := rfl

lemma syndromeLM_surjective {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    Function.Surjective (syndromeLM hk gap) := by
  intro y
  let x : Fin k → ZMod 2 :=
    ∑ r : Fin (Nat.gcd k gap),
      (y (r, 0) • pulse hk gap r.val 0 + y (r, 1) • pulse hk gap r.val 1)
  refine ⟨x, ?_⟩
  have hx : syndromeLM hk gap x =
      ∑ r : Fin (Nat.gcd k gap),
        (y (r, 0) • syndromeLM hk gap (pulse hk gap r.val 0) +
          y (r, 1) • syndromeLM hk gap (pulse hk gap r.val 1)) := by
    simp only [x, map_sum, map_add, map_smul]
  ext a
  rw [hx]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    syndromeLM_apply, syndrome_pulse_zero hk hgap h3, syndrome_pulse_one hk hgap h3]
  have hbit : a.2.val = 0 ∨ a.2.val = 1 := by
    have : a.2.val < 2 := a.2.isLt
    omega
  rcases hbit with hval | hval
  · have ha : a = (a.1, (0 : Fin 2)) := Prod.ext rfl (Fin.ext hval)
    rw [ha]
    simp only [Fin.val_zero]
    simp only [and_true, and_false, ite_true, ite_false, mul_zero, add_zero, mul_one]
    rw [Finset.sum_eq_single a.1]
    · simp
    · intro r _ hr
      simp [hr.symm]
    · intro h; exact (h (Finset.mem_univ _)).elim
  · have ha : a = (a.1, (1 : Fin 2)) := Prod.ext rfl (Fin.ext hval)
    rw [ha]
    simp only [Fin.val_one]
    simp only [and_true, and_false, ite_true, ite_false, mul_zero, zero_add, mul_one]
    rw [Finset.sum_eq_single a.1]
    · simp
    · intro r _ hr
      simp [hr.symm]
    · intro h; exact (h (Finset.mem_univ _)).elim

lemma range_mix_le_ker_syndrome {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    LinearMap.range (mixLM hk gap) ≤ LinearMap.ker (syndromeLM hk gap) :=
  LinearMap.range_le_ker_iff.mpr
    (LinearMap.ext fun x => mix_mem_ker_syndrome hk hgap h3 x)

lemma finrank_word_space :
    Module.finrank (ZMod 2) (Fin k → ZMod 2) = k := by
  rw [Module.finrank_eq_card_basis (Pi.basisFun (ZMod 2) (Fin k)), Fintype.card_fin]

lemma finrank_syndrome_space (gap : ℕ) :
    Module.finrank (ZMod 2) (Fin (Nat.gcd k gap) × Fin 2 → ZMod 2) =
      2 * Nat.gcd k gap := by
  rw [Module.finrank_eq_card_basis (Pi.basisFun (ZMod 2) (Fin (Nat.gcd k gap) × Fin 2)),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

lemma two_mul_gcd_le_k {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    2 * Nat.gcd k gap ≤ k := by
  have hn := orbit_len_ge_three hk hgap h3
  have hkn : Nat.gcd k gap * (k / Nat.gcd k gap) = k :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left k gap)
  have : 2 * Nat.gcd k gap ≤ Nat.gcd k gap * (k / Nat.gcd k gap) := by
    have : 2 ≤ k / Nat.gcd k gap := Nat.le_trans (by decide) hn
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (Nat.gcd k gap) this
  simpa [Nat.mul_comm, hkn] using this

lemma finrank_range_syndrome {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    Module.finrank (ZMod 2) (LinearMap.range (syndromeLM hk gap)) =
      2 * Nat.gcd k gap := by
  have hsurj := syndromeLM_surjective hk hgap h3
  have : LinearMap.range (syndromeLM hk gap) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  rw [this, finrank_top, finrank_syndrome_space hk gap]

lemma finrank_ker_syndrome {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    Module.finrank (ZMod 2) (LinearMap.ker (syndromeLM hk gap)) =
      k - 2 * Nat.gcd k gap := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (syndromeLM hk gap)
  have hr := finrank_range_syndrome hk hgap h3
  have hd := finrank_word_space (k := k) hk
  have hle := two_mul_gcd_le_k hk hgap h3
  omega

lemma orbit_residue (gap r t : ℕ) (hr : r < Nat.gcd k gap) :
    (ix hk (r + t * gap)).val % Nat.gcd k gap = r := by
  have hgap0 : gap % Nat.gcd k gap = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right k gap)
  simp only [ix]
  rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left k gap), Nat.add_mod, Nat.mul_mod, hgap0,
    Nat.mul_zero, Nat.zero_mod, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hr]

lemma residue_invariant_succ (gap : ℕ) (j : Fin k) :
    (ix hk (j.val + gap)).val % Nat.gcd k gap = j.val % Nat.gcd k gap := by
  have hgap0 : gap % Nat.gcd k gap = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right k gap)
  simp only [ix]
  rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left k gap), Nat.add_mod, hgap0, Nat.add_zero,
    Nat.mod_mod]

lemma residue_invariant_pred {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (j : Fin k) :
    (ix hk (j.val + k - gap % k)).val % Nat.gcd k gap = j.val % Nat.gcd k gap := by
  set g := Nat.gcd k gap
  have hge : gap < k := gap_lt_of_three hk hgap h3
  have hgapk : gap % k = gap := gap_mod_eq hk hgap h3
  have hks : g * (k / g) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k gap)
  have hgs : g * (gap / g) = gap := Nat.mul_div_cancel' (Nat.gcd_dvd_right k gap)
  have hsub : k - gap = g * (k / g - gap / g) := by
    have : gap / g ≤ k / g := Nat.div_le_div_right (Nat.le_of_lt hge)
    have hk' : k = g * (k / g) := hks.symm
    have hg' : gap = g * (gap / g) := hgs.symm
    conv_lhs => rw [hk']
    conv_lhs => right; rw [hg']
    exact (Nat.mul_sub_left_distrib g (k / g) (gap / g)).symm
  have hkm : (k - gap) % g = 0 := by
    rw [hsub, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  simp only [ix, hgapk]
  have hde : j.val + k - gap = j.val + (k - gap) := by
    have : gap ≤ k := Nat.le_of_lt hge
    omega
  rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left k gap), hde, Nat.add_mod, hkm,
    Nat.add_zero, Nat.mod_mod]

lemma orbit_cover (gap : ℕ) (j : Fin k) :
    ∃ t, t < k / Nat.gcd k gap ∧
      j = ix hk ((j.val % Nat.gcd k gap) + t * gap) := by
  let g := Nat.gcd k gap
  let n := k / g
  have hgpos : 0 < g := gcd_pos hk gap
  have hn : 0 < n := orbit_len_pos hk gap
  have hgs : g * (gap / g) = gap := Nat.mul_div_cancel' (Nat.gcd_dvd_right k gap)
  have hkn : g * n = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k gap)
  have hcop : Nat.Coprime (gap / g) n := by
    change Nat.Coprime (gap / Nat.gcd k gap) (k / Nat.gcd k gap)
    exact (Nat.coprime_div_gcd_div_gcd hgpos).symm
  have hq : j.val / g < n :=
    (Nat.div_lt_iff_lt_mul hgpos).mpr (by
      rw [Nat.mul_comm, hkn]
      exact j.isLt)
  obtain ⟨t, ht, htm⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (j.val / g) hcop (ne_of_gt hn)
  have hcong : t * (gap / g) ≡ j.val / g [MOD n] := by
    change (t * (gap / g)) % n = (j.val / g) % n
    have : (gap / g * t) % n = (j.val / g) % n := htm
    simpa [Nat.mul_comm] using this
  refine ⟨t, ht, ((ix_cast_eq hk ?_).trans (ix_val' hk j)).symm⟩
  have : NeZero k := ⟨Nat.pos_iff_ne_zero.mp hk⟩
  have htgap : t * gap = g * (t * (gap / g)) := by
    conv_lhs => rw [← hgs]
    rw [← mul_assoc, mul_comm t g, mul_assoc]
  have hmul : (g * (t * (gap / g))) % (g * n) = (g * (j.val / g)) % (g * n) := by
    rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left]
    have : t * (gap / g) % n = j.val / g % n := hcong
    rw [this]
  have hmulZ : ((g * (t * (gap / g)) : ℕ) : ZMod k) =
      ((g * (j.val / g) : ℕ) : ZMod k) := by
    have h := hmul
    rw [hkn] at h
    exact (ZMod.natCast_eq_natCast_iff _ _ k).mpr h
  have hde : (j.val : ZMod k) =
      ((g * (j.val / g) + j.val % g : ℕ) : ZMod k) := by
    rw [Nat.div_add_mod]
  simp only [Nat.cast_add, Nat.cast_mul, htgap, hmulZ] at hde ⊢
  exact (add_comm _ _).trans hde.symm

omit hk in
def kerPat (c t : ℕ) : ZMod 2 :=
  if t % 3 = c ∨ t % 3 = 2 then 1 else 0

def kerWord (gap : ℕ) (r : Fin (Nat.gcd k gap)) (c : Fin 2) : Fin k → ZMod 2 :=
  ∑ t ∈ Finset.range (k / Nat.gcd k gap),
    kerPat c.val t • pulse hk gap r.val t

lemma kerWord_apply_on (gap : ℕ) (r : Fin (Nat.gcd k gap)) (c : Fin 2)
    (t : ℕ) (ht : t < k / Nat.gcd k gap) :
    kerWord hk gap r c (ix hk (r.val + t * gap)) = kerPat c.val t := by
  simp only [kerWord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pulse]
  rw [Finset.sum_eq_single t]
  · simp
  · intro t' ht' hne
    have htlt : t' < k / Nat.gcd k gap := Finset.mem_range.mp ht'
    have hne' : ix hk (r.val + t * gap) ≠ ix hk (r.val + t' * gap) := by
      intro heq
      exact hne (orbit_eq hk r.isLt r.isLt ht htlt heq).2.symm
    simp [hne']
  · intro h
    exact (h (Finset.mem_range.mpr ht)).elim

lemma kerWord_apply_off (gap : ℕ) (r : Fin (Nat.gcd k gap)) (c : Fin 2)
    (j : Fin k)
    (hoff : ∀ t < k / Nat.gcd k gap, j ≠ ix hk (r.val + t * gap)) :
    kerWord hk gap r c j = 0 := by
  simp only [kerWord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pulse]
  refine Finset.sum_eq_zero ?_
  intro t ht
  have : j ≠ ix hk (r.val + t * gap) := hoff t (Finset.mem_range.mp ht)
  simp [this]

lemma not_mem_orbit_of_residue_ne (gap : ℕ) (r : Fin (Nat.gcd k gap)) (j : Fin k)
    (hne : j.val % Nat.gcd k gap ≠ r.val) (t : ℕ)
    (ht : t < k / Nat.gcd k gap) :
    j ≠ ix hk (r.val + t * gap) := by
  intro heq
  apply hne
  rw [heq, orbit_residue hk gap r.val t r.isLt]

omit hk in
lemma kerPat_zero_zero : kerPat 0 0 = 1 := by simp [kerPat]

omit hk in
lemma kerPat_one_zero : kerPat 1 0 = 0 := by simp [kerPat]

omit hk in
lemma kerPat_zero_one : kerPat 0 1 = 0 := by simp [kerPat]

omit hk in
lemma kerPat_one_one : kerPat 1 1 = 1 := by simp [kerPat]

lemma kerPat_cycle {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (c t : ℕ) (hc : c < 2) :
    kerPat c t + kerPat c ((t + 1) % (k / Nat.gcd k gap)) +
      kerPat c ((t + k / Nat.gcd k gap - 1) % (k / Nat.gcd k gap)) = 0 := by
  let n := k / Nat.gcd k gap
  have hn : 0 < n := orbit_len_pos hk gap
  have h3n : 3 ∣ n := three_dvd_k_div_gcd hgap h3
  have hs : kerPat c ((t + 1) % n) =
      if (t + 1) % 3 = c ∨ (t + 1) % 3 = 2 then (1 : ZMod 2) else 0 := by
    simp only [kerPat, add_one_mod_mod_three h3n]
  have hp : kerPat c ((t + n - 1) % n) =
      if (t + 2) % 3 = c ∨ (t + 2) % 3 = 2 then (1 : ZMod 2) else 0 := by
    simp only [kerPat, pred_mod_mod_three hn h3n]
  simp only [n] at hs hp
  rw [hs, hp]
  simp only [kerPat]
  convert syn_mask_coeff c t hc using 1
  ac_rfl

lemma mix_kerWord {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (r : Fin (Nat.gcd k gap)) (c : Fin 2) :
    mix hk gap (kerWord hk gap r c) = 0 := by
  ext j
  change mix hk gap (kerWord hk gap r c) j = 0
  let n := k / Nat.gcd k gap
  have hn : 0 < n := orbit_len_pos hk gap
  by_cases hr : j.val % Nat.gcd k gap = r.val
  · obtain ⟨t, ht, hj⟩ := orbit_cover hk gap j
    have hj' : j = ix hk (r.val + t * gap) := by
      simpa [hr] using hj
    rw [hj']
    have hmix := mix_at_orbit hk hgap h3 (kerWord hk gap r c) r.val t
    rw [hmix]
    have ht1 : (t + 1) % n < n := Nat.mod_lt _ hn
    have htp : (t + n - 1) % n < n := Nat.mod_lt _ hn
    have h0 := kerWord_apply_on hk gap r c t ht
    have h1 := kerWord_apply_on hk gap r c ((t + 1) % n) ht1
    have hp := kerWord_apply_on hk gap r c ((t + n - 1) % n) htp

    change
        kerWord hk gap r c (ix hk (r.val + t * gap)) +
          kerWord hk gap r c (ix hk (r.val + ((t + 1) % (k / Nat.gcd k gap)) * gap)) +
          kerWord hk gap r c
            (ix hk (r.val + ((t + k / Nat.gcd k gap - 1) % (k / Nat.gcd k gap)) * gap)) = 0
    rw [h0, h1, hp]
    exact kerPat_cycle hk hgap h3 c.val t c.isLt
  · have hoff :
        ∀ t < k / Nat.gcd k gap, j ≠ ix hk (r.val + t * gap) :=
      fun t ht => not_mem_orbit_of_residue_ne hk gap r j hr t ht
    have hoffs :
        ∀ t < k / Nat.gcd k gap,
          ix hk (j.val + gap) ≠ ix hk (r.val + t * gap) :=
      fun t ht =>
        not_mem_orbit_of_residue_ne hk gap r (ix hk (j.val + gap))
          (by rw [residue_invariant_succ hk gap j]; exact hr) t ht
    have hoffp :
        ∀ t < k / Nat.gcd k gap,
          ix hk (j.val + k - gap % k) ≠ ix hk (r.val + t * gap) :=
      fun t ht =>
        not_mem_orbit_of_residue_ne hk gap r (ix hk (j.val + k - gap % k))
          (by rw [residue_invariant_pred hk hgap h3 j]; exact hr) t ht
    simp only [mix, kerWord_apply_off hk gap r c j hoff,
      kerWord_apply_off hk gap r c (ix hk (j.val + gap)) hoffs,
      kerWord_apply_off hk gap r c (ix hk (j.val + k - gap % k)) hoffp]
    ring

lemma kerWord_mem_ker {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (r : Fin (Nat.gcd k gap)) (c : Fin 2) :
    kerWord hk gap r c ∈ LinearMap.ker (mixLM hk gap) := by
  simp [LinearMap.mem_ker, mixLM, mix_kerWord hk hgap h3]

lemma kerWord_at {gap : ℕ} (r r' : Fin (Nat.gcd k gap)) (c : Fin 2)
    (t : ℕ) (ht : t < k / Nat.gcd k gap) :
    kerWord hk gap r' c (ix hk (r.val + t * gap)) =
      if r' = r then kerPat c.val t else 0 := by
  by_cases hr : r' = r
  · subst hr
    simp [kerWord_apply_on hk gap r' c t ht]
  · rw [kerWord_apply_off]
    · simp [hr]
    · intro t' ht'
      intro heq
      exact hr (Fin.ext (orbit_eq hk r'.isLt r.isLt ht' ht heq.symm).1)

lemma kerWords_linearIndependent {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    LinearIndependent (ZMod 2)
      (fun rc : Fin (Nat.gcd k gap) × Fin 2 => kerWord hk gap rc.1 rc.2) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf rc
  have hn0 : 0 < k / Nat.gcd k gap := orbit_len_pos hk gap
  have hn1 : 1 < k / Nat.gcd k gap :=
    Nat.lt_of_lt_of_le (by decide) (orbit_len_ge_three hk hgap h3)
  have heval (t : ℕ) (ht : t < k / Nat.gcd k gap) :
      (∑ i : Fin (Nat.gcd k gap) × Fin 2,
        f i * kerWord hk gap i.1 i.2 (ix hk (rc.1.val + t * gap))) = 0 := by
    have := congrArg (fun v : Fin k → ZMod 2 => v (ix hk (rc.1.val + t * gap))) hf
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  have h0 : f (rc.1, (0 : Fin 2)) = 0 := by
    have h := heval 0 hn0
    have hterm (i : Fin (Nat.gcd k gap) × Fin 2) :
        kerWord hk gap i.1 i.2 (ix hk (rc.1.val + 0 * gap)) =
          if i.1 = rc.1 then kerPat i.2.val 0 else 0 :=
      kerWord_at hk rc.1 i.1 i.2 0 hn0
    simp_rw [hterm] at h
    rw [Finset.sum_eq_single (rc.1, (0 : Fin 2))] at h
    · simp [kerPat_zero_zero] at h
      exact h
    · intro i _ hne
      by_cases hr : i.1 = rc.1
      · have hi2 : i.2 = (1 : Fin 2) := by
          have hbit : i.2.val = 0 ∨ i.2.val = 1 := by
            have : i.2.val < 2 := i.2.isLt
            omega
          rcases hbit with hv | hv
          · exact (hne (Prod.ext hr (Fin.ext hv))).elim
          · exact Fin.ext hv
        simp [hr, hi2, kerPat_one_zero]
      · simp [hr]
    · intro hmem; exact (hmem (Finset.mem_univ _)).elim
  have h1 : f (rc.1, (1 : Fin 2)) = 0 := by
    have h := heval 1 hn1
    have hterm (i : Fin (Nat.gcd k gap) × Fin 2) :
        kerWord hk gap i.1 i.2 (ix hk (rc.1.val + 1 * gap)) =
          if i.1 = rc.1 then kerPat i.2.val 1 else 0 :=
      kerWord_at hk rc.1 i.1 i.2 1 hn1
    simp_rw [hterm] at h
    rw [Finset.sum_eq_single (rc.1, (1 : Fin 2))] at h
    · simp [kerPat_one_one] at h
      exact h
    · intro i _ hne
      by_cases hr : i.1 = rc.1
      · have hi2 : i.2 = (0 : Fin 2) := by
          have hbit : i.2.val = 0 ∨ i.2.val = 1 := by
            have : i.2.val < 2 := i.2.isLt
            omega
          rcases hbit with hv | hv
          · exact Fin.ext hv
          · exact (hne (Prod.ext hr (Fin.ext hv))).elim
        simp [hr, hi2, kerPat_zero_one]
      · simp [hr]
    · intro hmem; exact (hmem (Finset.mem_univ _)).elim
  have hbit : rc.2.val = 0 ∨ rc.2.val = 1 := by
    have : rc.2.val < 2 := rc.2.isLt
    omega
  rcases hbit with hv | hv
  · have hrc : rc = (rc.1, (0 : Fin 2)) := Prod.ext rfl (Fin.ext hv)
    rw [hrc]
    exact h0
  · have hrc : rc = (rc.1, (1 : Fin 2)) := Prod.ext rfl (Fin.ext hv)
    rw [hrc]
    exact h1

lemma finrank_span_kerWords {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (Set.range (fun rc : Fin (Nat.gcd k gap) × Fin 2 =>
          kerWord hk gap rc.1 rc.2))) = 2 * Nat.gcd k gap := by
  rw [finrank_span_eq_card (kerWords_linearIndependent hk hgap h3),
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

lemma span_kerWords_le_ker_mix {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    Submodule.span (ZMod 2)
      (Set.range (fun rc : Fin (Nat.gcd k gap) × Fin 2 =>
        kerWord hk gap rc.1 rc.2)) ≤ LinearMap.ker (mixLM hk gap) := by
  rw [Submodule.span_le]
  rintro _ ⟨rc, rfl⟩
  exact kerWord_mem_ker hk hgap h3 rc.1 rc.2

omit hk in
lemma eq_of_triple_sum_eq_zero {a b c : ZMod 2}
    (h : a + b + c = 0) : b = a + c := by
  have hb : b + b = 0 := CharTwo.add_self_eq_zero b
  calc
    b = b + 0 := by rw [add_zero]
    _ = b + (a + b + c) := by rw [h]
    _ = a + c := by
        have : b + (a + b + c) = a + (b + b) + c := by ac_rfl
        rw [this, hb, add_zero]

lemma kerPat_rec {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (c t : ℕ) (hc : c < 2) (ht : 2 ≤ t) (htn : t < k / Nat.gcd k gap) :
    kerPat c t = kerPat c (t - 1) + kerPat c (t - 2) := by
  let n := k / Nat.gcd k gap
  have hn : 0 < n := orbit_len_pos hk gap
  have hsum := kerPat_cycle hk hgap h3 c (t - 1) hc
  have h1 : ((t - 1) + 1) % n = t := by
    have : t - 1 + 1 = t := Nat.sub_add_cancel (Nat.le_trans (by decide) ht)
    have hlt : t < n := htn
    rw [this, Nat.mod_eq_of_lt hlt]
  have h2 : ((t - 1) + n - 1) % n = t - 2 := by
    have : t - 1 + n - 1 = (t - 2) + n := by omega
    rw [this, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega)]
  simp only [n] at h1 h2
  rw [h1, h2] at hsum
  exact eq_of_triple_sum_eq_zero hsum

lemma mix_zero_at_orbit {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    {x : Fin k → ZMod 2} (hx : mix hk gap x = 0) (r t : ℕ) :
    x (ix hk (r + t * gap)) +
      x (ix hk (r + ((t + 1) % (k / Nat.gcd k gap)) * gap)) +
      x (ix hk (r + ((t + k / Nat.gcd k gap - 1) % (k / Nat.gcd k gap)) * gap)) = 0 := by
  have := congrArg (fun v : Fin k → ZMod 2 => v (ix hk (r + t * gap))) hx
  rw [Pi.zero_apply, mix_at_orbit hk hgap h3 x r t] at this
  exact this

lemma ker_coord {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    {x : Fin k → ZMod 2} (hx : mix hk gap x = 0)
    (r : Fin (Nat.gcd k gap)) (t : ℕ) (ht : t < k / Nat.gcd k gap) :
    x (ix hk (r.val + t * gap)) =
      x (ix hk r.val) * kerPat 0 t +
        x (ix hk (r.val + gap)) * kerPat 1 t := by
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    have hn : 0 < k / Nat.gcd k gap := orbit_len_pos hk gap
    rcases Nat.lt_or_ge t 2 with ht2 | ht2
    · interval_cases t
      · simp [kerPat_zero_zero, kerPat_one_zero]
      · simp [kerPat_zero_one, kerPat_one_one]
    · have ht1 : t - 1 < t := Nat.sub_lt (Nat.lt_of_lt_of_le (by decide) ht2) (by decide)
      have ht2' : t - 2 < t := by omega
      have ht1n : t - 1 < k / Nat.gcd k gap := by omega
      have ht2n : t - 2 < k / Nat.gcd k gap := by omega
      have hrec := mix_zero_at_orbit hk hgap h3 hx r.val (t - 1)
      have hs : ((t - 1) + 1) % (k / Nat.gcd k gap) = t := by
        have : t - 1 + 1 = t := Nat.sub_add_cancel (Nat.le_trans (by decide) ht2)
        rw [this, Nat.mod_eq_of_lt ht]
      have hp : ((t - 1) + k / Nat.gcd k gap - 1) % (k / Nat.gcd k gap) = t - 2 := by
        have : t - 1 + k / Nat.gcd k gap - 1 = (t - 2) + k / Nat.gcd k gap := by omega
        rw [this, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod,
          Nat.mod_eq_of_lt ht2n]
      rw [hs, hp] at hrec
      have ih1 := ih (t - 1) ht1 ht1n
      have ih2 := ih (t - 2) ht2' ht2n
      have hpat0 := kerPat_rec hk hgap h3 0 t (by decide) ht2 ht
      have hpat1 := kerPat_rec hk hgap h3 1 t (by decide) ht2 ht
      have : x (ix hk (r.val + t * gap)) =
          x (ix hk (r.val + (t - 1) * gap)) +
            x (ix hk (r.val + (t - 2) * gap)) :=
        (eq_of_triple_sum_eq_zero hrec)
      rw [this, ih1, ih2, hpat0, hpat1]
      ring

lemma ker_eq_sum_kerWords {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    {x : Fin k → ZMod 2} (hx : mix hk gap x = 0) :
    x = ∑ rc : Fin (Nat.gcd k gap) × Fin 2,
      x (ix hk (rc.1.val + rc.2.val * gap)) • kerWord hk gap rc.1 rc.2 := by
  ext j
  obtain ⟨t, ht, hj⟩ := orbit_cover hk gap j
  have hgpos : 0 < Nat.gcd k gap := gcd_pos hk gap
  set r : Fin (Nat.gcd k gap) :=
    ⟨j.val % Nat.gcd k gap, Nat.mod_lt _ hgpos⟩
  have hj' : j = ix hk (r.val + t * gap) := hj
  rw [hj', Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single r]
  · rw [Fin.sum_univ_two]
    rw [kerWord_at hk r r 0 t ht, kerWord_at hk r r 1 t ht]
    simp only [↓reduceIte, Fin.val_zero, Fin.val_one, Nat.zero_mul, Nat.one_mul,
      Nat.add_zero]
    exact ker_coord hk hgap h3 hx r t ht
  · intro r' _ hne
    refine Finset.sum_eq_zero ?_
    intro c _
    rw [kerWord_at hk r r' c t ht]
    simp [hne]
  · intro hmem; exact (hmem (Finset.mem_univ _)).elim

lemma ker_mix_eq_span_kerWords {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    LinearMap.ker (mixLM hk gap) =
      Submodule.span (ZMod 2)
        (Set.range (fun rc : Fin (Nat.gcd k gap) × Fin 2 =>
          kerWord hk gap rc.1 rc.2)) := by
  apply le_antisymm
  · intro x hx
    have hx0 : mix hk gap x = 0 := by
      simpa [LinearMap.mem_ker, mixLM] using hx
    have hxsum := ker_eq_sum_kerWords hk hgap h3 hx0
    rw [hxsum]
    exact Submodule.sum_mem _ (fun rc _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨rc, rfl⟩))
  · exact span_kerWords_le_ker_mix hk hgap h3

lemma finrank_ker_mix {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    Module.finrank (ZMod 2) (LinearMap.ker (mixLM hk gap)) = 2 * Nat.gcd k gap := by
  rw [ker_mix_eq_span_kerWords hk hgap h3, finrank_span_kerWords hk hgap h3]

lemma finrank_range_mix {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    Module.finrank (ZMod 2) (LinearMap.range (mixLM hk gap)) =
      k - 2 * Nat.gcd k gap := by
  have hsum := LinearMap.finrank_range_add_finrank_ker (mixLM hk gap)
  have hd := finrank_word_space (k := k) hk
  rw [hd, finrank_ker_mix hk hgap h3] at hsum
  have h2 := two_mul_gcd_le_k hk hgap h3
  omega

lemma range_mix_eq_ker_syndrome {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    LinearMap.range (mixLM hk gap) = LinearMap.ker (syndromeLM hk gap) :=
  Submodule.eq_of_le_of_finrank_eq (range_mix_le_ker_syndrome hk hgap h3)
    (by rw [finrank_range_mix hk hgap h3, finrank_ker_syndrome hk hgap h3])

lemma mix_mem_range_iff {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (y : Fin k → ZMod 2) :
    y ∈ LinearMap.range (mixLM hk gap) ↔ syndromeLM hk gap y = 0 := by
  rw [range_mix_eq_ker_syndrome hk hgap h3, LinearMap.mem_ker]

lemma mixLM_apply (gap : ℕ) (x : Fin k → ZMod 2) :
    mixLM hk gap x = mix hk gap x := rfl

instance instFiniteKerMix (gap : ℕ) :
    Finite (LinearMap.ker (mixLM hk gap)) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance instFintypeKerMix (gap : ℕ) :
    Fintype (LinearMap.ker (mixLM hk gap)) :=
  Fintype.ofFinite _

lemma card_ker_mix {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k) :
    Fintype.card (LinearMap.ker (mixLM hk gap)) = 2 ^ (2 * Nat.gcd k gap) := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, finrank_ker_mix hk hgap h3]

lemma card_mix_preimage_of_mem {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (y : Fin k → ZMod 2) (hy : y ∈ LinearMap.range (mixLM hk gap)) :
    ((univ : Finset (Fin k → ZMod 2)).filter (fun x => mix hk gap x = y)).card =
      2 ^ (2 * Nat.gcd k gap) := by
  obtain ⟨x0, hx0⟩ := hy
  have hx0' : mix hk gap x0 = y := by
    simpa [mixLM_apply] using hx0
  let e : LinearMap.ker (mixLM hk gap) ≃ {x : Fin k → ZMod 2 // mix hk gap x = y} :=
    { toFun := fun v =>
        ⟨x0 + (v : Fin k → ZMod 2), by
          have hv : mix hk gap (v : Fin k → ZMod 2) = 0 := by
            simpa [← mixLM_apply] using (LinearMap.mem_ker.mp v.property)
          have hadd : mix hk gap (x0 + (v : Fin k → ZMod 2)) =
              mix hk gap x0 + mix hk gap (v : Fin k → ZMod 2) :=
            mix_linear hk gap x0 (v : Fin k → ZMod 2)
          rw [hadd, hx0', hv, add_zero]⟩
      invFun := fun x =>
        ⟨x.val + x0, by
          have hadd : mix hk gap (x.val + x0) =
              mix hk gap x.val + mix hk gap x0 :=
            mix_linear hk gap x.val x0
          rw [LinearMap.mem_ker, mixLM_apply, hadd, x.property, hx0']
          ext j
          simp [Pi.add_apply, CharTwo.add_self_eq_zero]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        ext j
        have hx : x0 j + x0 j = 0 := CharTwo.add_self_eq_zero (x0 j)
        simp [Pi.add_apply]
        rw [add_right_comm, hx, zero_add]
      right_inv := by
        intro x
        apply Subtype.ext
        ext j
        have hx : x0 j + x0 j = 0 := CharTwo.add_self_eq_zero (x0 j)
        simp [Pi.add_apply]
        rw [add_comm (x0 j), add_assoc, hx, add_zero] }
  have : Fintype {x : Fin k → ZMod 2 // mix hk gap x = y} := Fintype.ofFinite _
  rw [← Fintype.card_subtype, ← Fintype.card_congr e, card_ker_mix hk hgap h3]

lemma card_mix_preimage_of_not_mem {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (y : Fin k → ZMod 2) (hy : y ∉ LinearMap.range (mixLM hk gap)) :
    ((univ : Finset (Fin k → ZMod 2)).filter (fun x => mix hk gap x = y)).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _
  intro hx
  exact hy ⟨x, by simp [mixLM_apply, hx]⟩

def colorVec {s : ℕ} (D : Fin s → Fin k → ZMod 2) (j : Fin k) : Fin s → ZMod 2 :=
  fun p => D p j

def edge {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (u v : Fin k) : Prop :=
  ∃ j ∈ test, u = ix hk (j.val + 1) ∧ v = ix hk (j.val + 2) ∧
    colorVec D u = colorVec D v ∧ colorVec D u ≠ 0

noncomputable def joined {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) (u v : Fin k) : Bool :=
  @decide (Relation.EqvGen (edge hk D test) u v) (Classical.propDecidable _)

def pinned {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (z : Fin k) : Prop :=
  ∃ j ∈ test,
    let u := ix hk (j.val + 1)
    let v := ix hk (j.val + 2)
    colorVec D u ≠ colorVec D v ∧
      ((z = u ∧ colorVec D v ≠ 0) ∨ (z = v ∧ colorVec D u ≠ 0))

noncomputable def free {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) : Finset (Fin k) :=
  @Finset.filter _ (fun i : Fin k =>
    (∀ j, joined hk D test i j = true → i.val ≤ j.val) ∧
    (∀ j, joined hk D test i j = true → ¬pinned hk D test j))
    (Classical.decPred _) (univ : Finset (Fin k))

noncomputable def block {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) (i z : Fin k) : ZMod 2 :=
  if joined hk D test i z = true then 1 else 0

def allowed {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (delta : Fin k → ZMod 2) : Prop :=
  ∀ p : Fin s, ∀ j ∈ test,
    delta (ix hk (j.val + 1)) * D p (ix hk (j.val + 2)) +
      D p (ix hk (j.val + 1)) * delta (ix hk (j.val + 2)) = 0

lemma joined_iff {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (u v : Fin k) :
    joined hk D test u v = true ↔ Relation.EqvGen (edge hk D test) u v :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

lemma joined_refl {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (u : Fin k) : joined hk D test u u = true :=
  (joined_iff hk D test u u).mpr (Relation.EqvGen.refl _)

lemma joined_symm {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    {u v : Fin k} : joined hk D test u v = true → joined hk D test v u = true := by
  intro h
  exact (joined_iff hk D test v u).mpr
    (Relation.EqvGen.symm _ _ ((joined_iff hk D test u v).mp h))

lemma joined_trans {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    {u v w : Fin k} :
    joined hk D test u v = true → joined hk D test v w = true →
      joined hk D test u w = true := by
  intro h1 h2
  exact (joined_iff hk D test u w).mpr
    (Relation.EqvGen.trans _ _ _
      ((joined_iff hk D test u v).mp h1)
      ((joined_iff hk D test v w).mp h2))

lemma allowed_of_edge {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    {delta : Fin k → ZMod 2} (h : allowed hk D test delta) {u v : Fin k}
    (he : edge hk D test u v) : delta u = delta v := by
  obtain ⟨j, hj, hu, hv, hcol, hnz⟩ := he
  have hconst : ∀ p, delta u * D p v + D p u * delta v = 0 := by
    intro p
    have := h p j hj
    simpa [hu, hv] using this
  exact (constraint_same delta D u v hcol hnz).mp hconst

lemma allowed_const_on_class {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) {delta : Fin k → ZMod 2} (h : allowed hk D test delta)
    {u v : Fin k} (huv : joined hk D test u v = true) : delta u = delta v := by
  have heqv : Relation.EqvGen (edge hk D test) u v :=
    (joined_iff hk D test u v).mp huv
  clear huv
  induction heqv with
  | rel _ _ hrel => exact allowed_of_edge hk D test h hrel
  | refl _ => rfl
  | symm _ _ _ ih => exact Eq.symm ih
  | trans _ _ _ _ _ ih1 ih2 => exact Eq.trans ih1 ih2

lemma allowed_of_pinned {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) {delta : Fin k → ZMod 2} (h : allowed hk D test delta)
    {z : Fin k} (hp : pinned hk D test z) : delta z = 0 := by
  obtain ⟨j, hj, hdiff, hcases⟩ := hp
  have hconst : ∀ p,
      delta (ix hk (j.val + 1)) * D p (ix hk (j.val + 2)) +
        D p (ix hk (j.val + 1)) * delta (ix hk (j.val + 2)) = 0 :=
    fun p => h p j hj
  rcases hcases with ⟨hz, hvnz⟩ | ⟨hz, hunz⟩
  · subst hz
    exact constraint_pin_left delta D (ix hk (j.val + 1)) (ix hk (j.val + 2))
      hdiff hvnz hconst
  · subst hz
    exact constraint_pin_right delta D (ix hk (j.val + 1)) (ix hk (j.val + 2))
      hdiff hunz hconst

lemma out_eq_iff_allowed {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) (x a : Fin k → ZMod 2) :
    (∀ p, ∀ j ∈ test, out hk x (D p) j = out hk a (D p) j) ↔
      allowed hk D test (x + a) := by
  constructor
  · intro h p j hj
    have := (out_eq_iff hk x a (D p) j).mp (h p j hj)
    simpa [Pi.add_apply] using this
  · intro h p j hj
    exact (out_eq_iff hk x a (D p) j).mpr (by simpa [Pi.add_apply] using h p j hj)

lemma exists_class_min {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) (z : Fin k) :
    ∃ i, joined hk D test z i = true ∧
      (∀ j, joined hk D test z j = true → i.val ≤ j.val) := by
  let sclass : Finset (Fin k) :=
    univ.filter (fun j => joined hk D test z j = true)
  have hs : sclass.Nonempty :=
    ⟨z, by simp [sclass, mem_filter, joined_refl]⟩
  refine ⟨sclass.min' hs, ?_, ?_⟩
  · have := sclass.min'_mem hs
    simpa [sclass, mem_filter] using this
  · intro j hj
    have hj' : j ∈ sclass := by simp [sclass, mem_filter, hj]
    exact sclass.min'_le j hj'

lemma mem_free_iff {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) (i : Fin k) :
    i ∈ free hk D test ↔
      (∀ j, joined hk D test i j = true → i.val ≤ j.val) ∧
        (∀ j, joined hk D test i j = true → ¬pinned hk D test j) := by
  unfold free
  rw [(@mem_filter (Fin k)
      (fun i : Fin k =>
        (∀ j, joined hk D test i j = true → i.val ≤ j.val) ∧
          (∀ j, joined hk D test i j = true → ¬pinned hk D test j))
      (Classical.decPred _) univ i)]
  simp [mem_univ]

lemma unpinned_min_mem_free {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) (z : Fin k)
    (hunp : ∀ j, joined hk D test z j = true → ¬pinned hk D test j) :
    ∃ i ∈ free hk D test, joined hk D test i z = true := by
  obtain ⟨i, hzi, hmin⟩ := exists_class_min hk D test z
  refine ⟨i, ?_, joined_symm hk D test hzi⟩
  exact (mem_free_iff hk D test i).mpr
    ⟨fun j hij => hmin j (joined_trans hk D test hzi hij),
     fun j hij => hunp j (joined_trans hk D test hzi hij)⟩

lemma unique_free_of_joined {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) {i i' : Fin k}
    (hi : i ∈ free hk D test) (hi' : i' ∈ free hk D test)
    (h : joined hk D test i i' = true) : i = i' := by
  have h1 : i.val ≤ i'.val := (mem_free_iff hk D test i).mp hi |>.1 i' h
  have h2 : i'.val ≤ i.val :=
    (mem_free_iff hk D test i').mp hi' |>.1 i (joined_symm hk D test h)
  exact Fin.ext (Nat.le_antisymm h1 h2)

lemma allowed_eq_sum {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) {delta : Fin k → ZMod 2}
    (h : allowed hk D test delta) :
    delta = ∑ i ∈ free hk D test, delta i • block hk D test i := by
  ext z
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, block]
  by_cases hfree : ∃ i ∈ free hk D test, joined hk D test i z = true
  · obtain ⟨i, hi, hiz⟩ := hfree
    rw [sum_eq_single i]
    · simp [hiz]
      exact (allowed_const_on_class hk D test h hiz).symm
    · intro i' hi' hne
      have hfalse : joined hk D test i' z = false := by
        cases hji : joined hk D test i' z
        · rfl
        · exact (hne (unique_free_of_joined (i := i) (i' := i') hk D test hi hi'
            (joined_trans hk D test hiz (joined_symm hk D test hji))).symm).elim
      simp [hfalse]
    · intro hnot; exact (hnot hi).elim
  · have hz0 : delta z = 0 := by
      have hunp : ¬ (∀ j, joined hk D test z j = true → ¬pinned hk D test j) := by
        intro hunp
        obtain ⟨i, hi, hiz⟩ := unpinned_min_mem_free hk D test z hunp
        exact hfree ⟨i, hi, hiz⟩
      push_neg at hunp
      obtain ⟨j, hzj, hpj⟩ := hunp
      have hcz := allowed_const_on_class hk D test h hzj
      have hzj0 := allowed_of_pinned hk D test h hpj
      exact hcz.trans hzj0
    rw [hz0]
    apply Eq.symm
    refine sum_eq_zero ?_
    intro i hi
    have : joined hk D test i z = false := by
      cases hji : joined hk D test i z
      · rfl
      · exact (hfree ⟨i, hi, hji⟩).elim
    simp [this]

lemma blocks_linearIndependent {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) :
    LinearIndependent (ZMod 2)
      (fun i : ↥(free hk D test) => block hk D test i.val) := by
  rw [Fintype.linearIndependent_iff]
  intro f hf i
  have heval :
      (∑ j : ↥(free hk D test), f j * block hk D test j.val i.val) = 0 := by
    have := congrArg (fun v : Fin k → ZMod 2 => v i.val) hf
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  rw [Finset.sum_eq_single i] at heval
  · simp [block, joined_refl] at heval
    exact heval
  · intro i' _ hne
    have hfalse : joined hk D test i'.val i.val = false := by
      cases hji : joined hk D test i'.val i.val
      · rfl
      · exact (hne (Subtype.ext (unique_free_of_joined (i := i'.val) (i' := i.val)
          hk D test i'.property i.property hji))).elim
    simp [block, hfalse]
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

lemma finrank_span_blocks {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (Set.range (fun i : ↥(free hk D test) => block hk D test i.val))) =
      (free hk D test).card := by
  rw [finrank_span_eq_card (blocks_linearIndependent hk D test),
    Fintype.card_coe]

lemma joined_congr {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) {u v w : Fin k}
    (h : joined hk D test u v = true) :
    joined hk D test w u = joined hk D test w v := by
  cases hwu : joined hk D test w u <;> cases hwv : joined hk D test w v
  · rfl
  · have : joined hk D test w u = true :=
      joined_trans hk D test hwv (joined_symm hk D test h)
    rw [hwu] at this
    exact (Bool.false_ne_true this).elim
  · have : joined hk D test w v = true :=
      joined_trans hk D test hwu h
    rw [hwv] at this
    exact (Bool.false_ne_true this).elim
  · rfl

lemma joined_eq_false_of_pinned {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) {i z : Fin k}
    (hi : i ∈ free hk D test) (hp : pinned hk D test z) :
    joined hk D test i z = false := by
  cases h : joined hk D test i z
  · rfl
  · exact (((mem_free_iff hk D test i).mp hi).2 z h hp).elim

lemma block_allowed {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) {i : Fin k} (hi : i ∈ free hk D test) :
    allowed hk D test (block hk D test i) := by
  intro p j hj
  set u := ix hk (j.val + 1)
  set v := ix hk (j.val + 2)
  change block hk D test i u * D p v + D p u * block hk D test i v = 0
  by_cases hcol : colorVec D u = colorVec D v
  · by_cases hnz : colorVec D u = 0
    · have hu0 : D p u = 0 := congrFun hnz p
      have hv0 : D p v = 0 := (congrFun hcol p).symm.trans hu0
      simp [hu0, hv0]
    · have he : edge hk D test u v := ⟨j, hj, rfl, rfl, hcol, hnz⟩
      have hjn : joined hk D test u v = true :=
        (joined_iff hk D test u v).mpr (Relation.EqvGen.rel _ _ he)
      have hblock : block hk D test i u = block hk D test i v := by
        simp only [block, joined_congr hk D test hjn]
      have hdv : D p v = D p u := (congrFun hcol p).symm
      rw [hdv, hblock, mul_comm (block hk D test i v)]
      exact CharTwo.add_self_eq_zero _
  · by_cases hunz : colorVec D u = 0
    · have hvnz : colorVec D v ≠ 0 := by
        intro hv0
        exact hcol (hunz.trans hv0.symm)
      have hu_pin : pinned hk D test u :=
        ⟨j, hj, hcol, Or.inl ⟨rfl, hvnz⟩⟩
      have hju : joined hk D test i u = false :=
        joined_eq_false_of_pinned hk D test hi hu_pin
      have hu0 : D p u = 0 := congrFun hunz p
      simp [block, hju, hu0]
    · have hv_pin : pinned hk D test v :=
        ⟨j, hj, hcol, Or.inr ⟨rfl, hunz⟩⟩
      have hjv : joined hk D test i v = false :=
        joined_eq_false_of_pinned hk D test hi hv_pin
      by_cases hv0 : colorVec D v = 0
      · have : D p v = 0 := congrFun hv0 p
        simp [block, hjv, this]
      · have hu_pin : pinned hk D test u :=
          ⟨j, hj, hcol, Or.inl ⟨rfl, hv0⟩⟩
        have hju : joined hk D test i u = false :=
          joined_eq_false_of_pinned hk D test hi hu_pin
        simp [block, hju, hjv]

lemma allowed_zero {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k)) :
    allowed hk D test 0 := by
  intro p j hj
  simp

lemma allowed_add {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    {x y : Fin k → ZMod 2} (hx : allowed hk D test x) (hy : allowed hk D test y) :
    allowed hk D test (x + y) := by
  intro p j hj
  have hx' := hx p j hj
  have hy' := hy p j hj
  simp only [Pi.add_apply]
  have hsplit :
      ((x (ix hk (j.val + 1)) + y (ix hk (j.val + 1))) * D p (ix hk (j.val + 2)) +
        D p (ix hk (j.val + 1)) * (x (ix hk (j.val + 2)) + y (ix hk (j.val + 2)))) =
        (x (ix hk (j.val + 1)) * D p (ix hk (j.val + 2)) +
          D p (ix hk (j.val + 1)) * x (ix hk (j.val + 2))) +
        (y (ix hk (j.val + 1)) * D p (ix hk (j.val + 2)) +
          D p (ix hk (j.val + 1)) * y (ix hk (j.val + 2))) := by ring
  rw [hsplit, hx', hy', add_zero]

lemma allowed_smul {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (c : ZMod 2) {x : Fin k → ZMod 2} (hx : allowed hk D test x) :
    allowed hk D test (c • x) := by
  intro p j hj
  have hx' := hx p j hj
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsplit :
      (c * x (ix hk (j.val + 1))) * D p (ix hk (j.val + 2)) +
        D p (ix hk (j.val + 1)) * (c * x (ix hk (j.val + 2))) =
        c * (x (ix hk (j.val + 1)) * D p (ix hk (j.val + 2)) +
          D p (ix hk (j.val + 1)) * x (ix hk (j.val + 2))) := by ring
  rw [hsplit, hx', mul_zero]

noncomputable def allowedSub {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) : Submodule (ZMod 2) (Fin k → ZMod 2) :=
  Submodule.span (ZMod 2)
    (Set.range (fun i : ↥(free hk D test) => block hk D test i.val))

lemma allowed_of_mem_allowedSub {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) {delta : Fin k → ZMod 2}
    (h : delta ∈ allowedSub hk D test) : allowed hk D test delta := by
  refine Submodule.span_induction
    (p := fun x _ => allowed hk D test x) ?_ ?_ ?_ ?_ h
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact block_allowed hk D test i.property
  · exact allowed_zero hk D test
  · intro x y _ _ hx hy
    exact allowed_add hk D test hx hy
  · intro c x _ hx
    exact allowed_smul hk D test c hx

lemma mem_allowedSub_of_allowed {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) {delta : Fin k → ZMod 2}
    (h : allowed hk D test delta) : delta ∈ allowedSub hk D test := by
  have hsum := allowed_eq_sum hk D test h
  rw [hsum]
  refine Submodule.sum_mem _ ?_
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)

lemma mem_allowedSub_iff {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) {delta : Fin k → ZMod 2} :
    delta ∈ allowedSub hk D test ↔ allowed hk D test delta :=
  ⟨allowed_of_mem_allowedSub hk D test, mem_allowedSub_of_allowed hk D test⟩

lemma finrank_allowedSub {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) :
    Module.finrank (ZMod 2) (allowedSub hk D test) = (free hk D test).card :=
  finrank_span_blocks hk D test

lemma map_syndrome_allowedSub {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) (gap : ℕ) :
    Submodule.map (syndromeLM hk gap) (allowedSub hk D test) =
      Submodule.span (ZMod 2)
        (Set.range (fun i : ↥(free hk D test) =>
          syndrome hk gap (block hk D test i.val))) := by
  rw [allowedSub, Submodule.map_span]
  apply congrArg (Submodule.span (ZMod 2))
  ext z
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    exact (funext (syndromeLM_apply hk gap (block hk D test i.val))).symm
  · rintro ⟨i, rfl⟩
    refine ⟨block hk D test i.val, ⟨i, rfl⟩, ?_⟩
    exact funext (syndromeLM_apply hk gap (block hk D test i.val))

instance instFiniteAllowedSub {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) : Finite (allowedSub hk D test) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance instFintypeAllowedSub {s : ℕ} (D : Fin s → Fin k → ZMod 2)
    (test : Finset (Fin k)) : Fintype (allowedSub hk D test) :=
  Fintype.ofFinite _

lemma syndrome_add_left (gap : ℕ) (x y : Fin k → ZMod 2) :
    syndromeLM hk gap (x + y) = syndromeLM hk gap x + syndromeLM hk gap y :=
  map_add _ _ _

lemma syndrome_mix_zero_lm {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    (x : Fin k → ZMod 2) : syndromeLM hk gap (mix hk gap x) = 0 := by
  rw [← mix_mem_range_iff hk hgap h3]
  exact ⟨x, mixLM_apply hk gap x⟩

lemma syndrome_add_eq_of_eq (gap : ℕ) {x y : Fin k → ZMod 2}
    (h : syndromeLM hk gap x = syndromeLM hk gap y) :
    syndromeLM hk gap (x + y) = 0 := by
  rw [syndrome_add_left, h]
  ext i
  simp [Pi.add_apply, CharTwo.add_self_eq_zero]

lemma card_allowed_syn_fiber_of_mem {gap : ℕ} {s : ℕ}
    (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (a : Fin k → ZMod 2)
    (hS : syndromeLM hk gap a ∈
      Submodule.map (syndromeLM hk gap) (allowedSub hk D test)) :
    Fintype.card
      {d : allowedSub hk D test //
        syndromeLM hk gap d.val = syndromeLM hk gap a} =
      2 ^ ((free hk D test).card -
        Module.finrank (ZMod 2)
          (Submodule.map (syndromeLM hk gap) (allowedSub hk D test))) := by
  let φ : allowedSub hk D test →ₗ[ZMod 2]
      (Fin (Nat.gcd k gap) × Fin 2 → ZMod 2) :=
    (syndromeLM hk gap).comp (allowedSub hk D test).subtype
  have hrange :
      LinearMap.range φ =
        Submodule.map (syndromeLM hk gap) (allowedSub hk D test) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  obtain ⟨y, hy, hfy⟩ := Submodule.mem_map.mp hS
  let δ0 : allowedSub hk D test := ⟨y, hy⟩
  have hδ0 : φ δ0 = syndromeLM hk gap a := hfy
  haveI : Finite (LinearMap.ker φ) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Fintype (LinearMap.ker φ) := Fintype.ofFinite _
  let e : LinearMap.ker φ ≃
      {d : allowedSub hk D test //
        syndromeLM hk gap d.val = syndromeLM hk gap a} :=
    { toFun := fun v =>
        ⟨δ0 + (v : allowedSub hk D test), by
          have hadd : φ (δ0 + (v : allowedSub hk D test)) = φ δ0 + φ v :=
            φ.map_add _ _
          have hv : φ (v : allowedSub hk D test) = 0 :=
            LinearMap.mem_ker.mp v.property
          change syndromeLM hk gap (δ0 + (v : allowedSub hk D test)).val =
            syndromeLM hk gap a
          have : φ (δ0 + (v : allowedSub hk D test)) = syndromeLM hk gap a := by
            rw [hadd, hδ0, hv, add_zero]
          exact this⟩
      invFun := fun d =>
        ⟨d.val + δ0, by
          rw [LinearMap.mem_ker]
          have hadd : φ (d.val + δ0) = φ d.val + φ δ0 := φ.map_add _ _
          rw [hadd]
          change syndromeLM hk gap d.val.val + syndromeLM hk gap y = 0
          have hd : syndromeLM hk gap d.val.val = syndromeLM hk gap a := d.property
          rw [hd, hfy]
          ext i
          simp [Pi.add_apply, CharTwo.add_self_eq_zero]⟩
      left_inv := by
        intro v
        apply Subtype.ext
        ext j
        have hx : y j + y j = 0 := CharTwo.add_self_eq_zero (y j)
        simp [Pi.add_apply, allowedSub, Submodule.coe_add]
        change y j + (v : allowedSub hk D test).val j + y j =
          (v : allowedSub hk D test).val j
        rw [add_right_comm, hx, zero_add]
      right_inv := by
        intro d
        apply Subtype.ext
        apply Subtype.ext
        ext j
        have hx : y j + y j = 0 := CharTwo.add_self_eq_zero (y j)
        simp [Pi.add_apply, Submodule.coe_add]
        change y j + (d.val.val j + y j) = d.val.val j
        rw [add_comm (y j), add_assoc, hx, add_zero] }
  apply Eq.trans
  · convert (Fintype.card_congr e).symm
  · rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    have hd := finrank_allowedSub hk D test
    rw [hrange, hd] at hsum
    have hle :
        Module.finrank (ZMod 2)
          (Submodule.map (syndromeLM hk gap) (allowedSub hk D test)) ≤
          (free hk D test).card := by
      have : 0 ≤ Module.finrank (ZMod 2) (LinearMap.ker φ) := Nat.zero_le _
      omega
    have hker :
        Module.finrank (ZMod 2) (LinearMap.ker φ) =
          (free hk D test).card -
            Module.finrank (ZMod 2)
              (Submodule.map (syndromeLM hk gap) (allowedSub hk D test)) := by
      omega
    rw [hker]

lemma card_allowed_syn_fiber_of_not_mem {gap : ℕ} {s : ℕ}
    (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (a : Fin k → ZMod 2)
    (hS : syndromeLM hk gap a ∉
      Submodule.map (syndromeLM hk gap) (allowedSub hk D test)) :
    Fintype.card
      {d : allowedSub hk D test //
        syndromeLM hk gap d.val = syndromeLM hk gap a} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun d => hS ?_⟩
  exact Submodule.mem_map.mpr ⟨d.val.val, d.val.property, d.property⟩

lemma mix_add_self (gap : ℕ) (x a : Fin k → ZMod 2) :
    mix hk gap x = a + (mix hk gap x + a) := by
  ext j
  have hx : a j + a j = 0 := CharTwo.add_self_eq_zero (a j)
  simp [Pi.add_apply]
  rw [add_comm (a j), add_assoc, hx, add_zero]

lemma add_mix_cancel (gap : ℕ) (x a : Fin k → ZMod 2) :
    mix hk gap x + a + a = mix hk gap x := by
  ext j
  have hx : a j + a j = 0 := CharTwo.add_self_eq_zero (a j)
  simp [Pi.add_apply]
  rw [add_assoc, hx, add_zero]

lemma add_add_cancel_left (x a : Fin k → ZMod 2) : a + x + a = x := by
  ext j
  have hx : a j + a j = 0 := CharTwo.add_self_eq_zero (a j)
  simp [Pi.add_apply]
  rw [add_right_comm, hx, zero_add]

lemma card_solutions_of_mem {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (a : Fin k → ZMod 2)
    (hS : syndromeLM hk gap a ∈
      Submodule.map (syndromeLM hk gap) (allowedSub hk D test)) :
    ((univ : Finset (Fin k → ZMod 2)).filter
      (fun x => ∀ p, ∀ j ∈ test,
        out hk (mix hk gap x) (D p) j = out hk a (D p) j)).card =
      2 ^ (2 * Nat.gcd k gap + (free hk D test).card -
        Module.finrank (ZMod 2)
          (Submodule.map (syndromeLM hk gap) (allowedSub hk D test))) := by
  let Good :=
    {d : allowedSub hk D test //
      syndromeLM hk gap d.val = syndromeLM hk gap a}
  haveI : Fintype Good := Fintype.ofFinite _
  haveI : Fintype
      {x : Fin k → ZMod 2 //
        ∀ p, ∀ j ∈ test,
          out hk (mix hk gap x) (D p) j = out hk a (D p) j} :=
    Fintype.ofFinite _
  haveI : Fintype
      {x : Fin k → ZMod 2 // allowed hk D test (mix hk gap x + a)} :=
    Fintype.ofFinite _
  let e1 :
      {x : Fin k → ZMod 2 //
        ∀ p, ∀ j ∈ test,
          out hk (mix hk gap x) (D p) j = out hk a (D p) j} ≃
      {x : Fin k → ZMod 2 // allowed hk D test (mix hk gap x + a)} :=
    { toFun := fun x =>
        ⟨x.val, (out_eq_iff_allowed hk D test (mix hk gap x.val) a).mp x.property⟩
      invFun := fun x =>
        ⟨x.val, (out_eq_iff_allowed hk D test (mix hk gap x.val) a).mpr x.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl }
  let e2 :
      {x : Fin k → ZMod 2 // allowed hk D test (mix hk gap x + a)} ≃
        (δ : Good) × {x : Fin k → ZMod 2 // mix hk gap x = a + δ.1.val} :=
    { toFun := fun x =>
        let hmem : mix hk gap x.val + a ∈ allowedSub hk D test :=
          (mem_allowedSub_iff hk D test).mpr x.property
        let hsyn : syndromeLM hk gap (mix hk gap x.val + a) =
            syndromeLM hk gap a := by
          rw [syndrome_add_left, syndrome_mix_zero_lm hk hgap h3, zero_add]
        ⟨⟨⟨mix hk gap x.val + a, hmem⟩, hsyn⟩,
          ⟨x.val, mix_add_self hk gap x.val a⟩⟩
      invFun := fun p =>
        ⟨p.2.val, by
          have : mix hk gap p.2.val + a = p.1.1.val := by
            rw [p.2.property]
            exact add_add_cancel_left hk p.1.1.val a
          rw [this]
          exact allowed_of_mem_allowedSub hk D test p.1.1.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun p => by
        cases p with
        | mk δ x =>
          have hcoe : mix hk gap x.val + a = δ.val.val := by
            rw [x.property]
            exact add_add_cancel_left hk δ.val.val a
          refine Sigma.ext ?_ ?_
          · apply Subtype.ext
            apply Subtype.ext
            exact hcoe
          · dsimp
            exact (Subtype.heq_iff_coe_eq (fun z => by simp [hcoe])).2 rfl }
  have hfib : ∀ δ : Good,
      Fintype.card {x : Fin k → ZMod 2 // mix hk gap x = a + δ.1.val} =
        2 ^ (2 * Nat.gcd k gap) := by
    intro δ
    have hy : a + δ.1.val ∈ LinearMap.range (mixLM hk gap) := by
      rw [mix_mem_range_iff hk hgap h3, syndrome_add_left, δ.property]
      ext i
      simp [Pi.add_apply, CharTwo.add_self_eq_zero]
    haveI : Fintype {x : Fin k → ZMod 2 // mix hk gap x = a + δ.1.val} :=
      Fintype.ofFinite _
    rw [Fintype.card_subtype, card_mix_preimage_of_mem hk hgap h3 _ hy]
  rw [← Fintype.card_subtype]
  apply Eq.trans
  · convert Fintype.card_congr (e1.trans e2)
  · rw [Fintype.card_sigma]
    simp only [hfib]
    rw [Finset.sum_const, Finset.card_univ]
    have hle :
        Module.finrank (ZMod 2)
          (Submodule.map (syndromeLM hk gap) (allowedSub hk D test)) ≤
          (free hk D test).card := by
      have hd := finrank_allowedSub hk D test
      have hφ :
          Module.finrank (ZMod 2)
            (Submodule.map (syndromeLM hk gap) (allowedSub hk D test)) ≤
            Module.finrank (ZMod 2) (allowedSub hk D test) := by
        let φ : allowedSub hk D test →ₗ[ZMod 2]
            (Fin (Nat.gcd k gap) × Fin 2 → ZMod 2) :=
          (syndromeLM hk gap).comp (allowedSub hk D test).subtype
        have hsum := LinearMap.finrank_range_add_finrank_ker φ
        have : LinearMap.range φ =
            Submodule.map (syndromeLM hk gap) (allowedSub hk D test) := by
          rw [LinearMap.range_comp, Submodule.range_subtype]
        rw [this] at hsum
        have : 0 ≤ Module.finrank (ZMod 2) (LinearMap.ker φ) := Nat.zero_le _
        omega
      exact hφ.trans (le_of_eq hd)
    have hG :
        Fintype.card Good =
          2 ^ ((free hk D test).card -
            Module.finrank (ZMod 2)
              (Submodule.map (syndromeLM hk gap) (allowedSub hk D test))) := by
      convert card_allowed_syn_fiber_of_mem hk D test a hS
    rw [hG, Nat.nsmul_eq_mul, Nat.mul_comm, ← pow_add, Nat.add_sub_assoc hle]

lemma card_solutions_of_not_mem {gap : ℕ} (hgap : gap = 1 ∨ gap = 2) (h3 : 3 ∣ k)
    {s : ℕ} (D : Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (a : Fin k → ZMod 2)
    (hS : syndromeLM hk gap a ∉
      Submodule.map (syndromeLM hk gap) (allowedSub hk D test)) :
    ((univ : Finset (Fin k → ZMod 2)).filter
      (fun x => ∀ p, ∀ j ∈ test,
        out hk (mix hk gap x) (D p) j = out hk a (D p) j)).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x _ hx
  have hall : allowed hk D test (mix hk gap x + a) :=
    (out_eq_iff_allowed hk D test (mix hk gap x) a).mp hx
  have hmem : mix hk gap x + a ∈ allowedSub hk D test :=
    (mem_allowedSub_iff hk D test).mpr hall
  have hsyn : syndromeLM hk gap (mix hk gap x + a) = syndromeLM hk gap a := by
    rw [syndrome_add_left, syndrome_mix_zero_lm hk hgap h3, zero_add]
  exact hS (Submodule.mem_map.mpr ⟨mix hk gap x + a, hmem, hsyn⟩)

end PEqualNP.Outside.L_meta_25927

open PEqualNP.Outside

theorem PEqualNP.Outside.L_meta_25927 : (∀ (k s gap : Nat) (hk : 0 < k), (gap = 1 ∨ gap = 2) → 3 ∣ k →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun t : Nat => (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k)
  ∀ (D : Fin s → W) (test : Finset (Fin k)),
  let color := fun (j : Fin k) (p : Fin s) => D p j
  let chi := fun (x : W) (j : Fin k) => x j + (1+x (ix (j.val+1))) * x (ix (j.val+2))
  let out := fun (x : W) (p : Fin s) (j : Fin k) => chi (x+D p) j - chi x j
  let edge := fun (u v : Fin k) => ∃ j ∈ test,
    u = ix (j.val+1) ∧ v = ix (j.val+2) ∧ color u = color v ∧ color u ≠ 0
  let joined := fun u v => @decide (Relation.EqvGen edge u v) (Classical.propDecidable _)
  let pinned := fun (z : Fin k) => ∃ j ∈ test,
    let u := ix (j.val+1)
    let v := ix (j.val+2)
    color u ≠ color v ∧ ((z = u ∧ color v ≠ 0) ∨ (z = v ∧ color u ≠ 0))
  let free := (Finset.univ : Finset (Fin k)).filter (fun i =>
    (∀ j, joined i j = true → i.val ≤ j.val) ∧ (∀ j, joined i j = true → ¬pinned j))
  let mix := fun (x : W) (j : Fin k) => x j + x (ix (j.val+gap)) + x (ix (j.val+k-gap % k))
  let g := Nat.gcd k gap
  let syndrome := fun (x : W) (a : Fin g × Fin 2) =>
    ∑ t ∈ Finset.range (k/g),
      (if t % 3 = a.2.val ∨ t % 3 = 2 then x (ix (a.1.val+t*gap)) else 0)
  let block := fun (i : Fin k) (z : Fin k) => (if joined i z = true then 1 else 0 : F)
  let span := Submodule.span F (Set.range (fun i : ↥free => syndrome (block i.val)))
  ∀ a : W,
    ((Finset.univ : Finset W).filter
      (fun x => ∀ p, ∀ j ∈ test, out (mix x) p j = out a p j)).card =
      (if @decide (syndrome a ∈ span) (Classical.propDecidable _) then
        2^(2*g + free.card - Module.finrank F span) else 0)) := by
  intro k s gap hk hgap h3 F W ix D test color chi out edge joined pinned free
    mix g syndrome block span a
  have hmix : mix = L_meta_25927.mix hk gap := rfl
  have hout (x : W) (p : Fin s) (j : Fin k) :
      out x p j = L_meta_25927.out hk x (D p) j := rfl
  have hsyn (x : W) : syndrome x = L_meta_25927.syndrome hk gap x := rfl
  have hsynLM (x : W) : syndrome x = L_meta_25927.syndromeLM hk gap x := by
    rw [hsyn x]
    exact (funext (L_meta_25927.syndromeLM_apply hk gap x)).symm
  have hg : g = Nat.gcd k gap := rfl
  have hblock : block = L_meta_25927.block hk D test := rfl
  have hfree : free = L_meta_25927.free hk D test := by
    ext i
    constructor
    · intro hi
      have hpred := (Finset.mem_filter.mp hi).2
      exact (L_meta_25927.mem_free_iff hk D test i).mpr hpred
    · intro hi
      have hpred := (L_meta_25927.mem_free_iff hk D test i).mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpred⟩
  have hspan :
      span =
        Submodule.map (L_meta_25927.syndromeLM hk gap)
          (L_meta_25927.allowedSub hk D test) := by
    rw [L_meta_25927.map_syndrome_allowedSub]
    apply congrArg (Submodule.span (ZMod 2))
    ext y
    simp only [Set.mem_range]
    constructor
    · rintro ⟨⟨i, hi⟩, rfl⟩
      have hi' : i ∈ L_meta_25927.free hk D test := by
        simpa [hfree] using hi
      refine ⟨⟨i, hi'⟩, ?_⟩
      simp [hsyn, hblock]
    · rintro ⟨⟨i, hi⟩, rfl⟩
      have hi' : i ∈ free := by
        simpa [hfree] using hi
      refine ⟨⟨i, hi'⟩, ?_⟩
      simp [hsyn, hblock]
  have hfilter :
      ((Finset.univ : Finset W).filter
        (fun x => ∀ p, ∀ j ∈ test, out (mix x) p j = out a p j)) =
        ((Finset.univ : Finset (Fin k → ZMod 2)).filter
          (fun x => ∀ p, ∀ j ∈ test,
            L_meta_25927.out hk (L_meta_25927.mix hk gap x) (D p) j =
              L_meta_25927.out hk a (D p) j)) := by
    refine Finset.filter_congr ?_
    intro x _
    simp [hmix, hout]
  have hexp :
      2 * g + free.card - Module.finrank F span =
        2 * Nat.gcd k gap + (L_meta_25927.free hk D test).card -
          Module.finrank (ZMod 2)
            (Submodule.map (L_meta_25927.syndromeLM hk gap)
              (L_meta_25927.allowedSub hk D test)) := by
    rw [hfree, hspan]
  cases hdec : (@decide (syndrome a ∈ span) (Classical.propDecidable _) : Bool) with
  | true =>
    have hmem : syndrome a ∈ span :=
      @of_decide_eq_true (syndrome a ∈ span) (Classical.propDecidable _) hdec
    have hS :
        L_meta_25927.syndromeLM hk gap a ∈
          Submodule.map (L_meta_25927.syndromeLM hk gap)
            (L_meta_25927.allowedSub hk D test) := by
      rw [← hsynLM, ← hspan]
      exact hmem
    rw [hfilter]
    change _ = 2 ^ (2 * g + free.card - Module.finrank F span)
    rw [hexp]
    exact L_meta_25927.card_solutions_of_mem hk hgap h3 D test a hS
  | false =>
    have hnmem : syndrome a ∉ span :=
      @of_decide_eq_false (syndrome a ∈ span) (Classical.propDecidable _) hdec
    have hS :
        L_meta_25927.syndromeLM hk gap a ∉
          Submodule.map (L_meta_25927.syndromeLM hk gap)
            (L_meta_25927.allowedSub hk D test) := by
      intro h
      apply hnmem
      rw [hsynLM, hspan]
      exact h
    rw [hfilter]
    change _ = 0
    exact L_meta_25927.card_solutions_of_not_mem hk hgap h3 D test a hS
