import PEqualNP.Defs
import Mathlib.Data.Nat.Fib.Basic

namespace PEqualNP.Outside.L_meta_32032_aux

def ix {k : ℕ} (hk : 0 < k) (pos : ℕ) : Fin k := ⟨pos % k, Nat.mod_lt _ hk⟩

lemma ix_eq_iff {k : ℕ} (hk : 0 < k) (a b : ℕ) : ix hk a = ix hk b ↔ a % k = b % k := by
  simp [ix, Fin.ext_iff]

lemma ix_add_k {k : ℕ} (hk : 0 < k) (a : ℕ) : ix hk (a + k) = ix hk a := by
  rw [ix_eq_iff, Nat.add_mod_right]

lemma ix_self {k : ℕ} (hk : 0 < k) (a : Fin k) : ix hk a.val = a := by
  ext
  exact Nat.mod_eq_of_lt a.2

lemma ix_val_add {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ix hk ((ix hk a).val + b) = ix hk (a + b) := by
  rw [ix_eq_iff]
  simp only [ix]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ix_add_sub_mod {k : ℕ} (hk : 0 < k) (a s : ℕ) :
    ix hk ((ix hk a).val + k - s % k) = ix hk (a + (k - s % k)) := by
  have hs : s % k < k := Nat.mod_lt _ hk
  have h1 : (ix hk a).val + k - s % k = (ix hk a).val + (k - s % k) := by omega
  rw [h1, ix_val_add]

lemma ix_sub_add_one {k : ℕ} (hk : 0 < k) (p : Fin k) :
    ix hk ((ix hk (p.val + k - 1)).val + 1) = p := by
  rw [ix_val_add]
  have h1 : p.val + k - 1 + 1 = p.val + k := by omega
  rw [h1, ix_add_k, ix_self]

lemma ix_sub_add_two {k : ℕ} (hk : 0 < k) (p : Fin k) :
    ix hk ((ix hk (p.val + k - 1)).val + 2) = ix hk (p.val + 1) := by
  rw [ix_val_add]
  have h1 : p.val + k - 1 + 2 = (p.val + 1) + k := by omega
  rw [h1, ix_add_k]

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

lemma zmod2_sum_three_cancel (a b : ZMod 2) : a + b + (a + b) = 0 := by
  fin_cases a <;> fin_cases b <;> decide

def rotLin {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  { toFun := fun w j => w (ix hk (j.val + k - s % k))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

lemma rotLin_bijective {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Function.Bijective (rotLin hk s) := by
  let inv : (Fin k → ZMod 2) → (Fin k → ZMod 2) := fun w j => w (ix hk (j.val + s % k))
  have hs : s % k < k := Nat.mod_lt _ hk
  have h1 : ∀ w, inv (rotLin hk s w) = w := by
    intro w
    ext j
    simp only [inv, rotLin, LinearMap.coe_mk, AddHom.coe_mk]
    have hidx : ix hk ((ix hk (j.val + s % k)).val + k - s % k) = j := by
      rw [ix_add_sub_mod hk (j.val + s % k) s]
      have heq : j.val + s % k + (k - s % k) = j.val + k := by omega
      rw [heq, ix_add_k, ix_self]
    rw [hidx]
  have h2 : ∀ w, rotLin hk s (inv w) = w := by
    intro w
    ext j
    simp only [inv, rotLin, LinearMap.coe_mk, AddHom.coe_mk]
    have hidx : ix hk ((ix hk (j.val + k - s % k)).val + s % k) = j := by
      rw [ix_val_add]
      have heq : j.val + k - s % k + s % k = j.val + k := by omega
      rw [heq, ix_add_k, ix_self]
    rw [hidx]
  exact Function.bijective_iff_has_inverse.mpr ⟨inv, h1, h2⟩

def mixLin {k : ℕ} (hk : 0 < k) (d : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  { toFun := fun z m => z m + z (ix hk (m.val + d)) + z (ix hk (m.val + k - d % k))
    map_add' := fun x y => by ext m; simp only [Pi.add_apply]; ring
    map_smul' := fun c x => by ext m; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

def orb {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) : Fin k :=
  ix hk (r.val + t * d)

lemma orb_add_one {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) :
    ix hk ((orb hk d r t).val + d) = orb hk d r (t + 1) := by
  simp only [orb, ix_val_add]
  congr 1; ring

lemma orb_sub_one {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) :
    ix hk ((orb hk d r (t + 1)).val + k - d % k) = orb hk d r t := by
  simp only [orb, ix_add_sub_mod]
  rw [ix_eq_iff]
  have hd : d % k < k := Nat.mod_lt _ hk
  have htd : (t + 1) * d = t * d + d := by ring
  have h1 : r.val + (t + 1) * d + (k - d % k) = (r.val + t * d) + (d + k - d % k) := by
    rw [htd]; omega
  rw [h1, Nat.add_mod]
  have h2 : (d + k - d % k) % k = 0 := by
    have hdiv := Nat.div_add_mod d k
    have hmul : (d / k + 1) * k = k * (d / k) + k := by ring
    have h3 : d + k - d % k = (d / k + 1) * k := by rw [hmul]; omega
    rw [h3, Nat.mul_mod_left]
  rw [h2, Nat.add_zero, Nat.mod_mod]

lemma orb_period {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) :
    orb hk d r (t + k / Nat.gcd k d) = orb hk d r t := by
  simp only [orb, ix_eq_iff]
  have hg0 : 0 < Nat.gcd k d := Nat.gcd_pos_of_pos_left d hk
  have h1k : Nat.gcd k d * (k / Nat.gcd k d) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k d)
  have h1d : Nat.gcd k d * (d / Nat.gcd k d) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right k d)
  have hmul : (k / Nat.gcd k d) * d = k * (d / Nat.gcd k d) := by
    apply Nat.eq_of_mul_eq_mul_left hg0
    calc
      Nat.gcd k d * ((k / Nat.gcd k d) * d) = (Nat.gcd k d * (k / Nat.gcd k d)) * d := by ring
      _ = k * d := by rw [h1k]
      _ = k * (Nat.gcd k d * (d / Nat.gcd k d)) := by rw [h1d]
      _ = Nat.gcd k d * (k * (d / Nat.gcd k d)) := by ring
  have h1 : r.val + (t + k / Nat.gcd k d) * d = (r.val + t * d) + k * (d / Nat.gcd k d) := by
    rw [Nat.add_mul, hmul]; ring
  rw [h1, Nat.add_mul_mod_self_left]

lemma orb_bijective {k : ℕ} (hk : 0 < k) (d : ℕ) (hd : 0 < d) :
    Function.Bijective (fun p : Fin (Nat.gcd k d) × Fin (k / Nat.gcd k d) =>
      orb hk d p.1 p.2.val) := by
  have hg_pos : 0 < Nat.gcd k d := Nat.gcd_pos_of_pos_left d hk
  have hg_dvd_k : Nat.gcd k d ∣ k := Nat.gcd_dvd_left k d
  have hg_dvd_d : Nat.gcd k d ∣ d := Nat.gcd_dvd_right k d
  have hk_eq : Nat.gcd k d * (k / Nat.gcd k d) = k := Nat.mul_div_cancel' hg_dvd_k
  have hd_eq : Nat.gcd k d * (d / Nat.gcd k d) = d := Nat.mul_div_cancel' hg_dvd_d
  have hcop : Nat.Coprime (k / Nat.gcd k d) (d / Nat.gcd k d) :=
    Nat.coprime_div_gcd_div_gcd hg_pos
  have hcard : Fintype.card (Fin (Nat.gcd k d) × Fin (k / Nat.gcd k d)) = Fintype.card (Fin k) := by
    simp [hk_eq]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, hcard⟩
  intro ⟨r1, t1⟩ ⟨r2, t2⟩ heq
  simp only [orb, ix_eq_iff] at heq
  have hr_eq : r1 = r2 := by
    have hmod_g : ∀ a, (a % k) % Nat.gcd k d = a % Nat.gcd k d := fun a =>
      Nat.mod_mod_of_dvd a hg_dvd_k
    have h1 := congrArg (fun x => x % Nat.gcd k d) heq
    rw [hmod_g, hmod_g] at h1
    have hmul_g : ∀ t, (t * d) % Nat.gcd k d = 0 := fun t =>
      Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hg_dvd_d t)
    rw [Nat.add_mod, hmul_g, Nat.add_zero, Nat.mod_mod,
      Nat.add_mod, hmul_g, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt r1.2, Nat.mod_eq_of_lt r2.2] at h1
    exact Fin.ext h1
  subst hr_eq
  have ht_eq : t1 = t2 := by
    have haux : ∀ a b : Fin (k / Nat.gcd k d), a.val ≤ b.val →
        (r1.val + a.val * d) % k = (r1.val + b.val * d) % k → a = b := by
      intro a b hab hmod
      have hdvd : k ∣ (r1.val + b.val * d) - (r1.val + a.val * d) := by
        exact (Nat.modEq_iff_dvd' (by nlinarith)).mp hmod
      have hsub : (r1.val + b.val * d) - (r1.val + a.val * d) = (b.val - a.val) * d := by
        rw [Nat.add_sub_add_left, ← Nat.sub_mul]
      have hdvd' : (Nat.gcd k d * (k / Nat.gcd k d)) ∣
          (b.val - a.val) * (Nat.gcd k d * (d / Nat.gcd k d)) := by
        rwa [hk_eq, hd_eq, ← hsub]
      have hdvd2 : (k / Nat.gcd k d) ∣ (b.val - a.val) * (d / Nat.gcd k d) := by
        have hrew : (b.val - a.val) * (Nat.gcd k d * (d / Nat.gcd k d)) =
            Nat.gcd k d * ((b.val - a.val) * (d / Nat.gcd k d)) := by ring
        rw [hrew] at hdvd'
        exact (mul_dvd_mul_iff_left (ne_of_gt hg_pos)).mp hdvd'
      have hdvd3 : (k / Nat.gcd k d) ∣ (b.val - a.val) := hcop.dvd_of_dvd_mul_right hdvd2
      have hlt : b.val - a.val < k / Nat.gcd k d := by omega
      have h0 : b.val - a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd3 hlt
      ext; omega
    by_cases hle : t1.val ≤ t2.val
    · exact haux t1 t2 hle heq
    · exact (haux t2 t1 (by omega) heq.symm).symm
  subst ht_eq
  rfl

lemma ker_seq_period3 {k : ℕ} (hk : 0 < k) (d : ℕ)
    (z : Fin k → ZMod 2) (hz : mixLin hk d z = 0)
    (r : Fin (Nat.gcd k d)) (t : ℕ) :
    z (orb hk d r t) =
      if t % 3 = 0 then z (orb hk d r 0)
      else if t % 3 = 1 then z (orb hk d r 1)
      else z (orb hk d r 0) + z (orb hk d r 1) := by
  have hstep : ∀ n : ℕ, z (orb hk d r (n + 2)) = z (orb hk d r (n + 1)) + z (orb hk d r n) := by
    intro n
    have h0 := congrFun hz (orb hk d r (n + 1))
    simp only [mixLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
    rw [orb_add_one hk d r (n + 1), orb_sub_one hk d r n] at h0
    have h1 := congrArg (fun x => x + z (orb hk d r (n + 2))) h0
    simp only [zero_add] at h1
    have hlhs : z (orb hk d r (n + 1)) + z (orb hk d r (n + 2)) + z (orb hk d r n) +
        z (orb hk d r (n + 2)) = z (orb hk d r (n + 1)) + z (orb hk d r n) := by
      have hz2 := zmod2_add_self (z (orb hk d r (n + 2)))
      calc
        z (orb hk d r (n + 1)) + z (orb hk d r (n + 2)) + z (orb hk d r n) +
            z (orb hk d r (n + 2))
            = z (orb hk d r (n + 1)) + z (orb hk d r n) +
              (z (orb hk d r (n + 2)) + z (orb hk d r (n + 2))) := by ring
        _ = z (orb hk d r (n + 1)) + z (orb hk d r n) := by rw [hz2, add_zero]
    rw [hlhs] at h1
    exact h1.symm
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    match t with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      rw [hstep n, ih (n + 1) (by omega), ih n (by omega)]
      have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hmod with h0 | h1 | h2
      · have h1' : (n + 1) % 3 = 1 := by omega
        have h2' : (n + 2) % 3 = 2 := by omega
        simp only [h0, h1', h2', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one]
        ring
      · have h1' : (n + 1) % 3 = 2 := by omega
        have h2' : (n + 2) % 3 = 0 := by omega
        simp only [h1, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_add_self (z (orb hk d r 1))
        calc
          z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 1)
              = z (orb hk d r 0) + (z (orb hk d r 1) + z (orb hk d r 1)) := by ring
          _ = z (orb hk d r 0) := by rw [this, add_zero]
      · have h1' : (n + 1) % 3 = 0 := by omega
        have h2' : (n + 2) % 3 = 1 := by omega
        simp only [h2, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_add_self (z (orb hk d r 0))
        calc
          z (orb hk d r 0) + (z (orb hk d r 0) + z (orb hk d r 1))
              = (z (orb hk d r 0) + z (orb hk d r 0)) + z (orb hk d r 1) := by ring
          _ = z (orb hk d r 1) := by rw [this, zero_add]

lemma finrank_ker_mixLin {k : ℕ} (hk : 0 < k) (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (LinearMap.ker (mixLin hk d)) =
      if 3 ∣ k / Nat.gcd k d then 2 * Nat.gcd k d else 0 := by
  let g := Nat.gcd k d
  let L := k / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hk
  have hg_dvd_k : g ∣ k := Nat.gcd_dvd_left k d
  have hL_pos : 0 < L := Nat.div_pos (Nat.le_of_dvd hk hg_dvd_k) hg_pos
  let e : (Fin g × Fin L) ≃ Fin k := Equiv.ofBijective _ (orb_bijective hk d hd)
  split_ifs with hsing
  · have hL3 : 3 ≤ L := Nat.le_of_dvd hL_pos hsing
    let mkVec : (Fin g × Fin 2 → ZMod 2) → (Fin k → ZMod 2) := fun a v =>
      let p := e.symm v
      if p.2.val % 3 = 0 then a (p.1, 0)
      else if p.2.val % 3 = 1 then a (p.1, 1)
      else a (p.1, 0) + a (p.1, 1)
    have hmk_orb : ∀ a (r : Fin g) (t : ℕ),
        mkVec a (orb hk d r t) =
          if t % 3 = 0 then a (r, 0)
          else if t % 3 = 1 then a (r, 1)
          else a (r, 0) + a (r, 1) := by
      intro a r t
      have hdiv : t = (t / L) * L + t % L := (Nat.div_add_mod' t L).symm
      have horb_mod : orb hk d r t = orb hk d r (t % L) := by
        have hstep : ∀ q : ℕ, orb hk d r (q * L + t % L) = orb hk d r (t % L) := by
          intro q
          induction q with
          | zero => simp
          | succ q ih =>
            rw [show (q + 1) * L + t % L = (q * L + t % L) + L by ring, orb_period, ih]
        conv_lhs => rw [hdiv]
        exact hstep (t / L)
      have he_symm : e.symm (orb hk d r (t % L)) = (r, ⟨t % L, Nat.mod_lt _ hL_pos⟩) := by
        apply e.injective
        rw [Equiv.apply_symm_apply]
        rfl
      have hmod3 : (t % L) % 3 = t % 3 := Nat.mod_mod_of_dvd t hsing
      simp only [mkVec, horb_mod, he_symm, hmod3]
    have hmk_ker : ∀ a, mixLin hk d (mkVec a) = 0 := by
      intro a
      ext v
      have hv : v = orb hk d (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
      let r := (e.symm v).1
      let t := (e.symm v).2.val
      have hv_eq : v = orb hk d r (t + L) := by
        rw [orb_period]; exact hv
      simp only [mixLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      rw [hv_eq, orb_add_one, show t + L = (t + L - 1) + 1 by omega, orb_sub_one]
      rw [hmk_orb, hmk_orb, hmk_orb]
      have hmod : (t + L - 1) % 3 = 0 ∨ (t + L - 1) % 3 = 1 ∨ (t + L - 1) % 3 = 2 := by omega
      rcases hmod with h0 | h1 | h2
      · have h1' : (t + L - 1 + 1) % 3 = 1 := by omega
        have h2' : (t + L - 1 + 1 + 1) % 3 = 2 := by omega
        simp only [h0, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_sum_three_cancel (a (r, 0)) (a (r, 1))
        calc
          a (r, 1) + (a (r, 0) + a (r, 1)) + a (r, 0)
              = a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) := by ring
          _ = 0 := this
      · have h1' : (t + L - 1 + 1) % 3 = 2 := by omega
        have h2' : (t + L - 1 + 1 + 1) % 3 = 0 := by omega
        simp only [h1, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_sum_three_cancel (a (r, 0)) (a (r, 1))
        calc
          a (r, 0) + a (r, 1) + a (r, 0) + a (r, 1)
              = a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) := by ring
          _ = 0 := this
      · have h1' : (t + L - 1 + 1) % 3 = 0 := by omega
        have h2' : (t + L - 1 + 1 + 1) % 3 = 1 := by omega
        simp only [h2, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        exact zmod2_sum_three_cancel (a (r, 0)) (a (r, 1))
    let Ψ : (Fin g × Fin 2 → ZMod 2) →ₗ[ZMod 2] LinearMap.ker (mixLin hk d) :=
      { toFun := fun a => ⟨mkVec a, hmk_ker a⟩
        map_add' := fun a1 a2 => by
          apply Subtype.ext; ext v; simp only [mkVec, Submodule.coe_add, Pi.add_apply]
          split_ifs <;> ring
        map_smul' := fun c a => by
          apply Subtype.ext; ext v
          simp only [mkVec, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> ring }
    have hΨ_bij : Function.Bijective Ψ := by
      constructor
      · intro a1 a2 heq
        have hval : mkVec a1 = mkVec a2 := congrArg Subtype.val heq
        ext ⟨r, c⟩
        fin_cases c
        · have h0 := congrFun hval (orb hk d r 0)
          simpa [hmk_orb] using h0
        · have h1 := congrFun hval (orb hk d r 1)
          simpa [hmk_orb] using h1
      · rintro ⟨z, hz⟩
        let a : Fin g × Fin 2 → ZMod 2 := fun rc =>
          if rc.2.val = 0 then z (orb hk d rc.1 0) else z (orb hk d rc.1 1)
        refine ⟨a, ?_⟩
        apply Subtype.ext
        ext v
        have hv : v = orb hk d (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
        conv_lhs => rw [hv]
        conv_rhs => rw [hv]
        change mkVec a (orb hk d (e.symm v).1 (e.symm v).2.val) =
          z (orb hk d (e.symm v).1 (e.symm v).2.val)
        rw [hmk_orb, ker_seq_period3 hk d z hz]
        simp [a]
    have hequiv := LinearEquiv.ofBijective Ψ hΨ_bij
    rw [← hequiv.finrank_eq]
    simp [g, Nat.mul_comm]
  · have hker_bot : LinearMap.ker (mixLin hk d) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro z hz
      ext v
      have hv : v = orb hk d (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
      rw [hv]
      let r := (e.symm v).1
      have h0 : z (orb hk d r L) = z (orb hk d r 0) := by
        simpa using congrArg z (orb_period hk d r 0)
      have h1 : z (orb hk d r (L + 1)) = z (orb hk d r 1) := by
        have hp := orb_period hk d r 1
        rw [show 1 + L = L + 1 by omega] at hp
        exact congrArg z hp
      rw [ker_seq_period3 hk d z hz r L] at h0
      rw [ker_seq_period3 hk d z hz r (L + 1)] at h1
      have hmod : L % 3 = 1 ∨ L % 3 = 2 := by
        have hne : L % 3 ≠ 0 := fun h => hsing (Nat.dvd_of_mod_eq_zero h)
        omega
      have hzero01 : z (orb hk d r 0) = 0 ∧ z (orb hk d r 1) = 0 := by
        rcases hmod with hm1 | hm2
        · have hm1' : (L + 1) % 3 = 2 := by omega
          simp only [hm1, hm1', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
            OfNat.ofNat_ne_one] at h0 h1
          have hz0 : z (orb hk d r 0) = 0 := by
            have := congrArg (fun x => x + z (orb hk d r 1)) h1
            have hrhs : z (orb hk d r 1) + z (orb hk d r 1) = 0 := zmod2_add_self _
            have hlhs : z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 1) =
                z (orb hk d r 0) := by
              rw [add_assoc, hrhs, add_zero]
            rw [hlhs, hrhs] at this
            exact this
          exact ⟨hz0, by rw [h0, hz0]⟩
        · have hm2' : (L + 1) % 3 = 0 := by omega
          simp only [hm2, hm2', ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at h0 h1
          have hz1 : z (orb hk d r 1) = 0 := by
            have := congrArg (fun x => x + z (orb hk d r 0)) h0
            have hrhs : z (orb hk d r 0) + z (orb hk d r 0) = 0 := zmod2_add_self _
            have hlhs : z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 0) =
                z (orb hk d r 1) := by
              calc
                z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 0)
                    = (z (orb hk d r 0) + z (orb hk d r 0)) + z (orb hk d r 1) := by ring
                _ = z (orb hk d r 1) := by rw [hrhs, zero_add]
            rw [hlhs, hrhs] at this
            exact this
          exact ⟨by rw [h1, hz1], hz1⟩
      rw [ker_seq_period3 hk d z hz r (e.symm v).2.val, hzero01.1, hzero01.2]
      simp
    rw [hker_bot]
    simp

lemma finrank_ker_mixLin_gap {k : ℕ} (hk : 0 < k) (column : Bool) :
    Module.finrank (ZMod 2) (LinearMap.ker (mixLin hk (if column then 2 else 1))) =
      if 3 ∣ k then (if column = true ∧ 2 ∣ k then 4 else 2) else 0 := by
  have hd : 0 < (if column then 2 else 1) := by cases column <;> decide
  rw [finrank_ker_mixLin hk _ hd]
  cases column
  · simp only [Bool.false_eq_true, false_and, ↓reduceIte, Nat.gcd_one_right, Nat.div_one]
  · simp only [↓reduceIte, true_and]
    by_cases h2 : 2 ∣ k
    · have hg : Nat.gcd k 2 = 2 := Nat.gcd_eq_right h2
      rw [hg]
      have h3 : (3 ∣ k / 2) ↔ (3 ∣ k) := by
        obtain ⟨m, rfl⟩ := h2
        rw [Nat.mul_div_cancel_left m (by decide : 0 < 2)]
        exact ⟨fun ⟨t, ht⟩ => ⟨2 * t, by linarith⟩,
               fun h => (Nat.Coprime.dvd_of_dvd_mul_left (by decide : Nat.Coprime 3 2) h)⟩
      simp [h3, h2]
    · have hg : Nat.gcd k 2 = 1 := by
        have hle : Nat.gcd k 2 ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right k 2)
        have hpos : 0 < Nat.gcd k 2 := Nat.gcd_pos_of_pos_right k (by decide)
        have hne2 : Nat.gcd k 2 ≠ 2 := fun h => h2 (h ▸ Nat.gcd_dvd_left k 2)
        omega
      rw [hg, Nat.div_one]
      simp [h2]

def Bval (k p : ℕ) : ℕ :=
  if p = 0 then Nat.fib (k - 1) + Nat.fib (k + 1)
  else if 2 * p < k then 2 ^ (p - 1) * Nat.fib (k - 2 * p + 3)
  else 2 ^ (k - p)

lemma fib_succ_le_two_mul {n : ℕ} (hn : 1 ≤ n) : Nat.fib (n + 1) ≤ 2 * Nat.fib n := by
  cases n with
  | zero => omega
  | succ m =>
    rw [show m + 1 + 1 = m + 2 from rfl, Nat.fib_add_two]
    have hm := Nat.fib_mono (show m ≤ m + 1 by omega)
    omega

lemma fib_add_two_le_three_mul {n : ℕ} (hn : 1 ≤ n) : Nat.fib (n + 2) ≤ 3 * Nat.fib n := by
  cases n with
  | zero => omega
  | succ m =>
    rw [show m + 1 + 2 = (m + 1) + 2 from rfl, Nat.fib_add_two,
        show m + 1 + 1 = m + 2 from rfl, Nat.fib_add_two]
    have hm := Nat.fib_mono (show m ≤ m + 1 by omega)
    omega

lemma fib_merge (a b : ℕ) :
    Nat.fib (a + 2) * Nat.fib (b + 2) ≤ 2 * Nat.fib (a + b + 1) := by
  have hadd : ∀ m n, Nat.fib (m + n + 1) = Nat.fib m * Nat.fib n + Nat.fib (m + 1) * Nat.fib (n + 1) := by
    intro m
    induction m with
    | zero => intro n; simp
    | succ m ih =>
      intro n
      have h1 : m + 1 + n + 1 = m + (n + 1) + 1 := by omega
      rw [h1, ih (n + 1), Nat.fib_add_two, Nat.fib_add_two]
      ring
  rw [hadd a b, Nat.fib_add_two, Nat.fib_add_two]
  have h1 : Nat.fib a ≤ Nat.fib (a + 1) := Nat.fib_mono (Nat.le_succ a)
  have h2 : Nat.fib b ≤ Nat.fib (b + 1) := Nat.fib_mono (Nat.le_succ b)
  nlinarith

lemma fib_le_two_pow (m : ℕ) : Nat.fib (m + 2) ≤ 2 ^ m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    match m with
    | 0 => decide
    | 1 => decide
    | m + 2 =>
      rw [show m + 2 + 2 = (m + 2) + 2 from rfl, Nat.fib_add_two, show m + 2 + 1 = m + 1 + 2 from rfl]
      have h1 := ih m (by omega)
      have h2 := ih (m + 1) (by omega)
      have hp : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ]; ring
      have hp2 : 2 ^ m ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega

lemma Bval_le_two_mul_succ (k p : ℕ) (hk : 2 ≤ k) :
    Bval k p ≤ 2 * Bval k (p + 1) := by
  unfold Bval
  by_cases hp0 : p = 0
  · subst hp0
    simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.sub_self, pow_zero, one_mul,
      Nat.add_sub_cancel]
    split_ifs with h2
    · have hle : Nat.fib (k - 1) ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
      have heq : k - 2 * 1 + 3 = k + 1 := by omega
      rw [heq]; omega
    · have hk2 : k = 2 := by omega
      subst hk2; decide
  · simp only [hp0, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
    by_cases h1 : 2 * p < k <;> by_cases h2 : 2 * (p + 1) < k <;> simp only [h1, h2, ↓reduceIte]
    · have heq : k - 2 * p + 3 = (k - 2 * (p + 1) + 3) + 2 := by omega
      rw [heq]
      have hfib := fib_add_two_le_three_mul (show 1 ≤ k - 2 * (p + 1) + 3 by omega)
      have hp2 : 2 * (2 ^ p * Nat.fib (k - 2 * (p + 1) + 3)) =
          4 * (2 ^ (p - 1) * Nat.fib (k - 2 * (p + 1) + 3)) := by
        cases p with | zero => omega | succ q => simp [pow_succ]; ring
      rw [hp2]
      calc 2 ^ (p - 1) * Nat.fib (k - 2 * (p + 1) + 3 + 2)
          ≤ 2 ^ (p - 1) * (3 * Nat.fib (k - 2 * (p + 1) + 3)) := Nat.mul_le_mul_left _ hfib
        _ ≤ 4 * (2 ^ (p - 1) * Nat.fib (k - 2 * (p + 1) + 3)) := by
            have : 2 ^ (p - 1) * (3 * Nat.fib (k - 2 * (p + 1) + 3)) =
                3 * (2 ^ (p - 1) * Nat.fib (k - 2 * (p + 1) + 3)) := by ring
            omega
    · have hcase : k = 2 * p + 1 ∨ k = 2 * p + 2 := by omega
      rcases hcase with rfl | rfl
      · rw [show 2 * p + 1 - 2 * p + 3 = 4 by omega, show 2 * p + 1 - (p + 1) = p by omega]
        have hf4 : Nat.fib 4 = 3 := rfl
        rw [hf4]
        cases p with | zero => omega | succ q => rw [Nat.add_sub_cancel, pow_succ]; omega
      · rw [show 2 * p + 2 - 2 * p + 3 = 5 by omega, show 2 * p + 2 - (p + 1) = p + 1 by omega]
        have hf5 : Nat.fib 5 = 5 := rfl
        rw [hf5]
        cases p with | zero => omega | succ q => simp [pow_succ]; omega
    · omega
    · by_cases hpk : p + 1 ≤ k
      · rw [show k - p = (k - (p + 1)) + 1 by omega, pow_succ]; omega
      · rw [show k - p = 0 by omega, show k - (p + 1) = 0 by omega]; omega

lemma Bval_succ_le (k p : ℕ) (hk : 2 ≤ k) :
    Bval k (p + 1) ≤ Bval k p := by
  unfold Bval
  by_cases hp0 : p = 0
  · subst hp0
    simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.sub_self, pow_zero, one_mul,
      Nat.add_sub_cancel]
    split_ifs with h2
    · rw [show k - 2 * 1 + 3 = k + 1 by omega]; omega
    · have hk2 : k = 2 := by omega
      subst hk2; decide
  · simp only [hp0, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, Nat.add_sub_cancel]
    by_cases h1 : 2 * p < k <;> by_cases h2 : 2 * (p + 1) < k <;> simp only [h1, h2, ↓reduceIte]
    · have heq : k - 2 * p + 3 = (k - 2 * (p + 1) + 3) + 2 := by omega
      rw [heq]
      set u := k - 2 * (p + 1) + 3
      have hfib : 2 * Nat.fib u ≤ Nat.fib (u + 2) := by
        have h1 : Nat.fib (u + 2) = Nat.fib u + Nat.fib (u + 1) := Nat.fib_add_two
        have h2 : Nat.fib u ≤ Nat.fib (u + 1) := Nat.fib_mono (show u ≤ u + 1 by omega)
        omega
      have hp2 : 2 ^ p = 2 ^ (p - 1) * 2 := by
        cases p with | zero => omega | succ q => simp [pow_succ]
      rw [hp2, mul_assoc]
      exact Nat.mul_le_mul_left _ hfib
    · have hcase : k = 2 * p + 1 ∨ k = 2 * p + 2 := by omega
      rcases hcase with rfl | rfl
      · rw [show 2 * p + 1 - 2 * p + 3 = 4 by omega, show 2 * p + 1 - (p + 1) = p by omega]
        have hf4 : Nat.fib 4 = 3 := rfl
        rw [hf4]
        cases p with | zero => omega | succ q => rw [Nat.add_sub_cancel, pow_succ]; omega
      · rw [show 2 * p + 2 - 2 * p + 3 = 5 by omega, show 2 * p + 2 - (p + 1) = p + 1 by omega]
        have hf5 : Nat.fib 5 = 5 := rfl
        rw [hf5]
        cases p with | zero => omega | succ q => simp [pow_succ]; omega
    · omega
    · exact Nat.pow_le_pow_right (by decide) (by omega)

def Delta (k p : ℕ) : ℕ := 2 * Bval k (p + 1) - Bval k p

lemma Delta_antitone_step (k p : ℕ) (hk : 2 ≤ k) (hpk : p + 2 ≤ k) :
    Delta k (p + 1) ≤ Delta k p := by
  have hle1 := Bval_le_two_mul_succ k p hk
  have hle2 : Bval k (p + 1) ≤ 2 * Bval k (p + 2) := by
    simpa [Nat.add_assoc] using Bval_le_two_mul_succ k (p + 1) hk
  unfold Delta
  rw [show p + 1 + 1 = p + 2 by omega]
  suffices h : 2 * Bval k (p + 2) + Bval k p ≤ 3 * Bval k (p + 1) by omega
  unfold Bval
  by_cases hp0 : p = 0
  · subst hp0
    simp only [↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, OfNat.ofNat_ne_zero, and_false,
      Nat.sub_self, pow_zero, one_mul, Nat.add_sub_cancel, zero_add]
    by_cases h1 : 2 * 1 < k <;> by_cases h2 : 2 * 2 < k <;> simp only [h1, h2, ↓reduceIte]
    · rw [show k - 2 * 1 + 3 = k + 1 by omega, show k - 2 * 2 + 3 = k - 1 by omega,
          show 2 - 1 = 1 by omega, pow_one]
      have hfib : 5 * Nat.fib (k - 1) ≤ 2 * Nat.fib (k + 1) := by
        have hk5 : 5 ≤ k := by omega
        obtain ⟨r, hr⟩ : ∃ r, k = r + 5 := ⟨k - 5, by omega⟩
        rw [hr, show r + 5 - 1 = r + 4 by omega, show r + 5 + 1 = r + 6 by omega]
        have h4 : Nat.fib (r + 4) = Nat.fib (r + 2) + Nat.fib (r + 3) := by
          simpa [show r + 2 + 2 = r + 4 by omega, show r + 2 + 1 = r + 3 by omega] using Nat.fib_add_two (n := r + 2)
        have h5 : Nat.fib (r + 5) = Nat.fib (r + 3) + Nat.fib (r + 4) := by
          simpa [show r + 3 + 2 = r + 5 by omega, show r + 3 + 1 = r + 4 by omega] using Nat.fib_add_two (n := r + 3)
        have h6 : Nat.fib (r + 6) = Nat.fib (r + 4) + Nat.fib (r + 5) := by
          simpa [show r + 4 + 2 = r + 6 by omega, show r + 4 + 1 = r + 5 by omega] using Nat.fib_add_two (n := r + 4)
        have := Nat.fib_mono (show r + 2 ≤ r + 3 by omega)
        omega
      omega
    · have hk34 : k = 3 ∨ k = 4 := by omega
      rcases hk34 with rfl | rfl <;> decide
    · omega
    · have hk2 : k = 2 := by omega
      subst hk2; decide
  · have hp2_ne : p + 2 ≠ 0 := by omega
    have hp1_ne : p + 1 ≠ 0 := by omega
    simp only [hp0, hp1_ne, hp2_ne, ↓reduceIte, Nat.add_sub_cancel]
    by_cases h1 : 2 * p < k <;> by_cases h2 : 2 * (p + 1) < k <;> by_cases h3 : 2 * (p + 2) < k <;>
      simp only [h1, h2, h3, ↓reduceIte]
    · set m := k - 2 * (p + 2) + 3
      rw [show k - 2 * (p + 1) + 3 = m + 2 by omega, show k - 2 * p + 3 = m + 4 by omega,
          show p + 2 - 1 = p + 1 by omega]
      have hp1 : 2 ^ p = 2 * 2 ^ (p - 1) := by
        cases p with | zero => omega | succ q => rw [Nat.add_sub_cancel, pow_succ]; ring
      have hp2 : 2 ^ (p + 1) = 4 * 2 ^ (p - 1) := by
        cases p with | zero => omega | succ q => rw [Nat.add_sub_cancel, pow_succ, pow_succ]; ring
      rw [hp1, hp2]
      have hfib : 8 * Nat.fib m + Nat.fib (m + 4) ≤ 6 * Nat.fib (m + 2) := by
        have hm4 : 4 ≤ m := by omega
        obtain ⟨r, hr⟩ : ∃ r, m = r + 4 := ⟨m - 4, by omega⟩
        rw [hr]
        have f3 : Nat.fib (r + 3) = Nat.fib (r + 1) + Nat.fib (r + 2) := by
          simpa [show r + 1 + 2 = r + 3 by omega, show r + 1 + 1 = r + 2 by omega] using Nat.fib_add_two (n := r + 1)
        have f4 : Nat.fib (r + 4) = Nat.fib (r + 2) + Nat.fib (r + 3) := by
          simpa [show r + 2 + 2 = r + 4 by omega, show r + 2 + 1 = r + 3 by omega] using Nat.fib_add_two (n := r + 2)
        have f5 : Nat.fib (r + 5) = Nat.fib (r + 3) + Nat.fib (r + 4) := by
          simpa [show r + 3 + 2 = r + 5 by omega, show r + 3 + 1 = r + 4 by omega] using Nat.fib_add_two (n := r + 3)
        have f6 : Nat.fib (r + 6) = Nat.fib (r + 4) + Nat.fib (r + 5) := by
          simpa [show r + 4 + 2 = r + 6 by omega, show r + 4 + 1 = r + 5 by omega] using Nat.fib_add_two (n := r + 4)
        have f7 : Nat.fib (r + 7) = Nat.fib (r + 5) + Nat.fib (r + 6) := by
          simpa [show r + 5 + 2 = r + 7 by omega, show r + 5 + 1 = r + 6 by omega] using Nat.fib_add_two (n := r + 5)
        have f8 : Nat.fib (r + 8) = Nat.fib (r + 6) + Nat.fib (r + 7) := by
          simpa [show r + 6 + 2 = r + 8 by omega, show r + 6 + 1 = r + 7 by omega] using Nat.fib_add_two (n := r + 6)
        have hmono := Nat.fib_mono (show r + 1 ≤ r + 2 by omega)
        rw [show r + 4 + 4 = r + 8 by omega, show r + 4 + 2 = r + 6 by omega]
        omega
      calc 2 * (4 * 2 ^ (p - 1) * Nat.fib m) + 2 ^ (p - 1) * Nat.fib (m + 4)
          = 2 ^ (p - 1) * (8 * Nat.fib m + Nat.fib (m + 4)) := by ring
        _ ≤ 2 ^ (p - 1) * (6 * Nat.fib (m + 2)) := Nat.mul_le_mul_left _ hfib
        _ = 3 * (2 * 2 ^ (p - 1) * Nat.fib (m + 2)) := by ring
    · have hcase : k = 2 * p + 3 ∨ k = 2 * p + 4 := by omega
      have hp1 : 2 ^ p = 2 * 2 ^ (p - 1) := by
        cases p with | zero => omega | succ q => simp [pow_succ]; ring
      rcases hcase with rfl | rfl
      · rw [show 2 * p + 3 - 2 * p + 3 = 6 by omega,
            show 2 * p + 3 - 2 * (p + 1) + 3 = 4 by omega,
            show 2 * p + 3 - (p + 2) = p + 1 by omega, hp1]
        have hp2 : 2 ^ (p + 1) = 4 * 2 ^ (p - 1) := by
          cases p with | zero => omega | succ q => simp [pow_succ]; ring
        rw [hp2]
        have hf6 : Nat.fib 6 = 8 := rfl
        have hf4 : Nat.fib 4 = 3 := rfl
        rw [hf6, hf4]; omega
      · rw [show 2 * p + 4 - 2 * p + 3 = 7 by omega,
            show 2 * p + 4 - 2 * (p + 1) + 3 = 5 by omega,
            show 2 * p + 4 - (p + 2) = p + 2 by omega, hp1]
        have hp2 : 2 ^ (p + 2) = 8 * 2 ^ (p - 1) := by
          cases p with | zero => omega | succ q => simp [pow_succ]; ring
        rw [hp2]
        have hf7 : Nat.fib 7 = 13 := rfl
        have hf5 : Nat.fib 5 = 5 := rfl
        rw [hf7, hf5]; omega
    · omega
    · have hcase : k = 2 * p + 1 ∨ k = 2 * p + 2 := by omega
      rcases hcase with rfl | rfl
      · rw [show 2 * p + 1 - 2 * p + 3 = 4 by omega,
            show 2 * p + 1 - (p + 1) = p by omega,
            show 2 * p + 1 - (p + 2) = p - 1 by omega]
        have hf4 : Nat.fib 4 = 3 := rfl
        have hp1 : 2 ^ p = 2 * 2 ^ (p - 1) := by
          cases p with | zero => omega | succ q => simp [pow_succ]; ring
        rw [hf4, hp1]; omega
      · rw [show 2 * p + 2 - 2 * p + 3 = 5 by omega,
            show 2 * p + 2 - (p + 1) = p + 1 by omega,
            show 2 * p + 2 - (p + 2) = p by omega]
        have hf5 : Nat.fib 5 = 5 := rfl
        have hp1 : 2 ^ p = 2 * 2 ^ (p - 1) := by
          cases p with | zero => omega | succ q => simp [pow_succ]; ring
        have hp2 : 2 ^ (p + 1) = 4 * 2 ^ (p - 1) := by
          cases p with | zero => omega | succ q => simp [pow_succ]; ring
        rw [hf5, hp1, hp2]; omega
    · omega
    · omega
    · omega
    · have hp1 : 2 ^ (k - (p + 1)) = 2 * 2 ^ (k - (p + 2)) := by
        rw [show k - (p + 1) = (k - (p + 2)) + 1 by omega, pow_succ]; ring
      have hp0' : 2 ^ (k - p) = 4 * 2 ^ (k - (p + 2)) := by
        rw [show k - p = (k - (p + 2)) + 2 by omega, pow_succ, pow_succ]; ring
      rw [hp1, hp0']; omega

lemma Delta_antitone {k p q : ℕ} (hk : 2 ≤ k) (hpq : p ≤ q) (hq : q < k) :
    Delta k q ≤ Delta k p := by
  induction hpq with
  | refl => exact le_rfl
  | step hle ih => exact le_trans (Delta_antitone_step k _ hk (by omega)) (ih (by omega))

lemma Bval_tangent_ge (k d t : ℕ) (hk : 2 ≤ k) (hdtk : d + t ≤ k) :
    2 ^ t * Bval k (d + t) ≤ Bval k d + (2 ^ t - 1) * Delta k d := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hdt := Delta_antitone hk (show d ≤ d + t by omega) (by omega)
    have ih := ih (by omega)
    have h1 : Bval k (d + t) + Delta k (d + t) = 2 * Bval k (d + t + 1) := by
      unfold Delta; have := Bval_le_two_mul_succ k (d + t) hk; omega
    have hpos : 1 ≤ 2 ^ t := Nat.one_le_pow _ _ (by decide)
    have hpos2 : 1 ≤ 2 ^ (t + 1) := Nat.one_le_pow _ _ (by decide)
    calc 2 ^ (t + 1) * Bval k (d + (t + 1))
        = 2 ^ t * (2 * Bval k (d + t + 1)) := by rw [pow_succ]; ring
      _ = 2 ^ t * (Bval k (d + t) + Delta k (d + t)) := by rw [← h1]
      _ = 2 ^ t * Bval k (d + t) + 2 ^ t * Delta k (d + t) := by ring
      _ ≤ (Bval k d + (2 ^ t - 1) * Delta k d) + 2 ^ t * Delta k d :=
          Nat.add_le_add ih (Nat.mul_le_mul_left _ hdt)
      _ = Bval k d + (2 ^ (t + 1) - 1) * Delta k d := by
          zify [hpos, hpos2]; rw [pow_succ]; ring

lemma Bval_tangent_le (k p t : ℕ) (hk : 2 ≤ k) (hptk : p + t < k) :
    Bval k p + (2 ^ t - 1) * Delta k (p + t) ≤ 2 ^ t * Bval k (p + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hdt := Delta_antitone_step k (p + t) hk (by omega)
    have ih := ih (by omega)
    have h1 : Bval k (p + t) + Delta k (p + t) = 2 * Bval k (p + t + 1) := by
      unfold Delta; have := Bval_le_two_mul_succ k (p + t) hk; omega
    have hpos : 1 ≤ 2 ^ t := Nat.one_le_pow _ _ (by decide)
    have hpos2 : 1 ≤ 2 ^ (t + 1) := Nat.one_le_pow _ _ (by decide)
    have ih' : Bval k p + (2 ^ t - 1) * Delta k (p + t + 1) ≤ 2 ^ t * Bval k (p + t) :=
      le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hdt) _) ih
    have hmul : 2 ^ (t + 1) * Bval k (p + (t + 1)) =
        2 ^ t * Bval k (p + t) + 2 ^ t * Delta k (p + t) := by
      rw [show p + (t + 1) = p + t + 1 by omega, pow_succ]
      have : 2 ^ t * 2 * Bval k (p + t + 1) = 2 ^ t * (2 * Bval k (p + t + 1)) := by ring
      rw [this, ← h1]; ring
    have hstep : 2 ^ t * Delta k (p + t + 1) ≤ 2 ^ t * Delta k (p + t) :=
      Nat.mul_le_mul_left _ hdt
    rw [show p + (t + 1) = p + t + 1 by omega] at hmul ⊢
    zify [hpos, hpos2] at ih' hmul hstep ⊢
    rw [pow_succ] at hmul ⊢
    linarith

lemma Bval_tangent (k d p : ℕ) (hk : 2 ≤ k) (hd : d < k) (hp : p ≤ k) :
    2 ^ k * Bval k p ≤
      2 ^ (k - p) * (2 ^ (d + 1) * (Bval k d - Bval k (d + 1))) + 2 ^ k * Delta k d := by
  have hle_d := Bval_le_two_mul_succ k d hk
  have hdec_d := Bval_succ_le k d hk
  have hBD : Delta k d ≤ Bval k d := by unfold Delta; omega
  have hBD2 : Bval k d - Delta k d = 2 * (Bval k d - Bval k (d + 1)) := by unfold Delta; omega
  by_cases hpd : d ≤ p
  · have hs : 2 ^ (p - d) * Bval k p ≤ Bval k d + (2 ^ (p - d) - 1) * Delta k d := by
      have := Bval_tangent_ge k d (p - d) hk (by omega)
      rwa [Nat.add_sub_cancel' hpd] at this
    have h1 : 2 ^ k = 2 ^ (k - p) * 2 ^ p := by rw [← pow_add, Nat.sub_add_cancel hp]
    have h2 : 2 ^ p = 2 ^ d * 2 ^ (p - d) := by rw [← pow_add, Nat.add_sub_cancel' hpd]
    have hpos : 1 ≤ 2 ^ (p - d) := Nat.one_le_pow _ _ (by decide)
    calc 2 ^ k * Bval k p
        = 2 ^ (k - p) * 2 ^ d * (2 ^ (p - d) * Bval k p) := by rw [h1, h2]; ring
      _ ≤ 2 ^ (k - p) * 2 ^ d * (Bval k d + (2 ^ (p - d) - 1) * Delta k d) :=
          Nat.mul_le_mul_left _ hs
      _ = 2 ^ (k - p) * 2 ^ d * (Bval k d - Delta k d) +
          2 ^ (k - p) * 2 ^ d * (2 ^ (p - d) * Delta k d) := by
          zify [hpos, hBD]; ring
      _ = 2 ^ (k - p) * (2 ^ (d + 1) * (Bval k d - Bval k (d + 1))) + 2 ^ k * Delta k d := by
          rw [hBD2, show 2 ^ (k - p) * 2 ^ d * (2 ^ (p - d) * Delta k d) = 2 ^ k * Delta k d by
            rw [h1, h2]; ring, pow_succ]
          ring
  · have hpd' : p ≤ d := by omega
    have hs : Bval k p + (2 ^ (d - p) - 1) * Delta k d ≤ 2 ^ (d - p) * Bval k d := by
      have := Bval_tangent_le k p (d - p) hk (by omega)
      rwa [Nat.add_sub_cancel' hpd'] at this
    have h1 : 2 ^ k = 2 ^ (k - p) * 2 ^ p := by rw [← pow_add, Nat.sub_add_cancel hp]
    have h2 : 2 ^ d = 2 ^ p * 2 ^ (d - p) := by rw [← pow_add, Nat.add_sub_cancel' hpd']
    have hpos : 1 ≤ 2 ^ (d - p) := Nat.one_le_pow _ _ (by decide)
    have hs' : Bval k p ≤ 2 ^ (d - p) * (Bval k d - Delta k d) + Delta k d := by
      zify [hpos, hBD] at hs ⊢; linarith
    calc 2 ^ k * Bval k p
        ≤ 2 ^ k * (2 ^ (d - p) * (Bval k d - Delta k d) + Delta k d) :=
          Nat.mul_le_mul_left _ hs'
      _ = 2 ^ (k - p) * (2 ^ (d + 1) * (Bval k d - Bval k (d + 1))) + 2 ^ k * Delta k d := by
          rw [hBD2, h1, pow_succ, h2]; ring

def indepCount {k : ℕ} (hk : 0 < k) (I : Finset (Fin k)) : ℕ :=
  (I.powerset.filter (fun S => ∀ u ∈ S, ix hk (u.val + 1) ∉ S)).card

def Mbound (c r : ℕ) : ℕ :=
  if c ≤ r then 2 ^ c else 2 ^ (r - 1) * Nat.fib (c - r + 3)

lemma Mbound_mono_r {c r1 r2 : ℕ} (hr1 : 1 ≤ r1) (h : r1 ≤ r2) :
    Mbound c r1 ≤ Mbound c r2 := by
  induction h with
  | refl => exact le_rfl
  | step hle ih =>
    rename_i m
    refine le_trans ih ?_
    have hm1 : 1 ≤ m := le_trans hr1 hle
    unfold Mbound
    split_ifs with h1 h2
    · exact le_rfl
    · omega
    · have hcm : c = m + 1 := by omega
      subst hcm
      have e1 : m + 1 - m + 3 = 4 := by omega
      rw [e1]
      have hf4 : Nat.fib 4 = 3 := rfl
      rw [hf4]
      have hp : 2 ^ (m + 1) = 4 * 2 ^ (m - 1) := by
        cases m with | zero => omega | succ q => simp [pow_succ]; ring
      rw [hp]; omega
    · have heq : c - m + 3 = (c - (m + 1) + 3) + 1 := by omega
      rw [heq]
      have hfib := fib_succ_le_two_mul (by omega : 1 ≤ c - (m + 1) + 3)
      have hp : 2 ^ m = 2 ^ (m - 1) * 2 := by
        cases m with | zero => omega | succ q => simp [pow_succ]
      rw [show m + 1 - 1 = m by omega, hp, mul_assoc]
      exact Nat.mul_le_mul_left _ hfib

lemma Mbound_mul {c1 r1 c2 r2 : ℕ} (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2) :
    Mbound c1 r1 * Mbound c2 r2 ≤ Mbound (c1 + c2) (r1 + r2) := by
  have hfib_pow : ∀ t m, 1 ≤ m → Nat.fib (m + t) ≤ 2 ^ t * Nat.fib m := by
    intro t
    induction t with
    | zero => intro m _; simp
    | succ t ih =>
      intro m hm
      calc Nat.fib (m + (t + 1)) = Nat.fib ((m + t) + 1) := by ring_nf
        _ ≤ 2 * Nat.fib (m + t) := fib_succ_le_two_mul (by omega)
        _ ≤ 2 * (2 ^ t * Nat.fib m) := Nat.mul_le_mul_left _ (ih m hm)
        _ = 2 ^ (t + 1) * Nat.fib m := by rw [pow_succ]; ring
  unfold Mbound
  by_cases h1 : c1 ≤ r1 <;> by_cases h2 : c2 ≤ r2 <;> by_cases h3 : c1 + c2 ≤ r1 + r2 <;>
    simp only [h1, h2, h3, ↓reduceIte]
  · rw [← pow_add]
  · omega
  · have hf := fib_le_two_pow (c2 - r2 + 1)
    have heq : c2 - r2 + 1 + 2 = c2 - r2 + 3 := by omega
    rw [heq] at hf
    calc 2 ^ c1 * (2 ^ (r2 - 1) * Nat.fib (c2 - r2 + 3))
        ≤ 2 ^ c1 * (2 ^ (r2 - 1) * 2 ^ (c2 - r2 + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hf)
      _ = 2 ^ (c1 + c2) := by rw [← pow_add, ← pow_add]; congr 1; omega
  · have hdiff : c2 - r2 + 3 = (c1 + c2 - (r1 + r2) + 3) + (r1 - c1) := by omega
    rw [hdiff]
    calc 2 ^ c1 * (2 ^ (r2 - 1) * Nat.fib (c1 + c2 - (r1 + r2) + 3 + (r1 - c1)))
        ≤ 2 ^ c1 * (2 ^ (r2 - 1) * (2 ^ (r1 - c1) * Nat.fib (c1 + c2 - (r1 + r2) + 3))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (hfib_pow _ _ (by omega)))
      _ = 2 ^ (r1 + r2 - 1) * Nat.fib (c1 + c2 - (r1 + r2) + 3) := by
          have hp : 2 ^ c1 * (2 ^ (r2 - 1) * 2 ^ (r1 - c1)) = 2 ^ (r1 + r2 - 1) := by
            rw [← pow_add, ← pow_add]; congr 1; omega
          nlinarith
  · have hf := fib_le_two_pow (c1 - r1 + 1)
    have heq : c1 - r1 + 1 + 2 = c1 - r1 + 3 := by omega
    rw [heq] at hf
    calc (2 ^ (r1 - 1) * Nat.fib (c1 - r1 + 3)) * 2 ^ c2
        ≤ (2 ^ (r1 - 1) * 2 ^ (c1 - r1 + 1)) * 2 ^ c2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hf)
      _ = 2 ^ (c1 + c2) := by rw [← pow_add, ← pow_add]; congr 1; omega
  · have hdiff : c1 - r1 + 3 = (c1 + c2 - (r1 + r2) + 3) + (r2 - c2) := by omega
    rw [hdiff]
    calc (2 ^ (r1 - 1) * Nat.fib (c1 + c2 - (r1 + r2) + 3 + (r2 - c2))) * 2 ^ c2
        ≤ (2 ^ (r1 - 1) * (2 ^ (r2 - c2) * Nat.fib (c1 + c2 - (r1 + r2) + 3))) * 2 ^ c2 :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hfib_pow _ _ (by omega)))
      _ = 2 ^ (r1 + r2 - 1) * Nat.fib (c1 + c2 - (r1 + r2) + 3) := by
          have hp : 2 ^ (r1 - 1) * 2 ^ (r2 - c2) * 2 ^ c2 = 2 ^ (r1 + r2 - 1) := by
            rw [← pow_add, ← pow_add]; congr 1; omega
          nlinarith
  · omega
  · set a := c1 - r1 + 1
    set b := c2 - r2 + 1
    have ea : c1 - r1 + 3 = a + 2 := by omega
    have eb : c2 - r2 + 3 = b + 2 := by omega
    have es : c1 + c2 - (r1 + r2) + 3 = a + b + 1 := by omega
    rw [ea, eb, es]
    have hm := fib_merge a b
    have hp : 2 ^ (r1 - 1) * 2 ^ (r2 - 1) * 2 = 2 ^ (r1 + r2 - 1) := by
      rw [← pow_add, ← pow_succ]; congr 1; omega
    calc (2 ^ (r1 - 1) * Nat.fib (a + 2)) * (2 ^ (r2 - 1) * Nat.fib (b + 2))
        = (2 ^ (r1 - 1) * 2 ^ (r2 - 1)) * (Nat.fib (a + 2) * Nat.fib (b + 2)) := by ring
      _ ≤ (2 ^ (r1 - 1) * 2 ^ (r2 - 1)) * (2 * Nat.fib (a + b + 1)) := Nat.mul_le_mul_left _ hm
      _ = 2 ^ (r1 + r2 - 1) * Nat.fib (a + b + 1) := by rw [← hp]; ring

lemma indepCount_rot {k : ℕ} (hk : 0 < k) (s : ℕ) (I : Finset (Fin k)) :
    indepCount hk (I.image (fun i => ix hk (i.val + s))) = indepCount hk I := by
  let f : Fin k ≃ Fin k :=
    { toFun := fun i => ix hk (i.val + s)
      invFun := fun i => ix hk (i.val + k - s % k)
      left_inv := fun i => by
        dsimp only
        apply Fin.ext; simp only [ix]
        have hs := Nat.mod_lt s hk
        have h1 : (i.val + s) % k + k - s % k = (i.val + s) % k + (k - s % k) := by omega
        rw [h1]
        have h3 : ((i.val + s) + (k - s % k)) % k = i.val % k := by
          have : i.val + s + (k - s % k) = i.val + (s / k + 1) * k := by
            have hdiv := Nat.div_add_mod s k; have hlt := Nat.mod_lt s hk; zify [le_of_lt hlt] at hdiv ⊢; linarith
          rw [this, Nat.add_mul_mod_self_right]
        rw [← Nat.mod_add_mod] at h3
        simpa [Nat.mod_eq_of_lt i.isLt] using h3
      right_inv := fun i => by
        dsimp only
        apply Fin.ext; simp only [ix]
        have hs := Nat.mod_lt s hk
        have h3 : ((i.val + k - s % k) + s) % k = i.val % k := by
          have : i.val + k - s % k + s = i.val + (s / k + 1) * k := by
            have hdiv := Nat.div_add_mod s k
            have hle : s % k ≤ i.val + k := by have := Nat.mod_lt s hk; omega
            zify [hle] at hdiv ⊢; linarith
          rw [this, Nat.add_mul_mod_self_right]
        simpa [Nat.mod_add_mod, Nat.mod_eq_of_lt i.isLt] using h3 }
  have hstep : ∀ u : Fin k, f (ix hk (u.val + 1)) = ix hk ((f u).val + 1) := by
    intro u; apply Fin.ext; simp only [f, ix, Equiv.coe_fn_mk, Nat.mod_add_mod]; congr 1; ring
  unfold indepCount
  refine Finset.card_bij (fun S _ => S.image f.symm) ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    refine ⟨?_, ?_⟩
    · intro x hx
      obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨z, hzI, hzy⟩ := Finset.mem_image.mp (hS.1 hyS)
      have : f.symm y = z := by rw [← hzy]; exact f.symm_apply_apply z
      exact this ▸ hzI
    · intro u hu hnext
      obtain ⟨y, hyS, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨z, hzS, hz⟩ := Finset.mem_image.mp hnext
      have hfz : z = ix hk (y.val + 1) := by
        have h1 : f (f.symm z) = f (ix hk ((f.symm y).val + 1)) := congrArg f hz
        rw [f.apply_symm_apply, hstep, f.apply_symm_apply] at h1
        exact h1
      exact hS.2 y hyS (hfz ▸ hzS)
  · intro S1 _ S2 _ h
    ext y
    constructor
    · intro hy
      have : f.symm y ∈ S1.image f.symm := Finset.mem_image_of_mem _ hy
      rw [h] at this
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp this
      exact (f.symm.injective hzy) ▸ hz
    · intro hy
      have : f.symm y ∈ S2.image f.symm := Finset.mem_image_of_mem _ hy
      rw [← h] at this
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp this
      exact (f.symm.injective hzy) ▸ hz
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    refine ⟨T.image f, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.image_subset_image hT.1, ?_⟩
      intro u hu hnext
      obtain ⟨a, haT, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hbT, hb⟩ := Finset.mem_image.mp hnext
      rw [← hstep] at hb
      exact hT.2 a haT ((f.injective hb) ▸ hbT)
    · ext x; simp [Finset.mem_image]

lemma indepCount_disjoint_union {k : ℕ} (hk : 0 < k) (A B : Finset (Fin k))
    (hdisj : Disjoint A B)
    (hno1 : ∀ u ∈ A, ix hk (u.val + 1) ∉ B)
    (hno2 : ∀ v ∈ B, ix hk (v.val + 1) ∉ A) :
    indepCount hk (A ∪ B) = indepCount hk A * indepCount hk B := by
  unfold indepCount
  rw [← Finset.card_product]
  refine Finset.card_bij (fun S _ => (S ∩ A, S ∩ B)) ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨Finset.inter_subset_right, fun u hu hnext =>
      hS.2 u (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hnext).1⟩,
      ⟨Finset.inter_subset_right, fun u hu hnext =>
      hS.2 u (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hnext).1⟩⟩
  · intro S1 hS1 S2 hS2 h
    simp only [Prod.mk.injEq] at h
    have hsub1 : S1 ⊆ A ∪ B := Finset.mem_powerset.mp (Finset.mem_filter.mp hS1).1
    have hsub2 : S2 ⊆ A ∪ B := Finset.mem_powerset.mp (Finset.mem_filter.mp hS2).1
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp (hsub1 hx) with hxA | hxB
      · have : x ∈ S1 ∩ A := Finset.mem_inter.mpr ⟨hx, hxA⟩
        rw [h.1] at this; exact (Finset.mem_inter.mp this).1
      · have : x ∈ S1 ∩ B := Finset.mem_inter.mpr ⟨hx, hxB⟩
        rw [h.2] at this; exact (Finset.mem_inter.mp this).1
    · intro hx
      rcases Finset.mem_union.mp (hsub2 hx) with hxA | hxB
      · have : x ∈ S2 ∩ A := Finset.mem_inter.mpr ⟨hx, hxA⟩
        rw [← h.1] at this; exact (Finset.mem_inter.mp this).1
      · have : x ∈ S2 ∩ B := Finset.mem_inter.mpr ⟨hx, hxB⟩
        rw [← h.2] at this; exact (Finset.mem_inter.mp this).1
  · intro ⟨SA, SB⟩ hAB
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hAB
    refine ⟨SA ∪ SB, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.union_subset_union hAB.1.1 hAB.2.1, ?_⟩
      intro u hu hnext
      rcases Finset.mem_union.mp hu with huA | huB <;> rcases Finset.mem_union.mp hnext with hnA | hnB
      · exact hAB.1.2 u huA hnA
      · exact hno1 u (hAB.1.1 huA) (hAB.2.1 hnB)
      · exact hno2 u (hAB.2.1 huB) (hAB.1.1 hnA)
      · exact hAB.2.2 u huB hnB
    · ext x
      · simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxA | hxB, hA⟩
          · exact hxA
          · exact False.elim (Finset.disjoint_left.mp hdisj hA (hAB.2.1 hxB))
        · intro hxA; exact ⟨Or.inl hxA, hAB.1.1 hxA⟩
      · simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxA | hxB, hB⟩
          · exact False.elim (Finset.disjoint_left.mp hdisj (hAB.1.1 hxA) hB)
          · exact hxB
        · intro hxB; exact ⟨Or.inr hxB, hAB.2.1 hxB⟩

lemma indepCount_erase_endpoint {k : ℕ} (hk : 2 ≤ k) (I : Finset (Fin k))
    (u : Fin k) (hu : u ∈ I) (hprev : ix (by omega : 0 < k) (u.val + k - 1) ∉ I) :
    indepCount (by omega : 0 < k) I =
      indepCount (by omega : 0 < k) (I.erase u) +
      indepCount (by omega : 0 < k) ((I.erase u).erase (ix (by omega : 0 < k) (u.val + 1))) := by
  have hk0 : 0 < k := by omega
  let v := ix hk0 (u.val + 1)
  have hne : v ≠ u := by
    intro h
    have hval := congrArg Fin.val h
    simp only [v, ix] at hval
    by_cases hlt : u.val + 1 < k
    · rw [Nat.mod_eq_of_lt hlt] at hval; omega
    · have hu1 : u.val + 1 = k := by omega
      rw [hu1, Nat.mod_self] at hval; omega
  unfold indepCount
  let F := I.powerset.filter (fun S => ∀ a ∈ S, ix hk0 (a.val + 1) ∉ S)
  have hsplit : F.card = (F.filter (fun S => u ∉ S)).card + (F.filter (fun S => u ∈ S)).card := by
    rw [add_comm]; exact (Finset.card_filter_add_card_filter_not (fun S => u ∈ S)).symm
  rw [hsplit]
  congr 1
  · refine Finset.card_bij (fun S _ => S) ?_ ?_ ?_
    · intro S hS
      simp only [F, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
      exact ⟨Finset.subset_erase.mpr ⟨hS.1.1, hS.2⟩, hS.1.2⟩
    · intro _ _ _ _ h; exact h
    · intro S hS
      simp only [F, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
      exact ⟨S, ⟨⟨Finset.Subset.trans hS.1 (Finset.erase_subset _ _), hS.2⟩,
        fun huS => (Finset.mem_erase.mp (hS.1 huS)).1 rfl⟩, rfl⟩
  · refine Finset.card_bij (fun S _ => S.erase u) ?_ ?_ ?_
    · intro S hS
      simp only [F, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
      refine ⟨?_, fun a ha hnext => hS.1.2 a (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hnext)⟩
      intro x hx
      have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
      have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
      have hxv : x ≠ v := fun h => hS.1.2 u hS.2 (h ▸ hxS : v ∈ S)
      exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_erase.mpr ⟨hxu, hS.1.1 hxS⟩⟩
    · intro S1 hS1 S2 hS2 h
      have hu1 : u ∈ S1 := (Finset.mem_filter.mp hS1).2
      have hu2 : u ∈ S2 := (Finset.mem_filter.mp hS2).2
      rw [← Finset.insert_erase hu1, ← Finset.insert_erase hu2, h]
    · intro T hT
      simp only [F, Finset.mem_filter, Finset.mem_powerset] at hT ⊢
      refine ⟨insert u T, ?_, ?_⟩
      · refine ⟨⟨Finset.insert_subset hu (Finset.Subset.trans hT.1
            (Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _))), ?_⟩,
            Finset.mem_insert_self u T⟩
        intro a ha hnext
        rcases Finset.mem_insert.mp ha with rfl | haT
        · rcases Finset.mem_insert.mp hnext with hv | hvT
          · exact hne hv
          · exact (Finset.mem_erase.mp (hT.1 hvT)).1 rfl
        · rcases Finset.mem_insert.mp hnext with hnu | hnT
          · have ha_eq : a = ix hk0 (u.val + k - 1) := by
              have := congrArg Fin.val hnu
              simp only [ix] at this
              apply Fin.ext; simp only [ix]
              have hau : a.val < k := a.isLt
              have hu_lt : u.val < k := u.isLt
              by_cases ha1 : a.val + 1 < k
              · rw [Nat.mod_eq_of_lt ha1] at this
                have : u.val + k - 1 = a.val + k := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hau]
              · have ha_eq' : a.val + 1 = k := by omega
                rw [ha_eq', Nat.mod_self] at this
                have hu0 : u.val = 0 := this.symm
                rw [hu0, zero_add, Nat.mod_eq_of_lt (by omega)]; omega
            have haI : a ∈ I := (Finset.mem_erase.mp (Finset.mem_erase.mp (hT.1 haT)).2).2
            exact hprev (ha_eq ▸ haI)
          · exact hT.2 a haT hnT
      · apply Finset.erase_insert
        intro huT
        exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hT.1 huT)).2).1 rfl

lemma card_interval {k : ℕ} (a m : ℕ) (ham : a + m ≤ k) :
    (Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < a + m)).card = m := by
  have h : (Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < a + m)).card =
      (Finset.range m).card := by
    refine Finset.card_bij (fun i _ => i.val - a) ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_range.mpr (by omega)
    · intro i1 hi1 i2 hi2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
      exact Fin.ext (by omega)
    · intro j hj; rw [Finset.mem_range] at hj
      exact ⟨⟨a + j, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨by simp, by simp; omega⟩⟩, by simp⟩
  simpa using h

lemma indepCount_interval {k : ℕ} (hk : 2 ≤ k) (a m : ℕ) (ham : a + m < k) :
    indepCount (by omega : 0 < k)
      (Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < a + m)) = Nat.fib (m + 2) := by
  have hk0 : 0 < k := by omega
  induction m using Nat.strong_induction_on generalizing a with
  | ind m ih =>
    match m with
    | 0 =>
      have hemp : Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < a + 0) = ∅ := by
        ext i; simp
      rw [hemp]; unfold indepCount
      have h1 : ((∅ : Finset (Fin k)).powerset.filter (fun S => ∀ u ∈ S, ix hk0 (u.val + 1) ∉ S)) = {∅} := by
        ext S; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_empty, Finset.mem_singleton, and_iff_left_iff_imp]; rintro rfl u hu; exact False.elim (Finset.notMem_empty u hu)
      rw [h1, Finset.card_singleton]; rfl
    | 1 =>
      let u : Fin k := ⟨a, by omega⟩
      have hsing : Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < a + 1) = {u} := by
        ext i; simp [u, Fin.ext_iff]; omega
      rw [hsing]
      have hprev : ix hk0 (u.val + k - 1) ∉ ({u} : Finset (Fin k)) := by
        simp only [Finset.mem_singleton, Fin.ext_iff, u, ix]
        by_cases ha0 : a = 0
        · subst ha0; rw [zero_add, Nat.mod_eq_of_lt (by omega)]; omega
        · have : a + k - 1 = (a - 1) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
      rw [indepCount_erase_endpoint hk {u} u (Finset.mem_singleton_self u) hprev]
      have he1 : ({u} : Finset (Fin k)).erase u = ∅ := Finset.erase_singleton u
      rw [he1, Finset.erase_empty]
      have h0 : indepCount hk0 ∅ = 1 := by
        unfold indepCount
        have h1 : ((∅ : Finset (Fin k)).powerset.filter (fun S => ∀ u ∈ S, ix hk0 (u.val + 1) ∉ S)) = {∅} := by
          ext S; simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_empty, Finset.mem_singleton, and_iff_left_iff_imp]; rintro rfl u hu; exact False.elim (Finset.notMem_empty u hu)
        rw [h1, Finset.card_singleton]
      rw [h0]; rfl
    | m + 2 =>
      let I := Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < a + (m + 2))
      let u : Fin k := ⟨a, by omega⟩
      have hu : u ∈ I := by simp [I, u]
      have hprev : ix hk0 (u.val + k - 1) ∉ I := by
        simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, u, ix, not_and, not_lt]
        intro hge
        by_cases ha0 : a = 0
        · subst ha0; rw [zero_add, Nat.mod_eq_of_lt (by omega)]; omega
        · have : a + k - 1 = (a - 1) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hge; omega
      rw [indepCount_erase_endpoint hk I u hu hprev]
      have he1 : I.erase u = Finset.univ.filter (fun i : Fin k => a + 1 ≤ i.val ∧ i.val < (a + 1) + (m + 1)) := by
        ext i; simp [I, u, Fin.ext_iff]; omega
      have he2 : (I.erase u).erase (ix hk0 (u.val + 1)) =
          Finset.univ.filter (fun i : Fin k => a + 2 ≤ i.val ∧ i.val < (a + 2) + m) := by
        ext i
        have hlt : a + 1 < k := by omega
        simp [I, u, ix, Fin.ext_iff, Nat.mod_eq_of_lt hlt]; omega
      rw [he2, he1, ih (m + 1) (by omega) (a + 1) (by omega), ih m (by omega) (a + 2) (by omega)]
      have hf : Nat.fib (m + 2 + 2) = Nat.fib (m + 2) + Nat.fib (m + 3) := by simpa [show m + 2 + 1 = m + 3 by omega] using Nat.fib_add_two (n := m + 2)
      rw [show m + 1 + 2 = m + 3 by omega]; omega

lemma indepCount_subset_interval_le {k : ℕ} (hk : 2 ≤ k) :
    ∀ (n : ℕ) (hn : n < k) (a : ℕ) (han : a + n < k) (I : Finset (Fin k))
      (hI : ∀ i ∈ I, a ≤ i.val ∧ i.val < a + n),
      indepCount (by omega : 0 < k) I ≤ Mbound I.card (n + 1 - I.card) := by
  have hk0 : 0 < k := by omega
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn a han I hI
    have hsub_all : I ⊆ Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < a + n) := by
      intro i hi; simp [hI i hi]
    have hcard_le : I.card ≤ n := le_trans (Finset.card_le_card hsub_all) (le_of_eq (card_interval a n (by omega)))
    by_cases hfull : I.card = n
    · have hEq : I = Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < a + n) :=
        Finset.eq_of_subset_of_card_le hsub_all (by rw [card_interval a n (by omega), hfull])
      rw [hEq, indepCount_interval hk a n han, card_interval a n (by omega)]
      have hr1 : n + 1 - n = 1 := by omega
      rw [hr1]; unfold Mbound
      split_ifs with h1
      · exact fib_le_two_pow n
      · simp [show n - 1 + 3 = n + 2 by omega]
    · have hex : ∃ j : Fin k, a ≤ j.val ∧ j.val < a + n ∧ j ∉ I := by
        by_contra hall; push_neg at hall
        have hsup : Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < a + n) ⊆ I := by
          intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact hall i hi.1 hi.2
        have := Finset.card_le_card hsup
        rw [card_interval a n (by omega)] at this; omega
      obtain ⟨j, hj_ge, hj_lt, hj_not⟩ := hex
      let IL := I.filter (fun i => i.val < j.val)
      let IR := I.filter (fun i => j.val < i.val)
      have hdisj : Disjoint IL IR := Finset.disjoint_left.mpr fun x hxL hxR => by
        have := (Finset.mem_filter.mp hxL).2; have := (Finset.mem_filter.mp hxR).2; omega
      have hunion : I = IL ∪ IR := by
        ext x; simp only [IL, IR, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hx
          have hne : x.val ≠ j.val := fun h => hj_not (Fin.ext h ▸ hx)
          rcases lt_or_gt_of_ne hne with h | h
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨hx, h⟩
        · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      have hno1 : ∀ u ∈ IL, ix hk0 (u.val + 1) ∉ IR := by
        intro u hu hn'
        have hu1 := (Finset.mem_filter.mp hu).2
        have hn1 := (Finset.mem_filter.mp hn').2
        simp only [ix, Nat.mod_eq_of_lt (show u.val + 1 < k by omega)] at hn1; omega
      have hno2 : ∀ v ∈ IR, ix hk0 (v.val + 1) ∉ IL := by
        intro v hv hn'
        have hv0 := hI v (Finset.mem_filter.mp hv).1
        have hv1 := (Finset.mem_filter.mp hv).2
        have hn1 := (Finset.mem_filter.mp hn').2
        simp only [ix, Nat.mod_eq_of_lt (show v.val + 1 < k by omega)] at hn1; omega
      rw [hunion, indepCount_disjoint_union hk0 IL IR hdisj hno1 hno2]
      have hcsum : I.card = IL.card + IR.card := by rw [hunion, Finset.card_union_of_disjoint hdisj]
      let nL := j.val - a
      let nR := a + n - (j.val + 1)
      have hL := ih nL (by omega) (by omega) a (by omega) IL (fun i hi => by
        have := hI i (Finset.mem_filter.mp hi).1; have := (Finset.mem_filter.mp hi).2; omega)
      have hR := ih nR (by omega) (by omega) (j.val + 1) (by omega) IR (fun i hi => by
        have := hI i (Finset.mem_filter.mp hi).1; have := (Finset.mem_filter.mp hi).2; omega)
      have hcL : IL.card ≤ nL := by
        have hs : IL ⊆ Finset.univ.filter (fun i : Fin k => a ≤ i.val ∧ i.val < a + nL) := by
          intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have := hI i (Finset.mem_filter.mp hi).1; have := (Finset.mem_filter.mp hi).2; omega
        exact le_trans (Finset.card_le_card hs) (le_of_eq (card_interval a nL (by omega)))
      have hcR : IR.card ≤ nR := by
        have hs : IR ⊆ Finset.univ.filter (fun i : Fin k => j.val + 1 ≤ i.val ∧ i.val < (j.val + 1) + nR) := by
          intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have := hI i (Finset.mem_filter.mp hi).1; have := (Finset.mem_filter.mp hi).2; omega
        exact le_trans (Finset.card_le_card hs) (le_of_eq (card_interval (j.val + 1) nR (by omega)))
      have hrsum : (nL + 1 - IL.card) + (nR + 1 - IR.card) = n + 1 - (IL.card + IR.card) := by omega
      calc indepCount hk0 IL * indepCount hk0 IR
          ≤ Mbound IL.card (nL + 1 - IL.card) * Mbound IR.card (nR + 1 - IR.card) := Nat.mul_le_mul hL hR
        _ ≤ Mbound (IL.card + IR.card) ((nL + 1 - IL.card) + (nR + 1 - IR.card)) := Mbound_mul (by omega) (by omega)
        _ = Mbound (IL ∪ IR).card (n + 1 - (IL ∪ IR).card) := by
            rw [Finset.card_union_of_disjoint hdisj, hrsum]

lemma indepCount_le_Bval {k : ℕ} (hk : 2 ≤ k) (I : Finset (Fin k)) (hI : I ≠ Finset.univ) :
    indepCount (by omega : 0 < k) I ≤ Bval k (k - I.card) := by
  have hk0 : 0 < k := by omega
  have hex : ∃ m : Fin k, m ∉ I := by
    by_contra hall; push_neg at hall
    exact hI (Finset.eq_univ_iff_forall.mpr hall)
  obtain ⟨m, hm⟩ := hex
  let s := k - 1 - m.val
  let I' := I.image (fun i => ix hk0 (i.val + s))
  have hrot : indepCount hk0 I' = indepCount hk0 I := indepCount_rot hk0 s I
  have hcard : I'.card = I.card := by
    apply Finset.card_image_of_injective
    intro a b hab
    rw [ix_eq_iff] at hab
    have h1 : ((a.val + s) + (k - s % k)) % k = ((b.val + s) + (k - s % k)) % k := by
      rw [← Nat.mod_add_mod, hab, Nat.mod_add_mod]
    have ha : a.val + s + (k - s % k) = a.val + (s / k + 1) * k := by
      have hdiv := Nat.div_add_mod s k; have hlt := Nat.mod_lt s hk0; zify [le_of_lt hlt] at hdiv ⊢; linarith
    have hb : b.val + s + (k - s % k) = b.val + (s / k + 1) * k := by
      have hdiv := Nat.div_add_mod s k; have hlt := Nat.mod_lt s hk0; zify [le_of_lt hlt] at hdiv ⊢; linarith
    rw [ha, hb, Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at h1
    exact Fin.ext h1
  have hlt : ∀ i ∈ I', 0 ≤ i.val ∧ i.val < 0 + (k - 1) := by
    intro i hi
    obtain ⟨x, hxI, rfl⟩ := Finset.mem_image.mp hi
    refine ⟨Nat.zero_le _, ?_⟩
    have hne : ix hk0 (x.val + s) ≠ ⟨k - 1, by omega⟩ := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only [ix] at hval
      have hxm : x = m := by
        apply Fin.ext
        have h1 : (x.val + s) % k = (m.val + s) % k := by
          rw [hval, show m.val + s = k - 1 by omega, Nat.mod_eq_of_lt (by omega)]
        by_cases hlt1 : x.val + s < k
        · rw [Nat.mod_eq_of_lt hlt1, show m.val + s = k - 1 by omega, Nat.mod_eq_of_lt (by omega)] at h1
          omega
        · have h2 : x.val + s - k < k := by omega
          have h3 : (x.val + s) % k = x.val + s - k := by
            have hxlt : x.val < k := x.isLt
            conv_lhs => rw [show x.val + s = (x.val + s - k) + k by omega]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt h2]
          rw [h3, show m.val + s = k - 1 by omega, Nat.mod_eq_of_lt (by omega)] at h1
          omega
      exact hm (hxm ▸ hxI)
    have hlt_k : (ix hk0 (x.val + s)).val < k := (ix hk0 (x.val + s)).isLt
    have hne_val : (ix hk0 (x.val + s)).val ≠ k - 1 := fun h => hne (Fin.ext h)
    omega
  rw [← hrot]
  have hbound := indepCount_subset_interval_le hk (k - 1) (by omega) 0 (by omega) I' hlt
  rw [hcard] at hbound
  have hp_pos : 1 ≤ k - I.card := by
    have : I.card < k := by
      have := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hI)
      simpa using this
    omega
  have heq_r : k - 1 + 1 - I.card = k - I.card := by omega
  rw [heq_r] at hbound
  have hMB : Mbound I.card (k - I.card) = Bval k (k - I.card) := by
    unfold Mbound Bval
    have hp0 : k - I.card ≠ 0 := by omega
    simp only [hp0, ↓reduceIte]
    split_ifs with h1 h2
    · omega
    · congr 1; omega
    · congr 2; omega
    · omega
  rw [← hMB]
  exact hbound

open scoped Classical in
lemma exists_free_coords {k : ℕ} (V : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    ∃ I : Finset (Fin k), I.card = Module.finrank (ZMod 2) V ∧
      Function.Bijective (fun (v : V) (i : I) => v.val i.val) := by
  suffices h : ∀ m (V : Submodule (ZMod 2) (Fin k → ZMod 2)),
      Module.finrank (ZMod 2) V = m →
      ∃ I : Finset (Fin k), I.card = m ∧
        Function.Injective (fun (v : V) (i : I) => v.val i.val) by
    obtain ⟨I, hIcard, hinj⟩ := h _ V rfl
    refine ⟨I, hIcard, (Fintype.bijective_iff_injective_and_card _).mpr ?_⟩
    refine ⟨hinj, ?_⟩
    have hcV : Fintype.card V = 2 ^ Module.finrank (ZMod 2) V := by
      have := Module.card_eq_pow_finrank (K := ZMod 2) (V := V)
      simpa [Nat.card_eq_fintype_card, ZMod.card] using this
    rw [hcV, Fintype.card_fun, ZMod.card, Fintype.card_coe, hIcard]
  intro m
  induction m with
  | zero =>
    intro V hV
    refine ⟨∅, rfl, ?_⟩
    intro v1 v2 _
    have hbot : V = ⊥ := Submodule.finrank_eq_zero.mp hV
    have h1 : v1.val = 0 := by simpa [hbot] using v1.property
    have h2 : v2.val = 0 := by simpa [hbot] using v2.property
    exact Subtype.ext (h1.trans h2.symm)
  | succ m ih =>
    intro V hV
    have hne : V ≠ ⊥ := fun h => by rw [h, finrank_bot] at hV; omega
    obtain ⟨w, hwV, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hex_i : ∃ i : Fin k, w i ≠ 0 := by
      by_contra hall; push_neg at hall; exact hw0 (funext hall)
    obtain ⟨i, hi⟩ := hex_i
    let ev : V →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun v => v.val i
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let V' : Submodule (ZMod 2) (Fin k → ZMod 2) := (LinearMap.ker ev).map V.subtype
    have hsurj : Function.Surjective ev := by
      intro c
      have hwi : w i = 1 := zmod2_eq_one_of_ne_zero hi
      refine ⟨c • ⟨w, hwV⟩, ?_⟩
      change (c • w) i = c
      simp [hwi]
    have hker_dim : Module.finrank (ZMod 2) (LinearMap.ker ev) = m := by
      have hrank := LinearMap.finrank_range_add_finrank_ker ev
      have hrange : LinearMap.range ev = ⊤ := LinearMap.range_eq_top.mpr hsurj
      rw [hrange, finrank_top, Module.finrank_self, hV] at hrank
      omega
    have hV'_dim : Module.finrank (ZMod 2) V' = m := by
      rw [Submodule.finrank_map_subtype_eq, hker_dim]
    obtain ⟨I', hI'card, hI'inj⟩ := ih V' hV'_dim
    have hi_not : i ∉ I' := by
      intro hi'

      have hcardV' : Fintype.card V' = 2 ^ m := by
        have := Module.card_eq_pow_finrank (K := ZMod 2) (V := V')
        simpa [Nat.card_eq_fintype_card, ZMod.card, hV'_dim] using this
      have hbij : Function.Bijective (fun (v : V') (j : I') => v.val j.val) :=
        (Fintype.bijective_iff_injective_and_card _).mpr
          ⟨hI'inj, by rw [hcardV', Fintype.card_fun, ZMod.card, Fintype.card_coe, hI'card]⟩
      obtain ⟨v, hv⟩ := hbij.2 (fun _ => 1)
      have hvi : v.val i = 1 := congrFun hv ⟨i, hi'⟩
      obtain ⟨u, hu_ker, hu_eq⟩ := v.property
      have h0 : v.val i = 0 := by rw [← hu_eq]; exact hu_ker
      rw [h0] at hvi; exact zero_ne_one hvi
    refine ⟨insert i I', by rw [Finset.card_insert_of_notMem hi_not, hI'card], ?_⟩
    intro v1 v2 heq
    have hv_diff_i : (v1 - v2).val i = 0 := by
      have h1 := congrFun heq ⟨i, Finset.mem_insert_self i I'⟩
      change v1.val i - v2.val i = 0
      dsimp only at h1; rw [h1, sub_self]
    have hmem : (v1 - v2).val ∈ V' := ⟨v1 - v2, hv_diff_i, rfl⟩
    have hzero : (⟨(v1 - v2).val, hmem⟩ : V') = 0 := by
      apply hI'inj
      funext ⟨j, hj⟩
      have hj' := congrFun heq ⟨j, Finset.mem_insert_of_mem hj⟩
      change v1.val j - v2.val j = 0
      dsimp only at hj'; rw [hj', sub_self]
    have hsub0 : v1.val - v2.val = 0 := congrArg Subtype.val hzero
    exact Subtype.ext (sub_eq_zero.mp hsub0)

lemma quad_le_indepCount_of_ne_univ {k : ℕ} (hk : 2 ≤ k) :
    ∀ (m : ℕ) (I : Finset (Fin k)) (hI : I ≠ Finset.univ) (hm : I.card = m)
      (H : Finset (I → ZMod 2))
      (hquad : ∀ u : I, ∀ hv : ix (by omega : 0 < k) (u.val.val + 1) ∈ I,
        ∃ (L : (I → ZMod 2) →ₗ[ZMod 2] ZMod 2) (c : ZMod 2),
          ∀ x ∈ H, x u * x ⟨ix (by omega : 0 < k) (u.val.val + 1), hv⟩ = L x + c),
      H.card ≤ indepCount (by omega : 0 < k) I := by
  have hk0 : 0 < k := by omega
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro I hI hm H hquad
    by_cases hedge : ∃ u : I, ix hk0 (u.val.val + 1) ∈ I
    ·
      have hend : ∃ u : I, ix hk0 (u.val.val + 1) ∈ I ∧ ix hk0 (u.val.val + k - 1) ∉ I := by
        obtain ⟨u0, hu0_next⟩ := hedge
        have hstep_back : ∀ t : ℕ, ∃ u : Fin k, u ∈ I ∧ ix hk0 (u.val + 1) ∈ I ∧
            (ix hk0 (u.val + k - 1) ∉ I ∨ ∀ r ≤ t, ix hk0 (u0.val.val + k - r % k) ∈ I) := by
          intro t
          induction t with
          | zero =>
            refine ⟨u0.val, u0.property, hu0_next, Or.inr fun r hr => ?_⟩
            have hr0 : r = 0 := by omega
            subst hr0
            simpa [ix, Nat.mod_eq_of_lt u0.val.isLt] using u0.property
          | succ t iht =>
            obtain ⟨u, huI, hunext, hdisj⟩ := iht
            rcases hdisj with hdone | hall
            · exact ⟨u, huI, hunext, Or.inl hdone⟩
            · let w := ix hk0 (u0.val.val + k - (t + 1) % k)
              have hw_next : ix hk0 (w.val + 1) = ix hk0 (u0.val.val + k - t % k) := by
                apply Fin.ext; simp only [w, ix]
                have ht1 := Nat.mod_lt (t + 1) hk0
                have ht0 := Nat.mod_lt t hk0
                by_cases hmod : t % k + 1 < k
                · have hmt : (t + 1) % k = t % k + 1 := by
                    rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt hmod]
                  rw [hmt]
                  have : ((u0.val.val + k - (t % k + 1)) % k + 1) % k = (u0.val.val + k - t % k) % k := by
                    rw [Nat.mod_add_mod]; congr 1; omega
                  exact this
                · have hmt : t % k = k - 1 := by omega
                  have hmt1 : (t + 1) % k = 0 := by
                    rw [← Nat.mod_add_mod, hmt, show k - 1 + 1 = k by omega, Nat.mod_self]
                  rw [hmt, hmt1, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt u0.val.isLt]
                  have : (u0.val.val + 1) % k = (u0.val.val + k - (k - 1)) % k := by congr 1; omega
                  exact this
              by_cases hwI : w ∈ I
              · refine ⟨w, hwI, hw_next ▸ hall t le_rfl, Or.inr fun r hr => ?_⟩
                by_cases hrt : r ≤ t
                · exact hall r hrt
                · have hreq : r = t + 1 := by omega
                  subst hreq; exact hwI
              · have hu_cur := hall t le_rfl
                have hprev_eq : ix hk0 ((ix hk0 (u0.val.val + k - t % k)).val + k - 1) = w := by
                  apply Fin.ext; simp only [w, ix]
                  have ht1 := Nat.mod_lt (t + 1) hk0
                  have ht0 := Nat.mod_lt t hk0
                  by_cases hmod : t % k + 1 < k
                  · have hmt : (t + 1) % k = t % k + 1 := by
                      rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt hmod]
                    rw [hmt]
                    have h1 : (u0.val.val + k - t % k) % k + k - 1 = (u0.val.val + k - t % k) % k + (k - 1) := by omega
                    rw [h1, Nat.mod_add_mod]
                    have : u0.val.val + k - t % k + (k - 1) = (u0.val.val + k - (t % k + 1)) + k := by omega
                    rw [this, Nat.add_mod_right]
                  · have hmt : t % k = k - 1 := by omega
                    have hmt1 : (t + 1) % k = 0 := by
                      rw [← Nat.mod_add_mod, hmt, show k - 1 + 1 = k by omega, Nat.mod_self]
                    rw [hmt, hmt1, Nat.sub_zero, Nat.add_mod_right]
                    have h1 : (u0.val.val + k - (k - 1)) % k + k - 1 = (u0.val.val + 1) % k + (k - 1) := by
                      have he : u0.val.val + k - (k - 1) = u0.val.val + 1 := by omega
                      rw [he]; omega
                    rw [h1, Nat.mod_add_mod, show u0.val.val + 1 + (k - 1) = u0.val.val + k by omega,
                        Nat.add_mod_right]
                by_cases ht0 : t = 0
                · subst ht0
                  have h0eq : ix hk0 (u0.val.val + k - 0 % k) = u0.val := by
                    apply Fin.ext; simp [ix, Nat.mod_eq_of_lt u0.val.isLt]
                  rw [h0eq] at hprev_eq
                  exact ⟨u0.val, u0.property, hu0_next, Or.inl (hprev_eq ▸ hwI)⟩
                · have hnext_mem : ix hk0 ((ix hk0 (u0.val.val + k - t % k)).val + 1) ∈ I := by
                    have hstep1 : ix hk0 ((ix hk0 (u0.val.val + k - t % k)).val + 1) =
                        ix hk0 (u0.val.val + k - (t - 1) % k) := by
                      apply Fin.ext; simp only [ix]
                      have ht0' := Nat.mod_lt (t - 1) hk0
                      by_cases hmod : (t - 1) % k + 1 < k
                      · have hmt : t % k = (t - 1) % k + 1 := by
                          conv_lhs => rw [show t = (t - 1) + 1 by omega]
                          rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt hmod]
                        rw [hmt, Nat.mod_add_mod]; congr 1; omega
                      · have hmt1 : (t - 1) % k = k - 1 := by omega
                        have hmt : t % k = 0 := by
                          rw [show t = (t - 1) + 1 by omega, ← Nat.mod_add_mod, hmt1,
                              show k - 1 + 1 = k by omega, Nat.mod_self]
                        rw [hmt, hmt1, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt u0.val.isLt]
                        have : u0.val.val + k - (k - 1) = u0.val.val + 1 := by omega
                        rw [this]
                    rw [hstep1]
                    exact hall (t - 1) (by omega)
                  exact ⟨ix hk0 (u0.val.val + k - t % k), hu_cur, hnext_mem, Or.inl (hprev_eq ▸ hwI)⟩
        obtain ⟨u, huI, hunext, hdisj⟩ := hstep_back k
        rcases hdisj with hdone | hall
        · exact ⟨⟨u, huI⟩, hunext, hdone⟩
        · exfalso; apply hI; ext z; simp only [Finset.mem_univ, iff_true]
          let r := (u0.val.val + k - z.val) % k
          have hr : r ≤ k := le_of_lt (Nat.mod_lt _ hk0)
          have hz_eq : ix hk0 (u0.val.val + k - r % k) = z := by
            apply Fin.ext; simp only [ix, r]
            rw [Nat.mod_mod]
            have hlt_r : (u0.val.val + k - z.val) % k < k := Nat.mod_lt _ hk0
            by_cases hle : z.val ≤ u0.val.val
            · have h1 : (u0.val.val + k - z.val) % k = u0.val.val - z.val := by
                rw [show u0.val.val + k - z.val = (u0.val.val - z.val) + k by omega,
                    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
              rw [h1, show u0.val.val + k - (u0.val.val - z.val) = z.val + k by omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt]
            · have h1 : (u0.val.val + k - z.val) % k = u0.val.val + k - z.val :=
                Nat.mod_eq_of_lt (by omega)
              rw [h1, show u0.val.val + k - (u0.val.val + k - z.val) = z.val by omega,
                  Nat.mod_eq_of_lt z.isLt]
          exact hz_eq ▸ hall r hr
      obtain ⟨u, hv_mem, hprev⟩ := hend
      let v : I := ⟨ix hk0 (u.val.val + 1), hv_mem⟩
      have huv_ne : v ≠ u := by
        intro h
        have hval := congrArg (fun z : I => z.val.val) h
        simp only [v, ix] at hval
        by_cases hlt : u.val.val + 1 < k
        · rw [Nat.mod_eq_of_lt hlt] at hval; omega
        · have hu1 : u.val.val + 1 = k := by omega
          rw [hu1, Nat.mod_self] at hval; omega
      obtain ⟨L, c, hL⟩ := hquad u hv_mem
      let α : ZMod 2 := L (Pi.single u 1)
      let β : ZMod 2 := L (Pi.single v 1)

      let H0 := H.filter (fun x => x u = 0)
      let H1 := H.filter (fun x => x u = 1)
      have hcard_split : H.card = H0.card + H1.card := by
        have := (Finset.card_filter_add_card_filter_not (s := H) (fun x => x u = 0)).symm
        rw [this]; congr 1; congr 1; ext x; simp only [H1, Finset.mem_filter]
        exact ⟨fun ⟨hx, hne⟩ => ⟨hx, zmod2_eq_one_of_ne_zero hne⟩,
               fun ⟨hx, h1⟩ => ⟨hx, by rw [h1]; decide⟩⟩

      have bound_erase_u : ∀ (b_u : ZMod 2) (S : Finset (I → ZMod 2)),
          S ⊆ H → (∀ x ∈ S, x u = b_u) → S.card ≤ indepCount hk0 (I.erase u.val) := by
        intro b_u S hSH hS_u
        let I1 := I.erase u.val
        let restr : (I → ZMod 2) → (I1 → ZMod 2) := fun x j => x ⟨j.val, Finset.mem_of_mem_erase j.property⟩
        let lift : (I1 → ZMod 2) → (I → ZMod 2) := fun y j =>
          if hj : j = u then b_u else y ⟨j.val, Finset.mem_erase.mpr ⟨fun h => hj (Subtype.ext h), j.property⟩⟩
        let liftLin : (I1 → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2) :=
          { toFun := fun y j => if hj : j = u then 0 else y ⟨j.val, Finset.mem_erase.mpr ⟨fun h => hj (Subtype.ext h), j.property⟩⟩
            map_add' := fun y1 y2 => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp
            map_smul' := fun r y => by funext j; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
        let liftC : I → ZMod 2 := fun j => if j = u then b_u else 0
        have hlift_eq : ∀ x ∈ S, lift (restr x) = x := by
          intro x hx; funext j; simp only [lift, restr]
          split_ifs with hj
          · rw [hj, hS_u x hx]
          · rfl
        have hlift_aff : ∀ y, lift y = liftLin y + liftC := by
          intro y; funext j; simp only [lift, liftLin, liftC, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
          split_ifs <;> simp
        have hinj : Set.InjOn restr S := by
          intro x1 hx1 x2 hx2 heq
          rw [← hlift_eq x1 hx1, ← hlift_eq x2 hx2, heq]
        rw [← Finset.card_image_of_injOn hinj]
        refine ih I1.card (by rw [← hm]; exact Finset.card_erase_lt_of_mem u.property)
          I1 (fun h => by have : u.val ∉ I1 := Finset.notMem_erase _ _; rw [h] at this; exact this (Finset.mem_univ _))
          rfl (S.image restr) ?_
        intro a ha_next
        have haI : a.val ∈ I := Finset.mem_of_mem_erase a.property
        have hanI : ix hk0 (a.val.val + 1) ∈ I := Finset.mem_of_mem_erase ha_next
        obtain ⟨La, ca, hLa⟩ := hquad ⟨a.val, haI⟩ hanI
        refine ⟨La.comp liftLin, La liftC + ca, ?_⟩
        intro y hy
        obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
        have h1 := hLa x (hSH hxS)
        have h2 : La x = La (liftLin (restr x)) + La liftC := by
          rw [← map_add, ← hlift_aff, hlift_eq x hxS]
        simpa [restr, LinearMap.comp_apply, h2, add_assoc] using h1

      have bound_erase_uv : ∀ (b_u : ZMod 2) (S : Finset (I → ZMod 2))
          (Lv : (((I.erase u.val).erase v.val) → ZMod 2) →ₗ[ZMod 2] ZMod 2) (cv : ZMod 2),
          S ⊆ H → (∀ x ∈ S, x u = b_u) →
          (∀ x ∈ S, x v = Lv (fun j => x ⟨j.val, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase j.property)⟩) + cv) →
          S.card ≤ indepCount hk0 ((I.erase u.val).erase v.val) := by
        intro b_u S Lv cv hSH hS_u hS_v
        let I2 := (I.erase u.val).erase v.val
        let restr : (I → ZMod 2) → (I2 → ZMod 2) := fun x j =>
          x ⟨j.val, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase j.property)⟩
        let liftLin : (I2 → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2) :=
          { toFun := fun y j =>
              if hj : j = u then 0
              else if hjv : j = v then Lv y
              else y ⟨j.val, Finset.mem_erase.mpr ⟨fun h => hjv (Subtype.ext h),
                Finset.mem_erase.mpr ⟨fun h => hj (Subtype.ext h), j.property⟩⟩⟩
            map_add' := fun y1 y2 => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp [map_add]
            map_smul' := fun r y => by funext j; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp [map_smul] }
        let liftC : I → ZMod 2 := fun j => if j = u then b_u else if j = v then cv else 0
        have hlift_eq : ∀ x ∈ S, liftLin (restr x) + liftC = x := by
          intro x hx; funext j
          simp only [liftLin, liftC, restr, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
          split_ifs with hju hjv
          · rw [hju, zero_add, hS_u x hx]
          · rw [hjv, hS_v x hx]
          · simp
        have hinj : Set.InjOn restr S := by
          intro x1 hx1 x2 hx2 heq
          rw [← hlift_eq x1 hx1, ← hlift_eq x2 hx2, heq]
        rw [← Finset.card_image_of_injOn hinj]
        have hcard_lt : I2.card < m := by
          rw [← hm]
          have h1 : I2.card ≤ (I.erase u.val).card := Finset.card_erase_le
          have h2 : (I.erase u.val).card < I.card := Finset.card_erase_lt_of_mem u.property
          omega
        refine ih I2.card hcard_lt I2
          (fun h => by have : v.val ∉ I2 := Finset.notMem_erase _ _; rw [h] at this; exact this (Finset.mem_univ _))
          rfl (S.image restr) ?_
        intro a ha_next
        have haI : a.val ∈ I := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase a.property)
        have hanI : ix hk0 (a.val.val + 1) ∈ I := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha_next)
        obtain ⟨La, ca, hLa⟩ := hquad ⟨a.val, haI⟩ hanI
        refine ⟨La.comp liftLin, La liftC + ca, ?_⟩
        intro y hy
        obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
        have h1 := hLa x (hSH hxS)
        have h2 : La x = La (liftLin (restr x)) + La liftC := by
          rw [← map_add, hlift_eq x hxS]
        simpa [restr, LinearMap.comp_apply, h2, add_assoc] using h1

      let I2 := (I.erase u.val).erase v.val
      let embed2 : (I2 → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2) :=
        { toFun := fun y j =>
            if hj : j = u then 0
            else if hjv : j = v then 0
            else y ⟨j.val, Finset.mem_erase.mpr ⟨fun h => hjv (Subtype.ext h),
              Finset.mem_erase.mpr ⟨fun h => hj (Subtype.ext h), j.property⟩⟩⟩
          map_add' := fun y1 y2 => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp
          map_smul' := fun r y => by funext j; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
      let Lrest : (I2 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := L.comp embed2
      have hL_decomp : ∀ x : I → ZMod 2,
          L x = α * x u + β * x v +
            Lrest (fun j => x ⟨j.val, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase j.property)⟩) := by
        intro x
        have hx_eq : x = x u • Pi.single u 1 + x v • Pi.single v 1 +
            embed2 (fun j => x ⟨j.val, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase j.property)⟩) := by
          funext j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, embed2, LinearMap.coe_mk, AddHom.coe_mk]
          by_cases hju : j = u
          · subst hju; simp [Pi.single_eq_same, Pi.single_eq_of_ne huv_ne.symm]
          · by_cases hjv : j = v
            · subst hjv; simp [Pi.single_eq_same, Pi.single_eq_of_ne huv_ne]
            · simp [hju, hjv, Pi.single_eq_of_ne hju, Pi.single_eq_of_ne hjv]
        conv_lhs => rw [hx_eq]
        simp [map_add, map_smul, α, β, Lrest, LinearMap.comp_apply, mul_comm]
      rw [hcard_split, indepCount_erase_endpoint hk I u.val u.property hprev]
      by_cases hβ : β = 0
      ·
        have hH0 : H0.card ≤ indepCount hk0 (I.erase u.val) :=
          bound_erase_u 0 H0 (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2)
        have hH1 : H1.card ≤ indepCount hk0 ((I.erase u.val).erase v.val) := by
          refine bound_erase_uv 1 H1 Lrest (α + c) (Finset.filter_subset _ _)
            (fun x hx => (Finset.mem_filter.mp hx).2) ?_
          intro x hx
          have hxH : x ∈ H := (Finset.mem_filter.mp hx).1
          have hxu : x u = 1 := (Finset.mem_filter.mp hx).2
          have h1 := hL x hxH
          rw [hL_decomp x, hxu, hβ] at h1
          simp only [one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero] at h1; rw [h1]; ring
        exact Nat.add_le_add hH0 hH1
      ·
        have hβ1 : β = 1 := zmod2_eq_one_of_ne_zero hβ
        have hH1 : H1.card ≤ indepCount hk0 (I.erase u.val) :=
          bound_erase_u 1 H1 (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2)
        have hH0 : H0.card ≤ indepCount hk0 ((I.erase u.val).erase v.val) := by
          refine bound_erase_uv 0 H0 Lrest c (Finset.filter_subset _ _)
            (fun x hx => (Finset.mem_filter.mp hx).2) ?_
          intro x hx
          have hxH : x ∈ H := (Finset.mem_filter.mp hx).1
          have hxu : x u = 0 := (Finset.mem_filter.mp hx).2
          have h1 := hL x hxH
          rw [hL_decomp x, hxu, hβ1] at h1
          simp only [zero_mul, mul_zero, zero_add, one_mul] at h1

          have hadd : x v + x v = 0 := zmod2_add_self (x v)
          calc x v = x v + 0 := (add_zero _).symm
            _ = x v + (x v + Lrest (fun j => x ⟨j.val, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase j.property)⟩) + c) := by rw [← h1]
            _ = (x v + x v) + (Lrest (fun j => x ⟨j.val, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase j.property)⟩) + c) := by ring
            _ = Lrest (fun j => x ⟨j.val, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase j.property)⟩) + c := by rw [hadd, zero_add]
        rw [add_comm]
        exact Nat.add_le_add hH1 hH0
    ·
      push_neg at hedge
      have hindep : indepCount hk0 I = 2 ^ I.card := by
        unfold indepCount
        have hfilt : I.powerset.filter (fun S => ∀ u ∈ S, ix hk0 (u.val + 1) ∉ S) = I.powerset := by
          refine Finset.filter_true_of_mem fun S hS u hu hnext => ?_
          have hsub := Finset.mem_powerset.mp hS
          exact hedge ⟨u, hsub hu⟩ (hsub hnext)
        rw [hfilt, Finset.card_powerset]
      rw [hindep]
      calc H.card ≤ (Finset.univ : Finset (I → ZMod 2)).card := Finset.card_le_univ H
        _ = 2 ^ I.card := by simp [Fintype.card_fun, ZMod.card]

lemma quad_le_Bval_zero {k : ℕ} (hk : 2 ≤ k)
    (H : Finset (Fin k → ZMod 2))
    (hquad : ∀ u : Fin k, ∃ (L : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (c : ZMod 2),
      ∀ x ∈ H, x u * x (ix (by omega : 0 < k) (u.val + 1)) = L x + c) :
    H.card ≤ Bval k 0 := by
  have hk0 : 0 < k := by omega
  unfold Bval; simp only [↓reduceIte]
  by_cases hk2 : k = 2
  · subst hk2
    have hfib : Nat.fib (2 - 1) + Nat.fib (2 + 1) = 3 := rfl
    rw [hfib]
    by_contra hgt
    push_neg at hgt
    have hall : H = Finset.univ := Finset.eq_univ_of_card H (by
      have hc : Fintype.card (Fin 2 → ZMod 2) = 4 := by simp [Fintype.card_fun, ZMod.card]
      have hle : H.card ≤ 4 := hc ▸ Finset.card_le_univ H
      omega)
    obtain ⟨L, c, hL⟩ := hquad 0
    have h00 := hL ![0, 0] (by rw [hall]; exact Finset.mem_univ _)
    have h10 := hL ![1, 0] (by rw [hall]; exact Finset.mem_univ _)
    have h01 := hL ![0, 1] (by rw [hall]; exact Finset.mem_univ _)
    have h11 := hL ![1, 1] (by rw [hall]; exact Finset.mem_univ _)
    have hsum : (![1, 1] : Fin 2 → ZMod 2) = ![1, 0] + ![0, 1] := by ext i; fin_cases i <;> decide
    have h0eq : (![0, 0] : Fin 2 → ZMod 2) = 0 := by ext i; fin_cases i <;> rfl
    rw [h0eq, map_zero, zero_add] at h00
    rw [hsum, map_add] at h11
    have hc0 : c = 0 := by simpa [ix] using h00.symm
    have hL10 : L ![1, 0] = 0 := by simpa [ix, hc0] using h10.symm
    have hL01 : L ![0, 1] = 0 := by simpa [ix, hc0] using h01.symm
    have hbad : (1 : ZMod 2) = 0 := by simpa [ix, hc0, hL10, hL01] using h11
    exact one_ne_zero hbad
  ·
    have hk3 : 3 ≤ k := by omega
    let u0 : Fin k := ⟨0, hk0⟩
    let u1 : Fin k := ⟨1, by omega⟩
    let uk : Fin k := ⟨k - 1, by omega⟩
    have h01 : u1 ≠ u0 := by intro h; have := congrArg Fin.val h; simp [u0, u1] at this
    have h0k : uk ≠ u0 := by intro h; have := congrArg Fin.val h; simp [u0, uk] at this; omega
    have h1k : uk ≠ u1 := by intro h; have := congrArg Fin.val h; simp [u1, uk] at this; omega
    obtain ⟨L1, c1, hL1⟩ := hquad u0
    obtain ⟨L2, c2, hL2⟩ := hquad uk
    have hix0 : ix hk0 (u0.val + 1) = u1 := by apply Fin.ext; simp [u0, u1, ix, Nat.mod_eq_of_lt (show 1 < k by omega)]
    have hixk : ix hk0 (uk.val + 1) = u0 := by
      apply Fin.ext; simp [u0, uk, ix, show k - 1 + 1 = k by omega]
    let H0 := H.filter (fun x => x u0 = 0)
    let H1 := H.filter (fun x => x u0 = 1)
    have hsplit : H.card = H0.card + H1.card := by
      have := (Finset.card_filter_add_card_filter_not (s := H) (fun x => x u0 = 0)).symm
      rw [this]; congr 1; congr 1; ext x; simp only [H1, Finset.mem_filter]
      exact ⟨fun ⟨hx, hne⟩ => ⟨hx, zmod2_eq_one_of_ne_zero hne⟩,
             fun ⟨hx, h1⟩ => ⟨hx, by rw [h1]; decide⟩⟩

    have bound_sub : ∀ (I : Finset (Fin k)) (hI : I ≠ Finset.univ) (S : Finset (Fin k → ZMod 2))
        (liftLin : (I → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (liftC : Fin k → ZMod 2),
        S ⊆ H → (∀ x ∈ S, liftLin (fun j => x j.val) + liftC = x) →
        S.card ≤ indepCount hk0 I := by
      intro I hI S liftLin liftC hSH hlift
      let restr : (Fin k → ZMod 2) → (I → ZMod 2) := fun x j => x j.val
      have hinj : Set.InjOn restr S := by
        intro x1 hx1 x2 hx2 heq
        have heq' : (fun j : I => x1 j.val) = (fun j : I => x2 j.val) := heq; rw [← hlift x1 hx1, ← hlift x2 hx2, heq']
      rw [← Finset.card_image_of_injOn hinj]
      refine quad_le_indepCount_of_ne_univ hk I.card I hI rfl (S.image restr) ?_
      intro a han
      obtain ⟨La, ca, hLa⟩ := hquad a.val
      refine ⟨La.comp liftLin, La liftC + ca, ?_⟩
      intro y hy
      obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hy
      have h1 := hLa x (hSH hxS)
      have h2 : La x = La (liftLin (restr x)) + La liftC := by rw [← map_add, hlift x hxS]
      simpa [restr, LinearMap.comp_apply, h2, add_assoc] using h1

    let b1 : ZMod 2 := L1 (Pi.single u1 1)
    let b2 : ZMod 2 := L2 (Pi.single uk 1)

    have bound_0 : ∀ (v0 : ZMod 2) (S : Finset (Fin k → ZMod 2)),
        S ⊆ H → (∀ x ∈ S, x u0 = v0) → S.card ≤ Nat.fib (k + 1) := by
      intro v0 S hSH hS0
      let I1 := (Finset.univ : Finset (Fin k)).erase u0
      have hI1 : I1 ≠ Finset.univ := fun h => by
        have : u0 ∉ I1 := Finset.notMem_erase _ _; rw [h] at this; exact this (Finset.mem_univ _)
      have hle := bound_sub I1 hI1 S
        { toFun := fun y j => if hj : j = u0 then 0 else y ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩⟩
          map_add' := fun _ _ => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp
          map_smul' := fun _ _ => by funext j; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
        (fun j => if j = u0 then v0 else 0) hSH (fun x hx => by
          funext j; simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
          split_ifs with hj
          · rw [hj, zero_add, hS0 x hx]
          · simp)
      have heqI1 : I1 = Finset.univ.filter (fun i : Fin k => 1 ≤ i.val ∧ i.val < 1 + (k - 1)) := by
        ext i; have := i.isLt; simp only [I1, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter, true_and, ne_eq, Fin.ext_iff]; change ¬(i.val = 0) ↔ 1 ≤ i.val ∧ i.val < 1 + (k - 1); omega
      have hrot1 : indepCount hk0 I1 = indepCount hk0 (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 1))) := by
        have hIm : (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 1))).image
            (fun i => ix hk0 (i.val + 1)) = I1 := by
          ext i; have := i.isLt; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, heqI1, zero_add]
          constructor
          · rintro ⟨a, ha, rfl⟩; simp [ix, Nat.mod_eq_of_lt (show a.val + 1 < k by omega)]; omega
          · intro hi; refine ⟨⟨i.val - 1, by omega⟩, by dsimp only; omega, ?_⟩
            apply Fin.ext; simp [ix, Nat.mod_eq_of_lt (show i.val - 1 + 1 < k by omega)]; omega
        rw [← hIm, indepCount_rot hk0 1]
      rw [hrot1, indepCount_interval hk 0 (k - 1) (by omega), show k - 1 + 2 = k + 1 by omega] at hle
      exact hle

    have bound_01 : ∀ (v0 : ZMod 2) (S : Finset (Fin k → ZMod 2))
        (Lw : (((Finset.univ : Finset (Fin k)).erase u0).erase u1 → ZMod 2) →ₗ[ZMod 2] ZMod 2) (cw : ZMod 2),
        S ⊆ H → (∀ x ∈ S, x u0 = v0) → (∀ x ∈ S, x u1 = Lw (fun j => x j.val) + cw) →
        S.card ≤ Nat.fib k := by
      intro v0 S Lw cw hSH hS0 hS1
      let I2 := ((Finset.univ : Finset (Fin k)).erase u0).erase u1
      have hI2 : I2 ≠ Finset.univ := fun h => by
        have : u1 ∉ I2 := Finset.notMem_erase _ _
        rw [h] at this; exact this (Finset.mem_univ _)
      have hle := bound_sub I2 hI2 S
        { toFun := fun y j => if hj : j = u0 then 0 else if hj1 : j = u1 then Lw y else
            y ⟨j, Finset.mem_erase.mpr ⟨hj1, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩⟩⟩
          map_add' := fun _ _ => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp [map_add]
          map_smul' := fun _ _ => by funext j; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp [map_smul] }
        (fun j => if j = u0 then v0 else if j = u1 then cw else 0) hSH (fun x hx => by
          funext j; simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
          split_ifs with hj hj1
          · rw [hj, zero_add, hS0 x hx]
          · rw [hj1, hS1 x hx]
          · simp)
      have heqI2 : I2 = Finset.univ.filter (fun i : Fin k => 2 ≤ i.val ∧ i.val < 2 + (k - 2)) := by
        ext i; simp [I2, u0, u1, Fin.ext_iff]; omega
      have hrot : indepCount hk0 I2 = indepCount hk0 (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 2))) := by
        have hIm : (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 2))).image
            (fun i => ix hk0 (i.val + 2)) = I2 := by
          ext i; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, heqI2, zero_add]
          constructor
          · rintro ⟨a, ha, rfl⟩; simp [ix, Nat.mod_eq_of_lt (show a.val + 2 < k by omega)]; omega
          · intro hi; have := i.isLt; refine ⟨⟨i.val - 2, by omega⟩, by dsimp only; omega, ?_⟩
            apply Fin.ext; simp [ix, Nat.mod_eq_of_lt (show i.val - 2 + 2 < k by omega)]; omega
        rw [← hIm, indepCount_rot hk0 2]
      rw [hrot, indepCount_interval hk 0 (k - 2) (by omega), show k - 2 + 2 = k by omega] at hle
      exact hle

    have bound_0k : ∀ (v0 : ZMod 2) (S : Finset (Fin k → ZMod 2))
        (Lw : (((Finset.univ : Finset (Fin k)).erase u0).erase uk → ZMod 2) →ₗ[ZMod 2] ZMod 2) (cw : ZMod 2),
        S ⊆ H → (∀ x ∈ S, x u0 = v0) → (∀ x ∈ S, x uk = Lw (fun j => x j.val) + cw) →
        S.card ≤ Nat.fib k := by
      intro v0 S Lw cw hSH hS0 hSk
      let I2 := ((Finset.univ : Finset (Fin k)).erase u0).erase uk
      have hI2 : I2 ≠ Finset.univ := fun h => by
        have : uk ∉ I2 := Finset.notMem_erase _ _
        rw [h] at this; exact this (Finset.mem_univ _)
      have hle := bound_sub I2 hI2 S
        { toFun := fun y j => if hj : j = u0 then 0 else if hjk : j = uk then Lw y else
            y ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩⟩⟩
          map_add' := fun _ _ => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp [map_add]
          map_smul' := fun _ _ => by funext j; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp [map_smul] }
        (fun j => if j = u0 then v0 else if j = uk then cw else 0) hSH (fun x hx => by
          funext j; simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
          split_ifs with hj hjk
          · rw [hj, zero_add, hS0 x hx]
          · rw [hjk, hSk x hx]
          · simp)
      have heqI2 : I2 = Finset.univ.filter (fun i : Fin k => 1 ≤ i.val ∧ i.val < 1 + (k - 2)) := by
        ext i; simp [I2, u0, uk, Fin.ext_iff]; omega
      rw [heqI2, indepCount_interval hk 1 (k - 2) (by omega), show k - 2 + 2 = k by omega] at hle
      exact hle

    have bound_01k : ∀ (v0 : ZMod 2) (S : Finset (Fin k → ZMod 2))
        (L1w L2w : ((((Finset.univ : Finset (Fin k)).erase u0).erase u1).erase uk → ZMod 2) →ₗ[ZMod 2] ZMod 2)
        (c1w c2w : ZMod 2),
        S ⊆ H → (∀ x ∈ S, x u0 = v0) →
        (∀ x ∈ S, x u1 = L1w (fun j => x j.val) + c1w) →
        (∀ x ∈ S, x uk = L2w (fun j => x j.val) + c2w) →
        S.card ≤ Nat.fib (k - 1) := by
      intro v0 S L1w L2w c1w c2w hSH hS0 hS1 hSk
      let I3 := (((Finset.univ : Finset (Fin k)).erase u0).erase u1).erase uk
      have hI3 : I3 ≠ Finset.univ := fun h => by
        have : uk ∉ I3 := Finset.notMem_erase _ _
        rw [h] at this; exact this (Finset.mem_univ _)
      have hle := bound_sub I3 hI3 S
        { toFun := fun y j => if hj : j = u0 then 0 else if hj1 : j = u1 then L1w y
            else if hjk : j = uk then L2w y
            else y ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_erase.mpr ⟨hj1, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩⟩⟩⟩
          map_add' := fun _ _ => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp [map_add]
          map_smul' := fun _ _ => by funext j; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp [map_smul] }
        (fun j => if j = u0 then v0 else if j = u1 then c1w else if j = uk then c2w else 0) hSH (fun x hx => by
          funext j; simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
          split_ifs with hj hj1 hjk
          · rw [hj, zero_add, hS0 x hx]
          · rw [hj1, hS1 x hx]
          · rw [hjk, hSk x hx]
          · simp)
      have heqI3 : I3 = Finset.univ.filter (fun i : Fin k => 2 ≤ i.val ∧ i.val < 2 + (k - 3)) := by
        ext i; simp [I3, u0, u1, uk, Fin.ext_iff]; omega
      have hrot : indepCount hk0 I3 = indepCount hk0 (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 3))) := by
        have hIm : (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 3))).image
            (fun i => ix hk0 (i.val + 2)) = I3 := by
          ext i; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, heqI3, zero_add]
          constructor
          · rintro ⟨a, ha, rfl⟩; simp [ix, Nat.mod_eq_of_lt (show a.val + 2 < k by omega)]; omega
          · intro hi; have := i.isLt; refine ⟨⟨i.val - 2, by omega⟩, by dsimp only; omega, ?_⟩
            apply Fin.ext; simp [ix, Nat.mod_eq_of_lt (show i.val - 2 + 2 < k by omega)]; omega
        rw [← hIm, indepCount_rot hk0 2]
      rw [hrot, indepCount_interval hk 0 (k - 3) (by omega), show k - 3 + 2 = k - 1 by omega] at hle
      exact hle

    let I3 := (((Finset.univ : Finset (Fin k)).erase u0).erase u1).erase uk
    let emb3 : (I3 → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
      { toFun := fun y j => if hj : j = u0 then 0 else if hj1 : j = u1 then 0 else if hjk : j = uk then 0
          else y ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_erase.mpr ⟨hj1, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩⟩⟩⟩
        map_add' := fun _ _ => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp
        map_smul' := fun _ _ => by funext j; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
    have hdecomp3 : ∀ (L : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2) (x : Fin k → ZMod 2),
        L x = L (Pi.single u0 1) * x u0 + L (Pi.single u1 1) * x u1 +
              L (Pi.single uk 1) * x uk + L (emb3 (fun j => x j.val)) := by
      intro L x
      have hx : x = x u0 • Pi.single u0 1 + x u1 • Pi.single u1 1 + x uk • Pi.single uk 1 +
          emb3 (fun j => x j.val) := by
        funext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, emb3, LinearMap.coe_mk, AddHom.coe_mk]
        by_cases h0 : j = u0
        · subst h0; simp [Pi.single_eq_same, Pi.single_eq_of_ne h01.symm, Pi.single_eq_of_ne h0k.symm]
        · by_cases h1 : j = u1
          · subst h1; simp [Pi.single_eq_same, Pi.single_eq_of_ne h01, Pi.single_eq_of_ne h1k.symm]
          · by_cases hk' : j = uk
            · subst hk'; simp [Pi.single_eq_same, Pi.single_eq_of_ne h0k, Pi.single_eq_of_ne h1k]
            · simp [h0, h1, hk', Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne hk']
      conv_lhs => rw [hx]
      simp [map_add, map_smul]; ring

    let I01 := ((Finset.univ : Finset (Fin k)).erase u0).erase u1
    let emb01 : (I01 → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
      { toFun := fun y j => if hj : j = u0 then 0 else if hj1 : j = u1 then 0
          else y ⟨j, Finset.mem_erase.mpr ⟨hj1, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩⟩⟩
        map_add' := fun _ _ => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp
        map_smul' := fun _ _ => by funext j; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
    have hdecomp01 : ∀ (x : Fin k → ZMod 2),
        L1 x = L1 (Pi.single u0 1) * x u0 + b1 * x u1 + L1 (emb01 (fun j => x j.val)) := by
      intro x
      have hx : x = x u0 • Pi.single u0 1 + x u1 • Pi.single u1 1 + emb01 (fun j => x j.val) := by
        funext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, emb01, LinearMap.coe_mk, AddHom.coe_mk]
        by_cases h0 : j = u0
        · subst h0; simp [Pi.single_eq_same, Pi.single_eq_of_ne h01.symm]
        · by_cases h1 : j = u1
          · subst h1; simp [Pi.single_eq_same, Pi.single_eq_of_ne h01]
          · simp [h0, h1, Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1]
      conv_lhs => rw [hx]
      simp only [map_add, map_smul, smul_eq_mul, b1]; ring
    let I0k := ((Finset.univ : Finset (Fin k)).erase u0).erase uk
    let emb0k : (I0k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
      { toFun := fun y j => if hj : j = u0 then 0 else if hjk : j = uk then 0
          else y ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩⟩⟩
        map_add' := fun _ _ => by funext j; simp only [Pi.add_apply]; split_ifs <;> simp
        map_smul' := fun _ _ => by funext j; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp }
    have hdecomp0k : ∀ (x : Fin k → ZMod 2),
        L2 x = L2 (Pi.single u0 1) * x u0 + b2 * x uk + L2 (emb0k (fun j => x j.val)) := by
      intro x
      have hx : x = x u0 • Pi.single u0 1 + x uk • Pi.single uk 1 + emb0k (fun j => x j.val) := by
        funext j; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, emb0k, LinearMap.coe_mk, AddHom.coe_mk]
        by_cases h0 : j = u0
        · subst h0; simp [Pi.single_eq_same, Pi.single_eq_of_ne h0k.symm]
        · by_cases hk' : j = uk
          · subst hk'; simp [Pi.single_eq_same, Pi.single_eq_of_ne h0k]
          · simp [h0, hk', Pi.single_eq_of_ne h0, Pi.single_eq_of_ne hk']
      conv_lhs => rw [hx]
      simp only [map_add, map_smul, smul_eq_mul, b2]; ring

    let d1 : ZMod 2 := L1 (Pi.single uk 1)
    let d2 : ZMod 2 := L2 (Pi.single u1 1)
    have h2fib : 2 * Nat.fib k ≤ Nat.fib (k - 1) + Nat.fib (k + 1) := by
      have hk_eq : k + 1 = (k - 1) + 2 := by omega
      have hk_eq2 : k = (k - 1) + 1 := by omega
      rw [hk_eq, Nat.fib_add_two, ← hk_eq2]
      have := Nat.fib_mono (show k - 1 ≤ k by omega)
      have h3 : Nat.fib k = Nat.fib (k - 1) + Nat.fib (k - 2) := by
        conv_lhs => rw [show k = (k - 2) + 2 by omega]
        rw [Nat.fib_add_two, show k - 2 + 1 = k - 1 by omega]; ring
      have h4 : Nat.fib (k - 2) ≤ Nat.fib (k - 1) := Nat.fib_mono (by omega)
      omega
    have hfib_le : Nat.fib k ≤ Nat.fib (k + 1) := Nat.fib_mono (Nat.le_succ k)
    rw [hsplit]
    by_cases hb1 : b1 = 0 <;> by_cases hb2 : b2 = 0
    ·
      by_cases hd : d1 = 1 ∧ d2 = 1
      ·
        have hH0 : H0.card ≤ Nat.fib (k - 1) := by
          refine bound_01k 0 H0 (L2.comp emb3) (L1.comp emb3) c2 c1 (Finset.filter_subset _ _)
            (fun x hx => (Finset.mem_filter.mp hx).2) ?_ ?_
          · intro x hx
            have h2 := hL2 x (Finset.mem_filter.mp hx).1
            rw [hixk, (Finset.mem_filter.mp hx).2, hdecomp3 L2 x, (Finset.mem_filter.mp hx).2,
                show L2 (Pi.single uk 1) = b2 from rfl, hb2, show L2 (Pi.single u1 1) = d2 from rfl, hd.2] at h2
            simp only [mul_zero, zero_mul, zero_add, add_zero, one_mul] at h2
            have ha := zmod2_add_self (x u1)
            calc x u1 = x u1 + 0 := (add_zero _).symm
              _ = x u1 + (x u1 + L2 (emb3 (fun j => x j.val)) + c2) := by rw [← h2]
              _ = (x u1 + x u1) + (L2 (emb3 (fun j => x j.val)) + c2) := by ring
              _ = (L2.comp emb3) (fun j => x j.val) + c2 := by rw [ha, zero_add]; rfl
          · intro x hx
            have h1 := hL1 x (Finset.mem_filter.mp hx).1
            rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp3 L1 x, (Finset.mem_filter.mp hx).2,
                show L1 (Pi.single u1 1) = b1 from rfl, hb1, show L1 (Pi.single uk 1) = d1 from rfl, hd.1] at h1
            simp only [mul_zero, zero_mul, zero_add, add_zero, one_mul] at h1
            have ha := zmod2_add_self (x uk)
            calc x uk = x uk + 0 := (add_zero _).symm
              _ = x uk + (x uk + L1 (emb3 (fun j => x j.val)) + c1) := by rw [← h1]
              _ = (x uk + x uk) + (L1 (emb3 (fun j => x j.val)) + c1) := by ring
              _ = (L1.comp emb3) (fun j => x j.val) + c1 := by rw [ha, zero_add]; rfl
        have hH1 : H1.card ≤ Nat.fib k := by
          refine bound_01 1 H1 (L1.comp emb01) (L1 (Pi.single u0 1) + c1) (Finset.filter_subset _ _)
            (fun x hx => (Finset.mem_filter.mp hx).2) ?_
          intro x hx
          have h1 := hL1 x (Finset.mem_filter.mp hx).1
          rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp01 x, (Finset.mem_filter.mp hx).2, hb1] at h1
          simp only [one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero] at h1; simp only [LinearMap.comp_apply]; rw [h1]; ring
        omega
      ·
        have hH0 : H0.card ≤ Nat.fib (k + 1) :=
          bound_0 0 H0 (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2)
        have hH1 : H1.card ≤ Nat.fib (k - 1) := by
          have hd0 : d1 = 0 ∨ d2 = 0 := by
            by_contra h; push_neg at h
            exact hd ⟨zmod2_eq_one_of_ne_zero h.1, zmod2_eq_one_of_ne_zero h.2⟩
          rcases hd0 with hd1 | hd2
          ·
            let e1 := L1 (Pi.single u0 1) + c1
            let e2 := L2 (Pi.single u0 1) + c2
            refine bound_01k 1 H1 (L1.comp emb3) (d2 • (L1.comp emb3) + L2.comp emb3) e1 (d2 * e1 + e2)
              (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2) ?_ ?_
            · intro x hx
              have h1 := hL1 x (Finset.mem_filter.mp hx).1
              rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp3 L1 x, (Finset.mem_filter.mp hx).2,
                  show L1 (Pi.single u1 1) = b1 from rfl, hb1, show L1 (Pi.single uk 1) = d1 from rfl, hd1] at h1
              simp only [one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero] at h1; simp only [e1, LinearMap.comp_apply]; rw [h1]; ring
            · intro x hx
              have h1 := hL1 x (Finset.mem_filter.mp hx).1
              rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp3 L1 x, (Finset.mem_filter.mp hx).2,
                  show L1 (Pi.single u1 1) = b1 from rfl, hb1, show L1 (Pi.single uk 1) = d1 from rfl, hd1] at h1
              have hxu1 : x u1 = L1 (emb3 (fun j => x j.val)) + e1 := by
                simp only [one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero] at h1; simp only [e1]; rw [h1]; ring
              have h2 := hL2 x (Finset.mem_filter.mp hx).1
              rw [hixk, (Finset.mem_filter.mp hx).2, hdecomp3 L2 x, (Finset.mem_filter.mp hx).2,
                  show L2 (Pi.single uk 1) = b2 from rfl, hb2, show L2 (Pi.single u1 1) = d2 from rfl, hxu1] at h2
              simp only [mul_one, zero_mul, add_zero, LinearMap.add_apply, LinearMap.smul_apply,
                LinearMap.comp_apply, smul_eq_mul] at h2 ⊢
              rw [h2]; ring
          ·
            let e1 := L1 (Pi.single u0 1) + c1
            let e2 := L2 (Pi.single u0 1) + c2
            refine bound_01k 1 H1 (d1 • (L2.comp emb3) + L1.comp emb3) (L2.comp emb3) (d1 * e2 + e1) e2
              (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2) ?_ ?_
            · intro x hx
              have h2 := hL2 x (Finset.mem_filter.mp hx).1
              rw [hixk, (Finset.mem_filter.mp hx).2, hdecomp3 L2 x, (Finset.mem_filter.mp hx).2,
                  show L2 (Pi.single uk 1) = b2 from rfl, hb2, show L2 (Pi.single u1 1) = d2 from rfl, hd2] at h2
              have hxuk : x uk = L2 (emb3 (fun j => x j.val)) + e2 := by
                simp only [one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero] at h2; simp only [e2]; rw [h2]; ring
              have h1 := hL1 x (Finset.mem_filter.mp hx).1
              rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp3 L1 x, (Finset.mem_filter.mp hx).2,
                  show L1 (Pi.single u1 1) = b1 from rfl, hb1, show L1 (Pi.single uk 1) = d1 from rfl, hxuk] at h1
              simp only [one_mul, mul_one, zero_mul, add_zero, LinearMap.add_apply, LinearMap.smul_apply,
                LinearMap.comp_apply, smul_eq_mul] at h1 ⊢
              rw [h1]; ring
            · intro x hx
              have h2 := hL2 x (Finset.mem_filter.mp hx).1
              rw [hixk, (Finset.mem_filter.mp hx).2, hdecomp3 L2 x, (Finset.mem_filter.mp hx).2,
                  show L2 (Pi.single uk 1) = b2 from rfl, hb2, show L2 (Pi.single u1 1) = d2 from rfl, hd2] at h2
              simp only [one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero] at h2; simp only [e2, LinearMap.comp_apply]; rw [h2]; ring
        omega
    ·
      have hb2' : b2 = 1 := zmod2_eq_one_of_ne_zero hb2
      have hH0 : H0.card ≤ Nat.fib k := by
        refine bound_0k 0 H0 (L2.comp emb0k) c2 (Finset.filter_subset _ _)
          (fun x hx => (Finset.mem_filter.mp hx).2) ?_
        intro x hx
        have h2 := hL2 x (Finset.mem_filter.mp hx).1
        rw [hixk, (Finset.mem_filter.mp hx).2, hdecomp0k x, (Finset.mem_filter.mp hx).2, hb2'] at h2
        simp only [mul_zero, zero_add, one_mul] at h2
        have ha := zmod2_add_self (x uk)
        calc x uk = x uk + 0 := (add_zero _).symm
          _ = x uk + (x uk + L2 (emb0k (fun j => x j.val)) + c2) := by rw [← h2]
          _ = (x uk + x uk) + (L2 (emb0k (fun j => x j.val)) + c2) := by ring
          _ = (L2.comp emb0k) (fun j => x j.val) + c2 := by rw [ha, zero_add]; rfl
      have hH1 : H1.card ≤ Nat.fib k := by
        refine bound_01 1 H1 (L1.comp emb01) (L1 (Pi.single u0 1) + c1) (Finset.filter_subset _ _)
          (fun x hx => (Finset.mem_filter.mp hx).2) ?_
        intro x hx
        have h1 := hL1 x (Finset.mem_filter.mp hx).1
        rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp01 x, (Finset.mem_filter.mp hx).2, hb1] at h1
        simp only [one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero] at h1; simp only [LinearMap.comp_apply]; rw [h1]; ring
      omega
    ·
      have hb1' : b1 = 1 := zmod2_eq_one_of_ne_zero hb1
      have hH0 : H0.card ≤ Nat.fib k := by
        refine bound_01 0 H0 (L1.comp emb01) c1 (Finset.filter_subset _ _)
          (fun x hx => (Finset.mem_filter.mp hx).2) ?_
        intro x hx
        have h1 := hL1 x (Finset.mem_filter.mp hx).1
        rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp01 x, (Finset.mem_filter.mp hx).2, hb1'] at h1
        simp only [zero_mul, mul_zero, zero_add, one_mul] at h1
        have ha := zmod2_add_self (x u1)
        calc x u1 = x u1 + 0 := (add_zero _).symm
          _ = x u1 + (x u1 + L1 (emb01 (fun j => x j.val)) + c1) := by rw [← h1]
          _ = (x u1 + x u1) + (L1 (emb01 (fun j => x j.val)) + c1) := by ring
          _ = (L1.comp emb01) (fun j => x j.val) + c1 := by rw [ha, zero_add]; rfl
      have hH1 : H1.card ≤ Nat.fib k := by
        refine bound_0k 1 H1 (L2.comp emb0k) (L2 (Pi.single u0 1) + c2) (Finset.filter_subset _ _)
          (fun x hx => (Finset.mem_filter.mp hx).2) ?_
        intro x hx
        have h2 := hL2 x (Finset.mem_filter.mp hx).1
        rw [hixk, (Finset.mem_filter.mp hx).2, hdecomp0k x, (Finset.mem_filter.mp hx).2, hb2] at h2
        simp only [one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero] at h2; simp only [LinearMap.comp_apply]; rw [h2]; ring
      omega
    ·
      have hb1' : b1 = 1 := zmod2_eq_one_of_ne_zero hb1
      have hb2' : b2 = 1 := zmod2_eq_one_of_ne_zero hb2
      by_cases hd : d1 = 1 ∧ d2 = 1
      ·
        have hH1 : H1.card ≤ Nat.fib (k - 1) := by
          let e1 := L1 (Pi.single u0 1) + c1
          let e2 := L2 (Pi.single u0 1) + c2
          refine bound_01k 1 H1 (L2.comp emb3) (L1.comp emb3) e2 e1 (Finset.filter_subset _ _)
            (fun x hx => (Finset.mem_filter.mp hx).2) ?_ ?_
          · intro x hx
            have h2 := hL2 x (Finset.mem_filter.mp hx).1
            rw [hixk, (Finset.mem_filter.mp hx).2, hdecomp3 L2 x, (Finset.mem_filter.mp hx).2,
                show L2 (Pi.single uk 1) = b2 from rfl, hb2', show L2 (Pi.single u1 1) = d2 from rfl, hd.2] at h2
            simp only [mul_one, one_mul] at h2
            have ha := zmod2_add_self (x uk)
            have ha1 := zmod2_add_self (x u1)
            have h3 : x u1 + (L2 (emb3 (fun j => x j.val)) + e2) = 0 := by
              calc x u1 + (L2 (emb3 (fun j => x j.val)) + e2)
                  = (x uk + x uk) + (x u1 + L2 (emb3 (fun j => x j.val)) + e2) := by rw [ha, zero_add, add_assoc]
                _ = x uk + (L2 (Pi.single u0 1) + x u1 + x uk + L2 (emb3 (fun j => x j.val)) + c2) := by
                    simp only [e2]; ring
                _ = x uk + x uk := by rw [← h2]
                _ = 0 := ha
            calc x u1 = x u1 + 0 := (add_zero _).symm
              _ = x u1 + (x u1 + (L2 (emb3 (fun j => x j.val)) + e2)) := by rw [h3]
              _ = (x u1 + x u1) + (L2 (emb3 (fun j => x j.val)) + e2) := by ring
              _ = (L2.comp emb3) (fun j => x j.val) + e2 := by rw [ha1, zero_add]; rfl
          · intro x hx
            have h1 := hL1 x (Finset.mem_filter.mp hx).1
            rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp3 L1 x, (Finset.mem_filter.mp hx).2,
                show L1 (Pi.single u1 1) = b1 from rfl, hb1', show L1 (Pi.single uk 1) = d1 from rfl, hd.1] at h1
            simp only [mul_one, one_mul] at h1
            have ha := zmod2_add_self (x u1)
            have hak := zmod2_add_self (x uk)
            have h3 : x uk + (L1 (emb3 (fun j => x j.val)) + e1) = 0 := by
              calc x uk + (L1 (emb3 (fun j => x j.val)) + e1)
                  = (x u1 + x u1) + (x uk + L1 (emb3 (fun j => x j.val)) + e1) := by rw [ha, zero_add, add_assoc]
                _ = x u1 + (L1 (Pi.single u0 1) + x u1 + x uk + L1 (emb3 (fun j => x j.val)) + c1) := by
                    simp only [e1]; ring
                _ = x u1 + x u1 := by rw [← h1]
                _ = 0 := ha
            calc x uk = x uk + 0 := (add_zero _).symm
              _ = x uk + (x uk + (L1 (emb3 (fun j => x j.val)) + e1)) := by rw [h3]
              _ = (x uk + x uk) + (L1 (emb3 (fun j => x j.val)) + e1) := by ring
              _ = (L1.comp emb3) (fun j => x j.val) + e1 := by rw [hak, zero_add]; rfl
        have hH0 : H0.card ≤ Nat.fib k := by
          refine bound_01 0 H0 (L1.comp emb01) c1 (Finset.filter_subset _ _)
            (fun x hx => (Finset.mem_filter.mp hx).2) ?_
          intro x hx
          have h1 := hL1 x (Finset.mem_filter.mp hx).1
          rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp01 x, (Finset.mem_filter.mp hx).2, hb1'] at h1
          simp only [zero_mul, mul_zero, zero_add, one_mul] at h1
          have ha := zmod2_add_self (x u1)
          calc x u1 = x u1 + 0 := (add_zero _).symm
            _ = x u1 + (x u1 + L1 (emb01 (fun j => x j.val)) + c1) := by rw [← h1]
            _ = (x u1 + x u1) + (L1 (emb01 (fun j => x j.val)) + c1) := by ring
            _ = (L1.comp emb01) (fun j => x j.val) + c1 := by rw [ha, zero_add]; rfl
        omega
      ·
        have hH1 : H1.card ≤ Nat.fib (k + 1) :=
          bound_0 1 H1 (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2)
        have hH0 : H0.card ≤ Nat.fib (k - 1) := by
          have hd0 : d1 = 0 ∨ d2 = 0 := by
            by_contra h; push_neg at h
            exact hd ⟨zmod2_eq_one_of_ne_zero h.1, zmod2_eq_one_of_ne_zero h.2⟩
          rcases hd0 with hd1 | hd2
          · refine bound_01k 0 H0 (L1.comp emb3) (d2 • (L1.comp emb3) + L2.comp emb3) c1 (d2 * c1 + c2)
              (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2) ?_ ?_
            · intro x hx
              have h1 := hL1 x (Finset.mem_filter.mp hx).1
              rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp3 L1 x, (Finset.mem_filter.mp hx).2,
                  show L1 (Pi.single u1 1) = b1 from rfl, hb1', show L1 (Pi.single uk 1) = d1 from rfl, hd1] at h1
              simp only [zero_mul, mul_zero, zero_add, add_zero, one_mul] at h1
              have ha := zmod2_add_self (x u1)
              calc x u1 = x u1 + 0 := (add_zero _).symm
                _ = x u1 + (x u1 + L1 (emb3 (fun j => x j.val)) + c1) := by rw [← h1]
                _ = (x u1 + x u1) + (L1 (emb3 (fun j => x j.val)) + c1) := by ring
                _ = (L1.comp emb3) (fun j => x j.val) + c1 := by rw [ha, zero_add]; rfl
            · intro x hx
              have h1 := hL1 x (Finset.mem_filter.mp hx).1
              rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp3 L1 x, (Finset.mem_filter.mp hx).2,
                  show L1 (Pi.single u1 1) = b1 from rfl, hb1', show L1 (Pi.single uk 1) = d1 from rfl, hd1] at h1
              simp only [zero_mul, mul_zero, zero_add, add_zero, one_mul] at h1
              have hxu1 : x u1 = L1 (emb3 (fun j => x j.val)) + c1 := by
                have ha := zmod2_add_self (x u1)
                calc x u1 = x u1 + 0 := (add_zero _).symm
                  _ = x u1 + (x u1 + L1 (emb3 (fun j => x j.val)) + c1) := by rw [← h1]
                  _ = (x u1 + x u1) + (L1 (emb3 (fun j => x j.val)) + c1) := by ring
                  _ = L1 (emb3 (fun j => x j.val)) + c1 := by rw [ha, zero_add]
              have h2 := hL2 x (Finset.mem_filter.mp hx).1
              rw [hixk, (Finset.mem_filter.mp hx).2, hdecomp3 L2 x, (Finset.mem_filter.mp hx).2,
                  show L2 (Pi.single uk 1) = b2 from rfl, hb2', show L2 (Pi.single u1 1) = d2 from rfl, hxu1] at h2
              simp only [mul_zero, zero_add, one_mul, LinearMap.add_apply, LinearMap.smul_apply,
                LinearMap.comp_apply, smul_eq_mul] at h2 ⊢
              have ha := zmod2_add_self (x uk)
              calc x uk = x uk + 0 := (add_zero _).symm
                _ = x uk + (d2 * (L1 (emb3 (fun j => x j.val)) + c1) + x uk + L2 (emb3 (fun j => x j.val)) + c2) := by rw [← h2]
                _ = (x uk + x uk) + (d2 * L1 (emb3 (fun j => x j.val)) + L2 (emb3 (fun j => x j.val)) + (d2 * c1 + c2)) := by ring
                _ = d2 * L1 (emb3 (fun j => x j.val)) + L2 (emb3 (fun j => x j.val)) + (d2 * c1 + c2) := by rw [ha, zero_add]
          · refine bound_01k 0 H0 (d1 • (L2.comp emb3) + L1.comp emb3) (L2.comp emb3) (d1 * c2 + c1) c2
              (Finset.filter_subset _ _) (fun x hx => (Finset.mem_filter.mp hx).2) ?_ ?_
            · intro x hx
              have h2 := hL2 x (Finset.mem_filter.mp hx).1
              rw [hixk, (Finset.mem_filter.mp hx).2, hdecomp3 L2 x, (Finset.mem_filter.mp hx).2,
                  show L2 (Pi.single uk 1) = b2 from rfl, hb2', show L2 (Pi.single u1 1) = d2 from rfl, hd2] at h2
              simp only [zero_mul, mul_zero, zero_add, add_zero, one_mul] at h2
              have hxuk : x uk = L2 (emb3 (fun j => x j.val)) + c2 := by
                have ha := zmod2_add_self (x uk)
                calc x uk = x uk + 0 := (add_zero _).symm
                  _ = x uk + (x uk + L2 (emb3 (fun j => x j.val)) + c2) := by rw [← h2]
                  _ = (x uk + x uk) + (L2 (emb3 (fun j => x j.val)) + c2) := by ring
                  _ = L2 (emb3 (fun j => x j.val)) + c2 := by rw [ha, zero_add]
              have h1 := hL1 x (Finset.mem_filter.mp hx).1
              rw [hix0, (Finset.mem_filter.mp hx).2, hdecomp3 L1 x, (Finset.mem_filter.mp hx).2,
                  show L1 (Pi.single u1 1) = b1 from rfl, hb1', show L1 (Pi.single uk 1) = d1 from rfl, hxuk] at h1
              simp only [zero_mul, mul_zero, zero_add, one_mul, LinearMap.add_apply, LinearMap.smul_apply,
                LinearMap.comp_apply, smul_eq_mul] at h1 ⊢
              have ha := zmod2_add_self (x u1)
              calc x u1 = x u1 + 0 := (add_zero _).symm
                _ = x u1 + (x u1 + d1 * (L2 (emb3 (fun j => x j.val)) + c2) + L1 (emb3 (fun j => x j.val)) + c1) := by rw [← h1]
                _ = (x u1 + x u1) + (d1 * L2 (emb3 (fun j => x j.val)) + L1 (emb3 (fun j => x j.val)) + (d1 * c2 + c1)) := by ring
                _ = d1 * L2 (emb3 (fun j => x j.val)) + L1 (emb3 (fun j => x j.val)) + (d1 * c2 + c1) := by rw [ha, zero_add]
            · intro x hx
              have h2 := hL2 x (Finset.mem_filter.mp hx).1
              rw [hixk, (Finset.mem_filter.mp hx).2, hdecomp3 L2 x, (Finset.mem_filter.mp hx).2,
                  show L2 (Pi.single uk 1) = b2 from rfl, hb2', show L2 (Pi.single u1 1) = d2 from rfl, hd2] at h2
              simp only [zero_mul, mul_zero, zero_add, add_zero, one_mul] at h2
              have ha := zmod2_add_self (x uk)
              calc x uk = x uk + 0 := (add_zero _).symm
                _ = x uk + (x uk + L2 (emb3 (fun j => x j.val)) + c2) := by rw [← h2]
                _ = (x uk + x uk) + (L2 (emb3 (fun j => x j.val)) + c2) := by ring
                _ = (L2.comp emb3) (fun j => x j.val) + c2 := by rw [ha, zero_add]; rfl
        omega

def chi {k : ℕ} (hk : 0 < k) (y : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  y (ix hk (i.val + 1)) * y (ix hk (i.val + 2))

open scoped Classical in
lemma quad_cell_card_le_Bval {k : ℕ} (hk : 2 ≤ k)
    (V : Submodule (ZMod 2) (Fin k → ZMod 2)) (y0 : Fin k → ZMod 2)
    (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (c : Fin k → ZMod 2) :
    ((Finset.univ : Finset (Fin k → ZMod 2)).filter
      (fun y => y - y0 ∈ V ∧ chi (by omega : 0 < k) y = A y + c)).card ≤
      Bval k (k - Module.finrank (ZMod 2) V) := by
  have hk0 : 0 < k := by omega
  obtain ⟨I, hIcard, hIbij⟩ := exists_free_coords V
  let e : V ≃ₗ[ZMod 2] (I → ZMod 2) := LinearEquiv.ofBijective
    { toFun := fun v i => v.val i.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } hIbij
  let phi : (I → ZMod 2) → (Fin k → ZMod 2) := fun z => (e.symm z).val + y0
  let phiLin : (I → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) := V.subtype.comp e.symm.toLinearMap
  have hphi_eq : ∀ z, phi z = phiLin z + y0 := fun _ => rfl
  let H := (Finset.univ : Finset (Fin k → ZMod 2)).filter
    (fun y => y - y0 ∈ V ∧ chi hk0 y = A y + c)
  let restr : (Fin k → ZMod 2) → (I → ZMod 2) := fun y i => y i.val
  let shift : (I → ZMod 2) → (I → ZMod 2) := fun z i => z i + y0 i.val

  let y0I : I → ZMod 2 := fun i => y0 i.val
  let c_aff : Fin k → ZMod 2 := y0 - phiLin y0I
  have hlift : ∀ y ∈ H, phiLin (restr y) + c_aff = y := by
    intro y hy
    have hyV : y - y0 ∈ V := (Finset.mem_filter.mp hy).2.1
    have h1 : e ⟨y - y0, hyV⟩ = restr y - y0I := by
      funext i; rfl
    have h2 : phiLin (restr y - y0I) = y - y0 := by
      rw [← h1]; exact congrArg Subtype.val (e.symm_apply_apply ⟨y - y0, hyV⟩)
    simp only [c_aff, map_sub] at h2 ⊢
    calc phiLin (restr y) + (y0 - phiLin y0I)
        = (phiLin (restr y) - phiLin y0I) + y0 := by abel
      _ = (y - y0) + y0 := by rw [h2]
      _ = y := sub_add_cancel y y0
  have hinj : Set.InjOn restr H := by
    intro y1 hy1 y2 hy2 heq
    rw [← hlift y1 hy1, ← hlift y2 hy2, heq]
  rw [← Finset.card_image_of_injOn hinj]
  have hquad_I : ∀ u : I, ∀ hv : ix hk0 (u.val.val + 1) ∈ I,
      ∃ (L : (I → ZMod 2) →ₗ[ZMod 2] ZMod 2) (c0 : ZMod 2),
        ∀ z ∈ H.image restr, z u * z ⟨ix hk0 (u.val.val + 1), hv⟩ = L z + c0 := by
    intro u hv
    let site : Fin k := ix hk0 (u.val.val + k - 1)
    have hs1 : ix hk0 (site.val + 1) = u.val := by
      apply Fin.ext; simp only [site, ix]
      rw [Nat.mod_add_mod, show u.val.val + k - 1 + 1 = u.val.val + k by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt u.val.isLt]
    have hs2 : ix hk0 (site.val + 2) = ix hk0 (u.val.val + 1) := by
      apply Fin.ext; simp only [site, ix]
      rw [Nat.mod_add_mod, show u.val.val + k - 1 + 2 = (u.val.val + 1) + k by omega,
          Nat.add_mod_right]
    let evalSite : (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun w => w site, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine ⟨evalSite.comp (A.comp phiLin), A c_aff site + c site, ?_⟩
    intro z hz
    obtain ⟨y, hyH, rfl⟩ := Finset.mem_image.mp hz
    have hchi := congrFun (Finset.mem_filter.mp hyH).2.2 site
    simp only [chi, hs1, hs2, Pi.add_apply] at hchi
    have hAy : A y = A (phiLin (restr y)) + A c_aff := by rw [← map_add, hlift y hyH]
    rw [hAy] at hchi
    simpa [restr, evalSite, LinearMap.comp_apply, add_assoc] using hchi
  by_cases hIu : I = Finset.univ
  · have hdim : Module.finrank (ZMod 2) V = k := by
      rw [← hIcard, hIu, Finset.card_univ, Fintype.card_fin]
    rw [hdim, Nat.sub_self]
    let eqv : (I → ZMod 2) ≃ (Fin k → ZMod 2) :=
      Equiv.piCongrLeft' (fun _ => ZMod 2) (Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, fun x => ⟨⟨x, hIu ▸ Finset.mem_univ x⟩, rfl⟩⟩)
    rw [← Finset.card_image_of_injective _ eqv.injective]
    refine quad_le_Bval_zero hk ((H.image restr).image eqv) ?_
    intro u
    have huI : u ∈ I := hIu ▸ Finset.mem_univ u
    have hvI : ix hk0 (u.val + 1) ∈ I := hIu ▸ Finset.mem_univ _
    obtain ⟨L, c0, hL⟩ := hquad_I ⟨u, huI⟩ hvI
    let eqvLin : (Fin k → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2) :=
      { toFun := fun w i => w i.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    refine ⟨L.comp eqvLin, c0, ?_⟩
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    have h1 := hL z hz
    have heqv_apply : ∀ (z : I → ZMod 2) (x : Fin k) (hx : x ∈ I), eqv z x = z ⟨x, hx⟩ := by
      intro z x hx
      let eI : I ≃ Fin k := Equiv.ofBijective (Subtype.val : I → Fin k)
        ⟨Subtype.val_injective, fun a => ⟨⟨a, hIu ▸ Finset.mem_univ a⟩, rfl⟩⟩
      have hsymm : eI.symm x = ⟨x, hx⟩ := by
        apply eI.injective; rw [eI.apply_symm_apply]; rfl
      change z (eI.symm x) = z ⟨x, hx⟩
      rw [hsymm]
    have heqv_inv : eqvLin (eqv z) = z := by
      funext i; exact heqv_apply z i.val i.property
    have hwu : eqv z u = z ⟨u, huI⟩ := heqv_apply z u huI
    have hwv : eqv z (ix hk0 (u.val + 1)) = z ⟨ix hk0 (u.val + 1), hvI⟩ := heqv_apply z _ hvI
    simpa [hwu, hwv, LinearMap.comp_apply, heqv_inv] using h1
  · rw [← hIcard]
    exact le_trans (quad_le_indepCount_of_ne_univ hk I.card I hIu rfl (H.image restr) hquad_I)
      (indepCount_le_Bval hk I hIu)

def runTree {k : ℕ} (T : Finset (List Bool))
    (q : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : List Bool → ZMod 2) (x : Fin k → ZMod 2) : List Bool :=
  (List.range T.card).foldl (fun (p : List Bool) _ =>
    if p ∈ T then p ++ [decide (q p x + b p ≠ 0)] else p) []

def runSteps {k : ℕ} (T : Finset (List Bool))
    (q : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : List Bool → ZMod 2) (x : Fin k → ZMod 2) : ℕ → List Bool
  | 0 => []
  | m + 1 =>
    let p := runSteps T q b x m
    if p ∈ T then p ++ [decide (q p x + b p ≠ 0)] else p

lemma foldl_range_eq_runSteps {k : ℕ} (T : Finset (List Bool))
    (q : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : List Bool → ZMod 2) (x : Fin k → ZMod 2) (n : ℕ) :
    (List.range n).foldl (fun (p : List Bool) _ =>
      if p ∈ T then p ++ [decide (q p x + b p ≠ 0)] else p) [] = runSteps T q b x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rfl

lemma runSteps_props {k : ℕ} (T : Finset (List Bool))
    (q : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : List Bool → ZMod 2) (x : Fin k → ZMod 2) (n : ℕ) :
    (runSteps T q b x n ∈ T → (runSteps T q b x n).length = n) ∧
    (∀ j < (runSteps T q b x n).length, (runSteps T q b x n).take j ∈ T) ∧
    (∀ j (hj : j < (runSteps T q b x n).length),
      (runSteps T q b x n)[j] = decide (q ((runSteps T q b x n).take j) x + b ((runSteps T q b x n).take j) ≠ 0)) := by
  induction n with
  | zero => simp [runSteps]
  | succ n ih =>
    obtain ⟨hlen, hpref, hbits⟩ := ih
    simp only [runSteps]
    split_ifs with hmem
    · have hln : (runSteps T q b x n).length = n := hlen hmem
      refine ⟨fun _ => by simp [hln], ?_, ?_⟩
      · intro j hj
        rw [List.length_append, List.length_singleton] at hj
        by_cases hjlt : j < (runSteps T q b x n).length
        · rw [List.take_append_of_le_length (le_of_lt hjlt)]
          exact hpref j hjlt
        · have hjeq : j = (runSteps T q b x n).length := by omega
          rw [hjeq, List.take_left]
          exact hmem
      · intro j hj
        rw [List.length_append, List.length_singleton] at hj
        by_cases hjlt : j < (runSteps T q b x n).length
        · rw [List.getElem_append_left hjlt, List.take_append_of_le_length (le_of_lt hjlt)]
          exact hbits j hjlt
        · have hjeq : j = (runSteps T q b x n).length := by omega
          subst hjeq
          simp [List.getElem_append_right le_rfl, List.take_left]
    · exact ⟨fun h => False.elim (hmem h), hpref, hbits⟩

lemma runTree_not_mem {k : ℕ} (T : Finset (List Bool))
    (q : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : List Bool → ZMod 2) (x : Fin k → ZMod 2) :
    runTree T q b x ∉ T := by
  rw [runTree, foldl_range_eq_runSteps]
  intro hmem
  have hp := runSteps_props T q b x T.card
  have hlen : (runSteps T q b x T.card).length = T.card := hp.1 hmem
  let f : Fin (T.card + 1) → List Bool := fun i => (runSteps T q b x T.card).take i.val
  have hsub : (Finset.univ.image f) ⊆ T := by
    intro u hu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    by_cases hilt : i.val < T.card
    · exact hp.2.1 i.val (by omega)
    · have hieq : i.val = T.card := by omega
      change (runSteps T q b x T.card).take i.val ∈ T
      have htk : (runSteps T q b x T.card).take T.card = runSteps T q b x T.card :=
        List.take_of_length_le (le_of_eq hlen)
      rw [hieq, htk]; exact hmem
  have hinj : Function.Injective f := by
    intro i j hij
    have hl := congrArg List.length hij
    simp only [f, List.length_take, hlen] at hl
    have hi : min i.val T.card = i.val := Nat.min_eq_left (by omega)
    have hj : min j.val T.card = j.val := Nat.min_eq_left (by omega)
    rw [hi, hj] at hl
    exact Fin.ext hl
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hc
  omega

lemma runTree_eq_iff {k : ℕ} (T : Finset (List Bool))
    (q : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : List Bool → ZMod 2) (p : List Bool)
    (hp_not : p ∉ T) (hp_pref : ∀ j < p.length, p.take j ∈ T) (x : Fin k → ZMod 2) :
    runTree T q b x = p ↔
      ∀ j (hj : j < p.length), p[j] = decide (q (p.take j) x + b (p.take j) ≠ 0) := by
  constructor
  · intro heq j hj
    have h2 : runSteps T q b x T.card = p := by rw [← foldl_range_eq_runSteps, ← runTree, heq]
    have h1 := (runSteps_props T q b x T.card).2.2
    rw [h2] at h1
    exact h1 j hj
  · intro hbits
    rw [runTree, foldl_range_eq_runSteps]
    have hstep : ∀ n ≤ p.length, runSteps T q b x n = p.take n := by
      intro n hn
      induction n with
      | zero => simp [runSteps]
      | succ n ih =>
        simp only [runSteps, ih (by omega), hp_pref n (by omega), ↓reduceIte]
        rw [← hbits n (by omega), List.take_succ_eq_append_getElem (by omega)]
    have hplen : p.length ≤ T.card := by
      let f : Fin p.length → List Bool := fun i => p.take i.val
      have hsub : Finset.univ.image f ⊆ T := by
        intro u hu; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu; exact hp_pref i.val i.isLt
      have hinj : Function.Injective f := by
        intro i j hij
        have hl := congrArg List.length hij
        simp only [f, List.length_take, Nat.min_eq_left (le_of_lt i.isLt),
          Nat.min_eq_left (le_of_lt j.isLt)] at hl
        exact Fin.ext hl
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hc
      exact hc
    have hfix : ∀ t, runSteps T q b x (p.length + t) = p := by
      intro t
      induction t with
      | zero => simpa using hstep p.length le_rfl
      | succ t ih =>
        rw [show p.length + (t + 1) = (p.length + t) + 1 by omega]
        simp [runSteps, ih, hp_not]
    have := hfix (T.card - p.length)
    rwa [Nat.add_sub_cancel' hplen] at this

lemma card_leaves_le_succ {T S : Finset (List Bool)}
    (hnot : ∀ p ∈ S, p ∉ T)
    (hpref : ∀ p ∈ S, ∀ j < p.length, p.take j ∈ T) :
    S.card ≤ T.card + 1 := by
  suffices h : ∀ m (T S : Finset (List Bool)), T.card = m →
      (∀ p ∈ S, p ∉ T) → (∀ p ∈ S, ∀ j < p.length, p.take j ∈ T) → S.card ≤ m + 1 by
    exact h T.card T S rfl hnot hpref
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro T S hm hnot hpref
    let Tu := T.filter (fun u => ∃ p ∈ S, u.length < p.length ∧ p.take u.length = u)
    have hTu_sub : Tu ⊆ T := Finset.filter_subset _ _
    by_cases hTu_emp : Tu = ∅
    · have hS_sub : S ⊆ {[]} := by
        intro p hp
        rw [Finset.mem_singleton]
        by_contra hne
        have hpos : 0 < p.length := List.length_pos_iff.mpr hne
        have hmem : [] ∈ Tu := Finset.mem_filter.mpr ⟨by simpa using hpref p hp 0 hpos, ⟨p, hp, hpos, rfl⟩⟩
        rw [hTu_emp] at hmem; exact Finset.notMem_empty _ hmem
      exact le_trans (Finset.card_le_card hS_sub) (by simp)
    · have hTu_ne : Tu.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTu_emp
      obtain ⟨u, huTu, humax⟩ := Finset.exists_max_image Tu List.length hTu_ne
      let T' := Tu.erase u
      let S' := insert u ((S.erase (u ++ [false])).erase (u ++ [true]))
      have hcardS : S.card ≤ S'.card + 1 := by
        have h1 : (S.erase (u ++ [false])).card + 1 ≥ S.card := by
          by_cases hm1 : u ++ [false] ∈ S
          · rw [Finset.card_erase_of_mem hm1]; have := Finset.card_pos.mpr ⟨_, hm1⟩; omega
          · rw [Finset.erase_eq_of_notMem hm1]; omega
        have h2 : ((S.erase (u ++ [false])).erase (u ++ [true])).card + 1 ≥ (S.erase (u ++ [false])).card := by
          by_cases hm2 : u ++ [true] ∈ S.erase (u ++ [false])
          · rw [Finset.card_erase_of_mem hm2]; have := Finset.card_pos.mpr ⟨_, hm2⟩; omega
          · rw [Finset.erase_eq_of_notMem hm2]; omega
        have hu_notS : u ∉ (S.erase (u ++ [false])).erase (u ++ [true]) := fun h =>
          hnot u (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h)) (hTu_sub huTu)
        rw [show S'.card = ((S.erase (u ++ [false])).erase (u ++ [true])).card + 1 from
          Finset.card_insert_of_notMem hu_notS]
        omega
      have hnot' : ∀ p ∈ S', p ∉ T' := by
        intro p hp hpT'
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact Finset.notMem_erase _ _ hpT'
        · exact hnot p (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp'))
            (hTu_sub (Finset.mem_of_mem_erase hpT'))
      have hpref' : ∀ p ∈ S', ∀ j < p.length, p.take j ∈ T' := by
        intro p hp j hj
        rcases Finset.mem_insert.mp hp with hpu | hp'
        · rw [hpu] at hj ⊢
          obtain ⟨q, hqS, hqlen, hqeq⟩ := (Finset.mem_filter.mp huTu).2
          have htake : u.take j = q.take j := by rw [← hqeq, List.take_take, Nat.min_eq_left (le_of_lt hj)]
          refine Finset.mem_erase.mpr ⟨fun heq => by have := congrArg List.length heq; simp [Nat.min_eq_left (le_of_lt hj)] at this; omega, ?_⟩
          refine Finset.mem_filter.mpr ⟨htake ▸ hpref q hqS j (by omega), ⟨q, hqS, ?_, ?_⟩⟩
          · simp [Nat.min_eq_left (le_of_lt hj)]; omega
          · rw [List.length_take, Nat.min_eq_left (le_of_lt hj), ← htake]
        · have hpS : p ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hp')
          have hne_t : p ≠ u ++ [true] := (Finset.mem_erase.mp hp').1
          have hne_f : p ≠ u ++ [false] := (Finset.mem_erase.mp (Finset.mem_erase.mp hp').2).1
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hpref p hpS j hj, ⟨p, hpS, ?_, ?_⟩⟩⟩
          · intro htake_u
            have hju : j = u.length := by
              have := congrArg List.length htake_u
              rw [List.length_take, Nat.min_eq_left (le_of_lt hj)] at this; exact this
            have hlen_p : p.length = u.length + 1 := by
              by_contra hne_len
              have hgt : u.length + 1 < p.length := by omega
              have hmem_tu : p.take (u.length + 1) ∈ Tu :=
                Finset.mem_filter.mpr ⟨hpref p hpS (u.length + 1) hgt,
                  ⟨p, hpS, by simp [Nat.min_eq_left (le_of_lt hgt), hgt],
                   by rw [List.length_take, Nat.min_eq_left (le_of_lt hgt)]⟩⟩
              have hle := humax _ hmem_tu
              rw [List.length_take, Nat.min_eq_left (le_of_lt hgt)] at hle; omega
            have hpeq : p = u ++ [p[u.length]'(by omega)] := by
              have htake_u' : p.take u.length = u := hju ▸ htake_u
              have h1 : p = p.take u.length ++ [p[u.length]'(by omega)] := by
                rw [← List.take_succ_eq_append_getElem (by omega), List.take_of_length_le (by omega)]
              rwa [htake_u'] at h1
            cases hb : p[u.length]'(by omega)
            · rw [hb] at hpeq; exact hne_f hpeq
            · rw [hb] at hpeq; exact hne_t hpeq
          · rw [List.length_take, Nat.min_eq_left (le_of_lt hj)]; exact hj
          · rw [List.length_take, Nat.min_eq_left (le_of_lt hj)]
      have hT'card : T'.card < m := by
        rw [← hm]
        exact lt_of_lt_of_le (Finset.card_erase_lt_of_mem huTu) (Finset.card_le_card hTu_sub)
      have hih := ih T'.card hT'card T' S' rfl hnot' hpref'
      omega

def Nval (k L : ℕ) : ℕ :=
  let cap := min L (2 ^ ((k + 1) / 2))
  let d := Nat.log2 cap
  let a := cap - 2 ^ d
  if k = 1 then 2 else (2 ^ d - a) * Bval k d + 2 * a * Bval k (d + 1)

lemma log2_bounds {n : ℕ} (hn : 0 < n) :
    2 ^ Nat.log2 n ≤ n ∧ n < 2 ^ (Nat.log2 n + 1) := by
  refine ⟨(Nat.le_log2 (by omega)).mp le_rfl, ?_⟩
  by_contra h; push_neg at h
  have := (Nat.le_log2 (by omega)).mpr h
  omega

open scoped Classical in
lemma possibleY_le_N {k : ℕ} (hk : 0 < k) (L : ℕ) (hL : 0 < L)
    (T : Finset (List Bool))
    (q : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (b : List Bool → ZMod 2)
    (A : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (c : List Bool → (Fin k → ZMod 2))
    (hT : T.card < L) :
    ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun y =>
      let p := runTree T q b y
      chi hk y = A p y + c p)).card ≤ Nval k L := by
  by_cases hk1 : k = 1
  · subst hk1
    unfold Nval; simp only [↓reduceIte]
    calc _ ≤ (Finset.univ : Finset (Fin 1 → ZMod 2)).card := Finset.card_le_univ _
      _ = 2 := by simp [Fintype.card_fun, ZMod.card]
  · have hk2 : 2 ≤ k := by omega
    unfold Nval; simp only [hk1, ↓reduceIte]
    set cap := min L (2 ^ ((k + 1) / 2))
    set d := Nat.log2 cap
    set a := cap - 2 ^ d
    have hcap_pos : 0 < cap := lt_min hL (by positivity)
    obtain ⟨hd_le, hd_lt⟩ := log2_bounds hcap_pos
    by_cases hbig : 2 ^ ((k + 1) / 2) ≤ L
    · have hcap_eq : cap = 2 ^ ((k + 1) / 2) := min_eq_right hbig
      have hd_eq : d = (k + 1) / 2 := by
        have h1 : (k + 1) / 2 ≤ d := (Nat.le_log2 (by omega)).mpr (by rw [hcap_eq])
        have h2 : d ≤ (k + 1) / 2 := by
          by_contra hgt; push_neg at hgt
          have h1 : 2 ^ ((k + 1) / 2) < 2 ^ d := Nat.pow_lt_pow_right (by decide) hgt
          have h2 : 2 ^ d ≤ 2 ^ ((k + 1) / 2) := hcap_eq ▸ hd_le
          omega
        omega
      have ha_eq : a = 0 := by dsimp only [a]; rw [hcap_eq, hd_eq, Nat.sub_self]
      have hBd : Bval k d = 2 ^ (k - d) := by
        unfold Bval; rw [hd_eq]
        have h1 : (k + 1) / 2 ≠ 0 := by omega
        have h2 : ¬ (2 * ((k + 1) / 2) < k) := by omega
        simp [h1, h2]
      rw [ha_eq, Nat.sub_zero, mul_zero, zero_mul, add_zero, hBd, ← pow_add,
          Nat.add_sub_cancel' (by rw [hd_eq]; omega)]
      calc _ ≤ (Finset.univ : Finset (Fin k → ZMod 2)).card := Finset.card_le_univ _
        _ = 2 ^ k := by simp [Fintype.card_fun, ZMod.card]
    ·
      have hcap_eq : cap = L := min_eq_left (by omega)
      let S_all := (Finset.univ : Finset (Fin k → ZMod 2)).image (runTree T q b)
      have hS_not : ∀ p ∈ S_all, p ∉ T := by
        intro p hp; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp; exact runTree_not_mem T q b x
      have hS_pref : ∀ p ∈ S_all, ∀ j < p.length, p.take j ∈ T := by
        intro p hp j hj; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
        rw [runTree, foldl_range_eq_runSteps] at hj ⊢
        exact (runSteps_props T q b x T.card).2.1 j hj
      have hS_card : S_all.card ≤ L := le_trans (card_leaves_le_succ hS_not hS_pref) (by omega)
      let cell : List Bool → Finset (Fin k → ZMod 2) := fun p =>
        Finset.univ.filter (fun y => runTree T q b y = p)
      let hits : List Bool → Finset (Fin k → ZMod 2) := fun p =>
        Finset.univ.filter (fun y => runTree T q b y = p ∧ chi hk y = A p y + c p)
      have hsum_hits : ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun y =>
          let p := runTree T q b y
          chi hk y = A p y + c p)).card = ∑ p ∈ S_all, (hits p).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
            S_all, Finset.mem_image, hits]
          exact ⟨fun h => ⟨runTree T q b y, ⟨y, rfl⟩, rfl, h⟩, fun ⟨p, _, hp, h⟩ => hp ▸ h⟩
        · intro p1 _ p2 _ hne
          refine Finset.disjoint_left.mpr fun y h1 h2 => hne ?_
          exact (Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1
      have hsum_cells : ∑ p ∈ S_all, (cell p).card = 2 ^ k := by
        rw [← Finset.card_biUnion]
        · have huniv : S_all.biUnion cell = Finset.univ := by
            ext y; simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, true_and, S_all, Finset.mem_image, cell, Finset.mem_filter]
            exact ⟨runTree T q b y, ⟨y, rfl⟩, rfl⟩
          rw [huniv]; simp [Fintype.card_fun, ZMod.card]
        · intro p1 _ p2 _ hne
          refine Finset.disjoint_left.mpr fun y h1 h2 => hne ?_
          exact (Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2

      let Vp : List Bool → Submodule (ZMod 2) (Fin k → ZMod 2) := fun p =>
        ⨅ (j : Fin p.length), LinearMap.ker (q (p.take j.val))
      have hcell_card : ∀ p ∈ S_all, (cell p).card = 2 ^ (k - (k - Module.finrank (ZMod 2) (Vp p))) := by
        intro p hp
        obtain ⟨x0, _, hx0⟩ := Finset.mem_image.mp hp
        have hdim_le : Module.finrank (ZMod 2) (Vp p) ≤ k := by
          have := Submodule.finrank_le (Vp p)
          simpa [Module.finrank_pi] using this
        rw [Nat.sub_sub_self hdim_le]
        have hmem_iff : ∀ y, y ∈ cell p ↔ y - x0 ∈ Vp p := by
          intro y
          simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and, Vp, Submodule.mem_iInf, LinearMap.mem_ker]
          rw [runTree_eq_iff T q b p (hS_not p hp) (hS_pref p hp)]
          have hx0_bits := (runTree_eq_iff T q b p (hS_not p hp) (hS_pref p hp) x0).mp hx0
          constructor
          · intro hy j
            have h1 := hy j.val j.isLt
            have h2 := hx0_bits j.val j.isLt
            have hdec : decide (q (p.take j.val) y + b (p.take j.val) ≠ 0) =
                decide (q (p.take j.val) x0 + b (p.take j.val) ≠ 0) := h1.symm.trans h2
            rw [map_sub]
            by_cases hq : q (p.take j.val) x0 + b (p.take j.val) = 0
            · have hy0 : q (p.take j.val) y + b (p.take j.val) = 0 := by
                by_contra hne; simp [hq, hne] at hdec
              have heq : q (p.take j.val) y = q (p.take j.val) x0 := by
                have := congrArg (· + b (p.take j.val)) (hy0.trans hq.symm)
                simpa [add_assoc, zmod2_add_self] using this
              rw [heq, sub_self]
            · have hy1 : q (p.take j.val) y + b (p.take j.val) ≠ 0 := by
                intro hy0; simp [hq, hy0] at hdec
              have h1' := zmod2_eq_one_of_ne_zero hq
              have h2' := zmod2_eq_one_of_ne_zero hy1
              have heq : q (p.take j.val) y = q (p.take j.val) x0 := by
                have := congrArg (· + b (p.take j.val)) (h2'.trans h1'.symm)
                simpa [add_assoc, zmod2_add_self] using this
              rw [heq, sub_self]
          · intro hy j hj
            have hsub : q (p.take j) y - q (p.take j) x0 = 0 := by
              rw [← map_sub]; exact hy ⟨j, hj⟩
            have heq : q (p.take j) y = q (p.take j) x0 := sub_eq_zero.mp hsub
            rw [heq]; exact hx0_bits j hj
        have hbij : (cell p).card = Fintype.card (Vp p) := by
          refine Finset.card_bij (fun y hy => ⟨y - x0, (hmem_iff y).mp hy⟩) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro y1 _ y2 _ heq
            have h1 : y1 - x0 = y2 - x0 := congrArg Subtype.val heq
            exact sub_left_inj.mp h1
          · intro v _
            exact ⟨v.val + x0, (hmem_iff _).mpr (by simpa using v.property), Subtype.ext (by simp)⟩
        rw [hbij]
        have := Module.card_eq_pow_finrank (K := ZMod 2) (V := Vp p)
        simpa [Nat.card_eq_fintype_card, ZMod.card] using this
      have hhits_le : ∀ p ∈ S_all, (hits p).card ≤ Bval k (k - Module.finrank (ZMod 2) (Vp p)) := by
        intro p hp
        obtain ⟨x0, _, hx0⟩ := Finset.mem_image.mp hp
        have hsub : hits p ⊆ Finset.univ.filter (fun y => y - x0 ∈ Vp p ∧ chi hk y = A p y + c p) := by
          intro y hy
          simp only [hits, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
          refine ⟨?_, hy.2⟩
          simp only [Vp, Submodule.mem_iInf, LinearMap.mem_ker]
          have hy_bits := (runTree_eq_iff T q b p (hS_not p hp) (hS_pref p hp) y).mp hy.1
          have hx0_bits := (runTree_eq_iff T q b p (hS_not p hp) (hS_pref p hp) x0).mp hx0
          intro j
          have hdec : decide (q (p.take j.val) y + b (p.take j.val) ≠ 0) =
              decide (q (p.take j.val) x0 + b (p.take j.val) ≠ 0) :=
            (hy_bits j.val j.isLt).symm.trans (hx0_bits j.val j.isLt)
          rw [map_sub]
          by_cases hq : q (p.take j.val) x0 + b (p.take j.val) = 0
          · have hy0 : q (p.take j.val) y + b (p.take j.val) = 0 := by
              by_contra hne; simp [hq, hne] at hdec
            have heq : q (p.take j.val) y = q (p.take j.val) x0 := by
              have := congrArg (· + b (p.take j.val)) (hy0.trans hq.symm)
              simpa [add_assoc, zmod2_add_self] using this
            rw [heq, sub_self]
          · have hy1 : q (p.take j.val) y + b (p.take j.val) ≠ 0 := by
              intro hy0; simp [hq, hy0] at hdec
            have heq : q (p.take j.val) y = q (p.take j.val) x0 := by
              have := congrArg (· + b (p.take j.val)) ((zmod2_eq_one_of_ne_zero hy1).trans (zmod2_eq_one_of_ne_zero hq).symm)
              simpa [add_assoc, zmod2_add_self] using this
            rw [heq, sub_self]
        exact le_trans (Finset.card_le_card hsub) (quad_cell_card_le_Bval hk2 (Vp p) x0 (A p) (c p))

      rw [hsum_hits]
      suffices hmul : 2 ^ k * ∑ p ∈ S_all, (hits p).card ≤
          2 ^ k * ((2 ^ d - a) * Bval k d + 2 * a * Bval k (d + 1)) from
        Nat.le_of_mul_le_mul_left hmul (by positivity)
      rw [Finset.mul_sum]
      calc ∑ p ∈ S_all, 2 ^ k * (hits p).card
          ≤ ∑ p ∈ S_all, 2 ^ k * Bval k (k - Module.finrank (ZMod 2) (Vp p)) :=
            Finset.sum_le_sum fun p hp => Nat.mul_le_mul_left _ (hhits_le p hp)
        _ ≤ ∑ p ∈ S_all, (2 ^ (k - (k - Module.finrank (ZMod 2) (Vp p))) *
              (2 ^ (d + 1) * (Bval k d - Bval k (d + 1))) + 2 ^ k * Delta k d) :=
            Finset.sum_le_sum fun p _ => Bval_tangent k d (k - Module.finrank (ZMod 2) (Vp p)) hk2 (by have : d < (k + 1) / 2 := by { by_contra hge; push_neg at hge; have h1 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hge; have h2 : 2 ^ d ≤ L := hcap_eq ▸ hd_le; omega }; omega) (Nat.sub_le _ _)
        _ = (∑ p ∈ S_all, (cell p).card) * (2 ^ (d + 1) * (Bval k d - Bval k (d + 1))) +
            S_all.card * (2 ^ k * Delta k d) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, smul_eq_mul]
            congr 2; exact Finset.sum_congr rfl fun p hp => (hcell_card p hp).symm
        _ = 2 ^ k * (2 ^ (d + 1) * (Bval k d - Bval k (d + 1))) + S_all.card * (2 ^ k * Delta k d) := by
            rw [hsum_cells]
        _ ≤ 2 ^ k * (2 ^ (d + 1) * (Bval k d - Bval k (d + 1))) + L * (2 ^ k * Delta k d) :=
            Nat.add_le_add_left (Nat.mul_le_mul_right _ hS_card) _
        _ = 2 ^ k * ((2 ^ d - a) * Bval k d + 2 * a * Bval k (d + 1)) := by
            have hdec := Bval_succ_le k d hk2
            have hinc := Bval_le_two_mul_succ k d hk2
            have ha_le : a ≤ 2 ^ d := by
              have : cap < 2 * 2 ^ d := by rw [← pow_succ']; exact hd_lt
              omega
            have hL_eq : L = 2 ^ d + a := by have h1 : 2 ^ d ≤ L := hcap_eq ▸ hd_le; dsimp only [a]; rw [hcap_eq]; omega
            unfold Delta
            rw [hL_eq, pow_succ]
            zify [hdec, hinc, ha_le]
            ring

lemma sum_pow_two (n : ℕ) : ∑ t ∈ Finset.range n, 2 ^ t = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ r ihr =>
    rw [Finset.sum_range_succ, ihr, pow_succ]
    have : 1 ≤ 2 ^ r := Nat.one_le_pow _ _ (by decide)
    omega

def bitsOfNat (len n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin len => n.testBit i.val)

lemma bitsOfNat_length (len n : ℕ) : (bitsOfNat len n).length = len := by
  simp [bitsOfNat]

lemma bitsOfNat_inj {len : ℕ} : Set.InjOn (bitsOfNat len) (Finset.range (2 ^ len)) := by
  intro m1 hm1 m2 hm2 heq
  rw [Finset.mem_coe, Finset.mem_range] at hm1 hm2
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < len
  · have := congrArg (fun l : List Bool => l[i]?) heq
    simpa [bitsOfNat, hi] using this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hm1 (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hm2 (Nat.pow_le_pow_right (by decide) (by omega)))]

set_option maxHeartbeats 800000 in
lemma possibleY_N {k : ℕ} (hk : 0 < k) (L : ℕ) (hL : 0 < L) :
    ∃ (T : Finset (List Bool))
      (q : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2)
      (b : List Bool → ZMod 2)
      (A : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
      (c : List Bool → (Fin k → ZMod 2)),
      T.card < L ∧ Nval k L ≤ ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun y =>
        let p := runTree T q b y
        chi hk y = A p y + c p)).card := by
  by_cases hk1 : k = 1
  · subst hk1
    refine ⟨∅, fun _ => 0, fun _ => 0, fun _ => LinearMap.id, fun _ => 0, by simpa using hL, ?_⟩
    unfold Nval; simp only [↓reduceIte]
    have hall : (Finset.univ : Finset (Fin 1 → ZMod 2)).filter (fun y =>
        let p := runTree ∅ (fun _ => 0) (fun _ => 0) y
        chi hk y = (LinearMap.id : (Fin 1 → ZMod 2) →ₗ[ZMod 2] (Fin 1 → ZMod 2)) y + 0) = Finset.univ := by
      ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, LinearMap.id_apply, add_zero]
      funext i; fin_cases i
      simp [chi, ix, zmod2_mul_self]
    rw [hall]; simp [Fintype.card_fun, ZMod.card]
  · have hk2 : 2 ≤ k := by omega
    unfold Nval; simp only [hk1, ↓reduceIte]
    set cap := min L (2 ^ ((k + 1) / 2))
    set d := Nat.log2 cap
    set a := cap - 2 ^ d
    have hcap_pos : 0 < cap := lt_min hL (by positivity)
    obtain ⟨hd_le, hd_lt⟩ := log2_bounds hcap_pos
    have hcap_le_L : cap ≤ L := min_le_left _ _
    have hcap_le_pow : cap ≤ 2 ^ ((k + 1) / 2) := min_le_right _ _
    have hd_le_half : d ≤ (k + 1) / 2 := by
      by_contra hgt; push_neg at hgt
      have h1 : 2 ^ ((k + 1) / 2) < 2 ^ d := Nat.pow_lt_pow_right (by decide) hgt
      have h2 : 2 ^ d ≤ cap := hd_le
      omega
    have ha_lt : a < 2 ^ d := by
      have : cap < 2 * 2 ^ d := by rw [← pow_succ']; exact hd_lt
      omega
    have ha_pos_imp : a > 0 → d + 1 ≤ (k + 1) / 2 := by
      intro ha_pos
      have : 2 ^ d < 2 ^ ((k + 1) / 2) := by omega
      have hlt : d < (k + 1) / 2 := by
        by_contra hge; push_neg at hge
        exact not_lt_of_ge (Nat.pow_le_pow_right (by decide) hge) this
      omega

    let T_lt : Finset (List Bool) := (Finset.range d).biUnion (fun j => (Finset.range (2 ^ j)).image (bitsOfNat j))
    let T_eq : Finset (List Bool) := (Finset.range a).image (bitsOfNat d)
    let T : Finset (List Bool) := T_lt ∪ T_eq
    have hT_disj : Disjoint T_lt T_eq := Finset.disjoint_left.mpr fun l hl1 hl2 => by
      obtain ⟨j, hj, hl1'⟩ := Finset.mem_biUnion.mp hl1
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hl1'
      obtain ⟨_, _, heq⟩ := Finset.mem_image.mp hl2
      have := congrArg List.length heq
      simp only [bitsOfNat_length] at this
      rw [Finset.mem_range] at hj; omega
    have hT_lt_card : T_lt.card = 2 ^ d - 1 := by
      rw [Finset.card_biUnion]
      · have hsum : ∑ j ∈ Finset.range d, ((Finset.range (2 ^ j)).image (bitsOfNat j)).card =
            ∑ j ∈ Finset.range d, 2 ^ j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.card_image_of_injOn bitsOfNat_inj, Finset.card_range]
        rw [hsum]
        clear hsum
        induction d with
        | zero => simp
        | succ m ihm =>
          rw [Finset.sum_range_succ, ihm, pow_succ]
          have : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide)
          omega
      · intro j1 _ j2 _ hne
        refine Finset.disjoint_left.mpr fun l hl1 hl2 => hne ?_
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hl1
        obtain ⟨_, _, heq⟩ := Finset.mem_image.mp hl2
        have := congrArg List.length heq
        simpa [bitsOfNat_length] using this.symm
    have hT_eq_card : T_eq.card = a := by
      rw [Finset.card_image_of_injOn (bitsOfNat_inj.mono (Finset.range_mono (le_of_lt ha_lt))), Finset.card_range]
    have hT_card : T.card = cap - 1 := by
      rw [Finset.card_union_of_disjoint hT_disj, hT_lt_card, hT_eq_card]
      have h1 : 1 ≤ 2 ^ d := Nat.one_le_pow _ _ (by decide)
      have h2 : 2 ^ d ≤ cap := hd_le
      dsimp only [a]; omega
    have hT_lt_L : T.card < L := by omega

    let q : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2 := fun p =>
      { toFun := fun y => y (ix hk (2 * p.length))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let b : List Bool → ZMod 2 := fun _ => 0

    let bVal : Bool → ZMod 2 := fun bit => if bit then 1 else 0
    let A : List Bool → (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) := fun p =>
      { toFun := fun y i =>
          let u := ix hk (i.val + 1)
          let v := ix hk (i.val + 2)
          if hu : u.val % 2 = 0 ∧ u.val / 2 < p.length then
            bVal (p[u.val / 2]'hu.2) * y v
          else if hv : v.val % 2 = 0 ∧ v.val / 2 < p.length then
            bVal (p[v.val / 2]'hv.2) * y u
          else 0
        map_add' := fun y1 y2 => by funext i; simp only [Pi.add_apply]; split_ifs <;> simp [mul_add]
        map_smul' := fun r y => by funext i; simp only [Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp [mul_left_comm] }
    let c : List Bool → (Fin k → ZMod 2) := fun _ => 0
    refine ⟨T, q, b, A, c, hT_lt_L, ?_⟩

    let L_d : Finset (List Bool) := (Finset.Ico a (2 ^ d)).image (bitsOfNat d)
    let L_d1 : Finset (List Bool) := ((Finset.range a) ×ˢ (Finset.univ : Finset Bool)).image
      (fun mb => bitsOfNat d mb.1 ++ [mb.2])
    have hLd_card : L_d.card = 2 ^ d - a := by
      rw [Finset.card_image_of_injOn (bitsOfNat_inj.mono (by
        intro m hm; simp only [Finset.mem_coe, Finset.mem_Ico] at hm
        exact Finset.mem_coe.mpr (Finset.mem_range.mpr hm.2))), Nat.card_Ico]
    have hLd1_card : L_d1.card = 2 * a := by
      rw [Finset.card_image_of_injOn]
      · simp [Finset.card_product, mul_comm]
      · intro ⟨m1, b1⟩ h1 ⟨m2, b2⟩ h2 heq
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true] at h1 h2
        have hlen1 : (bitsOfNat d m1).length = (bitsOfNat d m2).length := by simp [bitsOfNat_length]
        obtain ⟨heq1, heq2⟩ := List.append_inj heq hlen1
        have hm : m1 = m2 := bitsOfNat_inj (Finset.mem_coe.mpr (Finset.mem_range.mpr (lt_trans h1 ha_lt)))
          (Finset.mem_coe.mpr (Finset.mem_range.mpr (lt_trans h2 ha_lt))) heq1
        have hb : b1 = b2 := List.singleton_injective heq2
        exact Prod.ext hm hb
    have hL_disj : Disjoint L_d L_d1 := Finset.disjoint_left.mpr fun l hl1 hl2 => by
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hl1
      obtain ⟨_, _, heq⟩ := Finset.mem_image.mp hl2
      have := congrArg List.length heq
      simp [bitsOfNat_length] at this

    have hleaf_props : ∀ p ∈ L_d ∪ L_d1, p ∉ T ∧ (∀ j < p.length, p.take j ∈ T) ∧ p.length ≤ (k + 1) / 2 := by
      intro p hp
      have htake_mem_Tlt : ∀ (l : List Bool) (j : ℕ), j < d → j ≤ l.length → l.take j ∈ T_lt := by
        intro l j hj hjl
        refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, Finset.mem_image.mpr ?_⟩
        let m := ∑ i : Fin j, if l[i.val]'(by omega) then 2 ^ i.val else 0
        have hm_lt : m < 2 ^ j := by
          have hsum : m ≤ ∑ i : Fin j, 2 ^ i.val :=
            Finset.sum_le_sum fun i _ => by split_ifs <;> [exact le_rfl; exact Nat.zero_le _]
          have hgeom : ∑ i : Fin j, 2 ^ i.val = 2 ^ j - 1 := by
            rw [Fin.sum_univ_eq_sum_range (fun t => 2 ^ t)]
            exact sum_pow_two j
          have : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by decide)
          omega
        refine ⟨m, Finset.mem_range.mpr hm_lt, ?_⟩
        apply List.ext_getElem
        · simp [bitsOfNat_length, Nat.min_eq_left hjl]
        · intro i h1 h2
          simp only [bitsOfNat, List.getElem_ofFn, List.getElem_take]
          have htb : ∀ (r : ℕ) (f : Fin r → Bool) (idx : Fin r),
              (∑ t : Fin r, if f t then 2 ^ t.val else 0).testBit idx.val = f idx := by
            intro r
            induction r with
            | zero => intro _ idx; exact Fin.elim0 idx
            | succ r ihr =>
              intro f idx
              rw [Fin.sum_univ_castSucc]
              by_cases hlast : idx.val = r
              · have h1 : (∑ t : Fin r, if f t.castSucc then 2 ^ t.val else 0) < 2 ^ r := by
                  have hs : (∑ t : Fin r, if f t.castSucc then 2 ^ t.val else 0) ≤ ∑ t : Fin r, 2 ^ t.val :=
                    Finset.sum_le_sum fun t _ => by split_ifs <;> [exact le_rfl; exact Nat.zero_le _]
                  have hg : ∑ t : Fin r, 2 ^ t.val = 2 ^ r - 1 := by
                    rw [Fin.sum_univ_eq_sum_range (fun t => 2 ^ t)]
                    exact sum_pow_two r
                  have : 1 ≤ 2 ^ r := Nat.one_le_pow _ _ (by decide); omega
                have hidx_eq : idx = Fin.last r := Fin.ext hlast
                rw [hidx_eq, Fin.val_last]
                cases hf : f (Fin.last r)
                · simp [Nat.testBit_lt_two_pow h1]
                · simp only [↓reduceIte, Nat.testBit, Nat.shiftRight_eq_div_pow, Fin.val_castSucc]
                  have hdiv0 : (∑ t : Fin r, if f t.castSucc then 2 ^ t.val else 0) / 2 ^ r = 0 :=
                    Nat.div_eq_of_lt h1
                  rw [Nat.add_div_right _ (by positivity), hdiv0, zero_add]; decide
              · have hlt : idx.val < r := by omega
                let idx' : Fin r := ⟨idx.val, hlt⟩
                have hidx_eq : idx = idx'.castSucc := Fin.ext rfl
                rw [hidx_eq]
                cases hf : f (Fin.last r)
                · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
                  exact ihr (fun t => f t.castSucc) idx'
                · simp only [↓reduceIte, Fin.val_castSucc, Fin.val_last]
                  have hdiv : 2 ^ r = 2 ^ (idx'.val + 1) * 2 ^ (r - (idx'.val + 1)) := by
                    rw [← pow_add]; congr 1; omega
                  have hbit : ((∑ t : Fin r, if f t.castSucc then 2 ^ t.val else 0) + 2 ^ r).testBit idx'.val =
                      (∑ t : Fin r, if f t.castSucc then 2 ^ t.val else 0).testBit idx'.val := by
                    rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
                    have hmul : 2 ^ r = 2 ^ idx'.val * (2 * 2 ^ (r - (idx'.val + 1))) := by
                      rw [hdiv, pow_succ]; ring
                    rw [hmul, Nat.add_mul_div_left _ _ (by positivity)]
                    simp [Nat.and_one_is_mod, Nat.add_mul_mod_self_left]
                  rw [hbit]
                  exact ihr (fun t => f t.castSucc) idx'
          have hi : i < j := by simp [bitsOfNat_length] at h1; exact h1
          exact htb j (fun t => l[t.val]'(by omega)) ⟨i, hi⟩
      rcases Finset.mem_union.mp hp with hp1 | hp2
      · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp1
        simp only [Finset.mem_Ico] at hm
        refine ⟨?_, ?_, by rw [bitsOfNat_length]; exact hd_le_half⟩
        · intro hmem
          rcases Finset.mem_union.mp hmem with h1 | h2
          · obtain ⟨j, hj, h1'⟩ := Finset.mem_biUnion.mp h1
            obtain ⟨_, _, heq⟩ := Finset.mem_image.mp h1'
            have := congrArg List.length heq; simp [bitsOfNat_length] at this
            rw [Finset.mem_range] at hj; omega
          · obtain ⟨m', hm', heq⟩ := Finset.mem_image.mp h2
            rw [Finset.mem_range] at hm'
            have := bitsOfNat_inj (Finset.mem_coe.mpr (Finset.mem_range.mpr (lt_trans hm' ha_lt)))
              (Finset.mem_coe.mpr (Finset.mem_range.mpr hm.2)) heq
            omega
        · intro j hj
          rw [bitsOfNat_length] at hj
          exact Finset.mem_union_left _ (htake_mem_Tlt _ j hj (by rw [bitsOfNat_length]; omega))
      · obtain ⟨⟨m, bit⟩, hmb, rfl⟩ := Finset.mem_image.mp hp2
        simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true] at hmb
        have ha_pos : a > 0 := by omega
        refine ⟨?_, ?_, by simp [bitsOfNat_length]; exact ha_pos_imp ha_pos⟩
        · intro hmem
          rcases Finset.mem_union.mp hmem with h1 | h2
          · obtain ⟨j, hj, h1'⟩ := Finset.mem_biUnion.mp h1
            obtain ⟨_, _, heq⟩ := Finset.mem_image.mp h1'
            have := congrArg List.length heq; simp [bitsOfNat_length] at this
            rw [Finset.mem_range] at hj; omega
          · obtain ⟨_, _, heq⟩ := Finset.mem_image.mp h2
            have := congrArg List.length heq; simp [bitsOfNat_length] at this
        · intro j hj
          simp only [List.length_append, bitsOfNat_length, List.length_singleton] at hj
          by_cases hjd : j < d
          · exact Finset.mem_union_left _ (htake_mem_Tlt _ j hjd (by simp [bitsOfNat_length]; omega))
          · have hjeq : j = d := by omega
            subst hjeq
            rw [show (bitsOfNat d m ++ [bit]).take d = bitsOfNat d m by
              rw [List.take_append_of_le_length (by simp [bitsOfNat_length]), List.take_of_length_le (by simp [bitsOfNat_length])]]
            exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hmb))

    have hleaf_hits : ∀ p ∈ L_d ∪ L_d1,
        Bval k p.length ≤ ((Finset.univ : Finset (Fin k → ZMod 2)).filter
          (fun y => runTree T q b y = p ∧ chi hk y = A p y + c p)).card := by
      intro p hp
      obtain ⟨hp_not, hp_pref, hp_len⟩ := hleaf_props p hp
      set len := p.length

      let U : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => ¬(i.val % 2 = 0 ∧ i.val / 2 < len))
      let mkY : Finset (Fin k) → (Fin k → ZMod 2) := fun S i =>
        if hi : i.val % 2 = 0 ∧ i.val / 2 < len then bVal (p[i.val / 2]'hi.2)
        else if i ∈ S then 1 else 0
      have hmkY_inj : Set.InjOn mkY (U.powerset.filter (fun S => ∀ u ∈ S, ix hk (u.val + 1) ∉ S)) := by
        intro S1 hS1 S2 hS2 heq
        have hsub1 := Finset.mem_powerset.mp (Finset.mem_filter.mp hS1).1
        have hsub2 := Finset.mem_powerset.mp (Finset.mem_filter.mp hS2).1
        ext i
        by_cases hi : i.val % 2 = 0 ∧ i.val / 2 < len
        · have hiU : i ∉ U := by simp [U, hi]
          exact ⟨fun h => False.elim (hiU (hsub1 h)), fun h => False.elim (hiU (hsub2 h))⟩
        · have h1 := congrFun heq i
          simp only [mkY, hi, ↓reduceDIte] at h1
          by_cases h1S : i ∈ S1 <;> by_cases h2S : i ∈ S2 <;> simp [h1S, h2S] at h1 ⊢
      have hmkY_mem : ∀ S ∈ U.powerset.filter (fun S => ∀ u ∈ S, ix hk (u.val + 1) ∉ S),
          mkY S ∈ Finset.univ.filter (fun y => runTree T q b y = p ∧ chi hk y = A p y + c p) := by
        intro S hS
        simp only [Finset.mem_filter, Finset.mem_powerset] at hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · rw [runTree_eq_iff T q b p hp_not hp_pref]
          intro j hj
          have h2j : 2 * j < k := by omega
          have hix2j : ix hk (2 * (p.take j).length) = ⟨2 * j, h2j⟩ := by
            apply Fin.ext; simp [ix, Nat.min_eq_left (le_of_lt hj), Nat.mod_eq_of_lt h2j]
          simp only [q, b, LinearMap.coe_mk, AddHom.coe_mk, hix2j, add_zero, mkY]
          have hcond : (⟨2 * j, h2j⟩ : Fin k).val % 2 = 0 ∧ (⟨2 * j, h2j⟩ : Fin k).val / 2 < len := ⟨by simp, by simp; omega⟩
          rw [dif_pos hcond]
          simp only [show (⟨2 * j, h2j⟩ : Fin k).val / 2 = j by simp, bVal]
          cases p[j] <;> decide
        · funext i
          simp only [chi, A, c, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.zero_apply, add_zero]
          set u := ix hk (i.val + 1)
          set v := ix hk (i.val + 2)
          by_cases hu : u.val % 2 = 0 ∧ u.val / 2 < p.length
          · rw [dif_pos hu]
            have hmu : mkY S u = bVal (p[u.val / 2]'hu.2) := dif_pos hu
            rw [hmu]
          · rw [dif_neg hu]
            by_cases hv : v.val % 2 = 0 ∧ v.val / 2 < p.length
            · rw [dif_pos hv]
              have hmv : mkY S v = bVal (p[v.val / 2]'hv.2) := dif_pos hv
              rw [hmv, mul_comm]
            · rw [dif_neg hv]
              have hmu : mkY S u = if u ∈ S then 1 else 0 := dif_neg hu
              have hmv : mkY S v = if v ∈ S then 1 else 0 := dif_neg hv
              rw [hmu, hmv]
              have hv_eq : v = ix hk (u.val + 1) := by
                apply Fin.ext; simp only [u, v, ix]; rw [Nat.mod_add_mod, add_assoc]
              by_cases huS : u ∈ S
              · have hvS : v ∉ S := hv_eq ▸ hS.2 u huS
                simp [huS, hvS]
              · simp [huS]
      have hcard_ge : indepCount hk U ≤ ((Finset.univ : Finset (Fin k → ZMod 2)).filter
          (fun y => runTree T q b y = p ∧ chi hk y = A p y + c p)).card := by
        unfold indepCount
        rw [← Finset.card_image_of_injOn hmkY_inj]
        exact Finset.card_le_card (Finset.image_subset_iff.mpr hmkY_mem)

      have hindep_U : indepCount hk U = Bval k len := by
        unfold Bval
        by_cases hlen0 : len = 0
        · simp only [hlen0, ↓reduceIte]
          have hU_univ : U = Finset.univ := by ext i; simp [U, hlen0]
          rw [hU_univ]

          unfold indepCount
          let u0 : Fin k := ⟨0, hk⟩
          let F := (Finset.univ : Finset (Fin k)).powerset.filter (fun S => ∀ u ∈ S, ix hk (u.val + 1) ∉ S)
          have hsp : F.card = (F.filter (fun S => u0 ∉ S)).card + (F.filter (fun S => u0 ∈ S)).card := by
            rw [add_comm]; exact (Finset.card_filter_add_card_filter_not (fun S => u0 ∈ S)).symm
          rw [hsp]
          have hc1 : (F.filter (fun S => u0 ∉ S)).card = Nat.fib (k + 1) := by
            have h1 : (F.filter (fun S => u0 ∉ S)).card =
                indepCount hk (Finset.univ.filter (fun i : Fin k => 1 ≤ i.val ∧ i.val < 1 + (k - 1))) := by
              unfold indepCount
              refine Finset.card_bij (fun S _ => S) ?_ ?_ ?_
              · intro S hS
                simp only [F, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
                refine ⟨fun x hx => ?_, hS.1.2⟩
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                have hne : x.val ≠ 0 := fun h => hS.2 ((Fin.ext h : x = u0) ▸ hx)
                omega
              · intro _ _ _ _ h; exact h
              · intro S hS
                simp only [F, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
                refine ⟨S, ⟨⟨Finset.subset_univ _, hS.2⟩, fun hu0 => ?_⟩, rfl⟩
                have h0 : 1 ≤ u0.val := (Finset.mem_filter.mp (hS.1 hu0)).2.1; exact absurd h0 (by simp [u0])
            have hrot1 : indepCount hk (Finset.univ.filter (fun i : Fin k => 1 ≤ i.val ∧ i.val < 1 + (k - 1))) =
                indepCount hk (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 1))) := by
              have hIm : (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 1))).image
                  (fun i => ix hk (i.val + 1)) =
                  Finset.univ.filter (fun i : Fin k => 1 ≤ i.val ∧ i.val < 1 + (k - 1)) := by
                ext i; have := i.isLt; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, zero_add]
                constructor
                · rintro ⟨a, ha, rfl⟩; simp [ix, Nat.mod_eq_of_lt (show a.val + 1 < k by omega)]; omega
                · intro hi; refine ⟨⟨i.val - 1, by omega⟩, by dsimp only; omega, ?_⟩
                  apply Fin.ext; simp [ix, Nat.mod_eq_of_lt (show i.val - 1 + 1 < k by omega)]; omega
              rw [← hIm, indepCount_rot hk 1]
            rw [h1, hrot1, indepCount_interval hk2 0 (k - 1) (by omega), show k - 1 + 2 = k + 1 by omega]
          have hc2 : (F.filter (fun S => u0 ∈ S)).card = Nat.fib (k - 1) := by
            by_cases hk2' : k = 2
            · subst hk2'
              have hsing : F.filter (fun S => u0 ∈ S) = {{u0}} := by
                ext S; simp only [F, Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and, Finset.mem_singleton]
                constructor
                · rintro ⟨hind, hu0⟩
                  ext x; fin_cases x
                  · simpa [u0] using hu0
                  · have hne1 : (⟨1, by decide⟩ : Fin 2) ≠ u0 := by intro h; have := congrArg Fin.val h; simp [u0] at this
                    have hix1 : ix hk (u0.val + 1) = ⟨1, by decide⟩ := by apply Fin.ext; simp [u0, ix]
                    simp only [Finset.mem_singleton, hne1, iff_false]
                    exact hix1 ▸ hind u0 hu0
                · rintro rfl
                  refine ⟨fun u hu hnext => ?_, Finset.mem_singleton_self _⟩
                  rw [Finset.mem_singleton] at hu hnext; subst hu
                  have := congrArg Fin.val hnext; simp [u0, ix] at this
              rw [hsing]; simp
            · have hk3 : 3 ≤ k := by omega
              have h2 : (F.filter (fun S => u0 ∈ S)).card =
                  indepCount hk (Finset.univ.filter (fun i : Fin k => 2 ≤ i.val ∧ i.val < 2 + (k - 3))) := by
                unfold indepCount
                refine Finset.card_bij (fun S _ => S.erase u0) ?_ ?_ ?_
                · intro S hS
                  simp only [F, Finset.mem_filter, Finset.mem_powerset] at hS ⊢
                  refine ⟨fun x hx => ?_, fun a ha hnext => hS.1.2 a (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hnext)⟩
                  have hxu := (Finset.mem_erase.mp hx).1
                  have hxS := (Finset.mem_erase.mp hx).2
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  have hne0 : x.val ≠ 0 := fun h => hxu (Fin.ext h)
                  have hne1 : x.val ≠ 1 := fun h => by
                    have hx1 : x = ix hk (u0.val + 1) := by apply Fin.ext; simp [u0, ix, h, Nat.mod_eq_of_lt (show 1 < k by omega)]
                    exact hS.1.2 u0 hS.2 (hx1 ▸ hxS)
                  have hnek : x.val ≠ k - 1 := fun h => by
                    have hxn : ix hk (x.val + 1) = u0 := by apply Fin.ext; simp [u0, ix, h, show k - 1 + 1 = k by omega]
                    exact hS.1.2 x hxS (hxn ▸ hS.2)
                  omega
                · intro S1 hS1 S2 hS2 h
                  rw [← Finset.insert_erase (Finset.mem_filter.mp hS1).2, ← Finset.insert_erase (Finset.mem_filter.mp hS2).2, h]
                · intro T hT
                  simp only [F, Finset.mem_filter, Finset.mem_powerset] at hT ⊢
                  refine ⟨insert u0 T, ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self _ _⟩, ?_⟩
                  · intro a ha hnext
                    rcases Finset.mem_insert.mp ha with rfl | haT
                    · rcases Finset.mem_insert.mp hnext with h1 | h2
                      · have := congrArg Fin.val h1; simp [u0, ix, Nat.mod_eq_of_lt (show 1 < k by omega)] at this
                      · have := (Finset.mem_filter.mp (hT.1 h2)).2; simp [u0, ix, Nat.mod_eq_of_lt (show 1 < k by omega)] at this
                    · rcases Finset.mem_insert.mp hnext with h1 | h2
                      · have ha_b := (Finset.mem_filter.mp (hT.1 haT)).2
                        have := congrArg Fin.val h1; simp [u0, ix, Nat.mod_eq_of_lt (show a.val + 1 < k by omega)] at this
                      · exact hT.2 a haT h2
                  · apply Finset.erase_insert; intro hu0
                    have := (Finset.mem_filter.mp (hT.1 hu0)).2; simp [u0] at this
              have hrot : indepCount hk (Finset.univ.filter (fun i : Fin k => 2 ≤ i.val ∧ i.val < 2 + (k - 3))) =
                  indepCount hk (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 3))) := by
                have hIm : (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 3))).image
                    (fun i => ix hk (i.val + 2)) =
                    Finset.univ.filter (fun i : Fin k => 2 ≤ i.val ∧ i.val < 2 + (k - 3)) := by
                  ext i; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, zero_add]
                  constructor
                  · rintro ⟨x, hx, rfl⟩; simp [ix, Nat.mod_eq_of_lt (show x.val + 2 < k by omega)]; omega
                  · intro hi; have := i.isLt; refine ⟨⟨i.val - 2, by omega⟩, by dsimp only; omega, ?_⟩
                    apply Fin.ext; simp [ix, Nat.mod_eq_of_lt (show i.val - 2 + 2 < k by omega)]; omega
                rw [← hIm, indepCount_rot hk 2]
              rw [h2, hrot, indepCount_interval hk2 0 (k - 3) (by omega), show k - 3 + 2 = k - 1 by omega]
          rw [hc1, hc2, add_comm]
        · simp only [hlen0, ↓reduceIte]
          split_ifs with h2len
          ·

            let U_iso := U.filter (fun i => i.val < 2 * len - 1)
            let U_tail := U.filter (fun i => 2 * len - 1 ≤ i.val)
            have hdisj : Disjoint U_iso U_tail := Finset.disjoint_left.mpr fun x h1 h2 => by
              have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
            have hunion : U = U_iso ∪ U_tail := by
              ext x; simp only [U_iso, U_tail, Finset.mem_union, Finset.mem_filter]
              exact ⟨fun hx => by rcases lt_or_ge x.val (2 * len - 1) with h | h <;> [exact Or.inl ⟨hx, h⟩; exact Or.inr ⟨hx, h⟩],
                     by rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx⟩
            have hno1 : ∀ u ∈ U_iso, ix hk (u.val + 1) ∉ U_tail := by
              intro u hu hn
              have huU := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
              have hu1 := (Finset.mem_filter.mp hu).2
              have hn1 := (Finset.mem_filter.mp hn).2
              have hodd : u.val % 2 = 1 := by omega
              simp only [ix, Nat.mod_eq_of_lt (show u.val + 1 < k by omega)] at hn1
              have : u.val + 1 = 2 * len - 1 := by omega
              omega
            have hno2 : ∀ v ∈ U_tail, ix hk (v.val + 1) ∉ U_iso := by
              intro v hv hn
              have hv1 := (Finset.mem_filter.mp hv).2
              have hnU := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
              have hn1 := (Finset.mem_filter.mp hn).2
              by_cases hvlt : v.val + 1 < k
              · simp only [ix, Nat.mod_eq_of_lt hvlt] at hn1; omega
              · have hveq : v.val + 1 = k := by omega
                simp only [ix, hveq, Nat.mod_self] at hnU
                exact hnU ⟨by decide, by omega⟩
            rw [hunion, indepCount_disjoint_union hk U_iso U_tail hdisj hno1 hno2]
            have hiso : indepCount hk U_iso = 2 ^ (len - 1) := by
              have hcard_iso : U_iso.card = len - 1 := by
                have hbij : U_iso.card = (Finset.range (len - 1)).card := by
                  refine Finset.card_bij (fun i _ => i.val / 2) ?_ ?_ ?_
                  · intro i hi; have h1 := (Finset.mem_filter.mp hi).2; have h2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2; exact Finset.mem_range.mpr (by omega)
                  · intro i1 hi1 i2 hi2 heq
                    have h1U := (Finset.mem_filter.mp (Finset.mem_filter.mp hi1).1).2
                    have h2U := (Finset.mem_filter.mp (Finset.mem_filter.mp hi2).1).2
                    have h1lt := (Finset.mem_filter.mp hi1).2
                    have h2lt := (Finset.mem_filter.mp hi2).2
                    exact Fin.ext (by omega)
                  · intro j hj; rw [Finset.mem_range] at hj
                    refine ⟨⟨2 * j + 1, by omega⟩, ?_, by simp; omega⟩
                    simp [U_iso, U]; omega
                simpa using hbij
              unfold indepCount
              have hfilt : U_iso.powerset.filter (fun S => ∀ u ∈ S, ix hk (u.val + 1) ∉ S) = U_iso.powerset := by
                refine Finset.filter_true_of_mem fun S hS u hu hnext => ?_
                have hsub := Finset.mem_powerset.mp hS
                have huU := (Finset.mem_filter.mp (Finset.mem_filter.mp (hsub hu)).1).2
                have hu1 := (Finset.mem_filter.mp (hsub hu)).2
                have hnU := (Finset.mem_filter.mp (Finset.mem_filter.mp (hsub hnext)).1).2
                have hn1 := (Finset.mem_filter.mp (hsub hnext)).2
                simp only [ix, Nat.mod_eq_of_lt (show u.val + 1 < k by omega)] at hnU hn1
                omega
              rw [hfilt, Finset.card_powerset, hcard_iso]
            have htail : indepCount hk U_tail = Nat.fib (k - 2 * len + 3) := by
              have hrot : indepCount hk U_tail = indepCount hk
                  (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 2 * len + 1))) := by
                have hIm : (Finset.univ.filter (fun i : Fin k => 0 ≤ i.val ∧ i.val < 0 + (k - 2 * len + 1))).image
                    (fun i => ix hk (i.val + (2 * len - 1))) = U_tail := by
                  ext i; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, U_tail, U, zero_add]
                  constructor
                  · rintro ⟨x, hx, rfl⟩
                    simp only [ix, Nat.mod_eq_of_lt (show x.val + (2 * len - 1) < k by omega)]
                    omega
                  · rintro ⟨hiU, hge⟩
                    have := i.isLt
                    refine ⟨⟨i.val - (2 * len - 1), by omega⟩, by dsimp only; omega, ?_⟩
                    apply Fin.ext; simp [ix, Nat.mod_eq_of_lt (show i.val - (2 * len - 1) + (2 * len - 1) < k by omega)]; omega
                rw [← hIm, indepCount_rot hk (2 * len - 1)]
              rw [hrot, indepCount_interval hk2 0 (k - 2 * len + 1) (by omega),
                  show k - 2 * len + 1 + 2 = k - 2 * len + 3 by omega]
            rw [hiso, htail]
          ·
            have hcard_U : U.card = k - len := by
              have hcomp : U = Finset.univ \ (Finset.univ : Finset (Fin len)).image (fun j => ⟨2 * j.val, by have := j.isLt; omega⟩) := by
                ext i; simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_image]
                constructor
                · intro h ⟨j, heq⟩; apply h; have hval := congrArg Fin.val heq; dsimp only at hval; have := j.isLt; omega
                · intro h ⟨he, hlt⟩; exact h ⟨⟨i.val / 2, hlt⟩, Fin.ext (by dsimp only; omega)⟩
              rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
              congr 1
              rw [Finset.card_image_of_injOn]
              · simp
              · intro j1 _ j2 _ heq; exact Fin.ext (by have := congrArg Fin.val heq; dsimp only at this; omega)
            unfold indepCount
            have hfilt : U.powerset.filter (fun S => ∀ u ∈ S, ix hk (u.val + 1) ∉ S) = U.powerset := by
              refine Finset.filter_true_of_mem fun S hS u hu hnext => ?_
              have hsub := Finset.mem_powerset.mp hS
              have huU := (Finset.mem_filter.mp (hsub hu)).2
              have hnU := (Finset.mem_filter.mp (hsub hnext)).2
              by_cases hult : u.val + 1 < k
              · simp only [ix, Nat.mod_eq_of_lt hult] at hnU; omega
              · have hueq : u.val + 1 = k := by omega
                simp only [ix, hueq, Nat.mod_self] at hnU
                exact hnU ⟨by decide, by omega⟩
            rw [hfilt, Finset.card_powerset, hcard_U]
      rw [← hindep_U]
      exact hcard_ge

    let hits : List Bool → Finset (Fin k → ZMod 2) := fun p =>
      Finset.univ.filter (fun y => runTree T q b y = p ∧ chi hk y = A p y + c p)
    have hsub : (L_d ∪ L_d1).biUnion hits ⊆
        Finset.univ.filter (fun y => let p := runTree T q b y; chi hk y = A p y + c p) := by
      intro y hy
      obtain ⟨p, _, hyp⟩ := Finset.mem_biUnion.mp hy
      simp only [hits, Finset.mem_filter, Finset.mem_univ, true_and] at hyp ⊢
      exact hyp.1.symm ▸ hyp.2
    have hcard_bi : ((L_d ∪ L_d1).biUnion hits).card = ∑ p ∈ L_d ∪ L_d1, (hits p).card := by
      refine Finset.card_biUnion fun p1 _ p2 _ hne => Finset.disjoint_left.mpr fun y h1 h2 => hne ?_
      exact (Finset.mem_filter.mp h1).2.1.symm.trans (Finset.mem_filter.mp h2).2.1
    refine le_trans ?_ (Finset.card_le_card hsub)
    rw [hcard_bi, Finset.sum_union hL_disj]
    have hs1 : (2 ^ d - a) * Bval k d ≤ ∑ p ∈ L_d, (hits p).card := by
      rw [← hLd_card, ← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun p hp => ?_
      have hlen : p.length = d := by
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp; exact bitsOfNat_length d _
      rw [← hlen]; exact hleaf_hits p (Finset.mem_union_left _ hp)
    have hs2 : 2 * a * Bval k (d + 1) ≤ ∑ p ∈ L_d1, (hits p).card := by
      rw [← hLd1_card, ← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun p hp => ?_
      have hlen : p.length = d + 1 := by
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hp; simp [bitsOfNat_length]
      rw [← hlen]; exact hleaf_hits p (Finset.mem_union_right _ hp)
    exact Nat.add_le_add hs1 hs2

lemma chi_translate {k : ℕ} (hk : 0 < k) (δ : Fin k → ZMod 2) :
    ∃ (D : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (d0 : Fin k → ZMod 2),
      ∀ u, chi hk (u + δ) = chi hk u + D u + d0 := by
  refine ⟨
    { toFun := fun u i => δ (ix hk (i.val + 1)) * u (ix hk (i.val + 2)) +
                          u (ix hk (i.val + 1)) * δ (ix hk (i.val + 2))
      map_add' := fun u1 u2 => by funext i; simp only [Pi.add_apply]; ring
      map_smul' := fun r u => by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
    fun i => δ (ix hk (i.val + 1)) * δ (ix hk (i.val + 2)),
    fun u => by funext i; simp only [chi, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]; ring⟩

end PEqualNP.Outside.L_meta_32032_aux

open scoped Classical in
open PEqualNP.Outside.L_meta_32032_aux in
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_32032 : (∀ (k : Nat) (hk : 0 < k) (L : Nat), 0 < L →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (n : Nat) (word : W) (i : Fin k) => word (ix (i.val+k-n % k))
  let B := fun p : Nat =>
    if p = 0 then Nat.fib (k-1) + Nat.fib (k+1)
    else if 2*p < k then 2^(p-1) * Nat.fib (k-2*p+3) else 2^(k-p)
  let cap := min L (2^((k+1)/2))
  let d := Nat.log2 cap
  let a := cap-2^d
  let N := if k = 1 then 2 else (2^d-a)*B d + 2*a*B (d+1)
  ∀ (column : Bool) (name constant : W),
    let gap := if column then 2 else 1
    let out := fun (raw : W) (site : Fin k) =>
      let old := rot (if column then 3 else 1) raw + name
      let y := fun u : Fin k => old u + old (ix (u.val+gap)) + old (ix (u.val+k-gap % k))
      y site + (1+y (ix (site.val+1)))*y (ix (site.val+2)) +
        rot (if column then 4 else 0) raw site + constant site
    let run := fun (T : Finset (List Bool)) (q : List Bool → W →ₗ[F] F)
        (b : List Bool → F) (x : W) =>
      (List.range T.card).foldl (fun (p : List Bool) _ =>
        if p ∈ T then p ++ [decide (q p x + b p ≠ 0)] else p) []
    let possible := fun n : Nat =>
      ∃ (T : Finset (List Bool)) (q : List Bool → W →ₗ[F] F) (b : List Bool → F)
          (A : List Bool → W →ₗ[F] W) (c : List Bool → W),
        T.card < L ∧ n ≤ ((Finset.univ : Finset W).filter (fun x =>
          let p := run T q b x
          out x = A p x + c p)).card
    let h := if 3 ∣ k then (if column = true ∧ 2 ∣ k then 4 else 2) else 0
    possible N ∧ ∀ n, possible n → n ≤ min (2^k) (2^h*N)) := by
  intro k hk L hL
  dsimp only
  intro column name constant
  let F := ZMod 2
  let W := Fin k → F
  let gap := if column then 2 else 1
  let sRot := if column then 3 else 1
  let sOut := if column then 4 else 0
  let M : W →ₗ[F] W := (mixLin hk gap).comp (rotLin hk sRot)
  let y0 : W := mixLin hk gap name

  let shift2 : W →ₗ[F] W :=
    { toFun := fun w i => w (ix hk (i.val + 2))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L_aff : W →ₗ[F] W := M + shift2.comp M + rotLin hk sOut
  let c_aff : W := y0 + shift2 y0 + constant
  have hout_eq : ∀ raw : W,
      (fun site : Fin k =>
        let old := (fun i : Fin k => raw (ix hk (i.val + k - sRot % k))) + name
        let y := fun u : Fin k => old u + old (ix hk (u.val + gap)) + old (ix hk (u.val + k - gap % k))
        y site + (1 + y (ix hk (site.val + 1))) * y (ix hk (site.val + 2)) +
          raw (ix hk (site.val + k - sOut % k)) + constant site) =
      chi hk (M raw + y0) + L_aff raw + c_aff := by
    intro raw
    funext site
    have hy_eq : ∀ u : Fin k,
        ((fun i : Fin k => raw (ix hk (i.val + k - sRot % k))) + name) u +
        ((fun i : Fin k => raw (ix hk (i.val + k - sRot % k))) + name) (ix hk (u.val + gap)) +
        ((fun i : Fin k => raw (ix hk (i.val + k - sRot % k))) + name) (ix hk (u.val + k - gap % k)) =
        (M raw + y0) u := by
      intro u
      change (raw (ix hk (u.val + k - sRot % k)) + name u) +
             (raw (ix hk ((ix hk (u.val + gap)).val + k - sRot % k)) + name (ix hk (u.val + gap))) +
             (raw (ix hk ((ix hk (u.val + k - gap % k)).val + k - sRot % k)) + name (ix hk (u.val + k - gap % k))) =
             (raw (ix hk (u.val + k - sRot % k)) +
              raw (ix hk ((ix hk (u.val + gap)).val + k - sRot % k)) +
              raw (ix hk ((ix hk (u.val + k - gap % k)).val + k - sRot % k))) +
             (name u + name (ix hk (u.val + gap)) + name (ix hk (u.val + k - gap % k)))
      ring
    dsimp only
    rw [hy_eq site, hy_eq (ix hk (site.val + 1)), hy_eq (ix hk (site.val + 2))]
    change (M raw site + y0 site) + (1 + (M raw (ix hk (site.val + 1)) + y0 (ix hk (site.val + 1)))) *
        (M raw (ix hk (site.val + 2)) + y0 (ix hk (site.val + 2))) +
        raw (ix hk (site.val + k - sOut % k)) + constant site =
      ((M raw (ix hk (site.val + 1)) + y0 (ix hk (site.val + 1))) *
       (M raw (ix hk (site.val + 2)) + y0 (ix hk (site.val + 2)))) +
      (M raw site + M raw (ix hk (site.val + 2)) + raw (ix hk (site.val + k - sOut % k))) +
      (y0 site + y0 (ix hk (site.val + 2)) + constant site)
    ring
  have hker_dim : Module.finrank F (LinearMap.ker M) =
      if 3 ∣ k then (if column = true ∧ 2 ∣ k then 4 else 2) else 0 := by
    have hbij := rotLin_bijective hk sRot
    let eR : W ≃ₗ[F] W := LinearEquiv.ofBijective (rotLin hk sRot) hbij
    have hker_eq : LinearMap.ker M = (LinearMap.ker (mixLin hk gap)).comap eR.toLinearMap := by
      ext x; simp [M, eR]
    rw [hker_eq]
    have hmap : (LinearMap.ker (mixLin hk gap)).comap eR.toLinearMap =
        (LinearMap.ker (mixLin hk gap)).map eR.symm.toLinearMap := by
      ext x; simp [Submodule.mem_map, eR]
    rw [hmap, LinearEquiv.finrank_map_eq]
    exact finrank_ker_mixLin_gap hk column
  have hker_card : Fintype.card (LinearMap.ker M) =
      2 ^ (if 3 ∣ k then (if column = true ∧ 2 ∣ k then 4 else 2) else 0) := by
    have := Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker M)
    simpa [Nat.card_eq_fintype_card, F, ZMod.card, hker_dim] using this
  constructor
  ·
    obtain ⟨T, q, b, A, c, hT, hN⟩ := possibleY_N hk L hL
    let S := (Finset.univ : Finset W).filter (fun u => chi hk u = A (runTree T q b u) u + c (runTree T q b u))
    obtain ⟨Kc, hKc⟩ := Submodule.exists_isCompl (LinearMap.range M)
    let eqvC : (LinearMap.range M × Kc) ≃ₗ[F] W := Submodule.prodEquivOfIsCompl _ _ hKc
    have hKc_dim : Module.finrank F Kc = Module.finrank F (LinearMap.ker M) := by
      have h1 := Submodule.finrank_add_eq_of_isCompl hKc
      have h2 := LinearMap.finrank_range_add_finrank_ker M
      omega
    have hKc_card : Fintype.card Kc = Fintype.card (LinearMap.ker M) := by
      have c1 : Fintype.card Kc = (Fintype.card F) ^ Module.finrank F Kc := by
        simpa [Nat.card_eq_fintype_card] using Module.card_eq_pow_finrank (K := F) (V := Kc)
      have c2 : Fintype.card (LinearMap.ker M) = (Fintype.card F) ^ Module.finrank F (LinearMap.ker M) := by
        simpa [Nat.card_eq_fintype_card] using Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker M)
      rw [c1, c2, hKc_dim]

    have hsum_coset : ∑ t : Kc, ((Finset.univ : Finset (LinearMap.range M)).filter
        (fun v => t.val + v.val ∈ S)).card = S.card := by
      have h1 : (∑ t : Kc, ((Finset.univ : Finset (LinearMap.range M)).filter
          (fun v => t.val + v.val ∈ S)).card) =
          ((Finset.univ : Finset (Kc × LinearMap.range M)).filter (fun p => p.1.val + p.2.val ∈ S)).card := by
        rw [Finset.card_filter, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.card_filter]
      rw [h1]
      refine Finset.card_bij (fun p _ => p.1.val + p.2.val) ?_ ?_ ?_
      · intro p hp; exact (Finset.mem_filter.mp hp).2
      · intro p1 _ p2 _ heq
        have h2 : eqvC (p1.2, p1.1) = eqvC (p2.2, p2.1) := by
          change p1.2.val + p1.1.val = p2.2.val + p2.1.val
          rw [add_comm p1.2.val, add_comm p2.2.val]; exact heq
        have h3 := eqvC.injective h2
        exact Prod.ext (congrArg Prod.snd h3) (congrArg Prod.fst h3)
      · intro u hu
        let pr := eqvC.symm u
        have hpr : pr.2.val + pr.1.val = u := by
          rw [add_comm]; exact eqvC.apply_symm_apply u
        exact ⟨(pr.2, pr.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpr.symm ▸ hu⟩, hpr⟩

    have hex_t : ∃ t : Kc, S.card ≤ Fintype.card Kc *
        ((Finset.univ : Finset (LinearMap.range M)).filter (fun v => t.val + v.val ∈ S)).card := by
      have hne : (Finset.univ : Finset Kc).Nonempty := ⟨0, Finset.mem_univ _⟩
      obtain ⟨t, _, htmax⟩ := Finset.exists_max_image Finset.univ
        (fun t : Kc => ((Finset.univ : Finset (LinearMap.range M)).filter (fun v => t.val + v.val ∈ S)).card) hne
      refine ⟨t, ?_⟩
      rw [← hsum_coset]
      calc ∑ x : Kc, ((Finset.univ : Finset (LinearMap.range M)).filter (fun v => x.val + v.val ∈ S)).card
          ≤ ∑ _x : Kc, ((Finset.univ : Finset (LinearMap.range M)).filter (fun v => t.val + v.val ∈ S)).card :=
            Finset.sum_le_sum fun x _ => htmax x (Finset.mem_univ x)
        _ = Fintype.card Kc * ((Finset.univ : Finset (LinearMap.range M)).filter (fun v => t.val + v.val ∈ S)).card := by
            simp [Finset.sum_const, smul_eq_mul]
    obtain ⟨t, ht⟩ := hex_t

    obtain ⟨D, d0, hD⟩ := chi_translate hk (y0 - t.val)
    let q' : List Bool → W →ₗ[F] F := fun p => (q p).comp M
    let b' : List Bool → F := fun p => b p + q p t.val
    let A' : List Bool → W →ₗ[F] W := fun p => (A p).comp M + D.comp M + L_aff
    let c' : List Bool → W := fun p => A p t.val + c p + D t.val + d0 + c_aff
    refine ⟨T, q', b', A', c', hT, ?_⟩

    have hrun_eq : ∀ raw : W, runTree T q' b' raw = runTree T q b (M raw + t.val) := by
      intro raw
      simp only [runTree]
      congr 1; funext p _
      have hqb : q' p raw + b' p = q p (M raw + t.val) + b p := by
        simp only [q', b', LinearMap.comp_apply, map_add]; ring
      rw [hqb]
    have hsub_raw : (Finset.univ : Finset W).filter (fun raw => t.val + M raw ∈ S) ⊆
        (Finset.univ : Finset W).filter (fun raw =>
          let p := runTree T q' b' raw
          (fun site : Fin k =>
            let old := (fun i : Fin k => raw (ix hk (i.val + k - sRot % k))) + name
            let y := fun u : Fin k => old u + old (ix hk (u.val + gap)) + old (ix hk (u.val + k - gap % k))
            y site + (1 + y (ix hk (site.val + 1))) * y (ix hk (site.val + 2)) +
              raw (ix hk (site.val + k - sOut % k)) + constant site) = A' p raw + c' p) := by
      intro raw hraw
      have hS_mem := (Finset.mem_filter.mp hraw).2
      have hchi_u := (Finset.mem_filter.mp hS_mem).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hout_eq raw, hrun_eq raw]
      have h1 : M raw + y0 = (M raw + t.val) + (y0 - t.val) := by abel
      rw [h1, hD (M raw + t.val)]
      have hcomm : M raw + t.val = t.val + M raw := add_comm _ _
      rw [hcomm, hchi_u, ← hcomm]
      simp only [A', c', LinearMap.add_apply, LinearMap.comp_apply, map_add]
      abel

    obtain ⟨K, hK⟩ := Submodule.exists_isCompl (LinearMap.ker M)
    let eqvK : (LinearMap.ker M × K) ≃ₗ[F] W := Submodule.prodEquivOfIsCompl _ _ hK
    let M_K_lin : K →ₗ[F] LinearMap.range M :=
      { toFun := fun w => ⟨M w.val, ⟨w.val, rfl⟩⟩
        map_add' := fun w1 w2 => Subtype.ext (map_add M w1.val w2.val)
        map_smul' := fun r w => Subtype.ext (map_smul M r w.val) }
    let M_K : K ≃ₗ[F] LinearMap.range M := LinearEquiv.ofBijective M_K_lin
      ⟨fun w1 w2 h => by
        have hsub : w1.val - w2.val ∈ LinearMap.ker M := by
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact congrArg Subtype.val h
        have hmemK : w1.val - w2.val ∈ K := K.sub_mem w1.property w2.property
        have h0 : w1.val - w2.val = 0 := by
          have : w1.val - w2.val ∈ LinearMap.ker M ⊓ K := ⟨hsub, hmemK⟩
          rw [hK.inf_eq_bot] at this; exact this
        exact Subtype.ext (sub_eq_zero.mp h0),
       fun ⟨y, x, hx⟩ => by
        let p := eqvK.symm x
        refine ⟨p.2, Subtype.ext ?_⟩
        have hsum : p.1.val + p.2.val = x := eqvK.apply_symm_apply x
        change M p.2.val = y
        rw [← hx, ← hsum, map_add, LinearMap.mem_ker.mp p.1.property, zero_add]⟩
    have hcard_raw : ((Finset.univ : Finset W).filter (fun raw => t.val + M raw ∈ S)).card =
        Fintype.card (LinearMap.ker M) *
          ((Finset.univ : Finset (LinearMap.range M)).filter (fun v => t.val + v.val ∈ S)).card := by
      have hbij : ((Finset.univ : Finset W).filter (fun raw => t.val + M raw ∈ S)).card =
          ((Finset.univ : Finset (LinearMap.ker M)) ×ˢ
            ((Finset.univ : Finset (LinearMap.range M)).filter (fun v => t.val + v.val ∈ S))).card := by
        refine Finset.card_bij (fun raw _ => ((eqvK.symm raw).1, M_K (eqvK.symm raw).2)) ?_ ?_ ?_
        · intro raw hraw
          simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter]
          have hsum : (eqvK.symm raw).1.val + (eqvK.symm raw).2.val = raw := eqvK.apply_symm_apply raw
          have hMeq : (M_K (eqvK.symm raw).2).val = M raw := by
            change M (eqvK.symm raw).2.val = M raw
            conv_rhs => rw [← hsum]
            rw [map_add, LinearMap.mem_ker.mp (eqvK.symm raw).1.property, zero_add]
          rw [hMeq]; exact (Finset.mem_filter.mp hraw).2
        · intro r1 _ r2 _ heq
          simp only [Prod.mk.injEq] at heq
          have : eqvK.symm r1 = eqvK.symm r2 := Prod.ext heq.1 (M_K.injective heq.2)
          exact eqvK.symm.injective this
        · intro ⟨v, w⟩ hvw
          simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter] at hvw
          let raw := eqvK (v, M_K.symm w)
          refine ⟨raw, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · have hMeq : M raw = w.val := by
              change M (v.val + (M_K.symm w).val) = w.val
              rw [map_add, LinearMap.mem_ker.mp v.property, zero_add]
              exact congrArg Subtype.val (M_K.apply_symm_apply w)
            rw [hMeq]; exact hvw
          · simp [raw]
      rw [hbij, Finset.card_product, Finset.card_univ]
    have hge : Nval k L ≤ ((Finset.univ : Finset W).filter (fun raw => t.val + M raw ∈ S)).card := by
      rw [hcard_raw, ← hKc_card]
      exact le_trans hN ht
    refine le_trans hge (Finset.card_le_card ?_)
    intro raw hraw
    have hmem := hsub_raw hraw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    exact hmem
  ·
    intro n ⟨T, q, b, A, c, hT, hn⟩
    refine le_min ?_ ?_
    · exact le_trans hn (le_trans (Finset.card_le_univ _) (by simp [W, F, Fintype.card_fun, ZMod.card]))
    ·
      obtain ⟨K, hK⟩ := Submodule.exists_isCompl (LinearMap.ker M)
      let eqvK : (LinearMap.ker M × K) ≃ₗ[F] W := Submodule.prodEquivOfIsCompl _ _ hK
      let M_K_lin : K →ₗ[F] LinearMap.range M :=
        { toFun := fun w => ⟨M w.val, ⟨w.val, rfl⟩⟩
          map_add' := fun w1 w2 => Subtype.ext (map_add M w1.val w2.val)
          map_smul' := fun r w => Subtype.ext (map_smul M r w.val) }
      let M_K : K ≃ₗ[F] LinearMap.range M := LinearEquiv.ofBijective M_K_lin
        ⟨fun w1 w2 h => by
          have hsub : w1.val - w2.val ∈ LinearMap.ker M := by
            rw [LinearMap.mem_ker, map_sub, sub_eq_zero]; exact congrArg Subtype.val h
          have h0 : w1.val - w2.val = 0 := by
            have : w1.val - w2.val ∈ LinearMap.ker M ⊓ K := ⟨hsub, K.sub_mem w1.property w2.property⟩
            rw [hK.inf_eq_bot] at this; exact this
          exact Subtype.ext (sub_eq_zero.mp h0),
         fun ⟨y, x, hx⟩ => by
          let p := eqvK.symm x
          refine ⟨p.2, Subtype.ext ?_⟩
          have hsum : p.1.val + p.2.val = x := eqvK.apply_symm_apply x
          change M p.2.val = y
          rw [← hx, ← hsum, map_add, LinearMap.mem_ker.mp p.1.property, zero_add]⟩
      obtain ⟨Kc, hKc⟩ := Submodule.exists_isCompl (LinearMap.range M)
      let projR : W →ₗ[F] LinearMap.range M :=
        (LinearMap.fst F (LinearMap.range M) Kc).comp (Submodule.prodEquivOfIsCompl _ _ hKc).symm.toLinearMap
      have hprojR : ∀ y : LinearMap.range M, projR y.val = y := by
        intro y
        have h1 : (Submodule.prodEquivOfIsCompl _ _ hKc) (y, 0) = y.val := by simp
        have h2 : (Submodule.prodEquivOfIsCompl _ _ hKc).symm y.val = (y, 0) :=
          (Submodule.prodEquivOfIsCompl _ _ hKc).symm_apply_eq.mpr h1.symm
        simp [projR, h2]
      let ψ : W →ₗ[F] W := K.subtype.comp (M_K.symm.toLinearMap.comp projR)
      have hψ : ∀ w : K, ψ (M w.val) = w.val := by
        intro w
        have h1 : projR (M w.val) = M_K w := hprojR (M_K w)
        simp [ψ, h1]
      let H := (Finset.univ : Finset W).filter (fun x =>
        let p := runTree T q b x
        (fun site : Fin k =>
          let old := (fun i : Fin k => x (ix hk (i.val + k - sRot % k))) + name
          let y := fun u : Fin k => old u + old (ix hk (u.val + gap)) + old (ix hk (u.val + k - gap % k))
          y site + (1 + y (ix hk (site.val + 1))) * y (ix hk (site.val + 2)) +
            x (ix hk (site.val + k - sOut % k)) + constant site) = A p x + c p)
      have hsum_ker : H.card = ∑ v : LinearMap.ker M,
          ((Finset.univ : Finset K).filter (fun w => v.val + w.val ∈ H)).card := by
        have h1 : (∑ v : LinearMap.ker M, ((Finset.univ : Finset K).filter (fun w => v.val + w.val ∈ H)).card) =
            ((Finset.univ : Finset (LinearMap.ker M × K)).filter (fun p => p.1.val + p.2.val ∈ H)).card := by
          rw [Finset.card_filter, Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun _ _ => Finset.card_filter _ _
        rw [h1]
        refine (Finset.card_bij (fun p _ => p.1.val + p.2.val) ?_ ?_ ?_).symm
        · intro p hp; exact (Finset.mem_filter.mp hp).2
        · intro p1 _ p2 _ heq; exact eqvK.injective heq
        · intro x hx
          refine ⟨eqvK.symm x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, eqvK.apply_symm_apply x⟩
          have hsum : (eqvK.symm x).1.val + (eqvK.symm x).2.val = x := eqvK.apply_symm_apply x
          rw [hsum]; exact hx
      have hslice_le : ∀ v : LinearMap.ker M,
          ((Finset.univ : Finset K).filter (fun w => v.val + w.val ∈ H)).card ≤ Nval k L := by
        intro v

        let qv : List Bool → W →ₗ[F] F := fun p => (q p).comp ψ
        let bv : List Bool → F := fun p => b p + q p (v.val - ψ y0)
        let Av : List Bool → W →ₗ[F] W := fun p => (A p - L_aff).comp ψ
        let cv : List Bool → W := fun p => (A p - L_aff) (v.val - ψ y0) + c p - c_aff
        have hrun_v : ∀ w : K, runTree T qv bv (M w.val + y0) = runTree T q b (v.val + w.val) := by
          intro w
          simp only [runTree]
          congr 1; funext p _
          have h1 : qv p (M w.val + y0) + bv p = q p (v.val + w.val) + b p := by
            simp only [qv, bv, LinearMap.comp_apply, map_add, map_sub, hψ w]
            ring
          rw [h1]
        have hinj : Set.InjOn (fun w : K => M w.val + y0)
            ((Finset.univ : Finset K).filter (fun w => v.val + w.val ∈ H)) := by
          intro w1 _ w2 _ heq
          have hM : M w1.val = M w2.val := add_right_cancel heq
          exact M_K.injective (Subtype.ext hM)
        rw [← Finset.card_image_of_injOn hinj]
        refine le_trans (Finset.card_le_card ?_) (possibleY_le_N hk L hL T qv bv Av cv hT)
        intro u hu
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
        have hwH := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).2).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hout_eq (v.val + w.val)] at hwH
        have hMvw : M (v.val + w.val) = M w.val := by
          rw [map_add, LinearMap.mem_ker.mp v.property, zero_add]
        rw [hMvw] at hwH
        rw [hrun_v w]
        have h2 : Av (runTree T q b (v.val + w.val)) (M w.val + y0) + cv (runTree T q b (v.val + w.val)) =
            (A (runTree T q b (v.val + w.val)) (v.val + w.val) + c (runTree T q b (v.val + w.val))) -
              (L_aff (v.val + w.val) + c_aff) := by
          simp only [Av, cv, LinearMap.comp_apply, LinearMap.sub_apply, map_add, map_sub, hψ w]
          abel
        rw [h2]
        have h3 : chi hk (M w.val + y0) + (L_aff (v.val + w.val) + c_aff) =
            A (runTree T q b (v.val + w.val)) (v.val + w.val) + c (runTree T q b (v.val + w.val)) := by
          simpa [add_assoc] using hwH
        rw [← h3, add_sub_cancel_right]
      refine le_trans hn ?_
      have hcard_eq : ((Finset.univ : Finset W).filter (fun x =>
          let p := (List.range T.card).foldl (fun (p : List Bool) _ =>
            if p ∈ T then p ++ [decide (q p x + b p ≠ 0)] else p) []
          (fun site : Fin k =>
            let old := (fun i : Fin k => x (ix hk (i.val + k - sRot % k))) + name
            let y := fun u : Fin k => old u + old (ix hk (u.val + gap)) + old (ix hk (u.val + k - gap % k))
            y site + (1 + y (ix hk (site.val + 1))) * y (ix hk (site.val + 2)) +
              x (ix hk (site.val + k - sOut % k)) + constant site) = A p x + c p)).card = H.card := by
        rfl
      refine le_trans (le_of_eq hcard_eq) ?_
      rw [hsum_ker]
      calc ∑ v : LinearMap.ker M, ((Finset.univ : Finset K).filter (fun w => v.val + w.val ∈ H)).card
          ≤ ∑ _v : LinearMap.ker M, Nval k L := Finset.sum_le_sum fun v _ => hslice_le v
        _ = Fintype.card (LinearMap.ker M) * Nval k L := by simp [Finset.sum_const, smul_eq_mul]
        _ = 2 ^ (if 3 ∣ k then (if column = true ∧ 2 ∣ k then 4 else 2) else 0) * Nval k L := by
            rw [hker_card]
