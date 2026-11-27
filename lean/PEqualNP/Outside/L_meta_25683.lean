import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25683_aux

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

def checkMap {k : ℕ} (d : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin (Nat.gcd k d) × Fin 2 → ZMod 2) :=
  let g := Nat.gcd k d
  { toFun := fun y rc =>
      if 3 ∣ k / g then
        ∑ v : Fin k,
          if v.val % g = rc.1.val ∧ (v.val / g % 3 = rc.2.val ∨ v.val / g % 3 = 2)
          then y v else 0
      else 0
    map_add' := fun y1 y2 => by
      ext rc
      simp only [Pi.add_apply]
      split_ifs
      · rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> simp
      · simp
    map_smul' := fun c y => by
      ext rc
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      split_ifs
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        split_ifs <;> simp
      · simp }

lemma shift_mod_g_div_mod3 {k : ℕ} (hk : 0 < k) (d : ℕ)
    (hsing : 3 ∣ k / Nat.gcd k d) (v : Fin k) :
    let g := Nat.gcd k d
    (ix hk (v.val + d)).val % g = v.val % g ∧
    (ix hk (v.val + d)).val / g % 3 = (v.val / g + d / g) % 3 := by
  intro g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hk
  have hg_dvd_k : g ∣ k := Nat.gcd_dvd_left k d
  have hg_dvd_d : g ∣ d := Nat.gcd_dvd_right k d
  have hk_eq : g * (k / g) = k := Nat.mul_div_cancel' hg_dvd_k
  have hd_eq : g * (d / g) = d := Nat.mul_div_cancel' hg_dvd_d
  have h1 : (v.val + d) % k % g = v.val % g := by
    rw [Nat.mod_mod_of_dvd _ hg_dvd_k, Nat.add_mod, Nat.mod_eq_zero_of_dvd hg_dvd_d,
      Nat.add_zero, Nat.mod_mod]
  refine ⟨h1, ?_⟩
  simp only [ix]
  have hdiv_mod : (v.val + d) % k / g = (v.val / g + d / g) % (k / g) := by
    have hv_split : v.val = g * (v.val / g) + v.val % g := (Nat.div_add_mod v.val g).symm
    have hsum : v.val + d = g * (v.val / g + d / g) + v.val % g := by
      calc
        v.val + d = g * (v.val / g) + v.val % g + g * (d / g) := by
          conv_lhs => rw [hv_split, ← hd_eq]
        _ = g * (v.val / g + d / g) + v.val % g := by ring
    let q := (v.val / g + d / g) / (k / g)
    let rem := (v.val / g + d / g) % (k / g)
    have hq : v.val / g + d / g = (k / g) * q + rem := (Nat.div_add_mod _ _).symm
    have hrem_lt : rem < k / g := Nat.mod_lt _ (Nat.div_pos (Nat.le_of_dvd hk hg_dvd_k) hg_pos)
    have hvmod_lt : v.val % g < g := Nat.mod_lt _ hg_pos
    have hlt_k : g * rem + v.val % g < k := by
      have hle : rem + 1 ≤ k / g := hrem_lt
      calc
        g * rem + v.val % g < g * rem + g := Nat.add_lt_add_left hvmod_lt _
        _ = g * (rem + 1) := by ring
        _ ≤ g * (k / g) := Nat.mul_le_mul_left g hle
        _ = k := hk_eq
    have hmod_k : (v.val + d) % k = g * rem + v.val % g := by
      have hmul : g * (k / g * q) = k * q := by rw [← mul_assoc, hk_eq]
      have heq : v.val + d = (g * rem + v.val % g) + k * q := by
        rw [hsum, hq, Nat.mul_add, hmul]; ring
      rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_k]
    rw [hmod_k, Nat.mul_add_div hg_pos, Nat.div_eq_of_lt hvmod_lt, Nat.add_zero]
  rw [hdiv_mod, Nat.mod_mod_of_dvd _ hsing]

lemma shift_neg_mod_g_div_mod3 {k : ℕ} (hk : 0 < k) (d : ℕ)
    (hsing : 3 ∣ k / Nat.gcd k d) (v : Fin k) :
    let g := Nat.gcd k d
    (ix hk (v.val + k - d % k)).val % g = v.val % g ∧
    ((ix hk (v.val + k - d % k)).val / g + d / g) % 3 = v.val / g % 3 := by
  intro g
  let w := ix hk (v.val + k - d % k)
  have hback : ix hk (w.val + d) = v := by
    simp only [w, ix_val_add]
    have hd : d % k < k := Nat.mod_lt _ hk
    have hdiv := Nat.div_add_mod d k
    have hmul : k * (d / k + 1) = k * (d / k) + k := by ring
    have heq : v.val + k - d % k + d = v.val + k * (d / k + 1) := by rw [hmul]; omega
    rw [heq]
    ext
    simp only [ix]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.2]
  have h := shift_mod_g_div_mod3 hk d hsing w
  rw [hback] at h
  exact ⟨h.1.symm, h.2.symm⟩

lemma range_mixLin_eq_ker_checkMap {k : ℕ} (hk : 0 < k) (d : ℕ) (hd12 : d = 1 ∨ d = 2) :
    LinearMap.range (mixLin hk d) = LinearMap.ker (checkMap (k := k) d) := by
  have hd : 0 < d := by omega
  let g := Nat.gcd k d
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hk
  have hg_dvd_k : g ∣ k := Nat.gcd_dvd_left k d
  have hg_dvd_d : g ∣ d := Nat.gcd_dvd_right k d
  have hk_eq : g * (k / g) = k := Nat.mul_div_cancel' hg_dvd_k
  have hd_eq : g * (d / g) = d := Nat.mul_div_cancel' hg_dvd_d
  have hle : LinearMap.range (mixLin hk d) ≤ LinearMap.ker (checkMap (k := k) d) := by
    rintro y ⟨z, rfl⟩
    show checkMap (k := k) d (mixLin hk d z) = 0
    ext ⟨r, c⟩
    simp only [checkMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    split_ifs with hsing
    · have hsum_res : ∀ c0 : ℕ, c0 < 3 →
          (∑ v : Fin k, if v.val % g = r.val ∧ v.val / g % 3 = c0 then mixLin hk d z v else 0) =
            ∑ w : Fin k, if w.val % g = r.val then z w else 0 := by
        intro c0 hc0
        have hdg : d / g = 1 ∨ d / g = 2 := by
          rcases hd12 with rfl | rfl
          · left
            have hg1 : g = 1 := Nat.gcd_one_right k
            simp [hg1]
          · have hg12 : g = 1 ∨ g = 2 := by
              have hle2 : g ≤ 2 := Nat.le_of_dvd (by omega) hg_dvd_d
              omega
            rcases hg12 with hg1 | hg2
            · right; simp [hg1]
            · left; simp [hg2]
        have hsplit :
            (∑ v : Fin k, if v.val % g = r.val ∧ v.val / g % 3 = c0 then mixLin hk d z v else 0) =
              (∑ v : Fin k, if v.val % g = r.val ∧ v.val / g % 3 = c0 then z v else 0) +
              (∑ v : Fin k, if v.val % g = r.val ∧ v.val / g % 3 = c0
                then z (ix hk (v.val + d)) else 0) +
              (∑ v : Fin k, if v.val % g = r.val ∧ v.val / g % 3 = c0
                then z (ix hk (v.val + k - d % k)) else 0) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun v _ => ?_
          simp only [mixLin, LinearMap.coe_mk, AddHom.coe_mk]
          split_ifs <;> ring
        rw [hsplit]
        have hinv1 : ∀ v : Fin k, ix hk ((ix hk (v.val + d)).val + k - d % k) = v := by
          intro v
          rw [ix_add_sub_mod]
          have hdiv := Nat.div_add_mod d k
          have hlt := Nat.mod_lt d hk
          have hmul : k * (d / k + 1) = k * (d / k) + k := by ring
          have h1 : v.val + d + (k - d % k) = v.val + k * (d / k + 1) := by rw [hmul]; omega
          rw [h1]
          ext; simp only [ix]; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.2]
        have hinv2 : ∀ v : Fin k, ix hk ((ix hk (v.val + k - d % k)).val + d) = v := by
          intro v
          rw [ix_val_add]
          have hdiv := Nat.div_add_mod d k
          have hlt := Nat.mod_lt d hk
          have hmul : k * (d / k + 1) = k * (d / k) + k := by ring
          have h1 : v.val + k - d % k + d = v.val + k * (d / k + 1) := by rw [hmul]; omega
          rw [h1]
          ext; simp only [ix]; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.2]
        have hbij_pos : Function.Bijective (fun v : Fin k => ix hk (v.val + d)) :=
          Function.bijective_iff_has_inverse.mpr ⟨fun v => ix hk (v.val + k - d % k), hinv1, hinv2⟩
        have hbij_neg : Function.Bijective (fun v : Fin k => ix hk (v.val + k - d % k)) :=
          Function.bijective_iff_has_inverse.mpr ⟨fun v => ix hk (v.val + d), hinv2, hinv1⟩
        have hterm2 :
            (∑ v : Fin k, if v.val % g = r.val ∧ v.val / g % 3 = c0
              then z (ix hk (v.val + d)) else 0) =
            ∑ w : Fin k, if w.val % g = r.val ∧ w.val / g % 3 = (c0 + d / g) % 3 then z w else 0 := by
          refine Fintype.sum_bijective (fun v => ix hk (v.val + d)) hbij_pos _ _ ?_
          intro v
          have hs := shift_mod_g_div_mod3 hk d hsing v
          have hs1 : (ix hk (v.val + d)).val % g = v.val % g := hs.1
          have hs2 : (ix hk (v.val + d)).val / g % 3 = (v.val / g + d / g) % 3 := hs.2
          have hiff : (v.val % g = r.val ∧ v.val / g % 3 = c0) ↔
              ((ix hk (v.val + d)).val % g = r.val ∧
                (ix hk (v.val + d)).val / g % 3 = (c0 + d / g) % 3) := by
            rw [hs1, hs2]
            constructor
            · rintro ⟨hr, hc⟩; refine ⟨hr, ?_⟩; omega
            · rintro ⟨hr, hc⟩; refine ⟨hr, ?_⟩; omega
          by_cases hp : v.val % g = r.val ∧ v.val / g % 3 = c0
          · have hq := hiff.mp hp; simp only [hp, hq, ↓reduceIte]
          · have hq : ¬ ((ix hk (v.val + d)).val % g = r.val ∧
                (ix hk (v.val + d)).val / g % 3 = (c0 + d / g) % 3) := mt hiff.mpr hp
            simp only [hp, hq, ↓reduceIte]
        have hterm3 :
            (∑ v : Fin k, if v.val % g = r.val ∧ v.val / g % 3 = c0
              then z (ix hk (v.val + k - d % k)) else 0) =
            ∑ w : Fin k, if w.val % g = r.val ∧ w.val / g % 3 = (c0 + 3 - d / g) % 3
              then z w else 0 := by
          refine Fintype.sum_bijective (fun v => ix hk (v.val + k - d % k)) hbij_neg _ _ ?_
          intro v
          have hs := shift_neg_mod_g_div_mod3 hk d hsing v
          have hs1 : (ix hk (v.val + k - d % k)).val % g = v.val % g := hs.1
          have hs2 : ((ix hk (v.val + k - d % k)).val / g + d / g) % 3 = v.val / g % 3 := hs.2
          have hiff : (v.val % g = r.val ∧ v.val / g % 3 = c0) ↔
              ((ix hk (v.val + k - d % k)).val % g = r.val ∧
                (ix hk (v.val + k - d % k)).val / g % 3 = (c0 + 3 - d / g) % 3) := by
            rw [hs1]
            constructor
            · rintro ⟨hr, hc⟩; refine ⟨hr, ?_⟩; omega
            · rintro ⟨hr, hc⟩; refine ⟨hr, ?_⟩; omega
          by_cases hp : v.val % g = r.val ∧ v.val / g % 3 = c0
          · have hq := hiff.mp hp; simp only [hp, hq, ↓reduceIte]
          · have hq : ¬ ((ix hk (v.val + k - d % k)).val % g = r.val ∧
                (ix hk (v.val + k - d % k)).val / g % 3 = (c0 + 3 - d / g) % 3) := mt hiff.mpr hp
            simp only [hp, hq, ↓reduceIte]
        rw [hterm2, hterm3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        by_cases hwr : w.val % g = r.val
        · simp only [hwr, true_and, ↓reduceIte]
          have hmod3 : w.val / g % 3 = 0 ∨ w.val / g % 3 = 1 ∨ w.val / g % 3 = 2 := by omega
          have hne1 : c0 ≠ (c0 + d / g) % 3 := by omega
          have hne2 : c0 ≠ (c0 + 3 - d / g) % 3 := by omega
          have hne3 : (c0 + d / g) % 3 ≠ (c0 + 3 - d / g) % 3 := by omega
          have hex : w.val / g % 3 = c0 ∨ w.val / g % 3 = (c0 + d / g) % 3 ∨
              w.val / g % 3 = (c0 + 3 - d / g) % 3 := by omega
          rcases hex with ha | hb | hc
          · simp only [ha, hne1, hne2, ↓reduceIte, add_zero]
          · simp only [hb, hne1.symm, hne3, ↓reduceIte, zero_add, add_zero]
          · simp only [hc, hne2.symm, hne3.symm, ↓reduceIte, zero_add]
        · simp [hwr]
      have hsplit2 :
          (∑ v : Fin k, if v.val % g = r.val ∧ (v.val / g % 3 = c.val ∨ v.val / g % 3 = 2)
            then mixLin hk d z v else 0) =
          (∑ v : Fin k, if v.val % g = r.val ∧ v.val / g % 3 = c.val then mixLin hk d z v else 0) +
          (∑ v : Fin k, if v.val % g = r.val ∧ v.val / g % 3 = 2 then mixLin hk d z v else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        have hc2 : c.val ≠ 2 := by omega
        by_cases hr : v.val % g = r.val
        · by_cases h1 : v.val / g % 3 = c.val
          · simp only [hr, h1, hc2, true_and, true_or, ↓reduceIte, add_zero]
          · by_cases h2 : v.val / g % 3 = 2
            · simp only [hr, h2, hc2.symm, true_and, or_true, ↓reduceIte, zero_add]
            · simp only [hr, h1, h2, true_and, or_self, ↓reduceIte, add_zero]
        · simp [hr]
      rw [hsplit2, hsum_res c.val (by omega), hsum_res 2 (by omega), zmod2_add_self]
    · rfl
  have hfin_eq : Module.finrank (ZMod 2) (LinearMap.range (mixLin hk d)) =
      Module.finrank (ZMod 2) (LinearMap.ker (checkMap (k := k) d)) := by
    have hr_mix := LinearMap.finrank_range_add_finrank_ker (mixLin hk d)
    have hr_chk := LinearMap.finrank_range_add_finrank_ker (checkMap (k := k) d)
    have hdim_k : Module.finrank (ZMod 2) (Fin k → ZMod 2) = k := by simp
    rw [hdim_k, finrank_ker_mixLin hk d hd] at hr_mix
    rw [hdim_k] at hr_chk
    by_cases hsing : 3 ∣ k / g
    · have hsing' : 3 ∣ k / Nat.gcd k d := hsing
      have hsurj : Function.Surjective (checkMap (k := k) d) := by
        have hL_pos : 0 < k / g := Nat.div_pos (Nat.le_of_dvd hk hg_dvd_k) hg_pos
        have hL3 : 3 ≤ k / g := Nat.le_of_dvd hL_pos hsing
        intro target
        let y : Fin k → ZMod 2 := fun v =>
          if v.val / g = 0 then target (⟨v.val % g, Nat.mod_lt _ hg_pos⟩, 0)
          else if v.val / g = 1 then target (⟨v.val % g, Nat.mod_lt _ hg_pos⟩, 1)
          else 0
        refine ⟨y, ?_⟩
        ext ⟨r, c⟩
        have hr_lt : r.val < g := r.2
        have hc_lt : c.val < 2 := c.2
        simp only [checkMap, LinearMap.coe_mk, AddHom.coe_mk, hsing', ↓reduceIte]
        let v0 : Fin k := ⟨g * c.val + r.val, by
          have hc1 : c.val + 1 ≤ k / g := by omega
          calc
            g * c.val + r.val < g * c.val + g := Nat.add_lt_add_left hr_lt _
            _ = g * (c.val + 1) := by ring
            _ ≤ g * (k / g) := Nat.mul_le_mul_left g hc1
            _ = k := hk_eq⟩
        rw [Finset.sum_eq_single v0]
        · have hv0_mod : v0.val % g = r.val := by
            show (g * c.val + r.val) % g = r.val
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr_lt]
          have hv0_div : v0.val / g = c.val := by
            show (g * c.val + r.val) / g = c.val
            rw [Nat.mul_add_div hg_pos, Nat.div_eq_of_lt hr_lt, Nat.add_zero]
          have hv0_div3 : v0.val / g % 3 = c.val := by rw [hv0_div, Nat.mod_eq_of_lt (by omega)]
          have hcond0 : v0.val % Nat.gcd k d = r.val ∧
              (v0.val / Nat.gcd k d % 3 = c.val ∨ v0.val / Nat.gcd k d % 3 = 2) :=
            ⟨hv0_mod, Or.inl hv0_div3⟩
          rw [ite_eq_left_iff.mpr fun h => absurd hcond0 h]
          simp only [y, hv0_div]
          fin_cases c
          · simp only [↓reduceIte]
            exact congrArg target (Prod.ext (Fin.ext hv0_mod) rfl)
          · simp only [Nat.one_ne_zero, ↓reduceIte]
            exact congrArg target (Prod.ext (Fin.ext hv0_mod) rfl)
        · intro v _ hne
          split_ifs with hcond
          · have hvr : v.val % g = r.val := hcond.1
            have hvc : v.val / g % 3 = c.val ∨ v.val / g % 3 = 2 := hcond.2
            simp only [y]
            by_cases h0 : v.val / g = 0
            · exfalso
              have hc0 : c.val = 0 := by rw [h0] at hvc; omega
              apply hne
              ext
              have hdiv := Nat.div_add_mod v.val g
              show v.val = g * c.val + r.val
              rw [h0, hvr] at hdiv
              rw [hc0]
              omega
            · by_cases h1 : v.val / g = 1
              · exfalso
                have hc1 : c.val = 1 := by rw [h1] at hvc; omega
                apply hne
                ext
                have hdiv := Nat.div_add_mod v.val g
                show v.val = g * c.val + r.val
                rw [h1, hvr] at hdiv
                rw [hc1]
                omega
              · simp [h0, h1]
          · rfl
        · intro hmem; exact absurd (Finset.mem_univ v0) hmem
      have hrange : LinearMap.range (checkMap (k := k) d) = ⊤ :=
        LinearMap.range_eq_top.mpr hsurj
      rw [hrange, finrank_top] at hr_chk
      have hdim_cod : Module.finrank (ZMod 2) (Fin (Nat.gcd k d) × Fin 2 → ZMod 2) =
          2 * Nat.gcd k d := by
        simp [Nat.mul_comm]
      rw [hdim_cod] at hr_chk
      simp only [hsing', ↓reduceIte] at hr_mix
      omega
    · have hsing' : ¬ 3 ∣ k / Nat.gcd k d := hsing
      have hchk0 : checkMap (k := k) d = 0 := by
        apply LinearMap.ext; intro y; ext rc
        simp [checkMap, hsing']
      have hfr0 : Module.finrank (ZMod 2) (LinearMap.range (checkMap (k := k) d)) = 0 := by
        rw [hchk0]; simp
      rw [hfr0, zero_add] at hr_chk
      simp only [hsing', ↓reduceIte, add_zero] at hr_mix
      omega
  exact Submodule.eq_of_le_of_finrank_eq hle hfin_eq

lemma prod_affine_iff {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (U : Submodule (ZMod 2) W) (α β : W →ₗ[ZMod 2] ZMod 2) :
    (∃ (ell : W →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), ∀ x ∈ U, α x * β x = ell x + b) ↔
      (∀ x ∈ U, α x = 0) ∨ (∀ x ∈ U, β x = 0) ∨ (∀ x ∈ U, α x = β x) := by
  constructor
  · rintro ⟨ell, b, h⟩
    have hb0 : b = 0 := by
      have h0 := h 0 U.zero_mem
      simp only [map_zero, mul_zero, zero_add] at h0
      exact h0.symm
    subst hb0
    have hsym : ∀ x ∈ U, ∀ y ∈ U, α x * β y + α y * β x = 0 := by
      intro x hx y hy
      have hxy := h (x + y) (U.add_mem hx hy)
      have hx' := h x hx
      have hy' := h y hy
      simp only [add_zero, map_add] at hxy hx' hy'
      have hexp : (α x + α y) * (β x + β y) = α x * β x + α y * β y + (α x * β y + α y * β x) := by
        ring
      rw [hexp, hx', hy'] at hxy
      have h1 := congrArg (fun t => t + (ell x + ell y)) hxy
      have hz := zmod2_add_self (ell x + ell y)
      calc
        α x * β y + α y * β x
            = (ell x + ell y + (ell x + ell y)) + (α x * β y + α y * β x) := by
          rw [hz, zero_add]
        _ = ell x + ell y + (α x * β y + α y * β x) + (ell x + ell y) := by ring
        _ = ell x + ell y + (ell x + ell y) := h1
        _ = 0 := hz
    by_cases hα : ∀ x ∈ U, α x = 0
    · exact Or.inl hα
    · by_cases hβ : ∀ x ∈ U, β x = 0
      · exact Or.inr (Or.inl hβ)
      · right; right
        push Not at hα hβ
        rcases hα with ⟨x0, hx0, hα0⟩
        rcases hβ with ⟨y0, hy0, hβ0⟩
        have hα1 : α x0 = 1 := zmod2_eq_one_of_ne_zero hα0
        have hβ1 : β y0 = 1 := zmod2_eq_one_of_ne_zero hβ0
        intro x hx
        have h1 := hsym x hx x0 hx0
        have h2 := hsym x hx y0 hy0
        rw [hα1, one_mul] at h1
        rw [hβ1, mul_one] at h2
        by_cases hax : α x = 0
        · rw [hax, zero_mul, zero_add] at h1
          rw [hax, h1]
        · have hax1 : α x = 1 := zmod2_eq_one_of_ne_zero hax
          by_cases hbx : β x = 0
          · rw [hbx, mul_zero, add_zero] at h2
            exact absurd h2 hax
          · rw [hax1, zmod2_eq_one_of_ne_zero hbx]
  · rintro (hα | hβ | heq)
    · refine ⟨0, 0, fun x hx => ?_⟩
      simp [hα x hx]
    · refine ⟨0, 0, fun x hx => ?_⟩
      simp [hβ x hx]
    · refine ⟨α, 0, fun x hx => ?_⟩
      rw [heq x hx, zmod2_mul_self, add_zero]

lemma reach_symm {k : ℕ} (mark : Fin k → Bool) (hk : 0 < k) (S : Finset (Fin k)) :
    let next := fun v : Fin k => ix hk (v.val + 1)
    let edge := fun i j : Fin k => (mark i = true ∧ next i = j) ∨ (mark j = true ∧ next j = i)
    let step := fun l r : Fin k => l ∈ S ∧ r ∈ S ∧ edge l r
    ∀ u v : Fin k, Relation.ReflTransGen step u v → Relation.ReflTransGen step v u := by
  intro next edge step u v h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    have hcb : step _ _ := ⟨hbc.2.1, hbc.1, hbc.2.2.symm⟩
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hcb) ih

lemma unique_comp_min_of_mem {k : ℕ} (mark : Fin k → Bool) (hk : 0 < k) (S : Finset (Fin k)) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let next := fun v : Fin k => ix hk (v.val + 1)
    let edge := fun i j : Fin k => (mark i = true ∧ next i = j) ∨ (mark j = true ∧ next j = i)
    let step := fun l r : Fin k => l ∈ S ∧ r ∈ S ∧ edge l r
    let reach := Relation.ReflTransGen step
    let roots := S.filter (fun candidate => ∀ j ∈ S, reach candidate j → candidate.val ≤ j.val)
    ∀ v ∈ S, ∃! r : roots, reach r.val v := by
  intro next edge step reach roots v hv
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let C : Finset (Fin k) := S.filter (fun u => reach v u)
  have hC_ne : C.Nonempty := ⟨v, Finset.mem_filter.mpr ⟨hv, Relation.ReflTransGen.refl⟩⟩
  let r0 : Fin k := C.min' hC_ne
  have hr0_mem : r0 ∈ C := Finset.min'_mem C hC_ne
  have hr0_S : r0 ∈ S := (Finset.mem_filter.mp hr0_mem).1
  have hv_r0 : reach v r0 := (Finset.mem_filter.mp hr0_mem).2
  have hr0_v : reach r0 v := reach_symm mark hk S v r0 hv_r0
  have hr0_root : r0 ∈ roots := by
    refine Finset.mem_filter.mpr ⟨hr0_S, ?_⟩
    intro j hj hreach
    have hvj : reach v j := Relation.ReflTransGen.trans hv_r0 hreach
    have hjC : j ∈ C := Finset.mem_filter.mpr ⟨hj, hvj⟩
    exact Finset.min'_le C j hjC
  refine ⟨⟨r0, hr0_root⟩, hr0_v, ?_⟩
  rintro ⟨r1, hr1_root⟩ hr1_v
  have hr1_S : r1 ∈ S := (Finset.mem_filter.mp hr1_root).1
  have hr1_min : ∀ j ∈ S, reach r1 j → r1.val ≤ j.val := (Finset.mem_filter.mp hr1_root).2
  have hr0_min : ∀ j ∈ S, reach r0 j → r0.val ≤ j.val := (Finset.mem_filter.mp hr0_root).2
  have h10 : reach r1 r0 := Relation.ReflTransGen.trans hr1_v hv_r0
  have h01 : reach r0 r1 := reach_symm mark hk S r1 r0 h10
  have hle1 : r1.val ≤ r0.val := hr1_min r0 hr0_S h10
  have hle2 : r0.val ≤ r1.val := hr0_min r1 hr1_S h01
  exact Subtype.ext (Fin.ext (le_antisymm hle1 hle2))

lemma reach_roots_eq_iff {k : ℕ} (mark : Fin k → Bool) (hk : 0 < k) (S : Finset (Fin k)) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    let next := fun v : Fin k => ix hk (v.val + 1)
    let edge := fun i j : Fin k => (mark i = true ∧ next i = j) ∨ (mark j = true ∧ next j = i)
    let step := fun l r : Fin k => l ∈ S ∧ r ∈ S ∧ edge l r
    let reach := Relation.ReflTransGen step
    let roots := S.filter (fun candidate => ∀ j ∈ S, reach candidate j → candidate.val ≤ j.val)
    ∀ r1 r2 : roots, reach r1.val r2.val ↔ r1 = r2 := by
  intro next edge step reach roots r1 r2
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  constructor
  · intro h
    have hr1_S : r1.val ∈ S := (Finset.mem_filter.mp r1.2).1
    have hr2_S : r2.val ∈ S := (Finset.mem_filter.mp r2.2).1
    have hle1 : r1.val.val ≤ r2.val.val := (Finset.mem_filter.mp r1.2).2 r2.val hr2_S h
    have hle2 : r2.val.val ≤ r1.val.val :=
      (Finset.mem_filter.mp r2.2).2 r1.val hr1_S (reach_symm mark hk S r1.val r2.val h)
    exact Subtype.ext (Fin.ext (le_antisymm hle1 hle2))
  · rintro rfl
    exact Relation.ReflTransGen.refl

lemma finrank_map_eq_of_injective {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (Φ : V →ₗ[ZMod 2] W) (hΦ : Function.Injective Φ) (S : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (S.map Φ) = Module.finrank (ZMod 2) S := by
  let f : S →ₗ[ZMod 2] S.map Φ :=
    { toFun := fun x => ⟨Φ x.1, ⟨x.1, x.2, rfl⟩⟩
      map_add' := fun x y => by apply Subtype.ext; simp
      map_smul' := fun c x => by apply Subtype.ext; simp }
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      exact hΦ (congrArg Subtype.val h)
    · rintro ⟨y, ⟨x, hx, rfl⟩⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact (LinearEquiv.ofBijective f hbij).finrank_eq.symm

end PEqualNP.Outside.L_meta_25683_aux

open PEqualNP.Outside.L_meta_25683_aux in
theorem PEqualNP.Outside.L_meta_25683 :
    ∀ (k : ℕ) (hk : 0 < k) (column : Bool) (mark : Fin k → Bool),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let K := ZMod 2
  let W := Fin k → K
  let ix := fun pos : ℕ => (⟨pos % k, Nat.mod_lt _ hk⟩ : Fin k)
  let d := if column then 2 else 1
  let g := Nat.gcd k d
  let sing := 3 ∣ k/g
  let defect := if sing then 2*g else 0
  let next := fun vertex : Fin k => ix (vertex.val+1)
  let edge := fun i j : Fin k => (mark i = true ∧ next i = j) ∨ (mark j = true ∧ next j = i)
  let price := fun S : Finset (Fin k) =>
    let step := fun left right : Fin k => left ∈ S ∧ right ∈ S ∧ edge left right
    let reach := Relation.ReflTransGen step
    let roots := S.filter (fun candidate => ∀ j ∈ S, reach candidate j → candidate.val ≤ j.val)
    let checks : Matrix (Fin g × Fin 2) roots K := fun rc root =>
      if sing then ∑ v : Fin k,
        (if v ∈ S ∧ reach root.val v ∧ v.val % g = rc.1.val ∧
            (v.val/g%3 = rc.2.val ∨ v.val/g%3 = 2) then 1 else 0) else 0
    defect + roots.card - checks.rank
  let best := (Finset.univ : Finset (Finset (Fin k))).sup price
  let independent := (Finset.univ : Finset (Finset (Fin k))).filter
    (fun A => ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ¬ edge i j)
  let rot := fun (s : ℕ) (raw : W) (j : Fin k) => raw (ix (j.val+k-s%k))
  let run := fun (key name c : W) =>
    let z := rot (if column then 3 else 1) key + name
    let y := fun atMix : Fin k => z atMix + z (ix (atMix.val+d)) + z (ix (atMix.val+k-d%k))
    fun output : Fin k => y output + (1+y (ix (output.val+1))) * y (ix (output.val+2)) +
      rot (if column then 4 else 0) key output + c output
  let affineOn := fun (U : Submodule K W) (base name c : W) =>
    ∀ p : Fin k, mark p = true → ∃ (ell : W →ₗ[K] K) (b : K),
      ∀ x ∈ U, run (base+x) name c (ix (p.val+k-1)) = ell x + b
  (∀ (U : Submodule K W) (base name c : W), affineOn U base name c → Module.finrank K U ≤ best) ∧
  (∃ U : Submodule K W, Module.finrank K U = best ∧ ∀ base name c, affineOn U base name c) ∧
  (¬ sing → best = independent.sup Finset.card) := by
  intro k hk column mark
  let : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro K W ix0 d g sing defect next edge price best independent rot run affineOn
  have hix0 : ix0 = PEqualNP.Outside.L_meta_25683_aux.ix hk := rfl
  have hd12 : d = 1 ∨ d = 2 := by
    dsimp only [d]
    cases column
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
  have hd_pos : 0 < d := by
    rcases hd12 with h | h
    · rw [h]; exact Nat.zero_lt_one
    · rw [h]; exact Nat.zero_lt_two
  let s0 : ℕ := if column then 3 else 1
  let s1 : ℕ := if column then 4 else 0
  let M : W →ₗ[K] W := (mixLin hk d).comp (rotLin hk s0)
  have hM_ker : Module.finrank K (LinearMap.ker M) = defect := by
    have hrot_bij := rotLin_bijective hk s0
    let eR : W ≃ₗ[K] W := LinearEquiv.ofBijective (rotLin hk s0) hrot_bij
    let eK : LinearMap.ker M ≃ₗ[K] LinearMap.ker (mixLin hk d) :=
      { toFun := fun x => ⟨eR x.1, x.2⟩
        invFun := fun y => ⟨eR.symm y.1, by
          show mixLin hk d (eR (eR.symm y.1)) = 0
          rw [eR.apply_symm_apply]
          exact y.2⟩
        left_inv := fun x => by apply Subtype.ext; exact eR.symm_apply_apply x.1
        right_inv := fun y => by apply Subtype.ext; exact eR.apply_symm_apply y.1
        map_add' := fun x y => by apply Subtype.ext; simp
        map_smul' := fun c x => by apply Subtype.ext; simp }
    rw [eK.finrank_eq]
    convert finrank_ker_mixLin hk d hd_pos
  have hM_range : LinearMap.range M = LinearMap.ker (checkMap (k := k) d) := by
    have hrot_surj : Function.Surjective (rotLin hk s0) := (rotLin_bijective hk s0).2
    have h1 : LinearMap.range M = LinearMap.range (mixLin hk d) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨rotLin hk s0 x, rfl⟩
      · rintro ⟨z, rfl⟩
        rcases hrot_surj z with ⟨x, rfl⟩
        exact ⟨x, rfl⟩
    rw [h1]
    exact range_mixLin_eq_ker_checkMap hk d hd12
  have hrun_decomp : ∀ (base name c : W) (p : Fin k),
      ∃ (linPart : W →ₗ[K] K) (constPart : K),
        ∀ x : W, run (base + x) name c (ix0 (p.val + k - 1)) =
          M x p * M x (next p) + linPart x + constPart := by
    intro base name c p
    let out := ix0 (p.val + k - 1)
    have h1 : ix0 (out.val + 1) = p := ix_sub_add_one hk p
    have h2 : ix0 (out.val + 2) = next p := ix_sub_add_two hk p
    let y0 : W := fun m =>
      (rot s0 base + name) m + (rot s0 base + name) (ix0 (m.val + d)) +
        (rot s0 base + name) (ix0 (m.val + k - d % k))
    have hy_split : ∀ (x : W) (m : Fin k),
        (rot s0 (base + x) + name) m + (rot s0 (base + x) + name) (ix0 (m.val + d)) +
          (rot s0 (base + x) + name) (ix0 (m.val + k - d % k)) = M x m + y0 m := by
      intro x m
      simp only [M, LinearMap.comp_apply, mixLin, rotLin, LinearMap.coe_mk, AddHom.coe_mk,
        y0, rot, hix0]
      dsimp only [W]
      simp only [Pi.add_apply]
      ring
    let linPart : W →ₗ[K] K :=
      { toFun := fun x =>
          M x out + (1 + y0 p) * M x (next p) + y0 (next p) * M x p + rot s1 x out
        map_add' := fun x1 x2 => by
          simp only [map_add, rot]
          dsimp only [W]
          simp only [Pi.add_apply]
          ring
        map_smul' := fun a x => by
          simp only [map_smul, rot]
          dsimp only [W]
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          ring }
    let constPart : K :=
      y0 out + (1 + y0 p) * y0 (next p) + rot s1 base out + c out
    refine ⟨linPart, constPart, fun x => ?_⟩
    show (let z := rot s0 (base + x) + name
      let y := fun atMix : Fin k => z atMix + z (ix0 (atMix.val + d)) + z (ix0 (atMix.val + k - d % k))
      y out + (1 + y (ix0 (out.val + 1))) * y (ix0 (out.val + 2)) + rot s1 (base + x) out + c out) =
      M x p * M x (next p) + linPart x + constPart
    dsimp only
    rw [h1, h2, hy_split x out, hy_split x p, hy_split x (next p)]
    have hrot_add : rot s1 (base + x) out = rot s1 base out + rot s1 x out := by
      simp only [rot]; dsimp only [W]; simp only [Pi.add_apply]
    rw [hrot_add]
    simp only [linPart, LinearMap.coe_mk, AddHom.coe_mk, constPart]
    ring
  have haffine_iff : ∀ (U : Submodule K W) (base name c : W),
      affineOn U base name c ↔
        ∀ p : Fin k, mark p = true →
          (∀ x ∈ U, M x p = 0) ∨ (∀ x ∈ U, M x (next p) = 0) ∨ (∀ x ∈ U, M x p = M x (next p)) := by
    intro U base name c
    constructor
    · intro haff p hmp
      rcases haff p hmp with ⟨ell, b, hell⟩
      rcases hrun_decomp base name c p with ⟨linPart, constPart, hdec⟩
      let α : W →ₗ[K] K := (LinearMap.proj p).comp M
      let β : W →ₗ[K] K := (LinearMap.proj (next p)).comp M
      have hprod : ∃ (ell' : W →ₗ[K] K) (b' : K), ∀ x ∈ U, α x * β x = ell' x + b' := by
        refine ⟨ell + linPart, b + constPart, fun x hx => ?_⟩
        have h1 := hell x hx
        have h2 := hdec x
        rw [h2] at h1
        simp only [α, β, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.add_apply]
        have h3 := congrArg (fun t => t + linPart x + constPart) h1
        have hz1 := zmod2_add_self (linPart x)
        have hz2 := zmod2_add_self constPart
        calc
          M x p * M x (next p)
              = M x p * M x (next p) + (linPart x + linPart x) + (constPart + constPart) := by
            rw [hz1, hz2, add_zero, add_zero]
          _ = M x p * M x (next p) + linPart x + constPart + linPart x + constPart := by ring
          _ = ell x + b + linPart x + constPart := h3
          _ = ell x + linPart x + (b + constPart) := by ring
      exact (prod_affine_iff U α β).mp hprod
    · intro hcond p hmp
      rcases hrun_decomp base name c p with ⟨linPart, constPart, hdec⟩
      let α : W →ₗ[K] K := (LinearMap.proj p).comp M
      let β : W →ₗ[K] K := (LinearMap.proj (next p)).comp M
      have hprod : ∃ (ell' : W →ₗ[K] K) (b' : K), ∀ x ∈ U, α x * β x = ell' x + b' :=
        (prod_affine_iff U α β).mpr (hcond p hmp)
      rcases hprod with ⟨ell', b', hpb⟩
      refine ⟨ell' + linPart, b' + constPart, fun x hx => ?_⟩
      rw [hdec x]
      have h1 := hpb x hx
      simp only [α, β, LinearMap.comp_apply, LinearMap.proj_apply] at h1
      rw [h1]
      simp only [LinearMap.add_apply]
      ring
  have hcomp_props : ∀ S : Finset (Fin k),
      let step := fun left right : Fin k => left ∈ S ∧ right ∈ S ∧ edge left right
      let reach := Relation.ReflTransGen step
      let roots := S.filter (fun candidate => ∀ j ∈ S, reach candidate j → candidate.val ≤ j.val)
      let checks : Matrix (Fin g × Fin 2) roots K := fun rc root =>
        if sing then ∑ v : Fin k,
          (if v ∈ S ∧ reach root.val v ∧ v.val % g = rc.1.val ∧
              (v.val / g % 3 = rc.2.val ∨ v.val / g % 3 = 2) then 1 else 0) else 0
      let Φ : (roots → K) →ₗ[K] W :=
        { toFun := fun f v => ∑ r : roots, if v ∈ S ∧ reach r.val v then f r else 0
          map_add' := fun f1 f2 => by
            ext v; dsimp only [W]; simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun r _ => ?_; split_ifs <;> simp
          map_smul' := fun c f => by
            ext v; dsimp only [W]; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => ?_; split_ifs <;> simp }
      Function.Injective Φ ∧
      (∀ f : roots → K, Φ f ∈ LinearMap.ker (checkMap (k := k) d) ↔
        f ∈ LinearMap.ker checks.mulVecLin) ∧
      (∀ f : roots → K, ∀ v : Fin k, v ∉ S → Φ f v = 0) ∧
      (∀ f : roots → K, ∀ u v : Fin k, u ∈ S → v ∈ S → edge u v → Φ f u = Φ f v) ∧
      (∀ y : W, (∀ v : Fin k, v ∉ S → y v = 0) →
        (∀ u v : Fin k, u ∈ S → v ∈ S → edge u v → y u = y v) →
        y ∈ LinearMap.range Φ) := by
    intro S step reach roots checks Φ
    have hΦ_root : ∀ (f : roots → K) (r : roots), Φ f r.val = f r := by
      intro f r
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
      have hrS : r.val ∈ S := (Finset.mem_filter.mp r.2).1
      have hrefl : reach r.val r.val := Relation.ReflTransGen.refl
      rw [Finset.sum_eq_single r]
      · simp only [hrS, hrefl, and_self, ↓reduceIte]
      · intro r' _ hne
        have hnr : ¬ reach r'.val r.val := fun hr =>
          hne ((reach_roots_eq_iff mark hk S r' r).mp hr)
        simp [hnr]
      · intro hmem; exact absurd (Finset.mem_univ r) hmem
    have hΦ_inj : Function.Injective Φ := by
      intro f1 f2 heq
      ext r
      have := congrFun heq r.val
      rw [hΦ_root, hΦ_root] at this
      exact this
    have hΦ_ker : ∀ f : roots → K, Φ f ∈ LinearMap.ker (checkMap (k := k) d) ↔
        f ∈ LinearMap.ker checks.mulVecLin := by
      intro f
      have hcomm : checkMap (k := k) d (Φ f) = checks.mulVecLin f := by
        ext rc
        rw [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
        simp only [checkMap, Φ, checks, LinearMap.coe_mk, AddHom.coe_mk]
        split_ifs with hsing
        · have h1 : (∑ v : Fin k,
              if v.val % g = rc.1.val ∧ (v.val / g % 3 = rc.2.val ∨ v.val / g % 3 = 2)
              then ∑ r : roots, if v ∈ S ∧ reach r.val v then f r else 0 else 0) =
            ∑ v : Fin k, ∑ r : roots,
              if v ∈ S ∧ reach r.val v ∧ v.val % g = rc.1.val ∧
                (v.val / g % 3 = rc.2.val ∨ v.val / g % 3 = 2) then f r else 0 := by
            refine Finset.sum_congr rfl fun v _ => ?_
            by_cases hrc : v.val % g = rc.1.val ∧ (v.val / g % 3 = rc.2.val ∨ v.val / g % 3 = 2)
            · simp only [hrc, ↓reduceIte, and_true]
            · simp only [hrc, ↓reduceIte, and_false, Finset.sum_const_zero]
          rw [h1, Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun v _ => ?_
          split_ifs <;> simp
        · simp
      constructor
      · intro h; show checks.mulVecLin f = 0; rw [← hcomm]; exact h
      · intro h; show checkMap (k := k) d (Φ f) = 0; rw [hcomm]; exact h
    have hΦ_zero : ∀ f : roots → K, ∀ v : Fin k, v ∉ S → Φ f v = 0 := by
      intro f v hv
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
      exact Finset.sum_eq_zero fun r _ => by simp [hv]
    have hΦ_edge : ∀ f : roots → K, ∀ u v : Fin k, u ∈ S → v ∈ S → edge u v → Φ f u = Φ f v := by
      intro f u v hu hv hedge
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
      refine Finset.sum_congr rfl fun r _ => ?_
      have hst1 : step u v := ⟨hu, hv, hedge⟩
      have hst2 : step v u := ⟨hv, hu, hedge.symm⟩
      have hiff : reach r.val u ↔ reach r.val v :=
        ⟨fun h => Relation.ReflTransGen.tail h hst1, fun h => Relation.ReflTransGen.tail h hst2⟩
      by_cases hr : reach r.val u
      · have hr' := hiff.mp hr; simp only [hu, hv, hr, hr', and_self, ↓reduceIte]
      · have hr' : ¬ reach r.val v := mt hiff.mpr hr; simp only [hr, hr', and_false, ↓reduceIte]
    have hΦ_range : ∀ y : W, (∀ v : Fin k, v ∉ S → y v = 0) →
        (∀ u v : Fin k, u ∈ S → v ∈ S → edge u v → y u = y v) →
        y ∈ LinearMap.range Φ := by
      intro y hy0 hyedge
      have hy_reach : ∀ u v : Fin k, reach u v → y u = y v := by
        intro u v hr
        induction hr with
        | refl => rfl
        | tail _ hst ih => exact ih.trans (hyedge _ _ hst.1 hst.2.1 hst.2.2)
      refine ⟨fun r => y r.val, ?_⟩
      ext v
      by_cases hv : v ∈ S
      · have huniq_all : ∀ u ∈ S, ∃! r : roots, reach r.val u := unique_comp_min_of_mem mark hk S
        rcases huniq_all v hv with ⟨r0, hr0, huniq⟩
        simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_eq_single r0]
        · simp only [hv, hr0, and_self, ↓reduceIte]
          exact hy_reach r0.val v hr0
        · intro r' _ hne
          have hnr : ¬ reach r'.val v := fun hr => hne (huniq r' hr)
          simp [hnr]
        · intro hmem; exact absurd (Finset.mem_univ r0) hmem
      · rw [hΦ_zero _ v hv, hy0 v hv]
    exact ⟨hΦ_inj, hΦ_ker, hΦ_zero, hΦ_edge, hΦ_range⟩
  have hupper : ∀ (U : Submodule K W) (base name c : W),
      affineOn U base name c → Module.finrank K U ≤ best := by
    intro U base name c haff
    have hcond := (haffine_iff U base name c).mp haff
    let V : Submodule K W := U.map M
    let S : Finset (Fin k) := Finset.univ.filter (fun v => ∃ y ∈ V, y v ≠ 0)
    have hU_le : Module.finrank K U ≤ defect + Module.finrank K V := by
      have hr := LinearMap.finrank_range_add_finrank_ker (M.domRestrict U)
      have hrange : LinearMap.range (M.domRestrict U) = V := by
        ext y
        constructor
        · rintro ⟨⟨x, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
      let ι : LinearMap.ker (M.domRestrict U) →ₗ[K] LinearMap.ker M :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hι_inj : Function.Injective ι := by
        intro x y h
        have hv : x.1.1 = y.1.1 := by simpa [ι] using congrArg Subtype.val h
        exact Subtype.ext (Subtype.ext hv)
      have hker_le : Module.finrank K (LinearMap.ker (M.domRestrict U)) ≤ defect := by
        rw [← hM_ker]
        exact LinearMap.finrank_le_finrank_of_injective hι_inj
      rw [hrange] at hr
      rw [← hr, Nat.add_comm]
      exact Nat.add_le_add_right hker_le _
    let step := fun left right : Fin k => left ∈ S ∧ right ∈ S ∧ edge left right
    let reach := Relation.ReflTransGen step
    let roots := S.filter (fun candidate => ∀ j ∈ S, reach candidate j → candidate.val ≤ j.val)
    let checks : Matrix (Fin g × Fin 2) roots K := fun rc root =>
      if sing then ∑ v : Fin k,
        (if v ∈ S ∧ reach root.val v ∧ v.val % g = rc.1.val ∧
            (v.val / g % 3 = rc.2.val ∨ v.val / g % 3 = 2) then 1 else 0) else 0
    let Φ : (roots → K) →ₗ[K] W :=
      { toFun := fun f v => ∑ r : roots, if v ∈ S ∧ reach r.val v then f r else 0
        map_add' := fun f1 f2 => by
          ext v; dsimp only [W]; simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_; split_ifs <;> simp
        map_smul' := fun c f => by
          ext v; dsimp only [W]; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_; split_ifs <;> simp }
    rcases hcomp_props S with ⟨hΦ_inj, hΦ_ker, _, _, hΦ_range⟩
    have hV_le : V ≤ (LinearMap.ker checks.mulVecLin).map Φ := by
      intro y hyV
      have hy0 : ∀ v : Fin k, v ∉ S → y v = 0 := by
        intro v hv
        by_contra hne
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, ⟨y, hyV, hne⟩⟩)
      have hyedge : ∀ u v : Fin k, u ∈ S → v ∈ S → edge u v → y u = y v := by
        intro u v hu hv hedge
        have hdir : ∀ p : Fin k, mark p = true → p ∈ S → next p ∈ S → y p = y (next p) := by
          intro p hmp hpS hnpS
          rcases hcond p hmp with h0 | h1 | heq
          · exfalso
            rcases (Finset.mem_filter.mp hpS).2 with ⟨y', ⟨x', hx', rfl⟩, hne⟩
            exact hne (h0 x' hx')
          · exfalso
            rcases (Finset.mem_filter.mp hnpS).2 with ⟨y', ⟨x', hx', rfl⟩, hne⟩
            exact hne (h1 x' hx')
          · rcases hyV with ⟨x, hx, rfl⟩
            exact heq x hx
        rcases hedge with ⟨hmu, rfl⟩ | ⟨hmv, rfl⟩
        · exact hdir u hmu hu hv
        · exact (hdir v hmv hv hu).symm
      rcases hΦ_range y hy0 hyedge with ⟨f, rfl⟩
      have hfC : Φ f ∈ LinearMap.ker (checkMap (k := k) d) := by
        rw [← hM_range]
        rcases hyV with ⟨x, _, hx⟩
        exact ⟨x, hx⟩
      exact ⟨f, (hΦ_ker f).mp hfC, rfl⟩
    have hrc := LinearMap.finrank_range_add_finrank_ker checks.mulVecLin
    have hdim_roots : Module.finrank K (roots → K) = roots.card := by simp
    rw [hdim_roots] at hrc
    have hchk_le : checks.rank ≤ roots.card := by
      change Module.finrank K (LinearMap.range checks.mulVecLin) ≤ roots.card
      exact le_trans (Nat.le_add_right _ _) (le_of_eq hrc)
    have hker_eq : Module.finrank K (LinearMap.ker checks.mulVecLin) = roots.card - checks.rank := by
      change Module.finrank K (LinearMap.ker checks.mulVecLin) =
        roots.card - Module.finrank K (LinearMap.range checks.mulVecLin)
      exact Nat.eq_sub_of_add_eq' hrc
    have hV_fin : Module.finrank K V ≤ roots.card - checks.rank := by
      have h1 : Module.finrank K V ≤
          Module.finrank K ((LinearMap.ker checks.mulVecLin).map Φ) :=
        Submodule.finrank_mono hV_le
      have h2 : Module.finrank K ((LinearMap.ker checks.mulVecLin).map Φ) =
          Module.finrank K (LinearMap.ker checks.mulVecLin) :=
        finrank_map_eq_of_injective Φ hΦ_inj _
      rw [h2, hker_eq] at h1
      exact h1
    have hprice_le : price S ≤ best := Finset.le_sup (f := price) (Finset.mem_univ S)
    have hprice_eq : price S = defect + roots.card - checks.rank := rfl
    have hadd_sub : defect + (roots.card - checks.rank) = defect + roots.card - checks.rank :=
      (Nat.add_sub_assoc hchk_le defect).symm
    exact le_trans (le_trans hU_le (Nat.add_le_add_left hV_fin defect))
      (by rw [hadd_sub, ← hprice_eq]; exact hprice_le)
  have hexists : ∃ U : Submodule K W, Module.finrank K U = best ∧
      ∀ base name c, affineOn U base name c := by
    have huniv_ne : (Finset.univ : Finset (Finset (Fin k))).Nonempty := ⟨∅, Finset.mem_univ _⟩
    rcases Finset.exists_mem_eq_sup Finset.univ huniv_ne price with ⟨S, _, hS_best⟩
    let step := fun left right : Fin k => left ∈ S ∧ right ∈ S ∧ edge left right
    let reach := Relation.ReflTransGen step
    let roots := S.filter (fun candidate => ∀ j ∈ S, reach candidate j → candidate.val ≤ j.val)
    let checks : Matrix (Fin g × Fin 2) roots K := fun rc root =>
      if sing then ∑ v : Fin k,
        (if v ∈ S ∧ reach root.val v ∧ v.val % g = rc.1.val ∧
            (v.val / g % 3 = rc.2.val ∨ v.val / g % 3 = 2) then 1 else 0) else 0
    let Φ : (roots → K) →ₗ[K] W :=
      { toFun := fun f v => ∑ r : roots, if v ∈ S ∧ reach r.val v then f r else 0
        map_add' := fun f1 f2 => by
          ext v; dsimp only [W]; simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_; split_ifs <;> simp
        map_smul' := fun c f => by
          ext v; dsimp only [W]; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_; split_ifs <;> simp }
    rcases hcomp_props S with ⟨hΦ_inj, hΦ_ker, hΦ_zero, hΦ_edge, _⟩
    let V : Submodule K W := (LinearMap.ker checks.mulVecLin).map Φ
    let U : Submodule K W := V.comap M
    have hV_sub_range : V ≤ LinearMap.range M := by
      rintro y ⟨f, hf, rfl⟩
      rw [hM_range]
      exact (hΦ_ker f).mpr hf
    have hU_fin : Module.finrank K U = best := by
      have hr := LinearMap.finrank_range_add_finrank_ker (M.domRestrict U)
      have hrange : LinearMap.range (M.domRestrict U) = V := by
        ext y
        constructor
        · rintro ⟨⟨x, hx⟩, rfl⟩; exact hx
        · intro hy
          rcases hV_sub_range hy with ⟨x, rfl⟩
          exact ⟨⟨x, hy⟩, rfl⟩
      let eK : LinearMap.ker (M.domRestrict U) ≃ₗ[K] LinearMap.ker M :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun y => ⟨⟨y.1, by
            show M y.1 ∈ V
            have h0 : M y.1 = 0 := y.2
            rw [h0]
            exact V.zero_mem⟩, y.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hker : Module.finrank K (LinearMap.ker (M.domRestrict U)) = defect := by
        rw [eK.finrank_eq, hM_ker]
      have hrc := LinearMap.finrank_range_add_finrank_ker checks.mulVecLin
      have hdim_roots : Module.finrank K (roots → K) = roots.card := by simp
      rw [hdim_roots] at hrc
      have hchk_le : checks.rank ≤ roots.card := by
        change Module.finrank K (LinearMap.range checks.mulVecLin) ≤ roots.card
        exact le_trans (Nat.le_add_right _ _) (le_of_eq hrc)
      have hV_dim : Module.finrank K V = roots.card - checks.rank := by
        have h1 : Module.finrank K V = Module.finrank K (LinearMap.ker checks.mulVecLin) :=
          finrank_map_eq_of_injective Φ hΦ_inj _
        rw [h1]
        change Module.finrank K (LinearMap.ker checks.mulVecLin) =
          roots.card - Module.finrank K (LinearMap.range checks.mulVecLin)
        exact Nat.eq_sub_of_add_eq' hrc
      rw [hrange, hker, hV_dim] at hr
      have hbest_eq : best = defect + roots.card - checks.rank := hS_best
      rw [hbest_eq, ← hr, Nat.add_comm, Nat.add_sub_assoc hchk_le defect]
    refine ⟨U, hU_fin, fun base name c => ?_⟩
    rw [haffine_iff U base name c]
    intro p hmp
    by_cases hp : p ∈ S
    · by_cases hnp : next p ∈ S
      · right; right
        intro x hx
        rcases hx with ⟨f, _, hf⟩
        rw [← hf]
        exact hΦ_edge f p (next p) hp hnp (Or.inl ⟨hmp, rfl⟩)
      · right; left
        intro x hx
        rcases hx with ⟨f, _, hf⟩
        rw [← hf]
        exact hΦ_zero f (next p) hnp
    · left
      intro x hx
      rcases hx with ⟨f, _, hf⟩
      rw [← hf]
      exact hΦ_zero f p hp
  have hnotsing : ¬ sing → best = independent.sup Finset.card := by
    intro hns
    have hprice_ns : ∀ S : Finset (Fin k),
        price S = (S.filter (fun candidate => ∀ j ∈ S,
          Relation.ReflTransGen (fun left right => left ∈ S ∧ right ∈ S ∧ edge left right)
            candidate j → candidate.val ≤ j.val)).card := by
      intro S
      let step := fun left right : Fin k => left ∈ S ∧ right ∈ S ∧ edge left right
      let reach := Relation.ReflTransGen step
      let roots := S.filter (fun candidate => ∀ j ∈ S, reach candidate j → candidate.val ≤ j.val)
      let checks : Matrix (Fin g × Fin 2) roots K := fun rc root =>
        if sing then ∑ v : Fin k,
          (if v ∈ S ∧ reach root.val v ∧ v.val % g = rc.1.val ∧
              (v.val / g % 3 = rc.2.val ∨ v.val / g % 3 = 2) then 1 else 0) else 0
      change defect + roots.card - checks.rank = roots.card
      have hdef0 : defect = 0 := by simp [defect, hns]
      have hchk_eq : checks = 0 := by
        ext rc root
        simp only [checks, hns, ↓reduceIte, Matrix.zero_apply]
      have hrank0 : checks.rank = 0 := by
        rw [hchk_eq]
        have h0 : LinearMap.range (0 : Matrix (Fin g × Fin 2) roots K).mulVecLin = ⊥ := by
          ext y; simp
        change Module.finrank K _ = 0
        rw [h0]; simp
      rw [hrank0, hdef0, zero_add, Nat.sub_zero]
    apply le_antisymm
    · refine Finset.sup_le fun S _ => ?_
      rw [hprice_ns S]
      let roots := S.filter (fun candidate => ∀ j ∈ S,
        Relation.ReflTransGen (fun left right => left ∈ S ∧ right ∈ S ∧ edge left right)
          candidate j → candidate.val ≤ j.val)
      have hroots_ind : roots ∈ independent := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ roots, ?_⟩
        intro i hi j hj hne hedge
        have hiS : i ∈ S := (Finset.mem_filter.mp hi).1
        have hjS : j ∈ S := (Finset.mem_filter.mp hj).1
        have hst1 : i ∈ S ∧ j ∈ S ∧ edge i j := ⟨hiS, hjS, hedge⟩
        have hst2 : j ∈ S ∧ i ∈ S ∧ edge j i := ⟨hjS, hiS, hedge.symm⟩
        have hle1 : i.val ≤ j.val :=
          (Finset.mem_filter.mp hi).2 j hjS (Relation.ReflTransGen.single hst1)
        have hle2 : j.val ≤ i.val :=
          (Finset.mem_filter.mp hj).2 i hiS (Relation.ReflTransGen.single hst2)
        exact hne (Fin.ext (le_antisymm hle1 hle2))
      exact Finset.le_sup (f := Finset.card) hroots_ind
    · refine Finset.sup_le fun A hA => ?_
      have hA_ind := (Finset.mem_filter.mp hA).2
      have hroots_eq : (A.filter (fun candidate => ∀ j ∈ A,
          Relation.ReflTransGen (fun left right => left ∈ A ∧ right ∈ A ∧ edge left right)
            candidate j → candidate.val ≤ j.val)) = A := by
        ext i
        simp only [Finset.mem_filter, and_iff_left_iff_imp]
        intro hi j hj hreach
        have heq : i = j := by
          induction hreach with
          | refl => rfl
          | tail _ hst ih =>
            have hib : i = _ := ih hst.1
            rw [hib]
            by_contra hne
            exact hA_ind _ hst.1 _ hst.2.1 hne hst.2.2
        subst heq
        exact le_rfl
      have hpA : price A = A.card := by
        rw [hprice_ns A, hroots_eq]
      rw [← hpA]
      exact Finset.le_sup (f := price) (Finset.mem_univ A)
  exact ⟨hupper, hexists, hnotsing⟩
