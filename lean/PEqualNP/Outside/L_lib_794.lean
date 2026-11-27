import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_794_aux

abbrev F := ZMod 2

lemma zmod2_add_self (a : F) : a + a = 0 := by
  fin_cases a <;> rfl

lemma zmod2_three (a : F) : a + a + a = a := by
  fin_cases a <;> rfl

lemma zmod2_eq_of_add_eq_zero {a b : F} (h : a + b = 0) : a = b := by
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)

def ix (k : ℕ) (hk : 0 < k) (j : ℕ) : Fin k :=
  ⟨j % k, Nat.mod_lt j hk⟩

lemma ix_add_k_sub_one (k : ℕ) (hk : 0 < k) (j : ℕ) :
    ix k hk (j + k - 1) = ix k hk ((ix k hk j).val + k - 1) := by
  apply Fin.ext
  dsimp [ix]
  have h1 : j + k - 1 = (j % k + k - 1) + k * (j / k) := by
    have hdiv := Nat.div_add_mod j k
    omega
  rw [h1, Nat.add_mul_mod_self_left]

lemma ix_add_one (k : ℕ) (hk : 0 < k) (j : ℕ) :
    ix k hk (j + 1) = ix k hk ((ix k hk j).val + 1) := by
  apply Fin.ext
  dsimp [ix]
  exact (Nat.mod_add_mod j k 1).symm

def mixMap (k : ℕ) (hk : 0 < k) : (Fin k → F) →ₗ[F] (Fin k → F) where
  toFun x i := x (ix k hk (i.val + k - 1)) + x i + x (ix k hk (i.val + 1))
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def stripMap (k L : ℕ) (hk : 0 < k) (start : ℕ) : (Fin k → F) →ₗ[F] (Fin L → F) where
  toFun z i := z (ix k hk (start + i.val))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def viewMap (k L : ℕ) (hk : 0 < k) (start : ℕ) : (Fin k → F) →ₗ[F] (Fin L → F) :=
  (stripMap k L hk start).comp (mixMap k hk)

lemma viewMap_apply (k L : ℕ) (hk : 0 < k) (start : ℕ) (x : Fin k → F) (i : Fin L) :
    viewMap k L hk start x i =
      x (ix k hk (start + i.val + k - 1)) + x (ix k hk (start + i.val)) +
        x (ix k hk (start + i.val + 1)) := by
  simp only [viewMap, LinearMap.comp_apply, stripMap, mixMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← ix_add_k_sub_one k hk (start + i.val), ← ix_add_one k hk (start + i.val)]

lemma ker_mixMap_period3 (k : ℕ) (hk : 0 < k) (x : Fin k → F) (hx : mixMap k hk x = 0) :
    ∀ n : ℕ, x (ix k hk (n + 3)) = x (ix k hk n) := by
  have hstep : ∀ m : ℕ, x (ix k hk m) + x (ix k hk (m + 1)) + x (ix k hk (m + 2)) = 0 := by
    intro m
    have hm := congrFun hx (ix k hk (m + 1))
    simp only [mixMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hm
    rw [← ix_add_k_sub_one k hk (m + 1), ← ix_add_one k hk (m + 1)] at hm
    have h1 : ix k hk (m + 1 + k - 1) = ix k hk m := by
      apply Fin.ext
      dsimp [ix]
      have : m + 1 + k - 1 = m + k := by omega
      rw [this, Nat.add_mod_right]
    rw [h1] at hm
    exact hm
  intro n
  have h1 := hstep n
  have h2 := hstep (n + 1)
  have h3 : x (ix k hk n) + x (ix k hk (n + 3)) = 0 := by
    calc x (ix k hk n) + x (ix k hk (n + 3))
        = (x (ix k hk n) + x (ix k hk (n + 1)) + x (ix k hk (n + 2))) +
            (x (ix k hk (n + 1)) + x (ix k hk (n + 2)) + x (ix k hk (n + 3))) -
            (x (ix k hk (n + 1)) + x (ix k hk (n + 1))) -
            (x (ix k hk (n + 2)) + x (ix k hk (n + 2))) := by ring
      _ = 0 + 0 - 0 - 0 := by
          rw [h1, h2, zmod2_add_self (x (ix k hk (n + 1))), zmod2_add_self (x (ix k hk (n + 2)))]
      _ = 0 := by ring
  exact (zmod2_eq_of_add_eq_zero h3).symm

lemma mixMap_surjective_of_not_dvd (k : ℕ) (hk : 0 < k) (h3 : k % 3 ≠ 0) :
    Function.Surjective (mixMap k hk) := by
  rw [← LinearMap.range_eq_top]
  have hker : LinearMap.ker (mixMap k hk) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hper : ∀ m n : ℕ, x (ix k hk (n + 3 * m)) = x (ix k hk n) := by
      intro m
      induction m with
      | zero => intro n; simp
      | succ m ih =>
        intro n
        have : n + 3 * (m + 1) = (n + 3 * m) + 3 := by omega
        rw [this, ker_mixMap_period3 k hk x hx, ih]
    have hconst : ∀ n : ℕ, x (ix k hk (n + 1)) = x (ix k hk n) := by
      intro n
      have hmod : k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hmod with hm1 | hm2
      · have h1 : n + 1 + 3 * (k / 3) = n + k := by omega
        have h2 := hper (k / 3) (n + 1)
        rw [h1] at h2
        have h3' : ix k hk (n + k) = ix k hk n := by
          apply Fin.ext; dsimp [ix]; exact Nat.add_mod_right n k
        rw [h3'] at h2
        exact h2.symm
      · have h1 : n + 3 * (k / 3 + 1) = n + 1 + k := by omega
        have h2 := hper (k / 3 + 1) n
        rw [h1] at h2
        have h3' : ix k hk (n + 1 + k) = ix k hk (n + 1) := by
          apply Fin.ext; dsimp [ix]; exact Nat.add_mod_right (n + 1) k
        rw [h3'] at h2
        exact h2
    have hall : ∀ n : ℕ, x (ix k hk n) = x (ix k hk 0) := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [hconst n, ih]
    have h0 := congrFun hx (ix k hk 0)
    simp only [mixMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
    rw [← ix_add_k_sub_one k hk 0, ← ix_add_one k hk 0, hall (0 + k - 1), hall (0 + 1),
      zmod2_three] at h0
    funext i
    have hi : i = ix k hk i.val := by apply Fin.ext; dsimp [ix]; exact (Nat.mod_eq_of_lt i.isLt).symm
    rw [hi, hall i.val, h0]
    rfl
  have hrk := LinearMap.finrank_range_add_finrank_ker (mixMap k hk)
  rw [hker, finrank_bot, add_zero] at hrk
  exact Submodule.eq_top_of_finrank_eq hrk

def psi0 (k : ℕ) : (Fin k → F) →ₗ[F] F where
  toFun y := ∑ i : Fin k, if i.val % 3 ≠ 1 then y i else 0
  map_add' x y := by
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp

def psi1 (k : ℕ) : (Fin k → F) →ₗ[F] F where
  toFun y := ∑ i : Fin k, if i.val % 3 ≠ 0 then y i else 0
  map_add' x y := by
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp

lemma psi0_single (k : ℕ) (p : Fin k) :
    psi0 k (Pi.single p 1) = if p.val % 3 ≠ 1 then 1 else 0 := by
  simp only [psi0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single p]
  · simp [Pi.single_apply]
  · intro i _ hne
    simp [Pi.single_apply, hne]
  · intro h; exact absurd (Finset.mem_univ p) h

lemma psi1_single (k : ℕ) (p : Fin k) :
    psi1 k (Pi.single p 1) = if p.val % 3 ≠ 0 then 1 else 0 := by
  simp only [psi1, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single p]
  · simp [Pi.single_apply]
  · intro i _ hne
    simp [Pi.single_apply, hne]
  · intro h; exact absurd (Finset.mem_univ p) h

def psiPair (k : ℕ) : (Fin k → F) →ₗ[F] (F × F) :=
  (psi0 k).prod (psi1 k)

lemma psiPair_comp_mixMap (k : ℕ) (hk : 0 < k) (h3 : k % 3 = 0) (x : Fin k → F) :
    psiPair k (mixMap k hk x) = 0 := by
  have hge3 : 3 ≤ k := by omega
  have hmod3 : ∀ m : ℕ, (ix k hk m).val % 3 = m % 3 := by
    intro m
    dsimp [ix]
    have hdiv := Nat.div_add_mod m k
    have h3k : 3 ∣ k := Nat.dvd_of_mod_eq_zero h3
    rcases h3k with ⟨q, rfl⟩
    have : m = (m % (3 * q)) + 3 * (q * (m / (3 * q))) := by
      have : 3 * q * (m / (3 * q)) = 3 * (q * (m / (3 * q))) := by ring
      omega
    conv_rhs => rw [this, Nat.add_mul_mod_self_left]
  have hsingle : ∀ j : Fin k, psiPair k (mixMap k hk (Pi.single j 1)) = 0 := by
    intro j
    have hsupp : ∀ i : Fin k, mixMap k hk (Pi.single j 1) i =
        (if i = ix k hk (j.val + 1) then 1 else 0) +
        (if i = j then 1 else 0) +
        (if i = ix k hk (j.val + k - 1) then 1 else 0) := by
      intro i
      simp only [mixMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
      have e1 : (ix k hk (i.val + k - 1) = j) ↔ (i = ix k hk (j.val + 1)) := by
        constructor <;> intro h
        · have hv := congrArg Fin.val h
          dsimp [ix] at hv
          apply Fin.ext; dsimp [ix]
          have h1 : (i.val + k - 1) + 1 ≡ j.val + 1 [MOD k] :=
            ((Nat.mod_modEq (i.val + k - 1) k).symm.trans (by rw [hv])).add_right 1
          have h2 : i.val + k - 1 + 1 = i.val + k := by omega
          rw [h2] at h1
          change i.val = (j.val + 1) % k
          rw [← Nat.mod_eq_of_lt i.isLt, ← Nat.add_mod_right i.val k]
          exact h1
        · subst h
          apply Fin.ext; dsimp [ix]
          have h2 : (j.val + 1) % k + (k - 1) ≡ (j.val + 1) + (k - 1) [MOD k] :=
            (Nat.mod_modEq (j.val + 1) k).add_right (k - 1)
          have ha : (j.val + 1) % k + (k - 1) = (j.val + 1) % k + k - 1 := by omega
          have hb : (j.val + 1) + (k - 1) = j.val + k := by omega
          rw [ha, hb] at h2
          change ((j.val + 1) % k + k - 1) % k = j.val
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
      have e2 : (ix k hk (i.val + 1) = j) ↔ (i = ix k hk (j.val + k - 1)) := by
        constructor <;> intro h
        · have hv := congrArg Fin.val h
          dsimp [ix] at hv
          apply Fin.ext; dsimp [ix]
          have h1 : (i.val + 1) % k + (k - 1) ≡ j.val + (k - 1) [MOD k] := by
            rw [hv]
          have h2 : (i.val + 1) + (k - 1) ≡ (i.val + 1) % k + (k - 1) [MOD k] :=
            (Nat.mod_modEq (i.val + 1) k).symm.add_right (k - 1)
          have h3' := h2.trans h1
          have ha : i.val + 1 + (k - 1) = i.val + k := by omega
          have hb : j.val + (k - 1) = j.val + k - 1 := by omega
          rw [ha, hb] at h3'
          change i.val = (j.val + k - 1) % k
          rw [← Nat.mod_eq_of_lt i.isLt, ← Nat.add_mod_right i.val k]
          exact h3'
        · subst h
          apply Fin.ext; dsimp [ix]
          have h2 : (j.val + k - 1) % k + 1 ≡ (j.val + k - 1) + 1 [MOD k] :=
            (Nat.mod_modEq (j.val + k - 1) k).add_right 1
          change ((j.val + k - 1) % k + 1) % k = j.val
          rw [h2]
          have : j.val + k - 1 + 1 = j.val + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
      simp only [e1, e2]
    have hsum_single : ∀ (P : Fin k → Prop) [DecidablePred P],
        (∑ i : Fin k, if P i then mixMap k hk (Pi.single j 1) i else 0) =
        (if P (ix k hk (j.val + 1)) then 1 else 0) +
        (if P j then 1 else 0) +
        (if P (ix k hk (j.val + k - 1)) then 1 else 0) := by
      intro P _
      simp_rw [hsupp]
      have hsplit : ∀ i : Fin k,
          (if P i then
            (if i = ix k hk (j.val + 1) then (1 : F) else 0) +
            (if i = j then 1 else 0) +
            (if i = ix k hk (j.val + k - 1) then 1 else 0) else 0) =
          (if i = ix k hk (j.val + 1) then (if P i then 1 else 0) else 0) +
          (if i = j then (if P i then 1 else 0) else 0) +
          (if i = ix k hk (j.val + k - 1) then (if P i then 1 else 0) else 0) := by
        intro i; split_ifs <;> simp
      simp_rw [hsplit, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    apply Prod.ext
    · change psi0 k (mixMap k hk (Pi.single j 1)) = 0
      dsimp only [psi0, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hsum_single]
      rw [hmod3 (j.val + 1), hmod3 (j.val + k - 1)]
      have hm : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
      have hsub : (j.val + k - 1) % 3 = (j.val + 2) % 3 := by omega
      rw [hsub]
      rcases hm with h | h | h
      · have h1 : (j.val + 1) % 3 = 1 := by omega
        have h2 : (j.val + 2) % 3 = 2 := by omega
        simp [h, h1, h2]; decide
      · have h1 : (j.val + 1) % 3 = 2 := by omega
        have h2 : (j.val + 2) % 3 = 0 := by omega
        simp [h, h1, h2]; decide
      · have h1 : (j.val + 1) % 3 = 0 := by omega
        have h2 : (j.val + 2) % 3 = 1 := by omega
        simp [h, h1, h2]; decide
    · change psi1 k (mixMap k hk (Pi.single j 1)) = 0
      dsimp only [psi1, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hsum_single]
      rw [hmod3 (j.val + 1), hmod3 (j.val + k - 1)]
      have hm : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
      have hsub : (j.val + k - 1) % 3 = (j.val + 2) % 3 := by omega
      rw [hsub]
      rcases hm with h | h | h
      · have h1 : (j.val + 1) % 3 = 1 := by omega
        have h2 : (j.val + 2) % 3 = 2 := by omega
        simp [h, h1, h2]; decide
      · have h1 : (j.val + 1) % 3 = 2 := by omega
        have h2 : (j.val + 2) % 3 = 0 := by omega
        simp [h, h1, h2]; decide
      · have h1 : (j.val + 1) % 3 = 0 := by omega
        have h2 : (j.val + 2) % 3 = 1 := by omega
        simp [h, h1, h2]; decide
  have hx_eq : x = ∑ j : Fin k, x j • Pi.single j (1 : F) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx_eq]
  simp only [map_sum, map_smul, hsingle, smul_zero, Finset.sum_const_zero]

lemma range_mixMap_of_dvd (k : ℕ) (hk : 0 < k) (h3 : k % 3 = 0) :
    LinearMap.range (mixMap k hk) = LinearMap.ker (psiPair k) ∧
    Module.finrank F (LinearMap.range (mixMap k hk)) = k - 2 := by
  have hge3 : 3 ≤ k := by omega
  let per : (F × F) →ₗ[F] (Fin k → F) :=
    { toFun := fun p i => if i.val % 3 = 0 then p.1 else if i.val % 3 = 1 then p.2 else p.1 + p.2
      map_add' := fun p q => by
        funext i
        simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
        split_ifs <;> ring
      map_smul' := fun c p => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Prod.smul_fst, Prod.smul_snd]
        split_ifs <;> ring }
  have hper_inj : Function.Injective per := by
    intro p q h
    have h0 := congrFun h ⟨0, by omega⟩
    have h1 := congrFun h ⟨1, by omega⟩
    simp only [per, LinearMap.coe_mk, AddHom.coe_mk] at h0 h1
    exact Prod.ext h0 h1
  have hker_le : LinearMap.ker (mixMap k hk) ≤ LinearMap.range per := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    refine ⟨(x ⟨0, by omega⟩, x ⟨1, by omega⟩), ?_⟩
    funext i
    rcases i with ⟨t, ht⟩
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      by_cases ht0 : t = 0
      · subst ht0; simp [per]
      · by_cases ht1 : t = 1
        · subst ht1; simp [per]
        · have ht2 : 2 ≤ t := by omega
          have hm := congrFun hx ⟨t - 1, by omega⟩
          simp only [mixMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hm
          have hprev : ix k hk (t - 1 + k - 1) = ⟨t - 2, by omega⟩ := by
            apply Fin.ext; dsimp [ix]
            have : t - 1 + k - 1 = (t - 2) + k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hnext : ix k hk (t - 1 + 1) = ⟨t, ht⟩ := by
            apply Fin.ext; dsimp [ix]
            have : t - 1 + 1 = t := by omega
            rw [this, Nat.mod_eq_of_lt ht]
          rw [hprev, hnext] at hm
          have heq : x ⟨t, ht⟩ = x ⟨t - 2, by omega⟩ + x ⟨t - 1, by omega⟩ := by
            apply zmod2_eq_of_add_eq_zero
            calc x ⟨t, ht⟩ + (x ⟨t - 2, by omega⟩ + x ⟨t - 1, by omega⟩)
                = x ⟨t - 2, by omega⟩ + x ⟨t - 1, by omega⟩ + x ⟨t, ht⟩ := by ring
              _ = 0 := hm
          rw [heq, ← ih (t - 2) (by omega) (by omega), ← ih (t - 1) (by omega) (by omega)]
          simp only [per, LinearMap.coe_mk, AddHom.coe_mk]
          have hm3 : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
          rcases hm3 with h | h | h
          · have h1 : (t - 2) % 3 = 1 := by omega
            have h2 : (t - 1) % 3 = 2 := by omega
            simp only [h, h1, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 0 by decide,
              show (2 : ℕ) ≠ 1 by decide]
            calc x ⟨0, by omega⟩ = x ⟨0, by omega⟩ + (x ⟨1, by omega⟩ + x ⟨1, by omega⟩) := by
                  rw [zmod2_add_self, add_zero]
              _ = x ⟨1, by omega⟩ + (x ⟨0, by omega⟩ + x ⟨1, by omega⟩) := by ring
          · have h1 : (t - 2) % 3 = 2 := by omega
            have h2 : (t - 1) % 3 = 0 := by omega
            simp only [h, h1, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 0 by decide,
              show (2 : ℕ) ≠ 1 by decide]
            calc x ⟨1, by omega⟩ = x ⟨1, by omega⟩ + (x ⟨0, by omega⟩ + x ⟨0, by omega⟩) := by
                  rw [zmod2_add_self, add_zero]
              _ = x ⟨0, by omega⟩ + x ⟨1, by omega⟩ + x ⟨0, by omega⟩ := by ring
          · have h1 : (t - 2) % 3 = 0 := by omega
            have h2 : (t - 1) % 3 = 1 := by omega
            simp only [h, h1, h2, ↓reduceIte, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 0 by decide,
              show (2 : ℕ) ≠ 1 by decide]
  have hker_dim_le : Module.finrank F (LinearMap.ker (mixMap k hk)) ≤ 2 := by
    calc Module.finrank F (LinearMap.ker (mixMap k hk))
        ≤ Module.finrank F (LinearMap.range per) := Submodule.finrank_mono hker_le
      _ = Module.finrank F (F × F) := LinearMap.finrank_range_of_inj hper_inj
      _ = 2 := by simp [Module.finrank_prod]
  have hpsi_surj : Function.Surjective (psiPair k) := by
    intro ⟨a, b⟩
    refine ⟨a • Pi.single ⟨0, by omega⟩ 1 + b • Pi.single ⟨1, by omega⟩ 1, ?_⟩
    apply Prod.ext
    · simp [psiPair, psi0_single]
    · simp [psiPair, psi1_single]
  have hpsi_rk := LinearMap.finrank_range_add_finrank_ker (psiPair k)
  rw [LinearMap.range_eq_top.mpr hpsi_surj, finrank_top] at hpsi_rk
  have hdimW : Module.finrank F (Fin k → F) = k := by simp
  have hdimFF : Module.finrank F (F × F) = 2 := by simp [Module.finrank_prod]
  rw [hdimW, hdimFF] at hpsi_rk
  have hker_psi_dim : Module.finrank F (LinearMap.ker (psiPair k)) = k - 2 := by omega
  have hle : LinearMap.range (mixMap k hk) ≤ LinearMap.ker (psiPair k) := by
    rintro y ⟨x, rfl⟩
    exact psiPair_comp_mixMap k hk h3 x
  have hmix_rk := LinearMap.finrank_range_add_finrank_ker (mixMap k hk)
  rw [hdimW] at hmix_rk
  have hrange_le : Module.finrank F (LinearMap.range (mixMap k hk)) ≤ k - 2 := by
    rw [← hker_psi_dim]
    exact Submodule.finrank_mono hle
  have hrange_eq : Module.finrank F (LinearMap.range (mixMap k hk)) = k - 2 := by omega
  exact ⟨Submodule.eq_of_le_of_finrank_eq hle (by rw [hrange_eq, hker_psi_dim]), hrange_eq⟩

lemma finrank_range_viewMap (k L : ℕ) (hk : 0 < k) (start : ℕ) :
    Module.finrank F (LinearMap.range (viewMap k L hk start)) =
      min L (if k % 3 = 0 then k - 2 else k) := by
  let r := min L (if k % 3 = 0 then k - 2 else k)
  have hrL : r ≤ L := min_le_left _ _
  let projR : (Fin L → F) →ₗ[F] (Fin r → F) :=
    { toFun := fun y i => y ⟨i.val, lt_of_lt_of_le i.isLt hrL⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hle_L : Module.finrank F (LinearMap.range (viewMap k L hk start)) ≤ L := by
    calc Module.finrank F (LinearMap.range (viewMap k L hk start))
        ≤ Module.finrank F (Fin L → F) := Submodule.finrank_le _
      _ = L := by simp
  by_cases h3 : k % 3 = 0
  · have hge3 : 3 ≤ k := by omega
    have hrk : r ≤ k - 2 := by simpa [r, h3] using min_le_right L (if k % 3 = 0 then k - 2 else k)
    obtain ⟨hrange_eq, hrange_dim⟩ := range_mixMap_of_dvd k hk h3
    have hle_k : Module.finrank F (LinearMap.range (viewMap k L hk start)) ≤ k - 2 := by
      have hsub : LinearMap.range (viewMap k L hk start) =
          (LinearMap.range (mixMap k hk)).map (stripMap k L hk start) := by
        simp [viewMap, LinearMap.range_comp]
      rw [hsub, ← hrange_dim]
      exact Submodule.finrank_map_le _ _
    have hsurj : Function.Surjective (projR.comp (viewMap k L hk start)) := by
      intro v
      let z0 : Fin k → F := fun j =>
        if h : (j.val + k - start % k) % k < r then v ⟨_, h⟩ else 0
      let p1 : Fin k := ix k hk (start + k - 2)
      let p2 : Fin k := ix k hk (start + k - 1)
      have hp1_not : ∀ i : Fin r, ix k hk (start + i.val) ≠ p1 := by
        intro i heq
        have hv := congrArg Fin.val heq
        dsimp [ix, p1] at hv
        have h1 : (start + i.val + 2) % k = (start + k - 2 + 2) % k := by
          rw [Nat.add_mod, hv, ← Nat.add_mod]
        have h2 : start + k - 2 + 2 = start + k := by omega
        rw [h2, Nat.add_mod_right] at h1
        have h3' : (start % k + (i.val + 2)) % k = start % k := by
          have hmod1 : (start + i.val + 2) % k = (start % k + (i.val + 2)) % k := by
            rw [Nat.add_assoc, Nat.mod_add_mod]
          rw [← hmod1, h1]
        have hlt : i.val + 2 < k := by have := i.isLt; omega
        have hdiv : (start % k + (i.val + 2)) % k ≠ start % k := by
          by_cases hs : start % k + (i.val + 2) < k
          · rw [Nat.mod_eq_of_lt hs]; omega
          · have : start % k + (i.val + 2) - k < k := by
              have := Nat.mod_lt start hk; omega
            rw [show start % k + (i.val + 2) = (start % k + (i.val + 2) - k) + k by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt this]
            omega
        exact hdiv h3'
      have hp2_not : ∀ i : Fin r, ix k hk (start + i.val) ≠ p2 := by
        intro i heq
        have hv := congrArg Fin.val heq
        dsimp [ix, p2] at hv
        have h1 : (start + i.val + 1) % k = (start + k - 1 + 1) % k := by
          rw [Nat.add_mod, hv, ← Nat.add_mod]
        have h2 : start + k - 1 + 1 = start + k := by omega
        rw [h2, Nat.add_mod_right] at h1
        have h3' : (start % k + (i.val + 1)) % k = start % k := by
          have hmod1 : (start + i.val + 1) % k = (start % k + (i.val + 1)) % k := by
            rw [Nat.add_assoc, Nat.mod_add_mod]
          rw [← hmod1, h1]
        have hlt : i.val + 1 < k := by have := i.isLt; omega
        have hdiv : (start % k + (i.val + 1)) % k ≠ start % k := by
          by_cases hs : start % k + (i.val + 1) < k
          · rw [Nat.mod_eq_of_lt hs]; omega
          · have : start % k + (i.val + 1) - k < k := by
              have := Nat.mod_lt start hk; omega
            rw [show start % k + (i.val + 1) = (start % k + (i.val + 1) - k) + k by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt this]
            omega
        exact hdiv h3'
      have hmod3 : ∀ m : ℕ, (ix k hk m).val % 3 = m % 3 := by
        intro m; dsimp [ix]
        have h3k : 3 ∣ k := Nat.dvd_of_mod_eq_zero h3
        rcases h3k with ⟨q, rfl⟩
        have hdiv := Nat.div_add_mod m (3 * q)
        have : m = (m % (3 * q)) + 3 * (q * (m / (3 * q))) := by
          have : 3 * q * (m / (3 * q)) = 3 * (q * (m / (3 * q))) := by ring
          omega
        conv_rhs => rw [this, Nat.add_mul_mod_self_left]
      have hp_mod : p2.val % 3 = (p1.val % 3 + 1) % 3 := by
        dsimp [p1, p2]
        rw [hmod3, hmod3]
        omega
      have hex_c : ∃ c1 c2 : F,
          psiPair k (z0 + c1 • Pi.single p1 1 + c2 • Pi.single p2 1) = 0 := by
        let a0 := psi0 k z0
        let a1 := psi1 k z0
        have hp1_0 := psi0_single k p1
        have hp1_1 := psi1_single k p1
        have hp2_0 := psi0_single k p2
        have hp2_1 := psi1_single k p2
        have hcase : p1.val % 3 = 0 ∨ p1.val % 3 = 1 ∨ p1.val % 3 = 2 := by omega
        rcases hcase with h0 | h1 | h2
        · refine ⟨a0, a1, Prod.ext ?_ ?_⟩
          · change psi0 k (z0 + a0 • Pi.single p1 1 + a1 • Pi.single p2 1) = 0
            rw [map_add, map_add, map_smul, map_smul, hp1_0, hp2_0, hp_mod, h0]
            simp only [smul_eq_mul, a0]
            norm_num
            exact zmod2_add_self _
          · change psi1 k (z0 + a0 • Pi.single p1 1 + a1 • Pi.single p2 1) = 0
            rw [map_add, map_add, map_smul, map_smul, hp1_1, hp2_1, hp_mod, h0]
            simp only [smul_eq_mul, a1]
            norm_num
            exact zmod2_add_self _
        · refine ⟨a0 + a1, a0, Prod.ext ?_ ?_⟩
          · change psi0 k (z0 + (a0 + a1) • Pi.single p1 1 + a0 • Pi.single p2 1) = 0
            rw [map_add, map_add, map_smul, map_smul, hp1_0, hp2_0, hp_mod, h1]
            simp only [smul_eq_mul, a0]
            norm_num
            exact zmod2_add_self _
          · change psi1 k (z0 + (a0 + a1) • Pi.single p1 1 + a0 • Pi.single p2 1) = 0
            rw [map_add, map_add, map_smul, map_smul, hp1_1, hp2_1, hp_mod, h1]
            simp only [smul_eq_mul, a0, a1]
            norm_num
            calc psi1 k z0 + (psi0 k z0 + psi1 k z0) + psi0 k z0
                = (psi1 k z0 + psi1 k z0) + (psi0 k z0 + psi0 k z0) := by ring
              _ = 0 := by rw [zmod2_add_self, zmod2_add_self, add_zero]
        · refine ⟨a1, a0 + a1, Prod.ext ?_ ?_⟩
          · change psi0 k (z0 + a1 • Pi.single p1 1 + (a0 + a1) • Pi.single p2 1) = 0
            rw [map_add, map_add, map_smul, map_smul, hp1_0, hp2_0, hp_mod, h2]
            simp only [smul_eq_mul, a0, a1]
            norm_num
            calc psi0 k z0 + psi1 k z0 + (psi0 k z0 + psi1 k z0)
                = (psi0 k z0 + psi0 k z0) + (psi1 k z0 + psi1 k z0) := by ring
              _ = 0 := by rw [zmod2_add_self, zmod2_add_self, add_zero]
          · change psi1 k (z0 + a1 • Pi.single p1 1 + (a0 + a1) • Pi.single p2 1) = 0
            rw [map_add, map_add, map_smul, map_smul, hp1_1, hp2_1, hp_mod, h2]
            simp only [smul_eq_mul, a1]
            norm_num
            exact zmod2_add_self _
      obtain ⟨c1, c2, hpsi0⟩ := hex_c
      let z := z0 + c1 • Pi.single p1 1 + c2 • Pi.single p2 1
      have hz_mem : z ∈ LinearMap.range (mixMap k hk) := by
        rw [hrange_eq, LinearMap.mem_ker]
        exact hpsi0
      obtain ⟨x, hx⟩ := hz_mem
      refine ⟨x, ?_⟩
      funext i
      simp only [LinearMap.comp_apply, projR, viewMap, stripMap, LinearMap.coe_mk, AddHom.coe_mk, hx,
        z, Pi.add_apply, Pi.smul_apply, Pi.single_apply, hp1_not i, hp2_not i, ↓reduceIte,
        smul_zero, add_zero]
      dsimp only [z0, ix]
      have hidx : ((start + i.val) % k + k - start % k) % k = i.val := by
        have h1 : (start + i.val) % k + k - start % k ≡ start + i.val + k - start % k [MOD k] := by
          have := Nat.mod_modEq (start + i.val) k
          have hlt := Nat.mod_lt start hk
          have h2 := this.add_right (k - start % k)
          have ha : (start + i.val) % k + (k - start % k) = (start + i.val) % k + k - start % k := by omega
          have hb : start + i.val + (k - start % k) = start + i.val + k - start % k := by omega
          rwa [ha, hb] at h2
        change ((start + i.val) % k + k - start % k) % k = i.val
        rw [h1]
        have hdiv := Nat.div_add_mod start k
        have h3' : start + i.val + k - start % k = i.val + k * (start / k + 1) := by
          have : k * (start / k + 1) = k * (start / k) + k := by ring
          omega
        rw [h3', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      simp only [hidx, i.isLt, ↓reduceDIte]
    have hge_r : r ≤ Module.finrank F (LinearMap.range (viewMap k L hk start)) := by
      have h1 : Module.finrank F (Fin r → F) = r := by simp
      have h2 : Module.finrank F (LinearMap.range (projR.comp (viewMap k L hk start))) = r := by
        rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, h1]
      rw [← h2, LinearMap.range_comp]
      exact Submodule.finrank_map_le _ _
    have hle_r : Module.finrank F (LinearMap.range (viewMap k L hk start)) ≤ r := by
      dsimp [r]; simp only [h3, ↓reduceIte]; exact le_min hle_L hle_k
    exact le_antisymm hle_r hge_r
  · have hrk : r ≤ k := by simpa [r, h3] using min_le_right L (if k % 3 = 0 then k - 2 else k)
    have hle_k : Module.finrank F (LinearMap.range (viewMap k L hk start)) ≤ k := by
      calc Module.finrank F (LinearMap.range (viewMap k L hk start))
          ≤ Module.finrank F (Fin k → F) := LinearMap.finrank_range_le _
        _ = k := by simp
    have hsurj : Function.Surjective (projR.comp (viewMap k L hk start)) := by
      intro v
      let z : Fin k → F := fun j =>
        if h : (j.val + k - start % k) % k < r then v ⟨_, h⟩ else 0
      obtain ⟨x, hx⟩ := mixMap_surjective_of_not_dvd k hk h3 z
      refine ⟨x, ?_⟩
      funext i
      simp only [LinearMap.comp_apply, projR, viewMap, stripMap, LinearMap.coe_mk, AddHom.coe_mk, hx]
      dsimp only [z, ix]
      have hidx : ((start + i.val) % k + k - start % k) % k = i.val := by
        have h1 : (start + i.val) % k + k - start % k ≡ start + i.val + k - start % k [MOD k] := by
          have := Nat.mod_modEq (start + i.val) k
          have hlt := Nat.mod_lt start hk
          have h2 := this.add_right (k - start % k)
          have ha : (start + i.val) % k + (k - start % k) = (start + i.val) % k + k - start % k := by omega
          have hb : start + i.val + (k - start % k) = start + i.val + k - start % k := by omega
          rwa [ha, hb] at h2
        change ((start + i.val) % k + k - start % k) % k = i.val
        rw [h1]
        have hdiv := Nat.div_add_mod start k
        have h3' : start + i.val + k - start % k = i.val + k * (start / k + 1) := by
          have : k * (start / k + 1) = k * (start / k) + k := by ring
          omega
        rw [h3', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
      simp only [hidx, i.isLt, ↓reduceDIte]
    have hge_r : r ≤ Module.finrank F (LinearMap.range (viewMap k L hk start)) := by
      have h1 : Module.finrank F (Fin r → F) = r := by simp
      have h2 : Module.finrank F (LinearMap.range (projR.comp (viewMap k L hk start))) = r := by
        rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, h1]
      rw [← h2, LinearMap.range_comp]
      exact Submodule.finrank_map_le _ _
    have hle_r : Module.finrank F (LinearMap.range (viewMap k L hk start)) ≤ r := by
      dsimp [r]; simp only [h3, ↓reduceIte]; exact le_min hle_L hle_k
    exact le_antisymm hle_r hge_r

def runTree {n d : ℕ} (ask : Fin d → ℕ → (Fin n → F) →ₗ[F] F) (x : Fin n → F) : ℕ :=
  (List.finRange d).foldl (fun tr j => 2 * tr + (if ask j tr x = 0 then 0 else 1)) (0 : ℕ)

lemma runTree_append {n c d : ℕ}
    (ask1 : Fin c → ℕ → (Fin n → F) →ₗ[F] F)
    (ask2 : Fin d → ℕ → (Fin n → F) →ₗ[F] F)
    (x : Fin n → F) :
    let ask : Fin (c + d) → ℕ → (Fin n → F) →ₗ[F] F := fun j tr =>
      if h : j.val < c then ask1 ⟨j.val, h⟩ tr
      else ask2 ⟨j.val - c, by omega⟩ (tr % 2 ^ (j.val - c))
    runTree ask x = runTree ask1 x * 2 ^ d + runTree ask2 x := by
  intro ask
  unfold runTree
  have hsplit : List.finRange (c + d) =
      (List.finRange c).map (Fin.castAdd d) ++ (List.finRange d).map (Fin.natAdd c) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      by_cases hi : i < c
      · rw [List.getElem_append_left (by simpa using hi)]
        simp
      · rw [List.getElem_append_right (by simpa using Nat.le_of_not_lt hi)]
        simp only [List.getElem_finRange, List.getElem_map, List.length_map, List.length_finRange,
          Fin.cast_mk, Fin.natAdd_mk]
        apply Fin.ext; dsimp; omega
  rw [hsplit, List.foldl_append, List.foldl_map, List.foldl_map]
  have hfirst : (List.finRange c).foldl
      (fun tr j => 2 * tr + if ask (Fin.castAdd d j) tr x = 0 then 0 else 1) 0 =
      (List.finRange c).foldl (fun tr j => 2 * tr + if ask1 j tr x = 0 then 0 else 1) 0 := by
    congr 1
    funext tr j
    simp [ask, j.isLt]
  rw [hfirst]
  set tr0 := (List.finRange c).foldl (fun tr j => 2 * tr + if ask1 j tr x = 0 then 0 else 1) 0
  have hgen : ∀ m (hm : m ≤ d),
      ((List.finRange d).take m).foldl
        (fun tr j => 2 * tr + if ask (Fin.natAdd c j) tr x = 0 then 0 else 1) tr0 =
      tr0 * 2 ^ m + ((List.finRange d).take m).foldl
        (fun tr j => 2 * tr + if ask2 j tr x = 0 then 0 else 1) 0 ∧
      ((List.finRange d).take m).foldl
        (fun tr j => 2 * tr + if ask2 j tr x = 0 then 0 else 1) 0 < 2 ^ m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hlt : m < (List.finRange d).length := by simp; omega
      have htk : (List.finRange d).take (m + 1) = (List.finRange d).take m ++ [⟨m, by omega⟩] := by
        rw [List.take_succ_eq_append_getElem hlt]; simp
      obtain ⟨iheq, ihlt⟩ := ih (by omega)
      rw [htk, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, iheq]
      have hnot : ¬ (c + m < c) := by omega
      have hsub : c + m - c = m := by omega
      have hmod : (tr0 * 2 ^ m + ((List.finRange d).take m).foldl
          (fun tr j => 2 * tr + if ask2 j tr x = 0 then 0 else 1) 0) % 2 ^ m =
          ((List.finRange d).take m).foldl
            (fun tr j => 2 * tr + if ask2 j tr x = 0 then 0 else 1) 0 := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt ihlt]
      have hask : ask (Fin.natAdd c ⟨m, by omega⟩)
          (tr0 * 2 ^ m + ((List.finRange d).take m).foldl
            (fun tr j => 2 * tr + if ask2 j tr x = 0 then 0 else 1) 0) =
          ask2 ⟨m, by omega⟩ (((List.finRange d).take m).foldl
            (fun tr j => 2 * tr + if ask2 j tr x = 0 then 0 else 1) 0) := by
        dsimp only [ask, Fin.val_natAdd]
        simp only [hnot, ↓reduceDIte, hsub, hmod]
      rw [hask]
      constructor
      · rw [pow_succ]; ring
      · rw [pow_succ]
        split_ifs <;> omega
  have hres := (hgen d (le_refl d)).1
  have htkd : (List.finRange d).take d = List.finRange d := List.take_of_length_le (by simp)
  rw [htkd] at hres
  exact hres

lemma runTree_lt {n d : ℕ} (ask : Fin d → ℕ → (Fin n → F) →ₗ[F] F) (x : Fin n → F) :
    runTree ask x < 2 ^ d := by
  unfold runTree
  have hgen : ∀ m (hm : m ≤ d),
      ((List.finRange d).take m).foldl
        (fun tr j => 2 * tr + if ask j tr x = 0 then 0 else 1) 0 < 2 ^ m := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hlt : m < (List.finRange d).length := by simp; omega
      have htk : (List.finRange d).take (m + 1) = (List.finRange d).take m ++ [⟨m, by omega⟩] := by
        rw [List.take_succ_eq_append_getElem hlt]; simp
      rw [htk, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, pow_succ]
      have := ih (by omega)
      split_ifs <;> omega
  have hres := hgen d (le_refl d)
  rwa [List.take_of_length_le (by simp)] at hres

lemma runTree_eq_zero {n d : ℕ} (ask : Fin d → ℕ → (Fin n → F) →ₗ[F] F) (x : Fin n → F)
    (h : ∀ j : Fin d, ask j 0 x = 0) : runTree ask x = 0 := by
  unfold runTree
  have hgen : ∀ m (hm : m ≤ d),
      ((List.finRange d).take m).foldl
        (fun tr j => 2 * tr + if ask j tr x = 0 then 0 else 1) 0 = 0 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hlt : m < (List.finRange d).length := by simp; omega
      have htk : (List.finRange d).take (m + 1) = (List.finRange d).take m ++ [⟨m, by omega⟩] := by
        rw [List.take_succ_eq_append_getElem hlt]; simp
      rw [htk, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, ih (by omega), h ⟨m, by omega⟩, ↓reduceIte]
  have hres := hgen d (le_refl d)
  rwa [List.take_of_length_le (by simp)] at hres

lemma runTree_nonadapt_inj {n c : ℕ} (phi : Fin c → (Fin n → F) →ₗ[F] F) (x y : Fin n → F)
    (heq : runTree (fun j _ => phi j) x = runTree (fun j _ => phi j) y) :
    ∀ j : Fin c, phi j x = phi j y := by
  have hgen : ∀ m (hm : m ≤ c),
      ((List.finRange c).take m).foldl (fun tr j => 2 * tr + if phi j x = 0 then 0 else 1) 0 =
      ((List.finRange c).take m).foldl (fun tr j => 2 * tr + if phi j y = 0 then 0 else 1) 0 →
      ∀ j : Fin c, j.val < m → phi j x = phi j y := by
    intro m
    induction m with
    | zero => intro _ _ j hj; omega
    | succ m ih =>
      intro hm hfeq j hj
      have hlt : m < (List.finRange c).length := by simp; omega
      have htk : (List.finRange c).take (m + 1) = (List.finRange c).take m ++ [⟨m, by omega⟩] := by
        rw [List.take_succ_eq_append_getElem hlt]; simp
      rw [htk, List.foldl_append, List.foldl_append] at hfeq
      simp only [List.foldl_cons, List.foldl_nil] at hfeq
      have hbit : (if phi ⟨m, by omega⟩ x = 0 then (0 : ℕ) else 1) =
          (if phi ⟨m, by omega⟩ y = 0 then 0 else 1) := by
        split_ifs at hfeq ⊢ <;> omega
      have hprev : ((List.finRange c).take m).foldl
            (fun tr j => 2 * tr + if phi j x = 0 then 0 else 1) 0 =
          ((List.finRange c).take m).foldl
            (fun tr j => 2 * tr + if phi j y = 0 then 0 else 1) 0 := by
        omega
      by_cases hjm : j.val < m
      · exact ih (by omega) hprev j hjm
      · have hjeq : j = ⟨m, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hjeq]
        generalize hxv : phi ⟨m, by omega⟩ x = vx at hbit ⊢
        generalize hyv : phi ⟨m, by omega⟩ y = vy at hbit ⊢
        fin_cases vx <;> fin_cases vy <;> first | rfl | exact absurd hbit (by decide)
  intro j
  apply hgen c (le_refl c)
  · simpa [runTree, List.take_of_length_le] using heq
  · exact j.isLt

lemma exists_decomp (k L : ℕ) (hk : 0 < k) (start : ℕ) :
    let R := LinearMap.range (viewMap k L hk start)
    let r := min L (if k % 3 = 0 then k - 2 else k)
    let c := L - r
    ∃ (T : (Fin L → F) →ₗ[F] (Fin k → F))
      (phi : Fin c → (Fin L → F) →ₗ[F] F)
      (cosetRep : ℕ → (Fin L → F)),
      (∀ i : Fin c, ∀ x : Fin k → F, phi i (viewMap k L hk start x) = 0) ∧
      (∀ y : Fin L → F, (∀ i : Fin c, phi i y = 0) ↔ y ∈ R) ∧
      (∀ y : Fin L → F, y = viewMap k L hk start (T y) + cosetRep (runTree (fun i _ => phi i) y)) := by
  intro R r c
  have hdimR : Module.finrank F R = r := finrank_range_viewMap k L hk start
  obtain ⟨C, hRC⟩ := Submodule.exists_isCompl R
  have hdimC : Module.finrank F C = c := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hRC
    have hdimV : Module.finrank F (Fin L → F) = L := by simp
    rw [hdimR, hdimV] at hsum
    have hrL : r ≤ L := min_le_left _ _
    omega
  let eC : C ≃ₗ[F] (Fin c → F) := LinearEquiv.ofFinrankEq C (Fin c → F) (by rw [hdimC]; simp)
  let piR : (Fin L → F) →ₗ[F] R := Submodule.projectionOnto R C hRC
  let piC : (Fin L → F) →ₗ[F] C := Submodule.projectionOnto C R hRC.symm
  have hsplit : ∀ y : Fin L → F, (piR y : Fin L → F) + (piC y : Fin L → F) = y := by
    intro y
    have hy : y ∈ R ⊔ C := by rw [hRC.sup_eq_top]; trivial
    obtain ⟨r', hr', c', hc', rfl⟩ := Submodule.mem_sup.mp hy
    have h1 : piR (r' + c') = ⟨r', hr'⟩ := by
      dsimp only [piR]
      rw [map_add, Submodule.projectionOnto_apply_left hRC ⟨r', hr'⟩,
        Submodule.projectionOnto_apply_right hRC ⟨c', hc'⟩, add_zero]
    have h2 : piC (r' + c') = ⟨c', hc'⟩ := by
      dsimp only [piC]
      rw [map_add, Submodule.projectionOnto_apply_right hRC.symm ⟨r', hr'⟩,
        Submodule.projectionOnto_apply_left hRC.symm ⟨c', hc'⟩, zero_add]
    rw [h1, h2]
  let phi : Fin c → (Fin L → F) →ₗ[F] F := fun i =>
    (LinearMap.proj i).comp (eC.toLinearMap.comp piC)
  have hphi_zero : ∀ y : Fin L → F, (∀ i : Fin c, phi i y = 0) ↔ y ∈ R := by
    intro y
    constructor
    · intro h
      have he0 : eC (piC y) = 0 := funext h
      have hc0 : piC y = 0 := eC.injective (by simpa using he0)
      have hy : (piR y : Fin L → F) = y := by simpa [hc0] using hsplit y
      rw [← hy]
      exact (piR y).property
    · intro hy i
      have hc0 : piC y = 0 := Submodule.projectionOnto_apply_right hRC.symm ⟨y, hy⟩
      simp [phi, hc0]
  have hphi_view : ∀ i : Fin c, ∀ x : Fin k → F, phi i (viewMap k L hk start x) = 0 := by
    intro i x
    exact (hphi_zero (viewMap k L hk start x)).mpr ⟨x, rfl⟩ i
  let bR := Module.finBasis F R
  have hsec_ex : ∀ u : R, ∃ x : Fin k → F, viewMap k L hk start x = u.val := fun u => u.property
  choose secFun hsecFun using hsec_ex
  let sec : R →ₗ[F] (Fin k → F) := bR.constr F (fun idx => secFun (bR idx))
  have hsec_ok : ∀ u : R, viewMap k L hk start (sec u) = u.val := by
    intro u
    have hu : u = ∑ idx, (bR.repr u idx) • bR idx := (bR.sum_repr u).symm
    conv_lhs => rw [hu]
    simp only [map_sum, map_smul, sec, Module.Basis.constr_basis, hsecFun]
    conv_rhs => rw [hu]
    simp only [Submodule.coe_sum, SetLike.val_smul]
  let T : (Fin L → F) →ₗ[F] (Fin k → F) := sec.comp piR
  let trMap : (Fin L → F) → ℕ := fun y => runTree (fun i _ => phi i) y
  let cosetRep : ℕ → (Fin L → F) := fun tr =>
    if h : ∃ y : Fin L → F, trMap y = tr then (piC h.choose : Fin L → F) else 0
  refine ⟨T, phi, cosetRep, hphi_view, hphi_zero, ?_⟩
  intro y
  have hex : ∃ y' : Fin L → F, trMap y' = trMap y := ⟨y, rfl⟩
  have hrep : cosetRep (trMap y) = (piC y : Fin L → F) := by
    simp only [cosetRep, hex, ↓reduceDIte]
    have hphi_eq := runTree_nonadapt_inj phi hex.choose y hex.choose_spec
    have he_eq : eC (piC hex.choose) = eC (piC y) := funext hphi_eq
    have hc_eq : piC hex.choose = piC y := eC.injective he_eq
    rw [hc_eq]
  rw [hrep]
  have hviewT : viewMap k L hk start (T y) = (piR y : Fin L → F) := hsec_ok (piR y)
  rw [hviewT, hsplit y]

lemma finrank_iInf_ker_ge {n d : ℕ} (f : Fin d → (Fin n → F) →ₗ[F] F) :
    n - d ≤ Module.finrank F (⨅ j : Fin d, LinearMap.ker (f j) : Submodule F (Fin n → F)) := by
  let M : (Fin n → F) →ₗ[F] (Fin d → F) := LinearMap.pi f
  have hker : LinearMap.ker M = (⨅ j : Fin d, LinearMap.ker (f j) : Submodule F (Fin n → F)) := by
    ext x
    simp [M, Submodule.mem_iInf, funext_iff]
  rw [← hker]
  have hrk := LinearMap.finrank_range_add_finrank_ker M
  have hdimN : Module.finrank F (Fin n → F) = n := by simp
  have hdimD : Module.finrank F (LinearMap.range M) ≤ d := by
    calc Module.finrank F (LinearMap.range M)
        ≤ Module.finrank F (Fin d → F) := Submodule.finrank_le _
      _ = d := by simp
  rw [hdimN] at hrk
  omega

end PEqualNP.Outside.L_lib_794_aux

open PEqualNP.Outside.L_lib_794_aux in
theorem PEqualNP.Outside.L_lib_794 : (∀ (k L : ℕ) (hk : 0 < k) (_hL : 0 < L) (start : ℕ),
  let F := ZMod 2
  let W := Fin k → F
  let V := Fin L → F
  let D := V →ₗ[F] F
  let ix := fun j : ℕ => (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k)
  let view := fun (x : W) (i : Fin L) =>
    let j := start + i.val
    x (ix (j+k-1)) + x (ix j) + x (ix (j+1))
  let c := L - min L (if k % 3 = 0 then k-2 else k)
  let fits := fun (n t : ℕ) (f : (Fin n → F) → Fin t → F) (d : ℕ) =>
    let U := Fin n → F
    let E := U →ₗ[F] F
    let run := fun (ask : Fin d → ℕ → E) (x : U) =>
      (List.finRange d).foldl (fun tr j => 2*tr + (if ask j tr x = 0 then 0 else 1)) (0 : ℕ)
    ∃ (ask : Fin d → ℕ → E) (readout : ℕ → Fin t → E) (bias : ℕ → Fin t → F),
      ∀ x j, f x j = readout (run ask x) j x + bias (run ask x) j
  let out := fun (t : ℕ) (a b : Fin t → D) (y : V) (j : Fin t) => a j y * b j y
  (∀ (t : ℕ) (a b : Fin t → D) (d : ℕ),
    (fits L t (out t a b) d → fits k t (fun x => out t a b (view x)) d) ∧
    (fits k t (fun x => out t a b (view x)) d → fits L t (out t a b) (d+c))) ∧
  ∃ a b : Fin (c*L) → D,
    (∀ x j, out (c*L) a b (view x) j = 0) ∧
    ∀ d : ℕ, fits L (c*L) (out (c*L) a b) d ↔ c ≤ d) := by
  intro k L hk hL start F W V D ix view c fits out
  have hview_eq : ∀ x : W, view x = viewMap k L hk start x := by
    intro x; funext i; exact (viewMap_apply k L hk start x i).symm
  obtain ⟨T, phi, cosetRep, hphi_view, hphi_zero, hdecomp⟩ := exists_decomp k L hk start
  have hback : ∀ (t : ℕ) (a b : Fin t → D) (d : ℕ),
      fits k t (fun x => out t a b (view x)) d → fits L t (out t a b) (d + c) := by
    intro t a b d ⟨ask, readout, bias, hok⟩
    let ask1 : Fin c → ℕ → D := fun i _ => phi i
    let ask2 : Fin d → ℕ → D := fun j tr => (ask j tr).comp T
    let askFull : Fin (c + d) → ℕ → D := fun j tr =>
      if h : j.val < c then ask1 ⟨j.val, h⟩ tr
      else ask2 ⟨j.val - c, by omega⟩ (tr % 2 ^ (j.val - c))
    let askDC : Fin (d + c) → ℕ → D := fun j tr => askFull (Fin.cast (Nat.add_comm d c) j) tr
    have hrun_cast : ∀ y : V, runTree askDC y = runTree askFull y := by
      intro y
      unfold runTree
      have heq : (List.finRange (d + c)).map (Fin.cast (Nat.add_comm d c)) = List.finRange (c + d) := by
        apply List.ext_getElem (by simp; omega)
        intro i h1 h2; simp
      rw [← heq, List.foldl_map]
    let readout' : ℕ → Fin t → D := fun tr j =>
      let tr0 := tr / 2 ^ d
      let tr1 := tr % 2 ^ d
      let v0 := cosetRep tr0
      (readout tr1 j).comp T +
        (a j v0) • ((b j).comp ((viewMap k L hk start).comp T)) +
        (b j v0) • ((a j).comp ((viewMap k L hk start).comp T))
    let bias' : ℕ → Fin t → F := fun tr j =>
      let tr0 := tr / 2 ^ d
      let tr1 := tr % 2 ^ d
      let v0 := cosetRep tr0
      bias tr1 j + a j v0 * b j v0
    refine ⟨askDC, readout', bias', ?_⟩
    intro y j
    have hrun1 : runTree askDC y = runTree ask1 y * 2 ^ d + runTree ask2 y := by
      rw [hrun_cast y]
      exact runTree_append ask1 ask2 y
    have hrun2 : runTree ask2 y = runTree ask (T y) := rfl
    have hlt2 : runTree ask (T y) < 2 ^ d := runTree_lt ask (T y)
    have hdiv : (runTree askDC y) / 2 ^ d = runTree ask1 y := by
      rw [hrun1, hrun2, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt hlt2, Nat.zero_add]
    have hmod : (runTree askDC y) % 2 ^ d = runTree ask (T y) := by
      rw [hrun1, hrun2, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hlt2]
    have hy := hdecomp y
    have hT := hok (T y) j
    dsimp only at hT
    rw [hview_eq (T y)] at hT
    change out t a b y j = readout' (runTree askDC y) j y + bias' (runTree askDC y) j
    have hrhs : readout' (runTree askDC y) j y + bias' (runTree askDC y) j =
        readout (runTree ask (T y)) j (T y) +
        a j (cosetRep (runTree ask1 y)) * b j (viewMap k L hk start (T y)) +
        b j (cosetRep (runTree ask1 y)) * a j (viewMap k L hk start (T y)) +
        (bias (runTree ask (T y)) j + a j (cosetRep (runTree ask1 y)) * b j (cosetRep (runTree ask1 y))) := by
      dsimp only [readout', bias']
      rw [hdiv, hmod]
      rfl
    rw [hrhs]
    have hT' : a j (viewMap k L hk start (T y)) * b j (viewMap k L hk start (T y)) =
        readout (runTree ask (T y)) j (T y) + bias (runTree ask (T y)) j := hT
    dsimp only [out]
    conv_lhs => rw [hy]
    simp only [map_add]
    calc (a j (viewMap k L hk start (T y)) + a j (cosetRep (runTree ask1 y))) *
            (b j (viewMap k L hk start (T y)) + b j (cosetRep (runTree ask1 y)))
        = a j (viewMap k L hk start (T y)) * b j (viewMap k L hk start (T y)) +
            a j (cosetRep (runTree ask1 y)) * b j (viewMap k L hk start (T y)) +
            b j (cosetRep (runTree ask1 y)) * a j (viewMap k L hk start (T y)) +
            a j (cosetRep (runTree ask1 y)) * b j (cosetRep (runTree ask1 y)) := by ring
      _ = readout (runTree ask (T y)) j (T y) + bias (runTree ask (T y)) j +
            a j (cosetRep (runTree ask1 y)) * b j (viewMap k L hk start (T y)) +
            b j (cosetRep (runTree ask1 y)) * a j (viewMap k L hk start (T y)) +
            a j (cosetRep (runTree ask1 y)) * b j (cosetRep (runTree ask1 y)) := by rw [hT']
      _ = _ := by ring
  constructor
  · intro t a b d
    constructor
    · rintro ⟨ask, readout, bias, hok⟩
      let ask' : Fin d → ℕ → W →ₗ[F] F := fun j tr => (ask j tr).comp (viewMap k L hk start)
      let readout' : ℕ → Fin t → W →ₗ[F] F := fun tr j => (readout tr j).comp (viewMap k L hk start)
      refine ⟨ask', readout', bias, ?_⟩
      intro x j
      have hrun : runTree ask' x = runTree ask (view x) := by
        rw [hview_eq x]; rfl
      change out t a b (view x) j = readout' (runTree ask' x) j x + bias (runTree ask' x) j
      rw [hrun]
      simpa only [readout', LinearMap.comp_apply, hview_eq x, runTree] using hok (view x) j
    · exact hback t a b d
  · let a : Fin (c * L) → D := fun j =>
      phi ⟨j.val / L, (Nat.div_lt_iff_lt_mul hL).mpr j.isLt⟩
    let b : Fin (c * L) → D := fun j =>
      LinearMap.proj ⟨j.val % L, Nat.mod_lt j.val hL⟩
    have hzero : ∀ x j, out (c * L) a b (view x) j = 0 := by
      intro x j
      dsimp only [out, a]
      rw [hview_eq x, hphi_view _ x, zero_mul]
    refine ⟨a, b, hzero, ?_⟩
    intro d
    constructor
    · rintro ⟨ask, readout, bias, hok⟩
      by_contra hlt
      have hdc : d < c := by omega
      let K : Submodule F V := ⨅ s : Fin d, LinearMap.ker (ask s 0)
      have hdimK : L - d ≤ Module.finrank F K := finrank_iInf_ker_ge (fun s => ask s 0)
      have hrun0 : ∀ y ∈ K, runTree ask y = 0 := by
        intro y hy
        apply runTree_eq_zero
        intro s
        simp only [K, Submodule.mem_iInf, LinearMap.mem_ker] at hy
        exact hy s
      have hbias0 : ∀ j : Fin (c * L), bias 0 j = 0 := by
        intro j
        have h0 := hok 0 j
        have hr0 : runTree ask 0 = 0 := hrun0 0 (Submodule.zero_mem K)
        change out (c * L) a b 0 j = readout (runTree ask 0) j 0 + bias (runTree ask 0) j at h0
        rw [hr0] at h0
        simp only [out, map_zero, mul_zero, zero_add] at h0
        exact h0.symm
      have hlin : ∀ y ∈ K, ∀ j : Fin (c * L), a j y * b j y = readout 0 j y := by
        intro y hy j
        have h1 := hok y j
        change out (c * L) a b y j = readout (runTree ask y) j y + bias (runTree ask y) j at h1
        rw [hrun0 y hy, hbias0 j, add_zero] at h1
        exact h1
      have hr_pos : 1 ≤ min L (if k % 3 = 0 then k - 2 else k) := by
        by_cases h3 : k % 3 = 0
        · simp only [h3, ↓reduceIte]; omega
        · simp only [h3, ↓reduceIte]; omega
      have hdimR : Module.finrank F (LinearMap.range (viewMap k L hk start)) =
          min L (if k % 3 = 0 then k - 2 else k) := finrank_range_viewMap k L hk start
      have hnotle : ¬ (K ≤ LinearMap.range (viewMap k L hk start)) := by
        intro hle
        have h1 := Submodule.finrank_mono hle
        rw [hdimR] at h1
        have : L - d > min L (if k % 3 = 0 then k - 2 else k) := by dsimp [c] at hdc; omega
        omega
      have hex_u : ∃ u ∈ K, u ∉ LinearMap.range (viewMap k L hk start) := by
        by_contra hall
        push Not at hall
        exact hnotle hall
      obtain ⟨u, huK, huR⟩ := hex_u
      have hex_p : ∃ p : Fin c, phi p u ≠ 0 := by
        by_contra hall
        push Not at hall
        exact huR ((hphi_zero u).mp hall)
      obtain ⟨p, hp⟩ := hex_p
      have hp1 : phi p u = 1 := by
        generalize hval : phi p u = v0 at hp ⊢
        fin_cases v0
        · exact absurd rfl hp
        · rfl
      have hK_le_span : K ≤ Submodule.span F {u} := by
        intro v hvK
        rw [Submodule.mem_span_singleton]
        refine ⟨phi p v, ?_⟩
        funext q
        let idx : Fin (c * L) := ⟨p.val * L + q.val, by
          have h1 : p.val + 1 ≤ c := p.isLt
          have h2 : (p.val + 1) * L ≤ c * L := Nat.mul_le_mul_right L h1
          have h3 : (p.val + 1) * L = p.val * L + L := by ring
          have := q.isLt; omega⟩
        have ha_idx : a idx = phi p := by
          dsimp only [a, idx]
          congr 1; apply Fin.ext; dsimp
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt q.isLt, Nat.zero_add]
        have hb_idx : b idx = LinearMap.proj q := by
          dsimp only [b, idx]
          congr 1; apply Fin.ext; dsimp
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt q.isLt]
        have hsum := hlin (u + v) (Submodule.add_mem K huK hvK) idx
        have hu' := hlin u huK idx
        have hv' := hlin v hvK idx
        rw [map_add (readout 0 idx), ← hu', ← hv'] at hsum
        rw [ha_idx, hb_idx] at hsum
        simp only [map_add, hp1] at hsum
        change (1 + phi p v) * (u q + v q) = 1 * u q + phi p v * v q at hsum
        have hcross : v q + phi p v * u q = 0 := by
          calc v q + phi p v * u q
              = (1 + phi p v) * (u q + v q) - (1 * u q + phi p v * v q) := by ring
            _ = 0 := by rw [hsum, sub_self]
        change phi p v * u q = v q
        exact (zmod2_eq_of_add_eq_zero hcross).symm
      have hdimK_le1 : Module.finrank F K ≤ 1 := by
        calc Module.finrank F K
            ≤ Module.finrank F (Submodule.span F ({u} : Set V)) := Submodule.finrank_mono hK_le_span
          _ ≤ 1 := le_trans (finrank_span_le_card ({u} : Set V)) (by simp)
      have hdimK_ge2 : 2 ≤ L - d := by dsimp [c] at hdc; omega
      omega
    · intro hcd
      have h0 : fits k (c * L) (fun x => out (c * L) a b (view x)) (d - c) := by
        refine ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, ?_⟩
        intro x j
        simp [hzero x j]
      have h1 := hback (c * L) a b (d - c) h0
      have heq : d - c + c = d := Nat.sub_add_cancel hcd
      rwa [heq] at h1
