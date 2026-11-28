import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33677_aux

open scoped BigOperators

abbrev F := ZMod 2

abbrev Word (t : ℕ) := Fin (6 * t) → F

abbrev Lane (t : ℕ) := Fin (3 * t) → F

def ixn (n : ℕ) (hn : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

def rotn (n : ℕ) (hn : 0 < n) (s : ℕ) (w : Fin n → F) (i : Fin n) : F :=
  w (ixn n hn (i.val + n - s % n))

def mixn (n : ℕ) (hn : 0 < n) (w : Fin n → F) (i : Fin n) : F :=
  let old := rotn n hn 3 w
  old i + old (ixn n hn (i.val + 2)) + old (ixn n hn (i.val + n - 2))

def outn (n : ℕ) (hn : 0 < n) (name c raw : Fin n → F) (i : Fin n) : F :=
  let old := rotn n hn 3 raw + name
  let y := fun j : Fin n => old j + old (ixn n hn (j.val + 2)) + old (ixn n hn (j.val + n - 2))
  y i + (1 + y (ixn n hn (i.val + 1))) * y (ixn n hn (i.val + 2)) + rotn n hn 4 raw i + c i

noncomputable def runn (n h : ℕ) (ask : Fin h → ℕ → (Fin n → F) →ₗ[F] F) (w : Fin n → F) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (List.finRange h).foldl (fun z i => 2 * z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)

def nx {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : Fin (3 * t) :=
  ⟨(i.val + 1) % (3 * t), Nat.mod_lt _ (by omega)⟩

def pv {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : Fin (3 * t) :=
  ⟨(i.val + 3 * t - 1) % (3 * t), Nat.mod_lt _ (by omega)⟩

def synd (n : ℕ) : (Fin n → F) →ₗ[F] (Fin 2 → F) where
  toFun x e := ∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0
  map_add' x y := by
    ext e
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp
  map_smul' c x := by
    ext e
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp

def codeSub (t : ℕ) : Submodule F (Lane t) := LinearMap.ker (synd (3 * t))

def hitsAt {t : ℕ} (ht : 0 < t) (x y : Lane t) : Prop :=
  ∀ i : Fin (3 * t), x i * y i = 0 ∧ x (nx ht i) * y i = 0

noncomputable def rectHits {t : ℕ} (ht : 0 < t) (P Q : Submodule F (Lane t)) : ℕ :=
  Nat.card {z : P × Q // hitsAt ht z.1.1 z.2.1}

def numVal (t : ℕ) : ℕ :=
  if t = 2 then 416 else if t = 3 then 348 else if t = 4 then 354 else 353

def siteVal (t : ℕ) (j : Fin (3 * t - 5)) : ℕ :=
  if t = 3 then (if j.val < 2 then j.val + 4 else j.val + 5)
  else if j.val = 0 then 2
  else if j.val < 3 then j.val + 3
  else if j.val < 5 then j.val + 4
  else j.val + 5

lemma F_cases (z : F) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma z2_add_self (x : F) : x + x = 0 := CharTwo.add_self_eq_zero x

lemma z2_sub_eq_add (x y : F) : x - y = x + y := CharTwo.sub_eq_add x y

lemma ixn_val (n : ℕ) (hn : 0 < n) (j : ℕ) : (ixn n hn j).val = j % n := rfl

lemma ixn_self (n : ℕ) (hn : 0 < n) (i : Fin n) : ixn n hn i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

lemma ixn_add_n (n : ℕ) (hn : 0 < n) (j : ℕ) : ixn n hn (j + n) = ixn n hn j := by
  apply Fin.ext
  exact Nat.add_mod_right j n

lemma nx_val {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) :
    (nx ht i).val = if i.val + 1 = 3 * t then 0 else i.val + 1 := by
  change (i.val + 1) % (3 * t) = _
  split_ifs with h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

lemma pv_val {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) :
    (pv ht i).val = if i.val = 0 then 3 * t - 1 else i.val - 1 := by
  change (i.val + 3 * t - 1) % (3 * t) = _
  split_ifs with h
  · rw [h, zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · have he : i.val + 3 * t - 1 = (i.val - 1) + 3 * t := by omega
    rw [he, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

lemma nx_pv {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : nx ht (pv ht i) = i := by
  apply Fin.ext
  have hi := i.isLt
  rw [nx_val, pv_val]
  by_cases h : i.val = 0
  · simp only [h, ↓reduceIte]
    have h1 : 3 * t - 1 + 1 = 3 * t := by omega
    simp [h1]
  · simp only [h, ↓reduceIte]
    have h1 : i.val - 1 + 1 ≠ 3 * t := by omega
    simp only [h1, ↓reduceIte]
    omega

lemma pv_nx {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : pv ht (nx ht i) = i := by
  apply Fin.ext
  have hi := i.isLt
  rw [pv_val, nx_val]
  by_cases h : i.val + 1 = 3 * t
  · simp only [h, ↓reduceIte]
    omega
  · simp only [h, ↓reduceIte]
    have h1 : i.val + 1 ≠ 0 := by omega
    simp only [h1, ↓reduceIte]
    omega

lemma nx_inj {t : ℕ} (ht : 0 < t) : Function.Injective (nx ht) := by
  intro a b h
  have := congrArg (pv ht) h
  rwa [pv_nx, pv_nx] at this

lemma nx_surj {t : ℕ} (ht : 0 < t) : Function.Surjective (nx ht) :=
  fun i => ⟨pv ht i, nx_pv ht i⟩

lemma synd_single {n : ℕ} (j : Fin n) (c : F) (e : Fin 2) :
    synd n (Pi.single j c) e = if j.val % 3 = e.val ∨ j.val % 3 = 2 then c else 0 := by
  change (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then Pi.single j c i else 0) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ h
    simp [Pi.single_eq_of_ne h]
  · simp

lemma synd_surj {n : ℕ} (hn : 2 ≤ n) : Function.Surjective (synd n) := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  intro y
  refine ⟨Pi.single a (y 0) + Pi.single b (y 1), ?_⟩
  rw [map_add]
  ext e
  fin_cases e <;> simp [synd_single, a, b]

lemma codeDimension {n : ℕ} (hn : 2 ≤ n) :
    Module.finrank F (LinearMap.ker (synd n)) + 2 = n := by
  have h := LinearMap.finrank_range_add_finrank_ker (synd n)
  rw [LinearMap.range_eq_top.mpr (synd_surj hn)] at h
  simp at h
  omega

lemma codeSub_finrank {t : ℕ} (ht : 0 < t) : Module.finrank F (codeSub t) = 3 * t - 2 := by
  have h := codeDimension (n := 3 * t) (by omega)
  change Module.finrank F (codeSub t) + 2 = 3 * t at h
  omega

def triLane {t : ℕ} (ht : 0 < t) : Lane t →ₗ[F] Lane t where
  toFun u i := u i + u (nx ht i) + u (pv ht i)
  map_add' u v := by
    ext i
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    ext i
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

lemma triLane_mem_codeSub {t : ℕ} (ht : 0 < t) (u : Lane t) : triLane ht u ∈ codeSub t := by
  change synd (3 * t) (triLane ht u) = 0
  ext e
  let p : Fin (3 * t) → Prop := fun i => i.val % 3 = e.val ∨ i.val % 3 = 2
  change (∑ i : Fin (3 * t),
    if p i then u i + u (nx ht i) + u (pv ht i) else 0) = 0
  have hsplit : ∀ i : Fin (3 * t), (if p i then u i + u (nx ht i) + u (pv ht i) else (0 : F)) =
      (if p i then u i else 0) + (if p i then u (nx ht i) else 0) + (if p i then u (pv ht i) else 0) := by
    intro i
    split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_add_distrib]
  have h1 : (∑ i : Fin (3 * t), if p i then u (nx ht i) else 0) =
      ∑ j : Fin (3 * t), if p (pv ht j) then u j else 0 := by
    refine Fintype.sum_equiv ⟨nx ht, pv ht, pv_nx ht, nx_pv ht⟩ _ _ fun i => ?_
    simp [pv_nx]
  have h2 : (∑ i : Fin (3 * t), if p i then u (pv ht i) else 0) =
      ∑ j : Fin (3 * t), if p (nx ht j) then u j else 0 := by
    refine Fintype.sum_equiv ⟨pv ht, nx ht, nx_pv ht, pv_nx ht⟩ _ _ fun i => ?_
    simp [nx_pv]
  rw [h1, h2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  have hjlt := j.isLt
  have hm : (nx ht j).val % 3 = (j.val + 1) % 3 := by
    rw [nx_val]
    split_ifs with h
    · omega
    · rfl
  have hpv : (pv ht j).val % 3 = (j.val + 2) % 3 := by
    rw [pv_val]
    split_ifs with h
    · omega
    · omega
  have hev : e.val = 0 ∨ e.val = 1 := by omega
  have hjm : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
  have h1m : (j.val + 1) % 3 = (j.val % 3 + 1) % 3 := by omega
  have h2m : (j.val + 2) % 3 = (j.val % 3 + 2) % 3 := by omega
  rcases hev with he | he <;> rcases hjm with hj | hj | hj <;>
    simp [p, hm, hpv, h1m, h2m, he, hj, z2_add_self]

lemma ker_triLane_card_le {t : ℕ} (ht : 0 < t) :
    Nat.card (LinearMap.ker (triLane ht)) ≤ 4 := by
  have hstep : ∀ u ∈ LinearMap.ker (triLane ht), ∀ (k : ℕ) (hk : k + 2 < 3 * t),
      u ⟨k + 2, by omega⟩ = u ⟨k + 1, by omega⟩ + u ⟨k, by omega⟩ := by
    intro u hu k hk
    have h0 := congrFun hu ⟨k + 1, by omega⟩
    change u ⟨k + 1, by omega⟩ + u (nx ht ⟨k + 1, by omega⟩) + u (pv ht ⟨k + 1, by omega⟩) = 0 at h0
    have hnx : nx ht ⟨k + 1, by omega⟩ = ⟨k + 2, by omega⟩ := by
      apply Fin.ext
      rw [nx_val]
      dsimp only
      rw [if_neg (by omega)]
    have hpv : pv ht ⟨k + 1, by omega⟩ = ⟨k, by omega⟩ := by
      apply Fin.ext
      rw [pv_val]
      dsimp only
      rw [if_neg (by omega)]
      omega
    rw [hnx, hpv] at h0
    have h3 : u ⟨k + 2, by omega⟩ = -(u ⟨k + 1, by omega⟩ + u ⟨k, by omega⟩) := by
      apply eq_neg_of_add_eq_zero_left
      linear_combination h0
    rwa [CharTwo.neg_eq] at h3
  have hinj : Function.Injective (fun u : LinearMap.ker (triLane ht) =>
      (u.1 ⟨0, by omega⟩, u.1 ⟨1, by omega⟩)) := by
    intro u v huv
    apply Subtype.ext
    funext i
    rcases i with ⟨m, hm⟩
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm2 : m < 2
      · interval_cases m
        · exact congrArg Prod.fst huv
        · exact congrArg Prod.snd huv
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
        rw [hstep u.1 u.2 k hm, hstep v.1 v.2 k hm,
          ih (k + 1) (by omega) (by omega), ih k (by omega) (by omega)]
  have hc := Nat.card_le_card_of_injective _ hinj
  have h4 : Nat.card (F × F) = 4 := by
    rw [Nat.card_prod, Nat.card_zmod]
  rwa [h4] at hc

lemma triLane_range_eq_codeSub {t : ℕ} (ht : 0 < t) :
    LinearMap.range (triLane ht) = codeSub t := by
  have hle : LinearMap.range (triLane ht) ≤ codeSub t := by
    rintro _ ⟨u, rfl⟩
    exact triLane_mem_codeSub ht u
  have hker_le : Module.finrank F (LinearMap.ker (triLane ht)) ≤ 2 := by
    have hc := ker_triLane_card_le ht
    rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_zmod] at hc
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4] at hc
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hc
  have hrk := LinearMap.finrank_range_add_finrank_ker (triLane ht)
  rw [Module.finrank_fin_fun] at hrk
  have hcd := codeSub_finrank ht
  exact Submodule.eq_of_le_of_finrank_eq hle (le_antisymm (Submodule.finrank_mono hle) (by omega))

lemma triLane_ker_finrank {t : ℕ} (ht : 0 < t) :
    Module.finrank F (LinearMap.ker (triLane ht)) = 2 := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (triLane ht)
  rw [triLane_range_eq_codeSub ht, codeSub_finrank ht, Module.finrank_fin_fun] at hrk
  omega

def rawShift {t : ℕ} (ht : 0 < t) : Word t ≃ₗ[F] Lane t × Lane t where
  toFun w :=
    (fun i => rotn (6 * t) (by omega) 3 w ⟨2 * i.val, by omega⟩,
     fun i => rotn (6 * t) (by omega) 3 w ⟨2 * i.val + 1, by omega⟩)
  invFun z j :=
    let k := ixn (6 * t) (by omega) (j.val + 3)
    if k.val % 2 = 0 then z.1 ⟨k.val / 2, by have := k.isLt; omega⟩
    else z.2 ⟨k.val / 2, by have := k.isLt; omega⟩
  left_inv w := by
    funext j
    have hjlt := j.isLt
    have h6 : 3 % (6 * t) = 3 := Nat.mod_eq_of_lt (by omega)
    dsimp only
    split_ifs with hp
    · dsimp only [rotn]
      rw [h6]
      refine congrArg w (Fin.ext ?_)
      dsimp only [ixn]
      have h2k : 2 * (((j.val + 3) % (6 * t)) / 2) = (j.val + 3) % (6 * t) := by
        dsimp only [ixn] at hp; omega
      rw [h2k]
      by_cases hj : j.val + 3 < 6 * t
      · rw [Nat.mod_eq_of_lt hj]
        have : j.val + 3 + 6 * t - 3 = j.val + 6 * t := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hjlt]
      · have hmod : (j.val + 3) % (6 * t) = j.val + 3 - 6 * t := by
          have h1 : j.val + 3 = (j.val + 3 - 6 * t) + 6 * t := by omega
          conv_lhs => rw [h1]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        have : j.val + 3 - 6 * t + 6 * t - 3 = j.val := by omega
        rw [this, Nat.mod_eq_of_lt hjlt]
    · dsimp only [rotn]
      rw [h6]
      refine congrArg w (Fin.ext ?_)
      dsimp only [ixn]
      have h2k : 2 * (((j.val + 3) % (6 * t)) / 2) + 1 = (j.val + 3) % (6 * t) := by
        dsimp only [ixn] at hp; omega
      rw [h2k]
      by_cases hj : j.val + 3 < 6 * t
      · rw [Nat.mod_eq_of_lt hj]
        have : j.val + 3 + 6 * t - 3 = j.val + 6 * t := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hjlt]
      · have hmod : (j.val + 3) % (6 * t) = j.val + 3 - 6 * t := by
          have h1 : j.val + 3 = (j.val + 3 - 6 * t) + 6 * t := by omega
          conv_lhs => rw [h1]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        have : j.val + 3 - 6 * t + 6 * t - 3 = j.val := by omega
        rw [this, Nat.mod_eq_of_lt hjlt]
  right_inv z := by
    have h6 : 3 % (6 * t) = 3 := Nat.mod_eq_of_lt (by omega)
    apply Prod.ext <;> funext i
    · have hi := i.isLt
      dsimp only [rotn]
      rw [h6]
      have hkval : (ixn (6 * t) (by omega) ((ixn (6 * t) (by omega) (2 * i.val + 6 * t - 3)).val + 3)).val =
          2 * i.val := by
        dsimp only [ixn]
        rw [Nat.mod_add_mod]
        have : 2 * i.val + 6 * t - 3 + 3 = 2 * i.val + 6 * t := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      split_ifs with hp
      · exact congrArg z.1 (Fin.ext (by dsimp only; rw [hkval]; omega))
      · exfalso
        rw [hkval] at hp
        omega
    · have hi := i.isLt
      dsimp only [rotn]
      rw [h6]
      have hkval : (ixn (6 * t) (by omega) ((ixn (6 * t) (by omega) (2 * i.val + 1 + 6 * t - 3)).val + 3)).val =
          2 * i.val + 1 := by
        dsimp only [ixn]
        rw [Nat.mod_add_mod]
        have : 2 * i.val + 1 + 6 * t - 3 + 3 = 2 * i.val + 1 + 6 * t := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      split_ifs with hp
      · exfalso
        rw [hkval] at hp
        omega
      · exact congrArg z.2 (Fin.ext (by dsimp only; rw [hkval]; omega))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evenLane {t : ℕ} (ht : 0 < t) : Word t →ₗ[F] Lane t :=
  (triLane ht).comp ((LinearMap.fst F (Lane t) (Lane t)).comp (rawShift ht).toLinearMap)

def oddLane {t : ℕ} (ht : 0 < t) : Word t →ₗ[F] Lane t :=
  (triLane ht).comp ((LinearMap.snd F (Lane t) (Lane t)).comp (rawShift ht).toLinearMap)

lemma evenLane_eq_mixn {t : ℕ} (ht : 0 < t) (w : Word t) (i : Fin (3 * t)) :
    evenLane ht w i = mixn (6 * t) (by omega) w ⟨2 * i.val, by omega⟩ := by
  have hi := i.isLt
  change rotn (6 * t) (by omega) 3 w ⟨2 * i.val, by omega⟩ +
      rotn (6 * t) (by omega) 3 w ⟨2 * (nx ht i).val, by omega⟩ +
      rotn (6 * t) (by omega) 3 w ⟨2 * (pv ht i).val, by omega⟩ =
    rotn (6 * t) (by omega) 3 w ⟨2 * i.val, by omega⟩ +
      rotn (6 * t) (by omega) 3 w (ixn (6 * t) (by omega) (2 * i.val + 2)) +
      rotn (6 * t) (by omega) 3 w (ixn (6 * t) (by omega) (2 * i.val + 6 * t - 2))
  congr 1
  · congr 1
    congr 1
    apply Fin.ext
    dsimp only [ixn]
    rw [nx_val]
    split_ifs with h
    · have : 2 * i.val + 2 = 6 * t := by omega
      rw [this, Nat.mod_self, mul_zero]
    · exact (Nat.mod_eq_of_lt (by omega)).symm
  · congr 1
    apply Fin.ext
    dsimp only [ixn]
    rw [pv_val]
    split_ifs with h
    · rw [h, mul_zero, zero_add]
      have : 2 * (3 * t - 1) = 6 * t - 2 := by omega
      rw [this]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    · have : 2 * i.val + 6 * t - 2 = 2 * (i.val - 1) + 6 * t := by omega
      rw [this, Nat.add_mod_right]
      exact (Nat.mod_eq_of_lt (by omega)).symm

lemma oddLane_eq_mixn {t : ℕ} (ht : 0 < t) (w : Word t) (i : Fin (3 * t)) :
    oddLane ht w i = mixn (6 * t) (by omega) w ⟨2 * i.val + 1, by omega⟩ := by
  have hi := i.isLt
  change rotn (6 * t) (by omega) 3 w ⟨2 * i.val + 1, by omega⟩ +
      rotn (6 * t) (by omega) 3 w ⟨2 * (nx ht i).val + 1, by omega⟩ +
      rotn (6 * t) (by omega) 3 w ⟨2 * (pv ht i).val + 1, by omega⟩ =
    rotn (6 * t) (by omega) 3 w ⟨2 * i.val + 1, by omega⟩ +
      rotn (6 * t) (by omega) 3 w (ixn (6 * t) (by omega) (2 * i.val + 1 + 2)) +
      rotn (6 * t) (by omega) 3 w (ixn (6 * t) (by omega) (2 * i.val + 1 + 6 * t - 2))
  congr 1
  · congr 1
    congr 1
    apply Fin.ext
    dsimp only [ixn]
    rw [nx_val]
    split_ifs with h
    · have : 2 * i.val + 1 + 2 = 1 + 6 * t := by omega
      rw [this, Nat.add_mod_right, mul_zero, zero_add]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    · exact (Nat.mod_eq_of_lt (by omega)).symm
  · congr 1
    apply Fin.ext
    dsimp only [ixn]
    rw [pv_val]
    split_ifs with h
    · rw [h, mul_zero, zero_add]
      have : 2 * (3 * t - 1) + 1 = 1 + 6 * t - 2 := by omega
      rw [this]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    · have : 2 * i.val + 1 + 6 * t - 2 = (2 * (i.val - 1) + 1) + 6 * t := by omega
      rw [this, Nat.add_mod_right]
      exact (Nat.mod_eq_of_lt (by omega)).symm

lemma evenLane_mem_codeSub {t : ℕ} (ht : 0 < t) (w : Word t) : evenLane ht w ∈ codeSub t :=
  triLane_mem_codeSub ht _

lemma oddLane_mem_codeSub {t : ℕ} (ht : 0 < t) (w : Word t) : oddLane ht w ∈ codeSub t :=
  triLane_mem_codeSub ht _

lemma lanes_surj {t : ℕ} (ht : 0 < t) (u v : Lane t) (hu : u ∈ codeSub t) (hv : v ∈ codeSub t) :
    ∃ w : Word t, evenLane ht w = u ∧ oddLane ht w = v := by
  rw [← triLane_range_eq_codeSub ht] at hu hv
  obtain ⟨u0, hu0⟩ := hu
  obtain ⟨v0, hv0⟩ := hv
  refine ⟨(rawShift ht).symm (u0, v0), ?_, ?_⟩
  · change triLane ht ((rawShift ht ((rawShift ht).symm (u0, v0))).1) = u
    rw [(rawShift ht).apply_symm_apply]
    exact hu0
  · change triLane ht ((rawShift ht ((rawShift ht).symm (u0, v0))).2) = v
    rw [(rawShift ht).apply_symm_apply]
    exact hv0

lemma ker_lanes_finrank {t : ℕ} (ht : 0 < t) :
    Module.finrank F (LinearMap.ker ((evenLane ht).prod (oddLane ht))) = 4 := by
  let e : LinearMap.ker ((evenLane ht).prod (oddLane ht)) ≃ₗ[F]
      LinearMap.ker (triLane ht) × LinearMap.ker (triLane ht) :=
    { toFun := fun w =>
        (⟨(rawShift ht w.1).1, by
          have hw := w.2
          rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero] at hw
          exact hw.1⟩,
         ⟨(rawShift ht w.1).2, by
          have hw := w.2
          rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero] at hw
          exact hw.2⟩)
      invFun := fun z =>
        ⟨(rawShift ht).symm (z.1.1, z.2.1), by
          rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero]
          constructor
          · change triLane ht ((rawShift ht ((rawShift ht).symm (z.1.1, z.2.1))).1) = 0
            rw [(rawShift ht).apply_symm_apply]
            exact z.1.2
          · change triLane ht ((rawShift ht ((rawShift ht).symm (z.1.1, z.2.1))).2) = 0
            rw [(rawShift ht).apply_symm_apply]
            exact z.2.2⟩
      left_inv := fun w => Subtype.ext ((rawShift ht).symm_apply_apply w.1)
      right_inv := fun z => by
        apply Prod.ext <;> apply Subtype.ext
        · exact congrArg Prod.fst ((rawShift ht).apply_symm_apply (z.1.1, z.2.1))
        · exact congrArg Prod.snd ((rawShift ht).apply_symm_apply (z.1.1, z.2.1))
      map_add' := fun _ _ => by apply Prod.ext <;> apply Subtype.ext <;> simp
      map_smul' := fun _ _ => by apply Prod.ext <;> apply Subtype.ext <;> simp }
  rw [e.finrank_eq, Module.finrank_prod, triLane_ker_finrank ht]

def Qw {t : ℕ} (ht : 0 < t) : Lane t →ₗ[F] Lane t →ₗ[F] Word t where
  toFun u :=
    { toFun := fun v i =>
        if i.val % 2 = 0 then
          u (nx ht ⟨i.val / 2, by have := i.isLt; omega⟩) * v ⟨i.val / 2, by have := i.isLt; omega⟩
        else
          u (nx ht ⟨i.val / 2, by have := i.isLt; omega⟩) * v (nx ht ⟨i.val / 2, by have := i.isLt; omega⟩)
      map_add' := fun v1 v2 => by
        funext i
        simp only [Pi.add_apply]
        split_ifs <;> ring
      map_smul' := fun c v => by
        funext i
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> ring }
  map_add' u1 u2 := by
    apply LinearMap.ext; intro v; funext i
    simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c u := by
    apply LinearMap.ext; intro v; funext i
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul]
    split_ifs <;> ring

lemma Qw_lanes {t : ℕ} (ht : 0 < t) (w : Word t) (i : Fin (6 * t)) :
    Qw ht (evenLane ht w) (oddLane ht w) i =
      mixn (6 * t) (by omega) w (ixn (6 * t) (by omega) (i.val + 1)) *
      mixn (6 * t) (by omega) w (ixn (6 * t) (by omega) (i.val + 2)) := by
  have hi := i.isLt
  dsimp only [Qw, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hp : i.val % 2 = 0
  · simp only [hp, ↓reduceIte]
    rw [evenLane_eq_mixn, oddLane_eq_mixn, mul_comm]
    congr 1
    · congr 1
      apply Fin.ext
      dsimp only [ixn]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · congr 1
      apply Fin.ext
      dsimp only [ixn]
      rw [nx_val]
      dsimp only
      split_ifs with h
      · have : i.val + 2 = 6 * t := by omega
        rw [this, Nat.mod_self, mul_zero]
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega
  · simp only [hp, ↓reduceIte]
    rw [evenLane_eq_mixn, oddLane_eq_mixn]
    congr 1
    · congr 1
      apply Fin.ext
      dsimp only [ixn]
      rw [nx_val]
      dsimp only
      split_ifs with h
      · have : i.val + 1 = 6 * t := by omega
        rw [this, Nat.mod_self, mul_zero]
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega
    · congr 1
      apply Fin.ext
      dsimp only [ixn]
      rw [nx_val]
      dsimp only
      split_ifs with h
      · have : i.val + 2 = 1 + 6 * t := by omega
        rw [this, Nat.add_mod_right, mul_zero, zero_add, Nat.mod_eq_of_lt (by omega)]
      · rw [Nat.mod_eq_of_lt (by omega)]
        omega

lemma Qw_eq_zero_iff {t : ℕ} (ht : 0 < t) (u v : Lane t) :
    Qw ht u v = 0 ↔ hitsAt ht u v := by
  constructor
  · intro h j
    have h1 := congrFun h ⟨2 * j.val, by omega⟩
    have h2 := congrFun h ⟨2 * (pv ht j).val + 1, by omega⟩
    simp only [Qw, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1 h2
    have he1 : (2 * j.val) % 2 = 0 := Nat.mul_mod_right 2 j.val
    have ho2 : (2 * (pv ht j).val + 1) % 2 ≠ 0 := by omega
    simp only [he1, ho2, ↓reduceIte] at h1 h2
    have hj1 : (⟨2 * j.val / 2, by omega⟩ : Fin (3 * t)) = j := Fin.ext (by dsimp; omega)
    have hj2 : (⟨(2 * (pv ht j).val + 1) / 2, by omega⟩ : Fin (3 * t)) = pv ht j :=
      Fin.ext (by dsimp; omega)
    rw [hj1] at h1
    rw [hj2, nx_pv] at h2
    exact ⟨h2, h1⟩
  · intro h
    funext i
    simp only [Qw, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    split_ifs
    · exact (h ⟨i.val / 2, by have := i.isLt; omega⟩).2
    · exact (h (nx ht ⟨i.val / 2, by have := i.isLt; omega⟩)).1

def m0 {t : ℕ} (ht : 0 < t) (name : Word t) (j : Fin (6 * t)) : F :=
  name j + name (ixn (6 * t) (by omega) (j.val + 2)) + name (ixn (6 * t) (by omega) (j.val + 6 * t - 2))

lemma mixn_add {n : ℕ} (hn : 0 < n) (w1 w2 : Fin n → F) (i : Fin n) :
    mixn n hn (w1 + w2) i = mixn n hn w1 i + mixn n hn w2 i := by
  simp only [mixn, rotn, Pi.add_apply]
  ring

lemma mixn_smul {n : ℕ} (hn : 0 < n) (a : F) (w : Fin n → F) (i : Fin n) :
    mixn n hn (a • w) i = a * mixn n hn w i := by
  simp only [mixn, rotn, Pi.smul_apply, smul_eq_mul]
  ring

def Lbase {t : ℕ} (ht : 0 < t) (name : Word t) : Word t →ₗ[F] Word t where
  toFun w i :=
    mixn (6 * t) (by omega) w i +
    mixn (6 * t) (by omega) w (ixn (6 * t) (by omega) (i.val + 2)) +
    m0 ht name (ixn (6 * t) (by omega) (i.val + 1)) *
      mixn (6 * t) (by omega) w (ixn (6 * t) (by omega) (i.val + 2)) +
    m0 ht name (ixn (6 * t) (by omega) (i.val + 2)) *
      mixn (6 * t) (by omega) w (ixn (6 * t) (by omega) (i.val + 1)) +
    rotn (6 * t) (by omega) 4 w i
  map_add' w1 w2 := by
    funext i
    simp only [mixn_add, rotn, Pi.add_apply]
    ring
  map_smul' a w := by
    funext i
    simp only [mixn_smul, rotn, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

def cbase {t : ℕ} (ht : 0 < t) (name c : Word t) : Word t := fun i =>
  m0 ht name i + m0 ht name (ixn (6 * t) (by omega) (i.val + 2)) +
  m0 ht name (ixn (6 * t) (by omega) (i.val + 1)) * m0 ht name (ixn (6 * t) (by omega) (i.val + 2)) +
  c i

lemma outn_normal {t : ℕ} (ht : 0 < t) (name c w : Word t) :
    outn (6 * t) (by omega) name c w =
      Qw ht (evenLane ht w) (oddLane ht w) + Lbase ht name w + cbase ht name c := by
  funext i
  simp only [Pi.add_apply, Qw_lanes]
  simp only [outn, Lbase, cbase, m0, mixn, rotn, Pi.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
  ring

def hbit (x : F) : ℕ := if x = 0 then 0 else 1

lemma hbit_le (x : F) : hbit x ≤ 1 := by
  unfold hbit; split_ifs <;> omega

lemma hbit_eq_iff (x y : F) : hbit x = hbit y ↔ x - y = 0 := by
  revert x y; decide

lemma runn_succ (n h : ℕ) (ask : Fin (h + 1) → ℕ → (Fin n → F) →ₗ[F] F) (w : Fin n → F) :
    runn n (h + 1) ask w = 2 * runn n h (fun j => ask j.castSucc) w +
      hbit (ask (Fin.last h) (runn n h (fun j => ask j.castSucc) w) w) := by
  unfold runn hbit
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  congr

lemma runn_eq_iff (n h : ℕ) (ask : Fin h → ℕ → (Fin n → F) →ₗ[F] F) (w0 : Fin n → F) :
    ∃ p : Fin h → ℕ, ∀ w, runn n h ask w = runn n h ask w0 ↔ ∀ j, ask j (p j) (w - w0) = 0 := by
  induction h with
  | zero =>
    refine ⟨fun _ => 0, fun w => ⟨fun _ j => j.elim0, fun _ => rfl⟩⟩
  | succ h ih =>
    obtain ⟨p', hp'⟩ := ih (fun j => ask j.castSucc)
    refine ⟨@Fin.snoc h (fun _ => ℕ) p' (runn n h (fun j => ask j.castSucc) w0), fun w => ?_⟩
    rw [runn_succ, runn_succ, Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← hp' w]
    have hb1 := hbit_le (ask (Fin.last h) (runn n h (fun j => ask j.castSucc) w) w)
    have hb2 := hbit_le (ask (Fin.last h) (runn n h (fun j => ask j.castSucc) w0) w0)
    constructor
    · intro he
      have h1 : runn n h (fun j => ask j.castSucc) w = runn n h (fun j => ask j.castSucc) w0 := by
        omega
      refine ⟨h1, ?_⟩
      rw [h1] at he
      have h2 : hbit (ask (Fin.last h) (runn n h (fun j => ask j.castSucc) w0) w) =
          hbit (ask (Fin.last h) (runn n h (fun j => ask j.castSucc) w0) w0) := by omega
      rw [hbit_eq_iff, ← map_sub] at h2
      exact h2
    · rintro ⟨h1, h2⟩
      rw [h1]
      congr 1
      rw [hbit_eq_iff, ← map_sub]
      exact h2

lemma cell_coset (n h : ℕ) (ask : Fin h → ℕ → (Fin n → F) →ₗ[F] F) (w0 : Fin n → F) :
    ∃ K : Submodule F (Fin n → F),
      (∀ w, runn n h ask w = runn n h ask w0 ↔ w - w0 ∈ K) ∧
      n ≤ Module.finrank F K + h := by
  obtain ⟨p, hp⟩ := runn_eq_iff n h ask w0
  refine ⟨LinearMap.ker (LinearMap.pi (fun j => ask j (p j))), fun w => ?_, ?_⟩
  · rw [hp w, LinearMap.mem_ker]
    exact ⟨fun hj => funext hj, fun hj j => congrFun hj j⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi (fun j => ask j (p j)))
    have h2 : Module.finrank F (LinearMap.range (LinearMap.pi (fun j => ask j (p j)))) ≤ h := by
      have h3 := Submodule.finrank_le (LinearMap.range (LinearMap.pi (fun j => ask j (p j))))
      rwa [Module.finrank_fin_fun] at h3
    rw [Module.finrank_fin_fun] at h1
    omega

lemma pull_count {A T : Type*} [AddCommGroup A] [AddCommGroup T]
    [Module F A] [Module F T] [Finite A] [Finite T] (f : A →ₗ[F] T)
    (hs : Function.Surjective f) (P : T → Prop) :
    Nat.card {a : A // P (f a)} * Nat.card T = Nat.card A * Nat.card {t : T // P t} := by
  classical
  choose s h using hs
  let pack (p : T → Prop) : {a : A // p (f a)} ≃ {t : T // p t} × f.ker :=
    { toFun := fun a => (⟨f a.val, a.property⟩, ⟨a.val - s (f a.val), by simp [LinearMap.mem_ker, h]⟩)
      invFun := fun z => ⟨z.2.val + s z.1.val, by
        have hz : f z.2.val = 0 := z.2.property
        simpa [hz, h] using z.1.property⟩
      left_inv := by intro a; apply Subtype.ext; simp
      right_inv := by
        rintro ⟨t, k⟩
        have hz : f k.val = 0 := k.property
        apply Prod.ext <;> apply Subtype.ext <;> simp [hz, h] }
  have hp := Nat.card_congr (pack P)
  rw [Nat.card_prod] at hp
  have ht := Nat.card_congr (pack (fun _ => True))
  simp only [Nat.card_prod, Nat.card_subtype_true] at ht
  rw [hp, ht]
  ac_rfl

lemma fib_card_le {α β γ : Type*} [Finite α] [Finite β] [Finite γ] (S : α → β → Prop)
    (T : α → γ → Prop) (h : ∀ a, Nat.card {b // S a b} ≤ Nat.card {c // T a c}) :
    Nat.card {p : α × β // S p.1 p.2} ≤ Nat.card {p : α × γ // T p.1 p.2} := by
  classical
  have := Fintype.ofFinite α
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype S),
    Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype T), Nat.card_sigma, Nat.card_sigma]
  exact Finset.sum_le_sum (fun a _ => h a)

lemma fib_card_le2 {α β γ : Type*} [Finite α] [Finite β] [Finite γ] (S : β → α → Prop)
    (T : γ → α → Prop) (h : ∀ a, Nat.card {b // S b a} ≤ Nat.card {c // T c a}) :
    Nat.card {p : β × α // S p.1 p.2} ≤ Nat.card {p : γ × α // T p.1 p.2} := by
  have h1 := fib_card_le (fun a b => S b a) (fun a c => T c a) h
  have e1 : Nat.card {p : β × α // S p.1 p.2} = Nat.card {p : α × β // S p.2 p.1} :=
    Nat.card_congr ((Equiv.prodComm β α).subtypeEquiv (fun _ => Iff.rfl))
  have e2 : Nat.card {p : γ × α // T p.1 p.2} = Nat.card {p : α × γ // T p.2 p.1} :=
    Nat.card_congr ((Equiv.prodComm γ α).subtypeEquiv (fun _ => Iff.rfl))
  rw [e1, e2]
  exact h1

lemma quad_double_count {t : ℕ} (ht : 0 < t) (K KZ : Submodule F (Word t))
    (hKZ : ∀ x, x ∈ KZ ↔ x ∈ K ∧ evenLane ht x = 0)
    (L : Word t →ₗ[F] Word t) (d : Word t) :
    Nat.card KZ * Nat.card {x : K // Qw ht (evenLane ht x.1) (oddLane ht x.1) = L x.1 + d} ≤
      Nat.card {z : K × KZ // hitsAt ht (evenLane ht z.1.1) (oddLane ht z.2.1)} := by
  let G (x : K) : Prop := Qw ht (evenLane ht x.1) (oddLane ht x.1) = L x.1 + d
  let T1 (k : K) (κ : KZ) : Prop := Qw ht (evenLane ht k.1) (oddLane ht κ.1) = L κ.1
  let T0 (k : K) (κ : KZ) : Prop := Qw ht (evenLane ht k.1) (oddLane ht κ.1) = 0
  have h1 : Nat.card (KZ × {x : K // G x}) ≤
      Nat.card {p : K × K // G p.2 ∧ p.2.1 - p.1.1 ∈ KZ} := by
    refine Nat.card_le_card_of_injective (fun q =>
      ⟨(⟨q.2.1.1 - q.1.1, K.sub_mem q.2.1.2 ((hKZ q.1.1).mp q.1.2).1⟩, q.2.1), ⟨q.2.2, ?_⟩⟩) ?_
    · show q.2.1.1 - (q.2.1.1 - q.1.1) ∈ KZ
      rw [sub_sub_cancel]
      exact q.1.2
    · intro q q' hqq
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at hqq
      have h2 : q.2 = q'.2 := Subtype.ext hqq.2
      have h3 := hqq.1
      rw [hqq.2] at h3
      exact Prod.ext (Subtype.ext (sub_right_injective h3)) h2
  rw [Nat.card_prod] at h1
  have h2 : Nat.card {p : K × K // G p.2 ∧ p.2.1 - p.1.1 ∈ KZ} ≤
      Nat.card {p : K × KZ // T1 p.1 p.2} := by
    refine fib_card_le (α := K) (β := K) (γ := KZ) (fun k g => G g ∧ g.1 - k.1 ∈ KZ) T1 fun k => ?_
    rcases isEmpty_or_nonempty {g : K // G g ∧ g.1 - k.1 ∈ KZ} with hE | ⟨⟨g0, hg0, hm0⟩⟩
    · rw [Nat.card_of_isEmpty]; exact Nat.zero_le _
    · have hd : ∀ g : {g : K // G g ∧ g.1 - k.1 ∈ KZ}, g.1.1 - g0.1 ∈ KZ := by
        intro g
        have h := KZ.sub_mem g.2.2 hm0
        rwa [sub_sub_sub_cancel_right] at h
      refine Nat.card_le_card_of_injective (fun g => ⟨⟨g.1.1 - g0.1, hd g⟩, ?_⟩) ?_
      · show Qw ht (evenLane ht k.1) (oddLane ht (g.1.1 - g0.1)) = L (g.1.1 - g0.1)
        have he1 : evenLane ht g.1.1 = evenLane ht k.1 := by
          have h := ((hKZ _).mp g.2.2).2
          rw [map_sub, sub_eq_zero] at h
          exact h
        have he0 : evenLane ht g0.1 = evenLane ht k.1 := by
          have h := ((hKZ _).mp hm0).2
          rw [map_sub, sub_eq_zero] at h
          exact h
        have hg1 := g.2.1
        have hg2 := hg0
        dsimp only [G] at hg1 hg2
        rw [he1] at hg1
        rw [he0] at hg2
        rw [map_sub, map_sub, map_sub, hg1, hg2]
        abel
      · intro g g' hgg
        simp only [Subtype.mk.injEq, sub_left_inj] at hgg
        exact Subtype.ext (Subtype.ext hgg)
  have h3 : Nat.card {p : K × KZ // T1 p.1 p.2} ≤ Nat.card {p : K × KZ // T0 p.1 p.2} := by
    refine fib_card_le2 (α := KZ) (β := K) (γ := K) T1 T0 fun κ => ?_
    rcases isEmpty_or_nonempty {k : K // T1 k κ} with hE | ⟨⟨k0, hk0⟩⟩
    · rw [Nat.card_of_isEmpty]; exact Nat.zero_le _
    · refine Nat.card_le_card_of_injective (fun k => ⟨k.1 - k0, ?_⟩) ?_
      · show Qw ht (evenLane ht (k.1.1 - k0.1)) (oddLane ht κ.1) = 0
        rw [map_sub, map_sub, LinearMap.sub_apply, k.2, hk0, sub_self]
      · intro k k' hkk
        exact Subtype.ext (sub_left_inj.mp (congrArg Subtype.val hkk))
  have h4 : Nat.card {p : K × KZ // T0 p.1 p.2} =
      Nat.card {z : K × KZ // hitsAt ht (evenLane ht z.1.1) (oddLane ht z.2.1)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun z => Qw_eq_zero_iff ht _ _)
  exact le_trans (le_trans h1 h2) (h3.trans_eq h4)

lemma sum_F {M : Type*} [AddCommMonoid M] (g : F → M) : ∑ z : F, g z = g 0 + g 1 := by
  rw [show (Finset.univ : Finset F) = {0, 1} from by decide]
  rw [Finset.sum_pair (by decide)]

section CountEngine

open Classical

noncomputable def wt {ι : Type*} [Fintype ι] (p : ι → F) : ℕ :=
  (Finset.univ.filter (fun i => p i ≠ 0)).card

lemma pow_wt {ι : Type*} [Fintype ι] (x : ℚ) (p : ι → F) :
    x ^ wt p = ∏ i, (if p i = 0 then 1 else x) := by
  unfold wt
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]

lemma sum_pow_wt {ι : Type*} [Fintype ι] (x : ℚ) :
    ∑ u : ι → F, x ^ wt u = (1 + x) ^ Fintype.card ι := by
  simp only [pow_wt]
  rw [← Fintype.prod_sum (fun _ z => if z = 0 then (1 : ℚ) else x)]
  have h : ∀ i : ι, (∑ z : F, if z = 0 then (1 : ℚ) else x) = 1 + x := by
    intro _; rw [sum_F]; norm_num
  rw [Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const, Finset.card_univ]

lemma wt_zero {ι : Type*} [Fintype ι] : wt (0 : ι → F) = 0 := by
  simp [wt]

lemma wt_le_card {ι : Type*} [Fintype ι] (v : ι → F) : wt v ≤ Fintype.card ι := by
  unfold wt
  exact Finset.card_le_univ _

lemma wt_single {ι : Type*} [Fintype ι] (k : ι) :
    wt (fun i => if i = k then (1 : F) else 0) = 1 := by
  unfold wt
  rw [Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  by_cases h : i = k
  · subst h; simp
  · simp [h]

lemma wt_split {ι : Type} [Fintype ι] (I : Finset ι) (v : ι → F) :
    wt v = wt (fun i : I => v i) + (Finset.univ.filter (fun i => i ∉ I ∧ v i ≠ 0)).card := by
  unfold wt
  have h1 : (Finset.univ.filter (fun i : I => v i ≠ 0)).card =
      (Finset.univ.filter (fun i => i ∈ I ∧ v i ≠ 0)).card := by
    apply Finset.card_bij (fun i _ => i.1)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact ⟨i.2, hi⟩
    · intro i _ j _ h; exact Subtype.ext h
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨⟨i, hi.1⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hi.2, rfl⟩
  rw [h1, ← Finset.card_union_of_disjoint]
  · congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2.1 h1.1

lemma card_SP {ι : Type} [Fintype ι] (P : Submodule F (ι → F)) :
    (Finset.univ.filter (fun v => v ∈ P)).card = 2 ^ Module.finrank F P := by
  have h := Module.card_eq_pow_finrank (K := F) (V := P)
  rw [ZMod.card] at h
  rw [← h]
  exact (Fintype.card_subtype (fun v => v ∈ P)).symm.trans (Fintype.card_congr (Equiv.refl _))

lemma infoSet {ι : Type*} [Fintype ι] (d : ℕ) :
    ∀ P : Submodule F (ι → F), Module.finrank F P = d →
      ∃ I : Finset ι, I.card ≤ d ∧ ∀ p ∈ P, (∀ i ∈ I, p i = 0) → p = 0 := by
  induction d with
  | zero =>
    intro P hP
    rw [Submodule.finrank_eq_zero] at hP
    refine ⟨∅, by simp, fun p hp _ => ?_⟩
    rw [hP] at hp
    exact (Submodule.mem_bot F).mp hp
  | succ d ih =>
    intro P hP
    have hne : P ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hP
      omega
    obtain ⟨p0, hp0, hp0ne⟩ := (Submodule.ne_bot_iff P).mp hne
    obtain ⟨i0, hi0⟩ : ∃ i0, p0 i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hp0ne (funext h)
    let f : P →ₗ[F] F := (LinearMap.proj i0).comp P.subtype
    have hrange : Module.finrank F (LinearMap.range f) = 1 := by
      apply le_antisymm
      · calc Module.finrank F (LinearMap.range f) ≤ Module.finrank F F :=
              Submodule.finrank_le _
          _ = 1 := Module.finrank_self F
      · rw [Nat.one_le_iff_ne_zero]
        intro h0
        rw [Submodule.finrank_eq_zero] at h0
        have : f ⟨p0, hp0⟩ ∈ LinearMap.range f := LinearMap.mem_range_self f _
        rw [h0, Submodule.mem_bot] at this
        exact hi0 this
    have hker : Module.finrank F (LinearMap.ker f) = d := by
      have := LinearMap.finrank_range_add_finrank_ker f
      omega
    set P0 := (LinearMap.ker f).map P.subtype with hP0
    have hP0d : Module.finrank F P0 = d := by
      rw [hP0, Submodule.finrank_map_subtype_eq, hker]
    obtain ⟨I0, hI0, hinj⟩ := ih P0 hP0d
    refine ⟨insert i0 I0, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
    intro p hp hvan
    have hpi0 : p i0 = 0 := hvan i0 (Finset.mem_insert_self _ _)
    have hpP0 : p ∈ P0 := by
      rw [hP0, Submodule.mem_map]
      refine ⟨⟨p, hp⟩, ?_, rfl⟩
      rw [LinearMap.mem_ker]
      exact hpi0
    exact hinj p hpP0 (fun i hi => hvan i (Finset.mem_insert_of_mem hi))

noncomputable def Bfun (d : ℕ) : ℚ := (5 / 8) * (5 / 4) ^ d + (3 / 8) * (3 / 4) ^ d

lemma Bfun_succ_gt (k : ℕ) : Bfun k < Bfun (k + 1) := by
  unfold Bfun
  have h1 : (3 / 4 : ℚ) ^ k ≤ (5 / 4) ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h2 : (0 : ℚ) < (3 / 4) ^ k := by positivity
  rw [pow_succ, pow_succ]
  nlinarith

lemma Bfun_strict : StrictMono Bfun := strictMono_nat_of_lt_succ Bfun_succ_gt

lemma Bfun_step (d : ℕ) : (1 / 4) * (5 / 4 : ℚ) ^ (d + 1) + (3 / 4) * Bfun d = Bfun (d + 1) := by
  unfold Bfun; ring

lemma Bfun_zero : Bfun 0 = 1 := by unfold Bfun; norm_num

lemma mainQ_le (d : ℕ) : ∀ (ι : Type) [Fintype ι] (P : Submodule F (ι → F)) (c : (ι → F) → ℚ),
    Module.finrank F P = d → d < Fintype.card ι → (∀ p ∈ P, wt p ≠ 1) → (∀ p, c p ≤ 4) →
    (∀ p, wt p ≤ d + 2 → c p = 1) →
    (∑ v ∈ Finset.univ.filter (fun v => v ∈ P), (1 / 4 : ℚ) ^ (wt v) * c v) ≤ Bfun d := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro ι _ P c hP hdι hno1 hc4 hcl
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    have hbot : P = ⊥ := Submodule.finrank_eq_zero.mp hP
    have hSP : Finset.univ.filter (fun v => v ∈ P) = {0} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hbot,
        Submodule.mem_bot]
    rw [hSP, Finset.sum_singleton, wt_zero, pow_zero, one_mul,
      hcl 0 (by rw [wt_zero]; omega), Bfun_zero]
  · obtain ⟨I, hIle, hinj⟩ := infoSet d P hP
    set SP := Finset.univ.filter (fun v => v ∈ P) with hSPdef
    let ρ : (ι → F) → (I → F) := fun v i => v i
    have hmemSP : ∀ v, v ∈ SP ↔ v ∈ P := by
      intro v; simp only [SP, Finset.mem_filter, Finset.mem_univ, true_and]
    have hρinj : Set.InjOn ρ SP := by
      intro v hv w hw hvw
      have hv' := (hmemSP v).mp hv
      have hw' := (hmemSP w).mp hw
      have h0 := hinj (v - w) (P.sub_mem hv' hw') (fun i hi => by
        have := congrFun hvw ⟨i, hi⟩
        simp only [ρ] at this
        simp [this])
      exact sub_eq_zero.mp h0
    have hcardSP : SP.card = 2 ^ d := by rw [← hP]; exact card_SP P
    have huniv : (Finset.univ : Finset (I → F)).card = 2 ^ I.card := by
      rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe]
    have himgc : (SP.image ρ).card = 2 ^ d := by
      rw [Finset.card_image_of_injOn hρinj, hcardSP]
    have hI : I.card = d := by
      have hle : (SP.image ρ).card ≤ (Finset.univ : Finset (I → F)).card := Finset.card_le_univ _
      rw [himgc, huniv] at hle
      exact le_antisymm hIle ((Nat.pow_le_pow_iff_right (by norm_num)).mp hle)
    have himg : SP.image ρ = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [huniv, himgc, hI]
    have hcardI : Fintype.card I = d := by rw [Fintype.card_coe, hI]
    set L := SP.filter (fun v => ∀ i ∉ I, v i = 0) with hLdef
    let Z : Submodule F (ι → F) :=
      { carrier := {v | ∀ i ∉ I, v i = 0}, add_mem' := by intro a b ha hb i hi; simp only [Set.mem_ofPred_eq] at ha hb; simp [ha i hi, hb i hi]
        zero_mem' := by intro i _; rfl
        smul_mem' := by intro s a ha i hi; simp only [Set.mem_ofPred_eq] at ha; simp [ha i hi] }
    let ρL : (ι → F) →ₗ[F] (I → F) := LinearMap.funLeft F F (Subtype.val : I → ι)
    set K := (P ⊓ Z).map ρL with hKdef
    have hK : ∀ u, u ∈ K ↔ ∃ v ∈ L, ρ v = u := by
      intro u
      rw [hKdef, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [Submodule.mem_inf] at hy
        refine ⟨y, ?_, rfl⟩
        simp only [L, Finset.mem_filter, hmemSP]
        exact ⟨hy.1, hy.2⟩
      · rintro ⟨v, hv, rfl⟩
        simp only [L, Finset.mem_filter, hmemSP] at hv
        exact ⟨v, Submodule.mem_inf.mpr ⟨hv.1, hv.2⟩, rfl⟩
    have hLsub : ∀ v ∈ L, v ∈ SP ∧ ∀ i ∉ I, v i = 0 := by
      intro v hv; simpa [L] using hv
    set r := fun v : ι → F => (Finset.univ.filter (fun i => i ∉ I ∧ v i ≠ 0)).card with hrdef
    have hwt : ∀ v, wt v = wt (ρ v) + r v := fun v => wt_split I v
    have hwtρ : ∀ v, wt (ρ v) ≤ d := fun v => (wt_le_card _).trans hcardI.le
    have hr0 : ∀ v, (∀ i ∉ I, v i = 0) ↔ r v = 0 := by
      intro v
      simp only [r, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_univ, true_implies,
        not_and, not_not]
    set X := fun v : ι → F => (1 / 4 : ℚ) ^ (wt (ρ v)) with hXdef
    have hXpos : ∀ v, 0 < X v := fun v => by positivity
    have hterm : ∀ v, (1 / 4 : ℚ) ^ (wt v) * c v ≤
        (if (∀ i ∉ I, v i = 0) then X v else (1 / 4) * X v) := by
      intro v
      split_ifs with hL
      · have hrv := (hr0 v).mp hL
        have hw : wt v = wt (ρ v) := by rw [hwt, hrv, add_zero]
        rw [hcl v (by rw [hw]; have := hwtρ v; omega), mul_one, hw]
      · have hrv : r v ≠ 0 := fun h => hL ((hr0 v).mpr h)
        by_cases hlight : wt v ≤ d + 2
        · rw [hcl v hlight, mul_one, hwt]
          calc (1 / 4 : ℚ) ^ (wt (ρ v) + r v) ≤ (1 / 4) ^ (wt (ρ v) + 1) :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ = (1 / 4) * X v := by rw [pow_succ]; simp only [X]; ring
        · have hr3 : 3 ≤ r v := by have := hwt v; have := hwtρ v; omega
          calc (1 / 4 : ℚ) ^ (wt v) * c v ≤ (1 / 4) ^ (wt v) * 4 :=
                mul_le_mul_of_nonneg_left (hc4 v) (by positivity)
            _ ≤ (1 / 4) ^ (wt (ρ v) + 3) * 4 := by
                rw [hwt]
                apply mul_le_mul_of_nonneg_right _ (by norm_num)
                exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            _ ≤ (1 / 4) * X v := by
                simp only [X]; rw [pow_add]
                have := hXpos v
                simp only [X] at this
                nlinarith
    have hsumX : ∑ v ∈ SP, X v = (5 / 4 : ℚ) ^ d := by
      have h1 : ∑ v ∈ SP, X v = ∑ u ∈ SP.image ρ, (1 / 4 : ℚ) ^ (wt u) :=
        (Finset.sum_image (f := fun u : I → F => (1 / 4 : ℚ) ^ (wt u))
          (fun a ha b hb h => hρinj ha hb h)).symm
      rw [h1, himg]
      have h2 := sum_pow_wt (ι := I) (1 / 4 : ℚ)
      rw [hcardI] at h2
      rw [show (5 / 4 : ℚ) = 1 + 1 / 4 by norm_num, ← h2]
      exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
    have hsumL : ∑ v ∈ L, X v =
        ∑ u ∈ Finset.univ.filter (fun u => u ∈ K), (1 / 4 : ℚ) ^ (wt u) * 1 := by
      apply Finset.sum_nbij ρ
      · intro v hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hK _).mpr ⟨v, hv, rfl⟩
      · exact hρinj.mono (fun v hv => (hLsub v hv).1)
      · intro u hu
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu
        obtain ⟨v, hv, hvu⟩ := (hK u).mp hu
        exact ⟨v, hv, hvu⟩
      · intro v _; simp [X]
    have hKno1 : ∀ u ∈ K, wt u ≠ 1 := by
      intro u hu
      obtain ⟨v, hv, rfl⟩ := (hK u).mp hu
      have hvL := hLsub v hv
      have : wt v = wt (ρ v) := by rw [hwt, (hr0 v).mp hvL.2, add_zero]
      rw [← this]
      exact hno1 v ((hmemSP v).mp hvL.1)
    obtain ⟨k0, hk0⟩ : I.Nonempty := Finset.card_pos.mp (by omega)
    set κ := Module.finrank F K with hκdef
    have hκ : κ < d := by
      have hle : κ ≤ d := by
        rw [hκdef, ← hcardI, ← Module.finrank_fintype_fun_eq_card (R := F)]
        exact Submodule.finrank_le K
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        have htop : K = ⊤ := by
          apply Submodule.eq_top_of_finrank_eq
          rw [← hκdef, h, Module.finrank_fintype_fun_eq_card, hcardI]
        have hmem := Submodule.eq_top_iff'.mp htop (fun i : I => if i = ⟨k0, hk0⟩ then (1 : F) else 0)
        exact hKno1 _ hmem (by convert wt_single (⟨k0, hk0⟩ : I))
    have hκI : κ < Fintype.card I := by rw [hcardI]; exact hκ
    have hKle := ih κ hκ I K (fun _ => 1) hκdef.symm hκI hKno1
      (fun _ => by norm_num) (fun _ _ => rfl)
    have hKle' : ∑ u ∈ Finset.univ.filter (fun u => u ∈ K), (1 / 4 : ℚ) ^ (wt u) * 1 ≤ Bfun κ := by
      convert hKle using 2
      ext u; simp
    have hBκ : Bfun κ ≤ Bfun (d - 1) := Bfun_strict.monotone (by omega)
    have hBd : (1 / 4) * (5 / 4 : ℚ) ^ d + (3 / 4) * Bfun (d - 1) = Bfun d := by
      have := Bfun_step (d - 1)
      rwa [Nat.sub_add_cancel hdpos] at this
    have hite : ∑ v ∈ SP, (if (∀ i ∉ I, v i = 0) then X v else (1 / 4) * X v) =
        (1 / 4) * ∑ v ∈ SP, X v + (3 / 4) * ∑ v ∈ L, X v := by
      rw [Finset.sum_ite, ← Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not SP
        (fun v => ∀ i ∉ I, v i = 0)]
      ring
    have hle1 := Finset.sum_le_sum (fun v (_ : v ∈ SP) => hterm v)
    rw [hite, hsumX, hsumL] at hle1
    linarith

end CountEngine

def chi (z : F) : ℚ := if z = 0 then 1 else -1

lemma chi_add (a b : F) : chi (a + b) = chi a * chi b := by
  rcases F_cases a with rfl | rfl <;> rcases F_cases b with rfl | rfl <;> simp [chi, z2_add_self]

lemma chi_sum {ι : Type} [DecidableEq ι] (s : Finset ι) (v : ι → F) :
    chi (∑ i ∈ s, v i) = ∏ i ∈ s, chi (v i) := by
  induction s using Finset.induction_on with
  | empty => simp [chi]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma chi_sq (z : F) : chi z * chi z = 1 := by
  rcases F_cases z with rfl | rfl <;> simp [chi]

lemma char_count {ι : Type} [Fintype ι] [DecidableEq ι] (S A : Finset ι) :
    ∑ y : ι → F, (∏ i, (if i ∈ S then (if y i = 0 then (1 : ℚ) else 0) else 1)) *
      ∏ i, (if i ∈ A then chi (y i) else 1) =
      if A ⊆ S then 2 ^ (Fintype.card ι - S.card) else 0 := by
  rw [show (fun y : ι → F => (∏ i, (if i ∈ S then (if y i = 0 then (1 : ℚ) else 0) else 1)) *
      ∏ i, (if i ∈ A then chi (y i) else 1)) = fun y => ∏ i,
      ((if i ∈ S then (if y i = 0 then (1 : ℚ) else 0) else 1) *
        (if i ∈ A then chi (y i) else 1)) from funext fun y => (Finset.prod_mul_distrib).symm]
  rw [← Fintype.prod_sum (fun i z => (if i ∈ S then (if z = 0 then (1 : ℚ) else 0) else 1) *
        (if i ∈ A then chi z else 1))]
  have e : ∀ i, (∑ z : F, (if i ∈ S then (if z = 0 then (1 : ℚ) else 0) else 1) *
        (if i ∈ A then chi z else 1)) =
      if i ∈ S then 1 else if i ∈ A then 0 else 2 := by
    intro i; rw [sum_F]
    by_cases hS : i ∈ S <;> by_cases hA : i ∈ A <;> simp [hS, hA, chi]
    norm_num
  rw [Finset.prod_congr rfl (fun i _ => e i)]
  split_ifs with hAS
  · rw [Finset.prod_congr rfl (fun i _ => show (if i ∈ S then (1 : ℚ) else if i ∈ A then 0 else 2)
        = if i ∈ S then 1 else 2 from by
          by_cases hS : i ∈ S
          · simp [hS]
          · have : i ∉ A := fun h => hS (hAS h)
            simp [hS, this])]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    simp
  · rw [Finset.not_subset] at hAS
    obtain ⟨i, hiA, hiS⟩ := hAS
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hiS, hiA])

def R0 (t : ℕ) : Finset (Fin (3 * t)) := Finset.univ.filter (fun i => i.val % 3 = 0 ∨ i.val % 3 = 2)
def R1 (t : ℕ) : Finset (Fin (3 * t)) := Finset.univ.filter (fun i => i.val % 3 = 1 ∨ i.val % 3 = 2)
def R2 (t : ℕ) : Finset (Fin (3 * t)) := Finset.univ.filter (fun i => i.val % 3 = 0 ∨ i.val % 3 = 1)

def codeF (t : ℕ) (y : Lane t) : Prop := ∑ i ∈ R0 t, y i = 0 ∧ ∑ i ∈ R1 t, y i = 0

instance instDecidableCodeF (t : ℕ) (y : Lane t) : Decidable (codeF t y) :=
  inferInstanceAs (Decidable (∑ i ∈ R0 t, y i = 0 ∧ ∑ i ∈ R1 t, y i = 0))

lemma codeSub_iff_codeF {t : ℕ} (y : Lane t) : y ∈ codeSub t ↔ codeF t y := by
  change synd (3 * t) y = 0 ↔ _
  rw [funext_iff, Fin.forall_fin_two]
  simp only [synd, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, Fin.val_zero, Fin.val_one,
    codeF, R0, R1, Finset.sum_filter]

noncomputable def cntS (t : ℕ) (S : Finset (Fin (3 * t))) : ℕ := by
  classical
  exact (Finset.univ.filter (fun y : Lane t => codeF t y ∧ ∀ i ∈ S, y i = 0)).card

def cvalNat (t : ℕ) (S : Finset (Fin (3 * t))) : ℕ :=
  1 + (if R0 t ⊆ S then 1 else 0) + (if R1 t ⊆ S then 1 else 0) + (if R2 t ⊆ S then 1 else 0)

def cval (t : ℕ) (S : Finset (Fin (3 * t))) : ℚ := (cvalNat t S : ℚ)

lemma cval_le (t : ℕ) (S : Finset (Fin (3 * t))) : cval t S ≤ 4 := by
  unfold cval cvalNat; split_ifs <;> norm_num

lemma prod_ind {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι) (y : ι → F) :
    ∏ i, (if i ∈ S then (if y i = 0 then (1 : ℚ) else 0) else 1) =
      if ∀ i ∈ S, y i = 0 then 1 else 0 := by
  split_ifs with h
  · apply Finset.prod_eq_one
    intro i _
    by_cases hi : i ∈ S
    · simp [hi, h i hi]
    · simp [hi]
  · push_neg at h
    obtain ⟨i, hi, hy⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hy])

lemma prod_chi_mem {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (y : ι → F) :
    ∏ i, (if i ∈ A then chi (y i) else 1) = chi (∑ i ∈ A, y i) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter, chi_sum]

lemma cnt_formula (t : ℕ) (S : Finset (Fin (3 * t))) :
    4 * (cntS t S : ℚ) = 2 ^ (3 * t - S.card) * cval t S := by
  classical
  unfold cntS
  rw [Finset.card_filter]
  push_cast
  set Q := fun (A : Finset (Fin (3 * t))) (y : Lane t) =>
    ∏ i, (if i ∈ A then chi (y i) else 1) with hQ
  set PS := fun (y : Lane t) =>
    ∏ i, (if i ∈ S then (if y i = 0 then (1 : ℚ) else 0) else 1) with hPS
  have hQ2 : ∀ y, Q (R2 t) y = Q (R0 t) y * Q (R1 t) y := by
    intro y
    simp only [hQ]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [R0, R1, R2, Finset.mem_filter, Finset.mem_univ, true_and]
    have h3 : i.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have := chi_sq (y i)
    rcases (by omega : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2) with h | h | h <;>
      simp [h, this]
  have hpt : ∀ y : Lane t, (if codeF t y ∧ ∀ i ∈ S, y i = 0 then (1 : ℚ) else 0) =
      (1 / 4) * (PS y * Q ∅ y + PS y * Q (R0 t) y + PS y * Q (R1 t) y + PS y * Q (R2 t) y) := by
    intro y
    have hQe : Q ∅ y = 1 := by simp [hQ]
    rw [hQ2, hQe]
    simp only [hPS, hQ]
    rw [prod_ind, prod_chi_mem, prod_chi_mem]
    unfold codeF
    have hc : ∀ z : F, chi z = if z = 0 then 1 else -1 := fun _ => rfl
    rw [hc, hc]
    by_cases hS : ∀ i ∈ S, y i = 0
    · have hS' : (∀ i ∈ S, y i = 0) = True := eq_true hS
      by_cases a : ∑ i ∈ R0 t, y i = 0 <;>
        by_cases b : ∑ i ∈ R1 t, y i = 0 <;> simp only [hS', a, b] <;> simp <;> norm_num
    · have hS' : (∀ i ∈ S, y i = 0) = False := eq_false hS
      simp only [hS']
      simp
  rw [Finset.sum_congr rfl (fun y _ => hpt y), ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, hPS, hQ]
  rw [char_count, char_count, char_count, char_count]
  simp only [Fintype.card_fin, Finset.empty_subset, if_true]
  unfold cval cvalNat
  push_cast
  split_ifs <;> ring

lemma cnt_formula_nat (t : ℕ) (S : Finset (Fin (3 * t))) :
    4 * cntS t S = 2 ^ (3 * t - S.card) * cvalNat t S := by
  have h := cnt_formula t S
  unfold cval at h
  exact_mod_cast h

lemma card_R0 {t : ℕ} : 2 * t ≤ (R0 t).card := by
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (2 * t)))) (t := R0 t)
    (fun m => (⟨3 * (m.val / 2) + 2 * (m.val % 2), by omega⟩ : Fin (3 * t)))
    (by intro m _; simp only [R0, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq]; omega)
    (by intro a _ b _ hab; simp only [Fin.mk.injEq] at hab; ext; omega)
  simpa using h

lemma card_R1 {t : ℕ} : 2 * t ≤ (R1 t).card := by
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (2 * t)))) (t := R1 t)
    (fun m => (⟨3 * (m.val / 2) + 1 + (m.val % 2), by omega⟩ : Fin (3 * t)))
    (by intro m _; simp only [R1, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq]; omega)
    (by intro a _ b _ hab; simp only [Fin.mk.injEq] at hab; ext; omega)
  simpa using h

lemma card_R2 {t : ℕ} : 2 * t ≤ (R2 t).card := by
  have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin (2 * t)))) (t := R2 t)
    (fun m => (⟨3 * (m.val / 2) + (m.val % 2), by omega⟩ : Fin (3 * t)))
    (by intro m _; simp only [R2, Finset.coe_filter, Finset.mem_univ, true_and,
          Set.mem_ofPred_eq]; omega)
    (by intro a _ b _ hab; simp only [Fin.mk.injEq] at hab; ext; omega)
  simpa using h

lemma cval_one {t : ℕ} {S : Finset (Fin (3 * t))} (hS : S.card < 2 * t) : cval t S = 1 := by
  unfold cval cvalNat
  have h0 : ¬ R0 t ⊆ S := fun h => by have := Finset.card_le_card h; have := card_R0 (t := t); omega
  have h1 : ¬ R1 t ⊆ S := fun h => by have := Finset.card_le_card h; have := card_R1 (t := t); omega
  have h2 : ¬ R2 t ⊆ S := fun h => by have := Finset.card_le_card h; have := card_R2 (t := t); omega
  simp [h0, h1, h2]

lemma cval_le_two_of_lt {t : ℕ} {S : Finset (Fin (3 * t))} (hS : S.card < 3 * t) : cval t S ≤ 2 := by
  have hnot : ∀ A B : Finset (Fin (3 * t)), A ∪ B = Finset.univ → ¬ (A ⊆ S ∧ B ⊆ S) := by
    intro A B hAB ⟨hA, hB⟩
    have hun : Finset.univ ⊆ S := hAB ▸ Finset.union_subset hA hB
    have hc := Finset.card_le_card hun
    simp at hc
    omega
  have h01 : R0 t ∪ R1 t = Finset.univ := by
    ext i; simp only [R0, R1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
  have h02 : R0 t ∪ R2 t = Finset.univ := by
    ext i; simp only [R0, R2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
  have h12 : R1 t ∪ R2 t = Finset.univ := by
    ext i; simp only [R1, R2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
  unfold cval cvalNat
  push_cast
  by_cases h0 : R0 t ⊆ S <;> by_cases h1 : R1 t ⊆ S <;> by_cases h2 : R2 t ⊆ S
  · exact absurd ⟨h0, h1⟩ (hnot _ _ h01)
  · exact absurd ⟨h0, h1⟩ (hnot _ _ h01)
  · exact absurd ⟨h0, h2⟩ (hnot _ _ h02)
  · simp only [h0, h1, h2, ↓reduceIte]; norm_num
  · exact absurd ⟨h1, h2⟩ (hnot _ _ h12)
  · simp only [h0, h1, h2, ↓reduceIte]; norm_num
  · simp only [h0, h1, h2, ↓reduceIte]; norm_num
  · simp only [h0, h1, h2, ↓reduceIte]; norm_num

def Nb {t : ℕ} (ht : 0 < t) (p : Lane t) : Finset (Fin (3 * t)) :=
  Finset.univ.filter (fun i => p i ≠ 0 ∨ p (nx ht i) ≠ 0)

lemma card_Nb {t : ℕ} (ht : 0 < t) (p : Lane t) (hs : ∀ i, ¬ (p i ≠ 0 ∧ p (nx ht i) ≠ 0)) :
    (Nb ht p).card = 2 * wt p := by
  classical
  have hsplit : Nb ht p = Finset.univ.filter (fun i => p i ≠ 0) ∪
      Finset.univ.filter (fun i => p (nx ht i) ≠ 0) := by
    ext i; simp [Nb]
  have hpre : (Finset.univ.filter (fun i => p (nx ht i) ≠ 0)).card = wt p := by
    unfold wt
    apply Finset.card_bij (fun i _ => nx ht i)
    · intro i hi; simpa using hi
    · intro a _ b _ h; exact nx_inj ht h
    · intro k hk
      obtain ⟨i, hi⟩ := nx_surj ht k
      exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hi]; simpa using hk, hi⟩
  rw [hsplit, Finset.card_union_of_disjoint, hpre]
  · unfold wt; ring
  · rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hs i ⟨h1, h2⟩

lemma no_wt_one {t : ℕ} {p : Lane t} (hc : codeF t p) : wt p ≠ 1 := by
  classical
  intro h1
  unfold wt at h1
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h1
  have hpk : p k ≠ 0 := by
    have := Finset.mem_singleton_self k; rw [← hk] at this; simpa using this
  have hoff : ∀ i, i ≠ k → p i = 0 := by
    intro i hi; by_contra h
    have : i ∈ Finset.univ.filter (fun i => p i ≠ 0) := by simp [h]
    rw [hk] at this; exact hi (Finset.mem_singleton.mp this)
  have hp1 : p k = 1 := (F_cases _).resolve_left hpk
  have hsum : ∀ R : Finset (Fin (3 * t)), k ∈ R → ∑ i ∈ R, p i = 1 := by
    intro R hR
    rw [Finset.sum_eq_single k (fun i _ hi => hoff i hi) (fun h => absurd hR h), hp1]
  obtain ⟨h0, h1'⟩ := hc
  have h3 : k.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : k.val % 3 = 0 ∨ k.val % 3 = 1 ∨ k.val % 3 = 2) with h | h | h
  · have := hsum (R0 t) (by simp [R0, h]); rw [this] at h0; exact one_ne_zero h0
  · have := hsum (R1 t) (by simp [R1, h]); rw [this] at h1'; exact one_ne_zero h1'
  · have := hsum (R0 t) (by simp [R0, h]); rw [this] at h0; exact one_ne_zero h0

lemma cntS_empty {t : ℕ} (ht : 0 < t) : (cntS t ∅ : ℚ) = 2 ^ (3 * t - 2) := by
  have h := cnt_formula t ∅
  rw [cval_one (by simp; omega), Finset.card_empty, Nat.sub_zero, mul_one] at h
  have h2 : (2 : ℚ) ^ (3 * t) = 4 * 2 ^ (3 * t - 2) := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  linarith

lemma cntS_ratio {t : ℕ} (ht : 0 < t) (S : Finset (Fin (3 * t))) :
    (cntS t S : ℚ) = (cntS t ∅ : ℚ) * ((1 / 2 : ℚ) ^ S.card * cval t S) := by
  rw [cntS_empty ht]
  have h := cnt_formula t S
  have hle : S.card ≤ 3 * t := (Finset.card_le_univ _).trans (by simp)
  have e1 : (2 : ℚ) ^ (3 * t - S.card) * 2 ^ S.card = 2 ^ (3 * t) := by
    rw [← pow_add]; congr 1; omega
  have e2 : (2 : ℚ) ^ (3 * t - 2) * 4 = 2 ^ (3 * t) := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have h2pos : (0 : ℚ) < 2 ^ S.card := by positivity
  have key : 4 * ((cntS t S : ℚ) * 2 ^ S.card) = 4 * (2 ^ (3 * t - 2) * cval t S) := by
    calc 4 * ((cntS t S : ℚ) * 2 ^ S.card)
        = (4 * (cntS t S : ℚ)) * 2 ^ S.card := by ring
      _ = (2 ^ (3 * t - S.card) * cval t S) * 2 ^ S.card := by rw [h]
      _ = (2 ^ (3 * t - S.card) * 2 ^ S.card) * cval t S := by ring
      _ = (2 ^ (3 * t - 2) * 4) * cval t S := by rw [e1, e2]
      _ = 4 * (2 ^ (3 * t - 2) * cval t S) := by ring
  have key2 := mul_left_cancel₀ (by norm_num : (4 : ℚ) ≠ 0) key
  rw [one_div_pow]
  field_simp
  linarith [key2]

lemma hitsAt_iff_Nb {t : ℕ} (ht : 0 < t) (p y : Lane t) :
    hitsAt ht p y ↔ ∀ i ∈ Nb ht p, y i = 0 := by
  constructor
  · intro h i hi
    simp only [Nb, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with hi | hi
    · exact (mul_eq_zero.mp (h i).1).resolve_left hi
    · exact (mul_eq_zero.mp (h i).2).resolve_left hi
  · intro h i
    by_cases hi : i ∈ Nb ht p
    · have := h i hi
      exact ⟨by rw [this, mul_zero], by rw [this, mul_zero]⟩
    · simp only [Nb, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hi
      exact ⟨by rw [hi.1, zero_mul], by rw [hi.2, zero_mul]⟩

lemma card_codeSub {t : ℕ} : Nat.card (codeSub t) = cntS t ∅ := by
  classical
  have e : codeSub t ≃ {y : Lane t // codeF t y ∧ ∀ i ∈ (∅ : Finset (Fin (3 * t))), y i = 0} :=
    { toFun := fun y => ⟨y.1, (codeSub_iff_codeF y.1).mp y.2, by simp⟩
      invFun := fun y => ⟨y.1, (codeSub_iff_codeF y.1).mpr y.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

open Classical in
lemma rectHits_codeSub_eq {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t)) :
    rectHits ht P (codeSub t) = ∑ p ∈ Finset.univ.filter (fun p => p ∈ P), cntS t (Nb ht p) := by
  have e : {z : P × codeSub t // hitsAt ht z.1.1 z.2.1} ≃
      {z : Lane t × Lane t // z.1 ∈ P ∧ codeF t z.2 ∧ hitsAt ht z.1 z.2} :=
    { toFun := fun z => ⟨(z.1.1.1, z.1.2.1), z.1.1.2, (codeSub_iff_codeF _).mp z.1.2.2, z.2⟩
      invFun := fun z => ⟨(⟨z.1.1, z.2.1⟩, ⟨z.1.2, (codeSub_iff_codeF _).mpr z.2.2.1⟩), z.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold rectHits
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    ← Finset.univ_product_univ, Finset.sum_product, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p ∈ P
  · rw [if_pos hp]
    unfold cntS
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y _
    apply if_congr _ rfl rfl
    simp only [hp, true_and, hitsAt_iff_Nb ht]
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    rintro ⟨h, _⟩
    exact hp h

open Classical in
lemma rectHits_le_sum_cntS {t : ℕ} (ht : 0 < t) (P Q : Submodule F (Lane t)) (hQ : Q ≤ codeSub t) :
    rectHits ht P Q ≤ Nat.card Q +
      ∑ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, cntS t (Nb ht p) := by
  have hsplit : rectHits ht P Q =
      ∑ p : P, Nat.card {y : Q // hitsAt ht p.1 y.1} := by
    unfold rectHits
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun (p : P) (y : Q) => hitsAt ht p.1 y.1)),
      Nat.card_sigma]
  rw [hsplit]
  have h0 : Nat.card {y : Q // hitsAt ht (0 : P).1 y.1} = Nat.card Q := by
    have e : {y : Q // hitsAt ht (0 : P).1 y.1} ≃ Q :=
      { toFun := fun y => y.1
        invFun := fun y => ⟨y, fun i => by simp⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Nat.card_congr e
  have hsum_P : (∑ p : P, Nat.card {y : Q // hitsAt ht p.1 y.1}) =
      Nat.card Q + ∑ p ∈ (Finset.univ : Finset P).erase 0, Nat.card {y : Q // hitsAt ht p.1 y.1} := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : P)), h0]
  rw [hsum_P]
  apply Nat.add_le_add_left
  have hbij : ∑ p ∈ (Finset.univ : Finset P).erase 0, Nat.card {y : Q // hitsAt ht p.1 y.1} ≤
      ∑ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, cntS t (Nb ht p) := by
    have heq : ∑ p ∈ (Finset.univ : Finset P).erase 0, cntS t (Nb ht p.1) =
        ∑ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, cntS t (Nb ht p) := by
      refine Finset.sum_nbij (fun p : P => p.1) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact ⟨fun h => hp.1 (Subtype.ext h), p.2⟩
      · intro a _ b _ h; exact Subtype.ext h
      · intro x hx
        simp only [Finset.coe_erase, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_sdiff,
          Set.mem_ofPred_eq, Set.mem_singleton_iff] at hx
        exact ⟨⟨x, hx.1⟩, by simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true]; exact fun h => hx.2 (congrArg Subtype.val h), rfl⟩
      · intro _ _; rfl
    rw [← heq]
    refine Finset.sum_le_sum fun p _ => ?_
    unfold cntS
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective (fun y =>
      ⟨y.1.1, (codeSub_iff_codeF _).mp (hQ y.1.2), (hitsAt_iff_Nb ht _ _).mp y.2⟩) ?_
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.1) hab))
  exact hbij

def mixL {t : ℕ} (ht : 0 < t) (i : Fin (6 * t)) : Word t →ₗ[F] F where
  toFun w := mixn (6 * t) (by omega) w i
  map_add' w1 w2 := mixn_add (by omega) w1 w2 i
  map_smul' a w := mixn_smul (by omega) a w i

def askFix {t : ℕ} (ht : 0 < t) (j : Fin (3 * t - 5)) (_ : ℕ) : Word t →ₗ[F] F :=
  if t = 2 then
    mixL ht (ixn (6 * t) (by omega) 0) + mixL ht (ixn (6 * t) (by omega) 6)
  else
    mixL ht (ixn (6 * t) (by omega) (2 * siteVal t j))

def laneFix {t : ℕ} (ht : 0 < t) (j : Fin (3 * t - 5)) : Lane t →ₗ[F] F :=
  if t = 2 then
    LinearMap.proj ⟨0, by omega⟩ + LinearMap.proj ⟨3 % (3 * t), Nat.mod_lt _ (by omega)⟩
  else
    LinearMap.proj ⟨siteVal t j % (3 * t), Nat.mod_lt _ (by omega)⟩

lemma siteVal_lt {t : ℕ} (ht3 : 3 ≤ t) (j : Fin (3 * t - 5)) : siteVal t j < 3 * t := by
  unfold siteVal
  split_ifs <;> omega

lemma askFix_eq_laneFix {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t) (j : Fin (3 * t - 5)) (p : ℕ) (w : Word t) :
    askFix ht j p w = laneFix ht j (evenLane ht w) := by
  unfold askFix laneFix
  split_ifs with h2
  · subst h2
    simp only [LinearMap.add_apply, mixL, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.proj_apply]
    rw [evenLane_eq_mixn, evenLane_eq_mixn]
    rfl
  · simp only [mixL, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.proj_apply]
    rw [evenLane_eq_mixn]
    refine congrArg (mixn (6 * t) (by omega) w) (Fin.ext ?_)
    have hlt : siteVal t j < 3 * t := siteVal_lt (by omega) j
    change (2 * siteVal t j) % (6 * t) = 2 * (siteVal t j % (3 * t))
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hlt]

def Pfix {t : ℕ} (ht : 0 < t) : Submodule F (Lane t) :=
  codeSub t ⊓ LinearMap.ker (LinearMap.pi (laneFix ht))

lemma Pfix2_check :
    4 * (Finset.univ.filter (fun p : Lane 2 => codeF 2 p ∧ p ⟨0, by decide⟩ + p ⟨3, by decide⟩ = 0)).card = 32 ∧
    (∑ p ∈ Finset.univ.filter (fun p : Lane 2 => codeF 2 p ∧ p ⟨0, by decide⟩ + p ⟨3, by decide⟩ = 0),
      2 ^ (6 - (Nb (by decide : 0 < 2) p).card) * cvalNat 2 (Nb (by decide : 0 < 2) p)) = 104 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma Pfix3_check :
    (Finset.univ.filter (fun p : Lane 3 => codeF 3 p ∧
      p ⟨4, by decide⟩ = 0 ∧ p ⟨5, by decide⟩ = 0 ∧ p ⟨7, by decide⟩ = 0 ∧ p ⟨8, by decide⟩ = 0)).card = 8 ∧
    (∑ p ∈ Finset.univ.filter (fun p : Lane 3 => codeF 3 p ∧
      p ⟨4, by decide⟩ = 0 ∧ p ⟨5, by decide⟩ = 0 ∧ p ⟨7, by decide⟩ = 0 ∧ p ⟨8, by decide⟩ = 0),
      2 ^ (9 - (Nb (by decide : 0 < 3) p).card) * cvalNat 3 (Nb (by decide : 0 < 3) p)) = 696 := by
  decide +kernel

def wt4 (a : Fin 4 → F) : ℕ := (Finset.univ.filter (fun k : Fin 4 => a k ≠ 0)).card

def E4set : Finset (Fin 4 → F) :=
  Finset.univ.filter (fun a : Fin 4 → F => a 0 + a 1 + a 2 + a 3 = 0)

lemma E4_checks : E4set.card = 8 ∧
    (∑ a ∈ E4set, 4 ^ (4 - wt4 a) * (if wt4 a = 4 then 2 else 1)) = 354 ∧
    (∑ a ∈ E4set, 4 ^ (4 - wt4 a)) = 353 := by
  decide +kernel

lemma wt4_eq_wt (a : Fin 4 → F) : wt4 a = wt a := by
  classical
  unfold wt4 wt
  congr 1

lemma Pfix_hits_eq {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t) :
    2048 * rectHits ht (Pfix ht) (codeSub t) =
      numVal t * (Nat.card (Pfix ht) * Nat.card (codeSub t)) := by
  classical
  rw [rectHits_codeSub_eq ht, card_codeSub]
  by_cases h2 : t = 2
  · subst h2
    have hPeq : Finset.univ.filter (fun p : Lane 2 => p ∈ Pfix ht) =
        Finset.univ.filter (fun p : Lane 2 => codeF 2 p ∧ p ⟨0, by decide⟩ + p ⟨3, by decide⟩ = 0) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pfix, Submodule.mem_inf,
        codeSub_iff_codeF, LinearMap.mem_ker]
      apply and_congr_right
      intro _
      constructor
      · intro h
        have h0 := congrFun h ⟨0, by decide⟩
        simpa [laneFix] using h0
      · intro h
        funext j
        fin_cases j
        simpa [laneFix] using h
    have hPcard : Nat.card (Pfix ht) = 8 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hPeq]
      have := Pfix2_check.1
      omega
    have hCcard : cntS 2 ∅ = 16 := by
      have h := cnt_formula_nat 2 ∅
      have hc1 : cvalNat 2 ∅ = 1 := by decide
      rw [hc1] at h
      simp at h
      omega
    have hsum : 4 * ∑ p ∈ Finset.univ.filter (fun p : Lane 2 => p ∈ Pfix ht), cntS 2 (Nb ht p) = 104 := by
      rw [Finset.mul_sum, hPeq]
      have hcongr : ∀ p : Lane 2, 4 * cntS 2 (Nb ht p) =
          2 ^ (6 - (Nb (by decide : 0 < 2) p).card) * cvalNat 2 (Nb (by decide : 0 < 2) p) :=
        fun p => cnt_formula_nat 2 (Nb ht p)
      simp_rw [hcongr]
      exact Pfix2_check.2
    rw [hPcard, hCcard]
    simp only [numVal, ↓reduceIte]
    omega
  · by_cases h3 : t = 3
    · subst h3
      have hPeq : Finset.univ.filter (fun p : Lane 3 => p ∈ Pfix ht) =
          Finset.univ.filter (fun p : Lane 3 => codeF 3 p ∧
            p ⟨4, by decide⟩ = 0 ∧ p ⟨5, by decide⟩ = 0 ∧ p ⟨7, by decide⟩ = 0 ∧ p ⟨8, by decide⟩ = 0) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pfix, Submodule.mem_inf,
          codeSub_iff_codeF, LinearMap.mem_ker]
        apply and_congr_right
        intro _
        constructor
        · intro h
          refine ⟨?_, ?_, ?_, ?_⟩
          · simpa [laneFix, siteVal] using congrFun h ⟨0, by decide⟩
          · simpa [laneFix, siteVal] using congrFun h ⟨1, by decide⟩
          · simpa [laneFix, siteVal] using congrFun h ⟨2, by decide⟩
          · simpa [laneFix, siteVal] using congrFun h ⟨3, by decide⟩
        · rintro ⟨h4, h5, h7, h8⟩
          funext j
          fin_cases j
          · simpa [laneFix, siteVal] using h4
          · simpa [laneFix, siteVal] using h5
          · simpa [laneFix, siteVal] using h7
          · simpa [laneFix, siteVal] using h8
      have hPcard : Nat.card (Pfix ht) = 8 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hPeq]
        exact Pfix3_check.1
      have hCcard : cntS 3 ∅ = 128 := by
        have h := cnt_formula_nat 3 ∅
        have hc1 : cvalNat 3 ∅ = 1 := by decide
        rw [hc1] at h
        simp at h
        omega
      have hsum : 4 * ∑ p ∈ Finset.univ.filter (fun p : Lane 3 => p ∈ Pfix ht), cntS 3 (Nb ht p) = 696 := by
        rw [Finset.mul_sum, hPeq]
        have hcongr : ∀ p : Lane 3, 4 * cntS 3 (Nb ht p) =
            2 ^ (9 - (Nb (by decide : 0 < 3) p).card) * cvalNat 3 (Nb (by decide : 0 < 3) p) :=
          fun p => cnt_formula_nat 3 (Nb ht p)
        simp_rw [hcongr]
        exact Pfix3_check.2
      rw [hPcard, hCcard]
      simp only [numVal, show ¬ (3 = 2) by decide, ↓reduceIte]
      omega
    · have ht4 : 4 ≤ t := by omega
      let i0 : Fin (3 * t) := ⟨0, by omega⟩
      let i3 : Fin (3 * t) := ⟨3, by omega⟩
      let i6 : Fin (3 * t) := ⟨6, by omega⟩
      let i9 : Fin (3 * t) := ⟨9, by omega⟩
      let S4 : Finset (Fin (3 * t)) := {i0, i3, i6, i9}
      have hmemP : ∀ p : Lane t, p ∈ Pfix ht ↔
          (∀ i : Fin (3 * t), i ∉ S4 → p i = 0) ∧ p i0 + p i3 + p i6 + p i9 = 0 := by
        intro p
        simp only [Pfix, Submodule.mem_inf, codeSub_iff_codeF, LinearMap.mem_ker]
        have hmiss : ∀ i : Fin (3 * t), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 3 → i.val ≠ 6 → i.val ≠ 9 →
            ∃ j : Fin (3 * t - 5), siteVal t j = i.val := by
          intro i h0 h1 h3' h6 h9
          have hi := i.isLt
          by_cases h2' : i.val = 2
          · exact ⟨⟨0, by omega⟩, by simp [siteVal, h3, h2']⟩
          · by_cases h45 : i.val < 6
            · refine ⟨⟨i.val - 3, by omega⟩, ?_⟩
              unfold siteVal
              simp only [h3, ↓reduceIte]
              split_ifs <;> omega
            · by_cases h78 : i.val < 9
              · refine ⟨⟨i.val - 4, by omega⟩, ?_⟩
                unfold siteVal
                simp only [h3, ↓reduceIte]
                split_ifs <;> omega
              · refine ⟨⟨i.val - 5, by omega⟩, ?_⟩
                unfold siteVal
                simp only [h3, ↓reduceIte]
                split_ifs <;> omega
        have hvan : (LinearMap.pi (laneFix ht) p = 0) →
            ∀ i : Fin (3 * t), i.val ≠ 0 → i.val ≠ 1 → i.val ≠ 3 → i.val ≠ 6 → i.val ≠ 9 → p i = 0 := by
          intro hker i h0 h1 h3' h6 h9
          obtain ⟨j, hj⟩ := hmiss i h0 h1 h3' h6 h9
          have hkj := congrFun hker j
          simp only [LinearMap.pi_apply, Pi.zero_apply, laneFix, h2, ↓reduceIte,
            LinearMap.proj_apply] at hkj
          have heq : (⟨siteVal t j % (3 * t), Nat.mod_lt _ (by omega)⟩ : Fin (3 * t)) = i := by
            apply Fin.ext; dsimp only; rw [hj, Nat.mod_eq_of_lt i.isLt]
          rwa [heq] at hkj
        constructor
        · rintro ⟨⟨hc0, hc1⟩, hker⟩
          have hoff := hvan hker
          have hp1 : p ⟨1, by omega⟩ = 0 := by
            have h1in : (⟨1, by omega⟩ : Fin (3 * t)) ∈ R1 t := by simp [R1]
            rw [Finset.sum_eq_single ⟨1, by omega⟩] at hc1
            · exact hc1
            · intro b hb hne
              have hb1 : b.val % 3 = 1 ∨ b.val % 3 = 2 := (Finset.mem_filter.mp hb).2
              apply hoff b <;> intro he <;> simp [he] at hb1
              exact hne (Fin.ext he)
            · intro h; exact absurd h1in h
          have hoff4 : ∀ i : Fin (3 * t), i ∉ S4 → p i = 0 := by
            intro i hi
            simp only [S4, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
            by_cases h1 : i.val = 1
            · have : i = ⟨1, by omega⟩ := Fin.ext h1
              rw [this]; exact hp1
            · exact hoff i (fun h => hi.1 (Fin.ext h)) h1 (fun h => hi.2.1 (Fin.ext h))
                (fun h => hi.2.2.1 (Fin.ext h)) (fun h => hi.2.2.2 (Fin.ext h))
          refine ⟨hoff4, ?_⟩
          have hS4sub : S4 ⊆ R0 t := by
            intro i hi
            simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with rfl | rfl | rfl | rfl <;> simp [R0, i0, i3, i6, i9]
          rw [← Finset.sum_subset hS4sub (fun i _ hi => hoff4 i hi)] at hc0
          have hne03 : i0 ≠ i3 := by intro h; have := congrArg Fin.val h; simp [i0, i3] at this
          have hne06 : i0 ≠ i6 := by intro h; have := congrArg Fin.val h; simp [i0, i6] at this
          have hne09 : i0 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i0, i9] at this
          have hne36 : i3 ≠ i6 := by intro h; have := congrArg Fin.val h; simp [i3, i6] at this
          have hne39 : i3 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i3, i9] at this
          have hne69 : i6 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i6, i9] at this
          simp only [S4, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, hne03, hne06,
            hne09, hne36, hne39, hne69, or_self, not_false_eq_true, Finset.sum_singleton] at hc0
          linear_combination hc0
        · rintro ⟨hoff4, hsum4⟩
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · have hS4sub : S4 ⊆ R0 t := by
              intro i hi
              simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hi
              rcases hi with rfl | rfl | rfl | rfl <;> simp [R0, i0, i3, i6, i9]
            rw [← Finset.sum_subset hS4sub (fun i _ hi => hoff4 i hi)]
            have hne03 : i0 ≠ i3 := by intro h; have := congrArg Fin.val h; simp [i0, i3] at this
            have hne06 : i0 ≠ i6 := by intro h; have := congrArg Fin.val h; simp [i0, i6] at this
            have hne09 : i0 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i0, i9] at this
            have hne36 : i3 ≠ i6 := by intro h; have := congrArg Fin.val h; simp [i3, i6] at this
            have hne39 : i3 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i3, i9] at this
            have hne69 : i6 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i6, i9] at this
            simp only [S4, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, hne03, hne06,
              hne09, hne36, hne39, hne69, or_self, not_false_eq_true, Finset.sum_singleton]
            linear_combination hsum4
          · apply Finset.sum_eq_zero
            intro i hi
            apply hoff4 i
            have hi1 : i.val % 3 = 1 ∨ i.val % 3 = 2 := (Finset.mem_filter.mp hi).2
            simp only [S4, Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he <;> simp [he, i0, i3, i6, i9] at hi1
          · funext j
            simp only [LinearMap.pi_apply, Pi.zero_apply, laneFix, h2, ↓reduceIte, LinearMap.proj_apply]
            apply hoff4
            have hlt : siteVal t j < 3 * t := siteVal_lt (by omega) j
            have hneS : siteVal t j ≠ 0 ∧ siteVal t j ≠ 3 ∧ siteVal t j ≠ 6 ∧ siteVal t j ≠ 9 := by
              unfold siteVal
              simp only [h3, ↓reduceIte]
              split_ifs <;> omega
            simp only [S4, Finset.mem_insert, Finset.mem_singleton, not_or]
            refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he <;> have hv := congrArg Fin.val he <;>
              dsimp only [i0, i3, i6, i9] at hv <;> rw [Nat.mod_eq_of_lt hlt] at hv <;> omega
      let E4 : Finset (Fin 4 → F) := Finset.univ.filter (fun a : Fin 4 → F => a 0 + a 1 + a 2 + a 3 = 0)
      let mkP : (Fin 4 → F) → Lane t := fun a i =>
        if i = i0 then a 0 else if i = i3 then a 1 else if i = i6 then a 2 else if i = i9 then a 3 else 0
      have hmkP_eval : ∀ a : Fin 4 → F,
          mkP a i0 = a 0 ∧ mkP a i3 = a 1 ∧ mkP a i6 = a 2 ∧ mkP a i9 = a 3 := by
        intro a
        have h03 : i0 ≠ i3 := by intro h; have := congrArg Fin.val h; simp [i0, i3] at this
        have h06 : i0 ≠ i6 := by intro h; have := congrArg Fin.val h; simp [i0, i6] at this
        have h09 : i0 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i0, i9] at this
        have h36 : i3 ≠ i6 := by intro h; have := congrArg Fin.val h; simp [i3, i6] at this
        have h39 : i3 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i3, i9] at this
        have h69 : i6 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i6, i9] at this
        simp [mkP, h03, h06, h09, h36, h39, h69, h03.symm, h06.symm, h09.symm, h36.symm, h39.symm, h69.symm]
      have hP_bij : Finset.univ.filter (fun p : Lane t => p ∈ Pfix ht) = E4.image mkP := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmemP, Finset.mem_image, E4]
        constructor
        · rintro ⟨hoff, hsum⟩
          refine ⟨![p i0, p i3, p i6, p i9], hsum, ?_⟩
          funext i
          by_cases h0 : i = i0
          · subst h0; exact (hmkP_eval _).1
          · by_cases h3' : i = i3
            · subst h3'; exact (hmkP_eval _).2.1
            · by_cases h6' : i = i6
              · subst h6'; exact (hmkP_eval _).2.2.1
              · by_cases h9' : i = i9
                · subst h9'; exact (hmkP_eval _).2.2.2
                · simp only [mkP, h0, h3', h6', h9', ↓reduceIte]
                  exact (hoff i (by simp [S4, h0, h3', h6', h9'])).symm
        · rintro ⟨a, ha, rfl⟩
          refine ⟨fun i hi => ?_, ?_⟩
          · simp only [S4, Finset.mem_insert, Finset.mem_singleton, not_or] at hi
            simp [mkP, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]
          · obtain ⟨e0, e1, e2, e3⟩ := hmkP_eval a
            rw [e0, e1, e2, e3]; exact ha
      have hmkP_inj : Function.Injective mkP := by
        intro a b hab
        have ha := hmkP_eval a
        have hb := hmkP_eval b
        funext k
        fin_cases k
        · exact ha.1.symm.trans ((congrFun hab i0).trans hb.1)
        · exact ha.2.1.symm.trans ((congrFun hab i3).trans hb.2.1)
        · exact ha.2.2.1.symm.trans ((congrFun hab i6).trans hb.2.2.1)
        · exact ha.2.2.2.symm.trans ((congrFun hab i9).trans hb.2.2.2)
      have hE4_eq : E4 = E4set := by
        ext a; simp [E4, E4set]
      have hE4_card : E4.card = 8 := hE4_eq ▸ E4_checks.1
      have hPcard : Nat.card (Pfix ht) = 8 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hP_bij,
          Finset.card_image_of_injective _ hmkP_inj, hE4_card]
      have hsep_mk : ∀ a : Fin 4 → F, ∀ i : Fin (3 * t), ¬ (mkP a i ≠ 0 ∧ mkP a (nx ht i) ≠ 0) := by
        intro a i ⟨h1, h2'⟩
        have hmem1 : i ∈ S4 := by
          by_contra h
          simp only [S4, Finset.mem_insert, Finset.mem_singleton, not_or] at h
          apply h1; simp [mkP, h.1, h.2.1, h.2.2.1, h.2.2.2]
        have hmem2 : nx ht i ∈ S4 := by
          by_contra h
          simp only [S4, Finset.mem_insert, Finset.mem_singleton, not_or] at h
          apply h2'; simp [mkP, h.1, h.2.1, h.2.2.1, h.2.2.2]
        have hval := nx_val ht i
        simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2
        rcases hmem1 with rfl | rfl | rfl | rfl <;>
          rcases hmem2 with hm | hm | hm | hm <;>
          have hv := congrArg Fin.val hm <;>
          simp only [i0, i3, i6, i9] at hval hv <;>
          split_ifs at hval <;> omega
      have hwt_mk : ∀ a : Fin 4 → F, wt (mkP a) = wt a := by
        intro a
        unfold wt
        refine Finset.card_bij (fun i _ =>
          if i = i0 then (0 : Fin 4) else if i = i3 then 1 else if i = i6 then 2 else 3) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          split_ifs with h0 h3' h6'
          · subst h0; rwa [(hmkP_eval a).1] at hi
          · subst h3'; rwa [(hmkP_eval a).2.1] at hi
          · subst h6'; rwa [(hmkP_eval a).2.2.1] at hi
          · by_cases h9' : i = i9
            · subst h9'; rwa [(hmkP_eval a).2.2.2] at hi
            · exfalso; apply hi; simp [mkP, h0, h3', h6', h9']
        · intro x hx y hy hxy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
          have hxS : x ∈ S4 := by
            by_contra h; simp only [S4, Finset.mem_insert, Finset.mem_singleton, not_or] at h
            apply hx; simp [mkP, h.1, h.2.1, h.2.2.1, h.2.2.2]
          have hyS : y ∈ S4 := by
            by_contra h; simp only [S4, Finset.mem_insert, Finset.mem_singleton, not_or] at h
            apply hy; simp [mkP, h.1, h.2.1, h.2.2.1, h.2.2.2]
          simp only [S4, Finset.mem_insert, Finset.mem_singleton] at hxS hyS
          have h03 : i0 ≠ i3 := by intro h; have := congrArg Fin.val h; simp [i0, i3] at this
          have h06 : i0 ≠ i6 := by intro h; have := congrArg Fin.val h; simp [i0, i6] at this
          have h09 : i0 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i0, i9] at this
          have h36 : i3 ≠ i6 := by intro h; have := congrArg Fin.val h; simp [i3, i6] at this
          have h39 : i3 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i3, i9] at this
          have h69 : i6 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i6, i9] at this
          rcases hxS with rfl | rfl | rfl | rfl <;> rcases hyS with rfl | rfl | rfl | rfl <;>
            simp [h03, h06, h09, h36, h39, h69, h03.symm, h06.symm, h09.symm, h36.symm, h39.symm, h69.symm] at hxy ⊢
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
          have h03 : i0 ≠ i3 := by intro h; have := congrArg Fin.val h; simp [i0, i3] at this
          have h06 : i0 ≠ i6 := by intro h; have := congrArg Fin.val h; simp [i0, i6] at this
          have h09 : i0 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i0, i9] at this
          have h36 : i3 ≠ i6 := by intro h; have := congrArg Fin.val h; simp [i3, i6] at this
          have h39 : i3 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i3, i9] at this
          have h69 : i6 ≠ i9 := by intro h; have := congrArg Fin.val h; simp [i6, i9] at this
          fin_cases k
          · exact ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(hmkP_eval a).1]; exact hk⟩, by simp⟩
          · exact ⟨i3, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(hmkP_eval a).2.1]; exact hk⟩, by simp [h03.symm]⟩
          · exact ⟨i6, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(hmkP_eval a).2.2.1]; exact hk⟩, by simp [h06.symm, h36.symm]⟩
          · exact ⟨i9, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [(hmkP_eval a).2.2.2]; exact hk⟩, by simp [h09.symm, h39.symm, h69.symm]⟩
      have htermQ : ∀ a ∈ E4, (cntS t (Nb ht (mkP a)) : ℚ) =
          (cntS t ∅ : ℚ) * ((1 / 4 : ℚ) ^ (wt a) * cval t (Nb ht (mkP a))) := by
        intro a _
        rw [cntS_ratio ht, card_Nb ht _ (hsep_mk a), hwt_mk a, pow_mul]
        norm_num
      have hcval_eq : ∀ a ∈ E4, cval t (Nb ht (mkP a)) =
          if wt a = 4 ∧ t = 4 then 2 else 1 := by
        intro a _
        have hcard : (Nb ht (mkP a)).card = 2 * wt a := by rw [card_Nb ht _ (hsep_mk a), hwt_mk a]
        have hwt4 : wt a ≤ 4 := (wt_le_card a).trans (by simp)
        split_ifs with h44
        · rcases h44 with ⟨hwa, rfl⟩
          have hall1 : ∀ k : Fin 4, a k = 1 := by
            have hfu : Finset.univ.filter (fun k : Fin 4 => a k ≠ 0) = Finset.univ :=
              Finset.eq_univ_of_card _ (by simpa [wt] using hwa)
            intro k
            have hm : k ∈ Finset.univ.filter (fun k : Fin 4 => a k ≠ 0) := by
              rw [hfu]; exact Finset.mem_univ k
            have hk : a k ≠ 0 := (Finset.mem_filter.mp hm).2
            exact (F_cases _).resolve_left hk
          have hR0 : R0 4 ⊆ Nb ht (mkP a) := by
            intro i hi
            simp only [R0, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            simp only [Nb, Finset.mem_filter, Finset.mem_univ, true_and]
            have hi12 := i.isLt
            rcases hi with hm | hm
            · left
              have : i = i0 ∨ i = i3 ∨ i = i6 ∨ i = i9 := by
                have : i.val = 0 ∨ i.val = 3 ∨ i.val = 6 ∨ i.val = 9 := by omega
                rcases this with h | h | h | h
                · exact Or.inl (Fin.ext h)
                · exact Or.inr (Or.inl (Fin.ext h))
                · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
                · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
              rcases this with rfl | rfl | rfl | rfl <;>
                simp [hmkP_eval, hall1]
            · right
              have hnv := nx_val ht i
              have : nx ht i = i0 ∨ nx ht i = i3 ∨ nx ht i = i6 ∨ nx ht i = i9 := by
                have : (nx ht i).val = 0 ∨ (nx ht i).val = 3 ∨ (nx ht i).val = 6 ∨ (nx ht i).val = 9 := by
                  rw [hnv]; split_ifs <;> omega
                rcases this with h | h | h | h
                · exact Or.inl (Fin.ext h)
                · exact Or.inr (Or.inl (Fin.ext h))
                · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
                · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
              rcases this with h | h | h | h <;> rw [h] <;> simp [hmkP_eval, hall1]
          have hnot1 : ¬ R1 4 ⊆ Nb ht (mkP a) := by
            intro hsub
            have h1in : (⟨1, by decide⟩ : Fin 12) ∈ Nb ht (mkP a) := hsub (by simp [R1])
            simp only [Nb, Finset.mem_filter, Finset.mem_univ, true_and] at h1in
            have hnx1 : nx ht ⟨1, by decide⟩ = ⟨2, by decide⟩ := by
              apply Fin.ext; rw [nx_val]; decide
            rw [hnx1] at h1in
            rcases h1in with h | h <;> apply h <;> simp [mkP, i0, i3, i6, i9]
          have hnot2 : ¬ R2 4 ⊆ Nb ht (mkP a) := by
            intro hsub
            have h1in : (⟨1, by decide⟩ : Fin 12) ∈ Nb ht (mkP a) := hsub (by simp [R2])
            simp only [Nb, Finset.mem_filter, Finset.mem_univ, true_and] at h1in
            have hnx1 : nx ht ⟨1, by decide⟩ = ⟨2, by decide⟩ := by
              apply Fin.ext; rw [nx_val]; decide
            rw [hnx1] at h1in
            rcases h1in with h | h <;> apply h <;> simp [mkP, i0, i3, i6, i9]
          unfold cval cvalNat
          simp [hR0, hnot1, hnot2]
        · exact cval_one (by rw [hcard]; omega)
      have hE4_sum4 : ∑ a ∈ E4, (1 / 4 : ℚ) ^ (wt a) * (if wt a = 4 then (2 : ℚ) else 1) = 354 / 256 := by
        rw [hE4_eq]
        have hnat : ((∑ a ∈ E4set, 4 ^ (4 - wt4 a) * (if wt4 a = 4 then 2 else 1) : ℕ) : ℚ) = 354 := by
          exact_mod_cast E4_checks.2.1
        rw [← hnat]
        push_cast
        conv_rhs => rw [div_eq_mul_inv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← wt4_eq_wt a]
        have hle : wt4 a ≤ 4 := by rw [wt4_eq_wt]; exact (wt_le_card a).trans (by simp)
        have hp : (4 : ℚ) ^ (4 - wt4 a) * 4 ^ wt4 a = 256 := by
          rw [← pow_add, show 4 - wt4 a + wt4 a = 4 by omega]; norm_num
        rw [one_div_pow]
        split_ifs <;> field_simp <;> linarith [hp]
      have hE4_sum5 : ∑ a ∈ E4, (1 / 4 : ℚ) ^ (wt a) * (1 : ℚ) = 353 / 256 := by
        rw [hE4_eq]
        have hnat : ((∑ a ∈ E4set, 4 ^ (4 - wt4 a) : ℕ) : ℚ) = 353 := by
          exact_mod_cast E4_checks.2.2
        rw [← hnat]
        push_cast
        conv_rhs => rw [div_eq_mul_inv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← wt4_eq_wt a]
        have hle : wt4 a ≤ 4 := by rw [wt4_eq_wt]; exact (wt_le_card a).trans (by simp)
        have hp : (4 : ℚ) ^ (4 - wt4 a) * 4 ^ wt4 a = 256 := by
          rw [← pow_add, show 4 - wt4 a + wt4 a = 4 by omega]; norm_num
        rw [one_div_pow, mul_one]
        field_simp
        linarith [hp]
      have hsumQ : ((∑ p ∈ Finset.univ.filter (fun p : Lane t => p ∈ Pfix ht), cntS t (Nb ht p) : ℕ) : ℚ) =
          (cntS t ∅ : ℚ) * ((if t = 4 then 354 else 353 : ℚ) / 256) := by
        rw [hP_bij, Finset.sum_image (fun a _ b _ h => hmkP_inj h)]
        push_cast
        rw [Finset.sum_congr rfl htermQ, ← Finset.mul_sum]
        congr 1
        by_cases h4 : t = 4
        · subst h4
          simp only [↓reduceIte]
          convert hE4_sum4 using 2 with a ha
          rw [hcval_eq a ha]
          simp
        · simp only [h4, ↓reduceIte]
          convert hE4_sum5 using 2 with a ha
          rw [hcval_eq a ha]
          simp [h4]
      rw [hPcard]
      have hQeq : ((2048 * ∑ p ∈ Finset.univ.filter (fun p : Lane t => p ∈ Pfix ht), cntS t (Nb ht p) : ℕ) : ℚ) =
          ((numVal t * (8 * cntS t ∅) : ℕ) : ℚ) := by
        rw [Nat.cast_mul, hsumQ]
        push_cast
        unfold numVal
        simp only [h2, h3, ↓reduceIte]
        split_ifs <;> push_cast <;> ring
      exact_mod_cast hQeq

lemma double_ker_sub {V : Type*} [AddCommGroup V] [Module F V] [Finite V]
    (L : Submodule F V) (r : V →ₗ[F] F) :
    Nat.card L ≤ 2 * Nat.card {x : L // r x.1 = 0} := by
  let ry : L →ₗ[F] F := r.comp L.subtype
  have hrange_le : Module.finrank F (LinearMap.range ry) ≤ 1 := by
    calc Module.finrank F (LinearMap.range ry) ≤ Module.finrank F F := Submodule.finrank_le _
      _ = 1 := Module.finrank_self F
  have h1 := LinearMap.finrank_range_add_finrank_ker ry
  have h2 : Module.finrank F L ≤ Module.finrank F (LinearMap.ker ry) + 1 := by omega
  have he : LinearMap.ker ry ≃ {x : L // r x.1 = 0} :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr he, Module.natCard_eq_pow_finrank (K := F) (V := L),
    Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker ry), Nat.card_zmod]
  calc 2 ^ Module.finrank F L ≤ 2 ^ (Module.finrank F (LinearMap.ker ry) + 1) :=
        Nat.pow_le_pow_right (by norm_num) h2
    _ = 2 * 2 ^ Module.finrank F (LinearMap.ker ry) := by rw [pow_succ']

lemma double_ker_hits {t : ℕ} (ht : 0 < t) (P Q : Submodule F (Lane t))
    (r : P →ₗ[F] F) (hr : r ≠ 0) :
    let P' : Submodule F (Lane t) := (LinearMap.ker r).map P.subtype
    Module.finrank F P' + 1 = Module.finrank F P ∧
    Nat.card P = 2 * Nat.card P' ∧
    rectHits ht P Q ≤ 2 * rectHits ht P' Q := by
  classical
  intro P'
  have hsurj : Function.Surjective r := by
    obtain ⟨p0, hp0⟩ : ∃ p0 : P, r p0 ≠ 0 := by
      by_contra h; push_neg at h; exact hr (LinearMap.ext h)
    intro c
    rcases F_cases c with rfl | rfl
    · exact ⟨0, map_zero r⟩
    · exact ⟨p0, (F_cases _).resolve_left hp0⟩
  have hrk : Module.finrank F P' + 1 = Module.finrank F P := by
    have h1 := LinearMap.finrank_range_add_finrank_ker r
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self] at h1
    rw [Submodule.finrank_map_subtype_eq]
    omega
  have hcard : Nat.card P = 2 * Nat.card P' := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := P),
      Module.natCard_eq_pow_finrank (K := F) (V := P'), Nat.card_zmod, ← hrk, pow_succ']
  refine ⟨hrk, hcard, ?_⟩
  have hP_sum : rectHits ht P Q = ∑ y : Q, Nat.card {x : P // hitsAt ht x.1 y.1} := by
    unfold rectHits
    have e : {z : P × Q // hitsAt ht z.1.1 z.2.1} ≃ Σ y : Q, {x : P // hitsAt ht x.1 y.1} :=
      { toFun := fun z => ⟨z.1.2, ⟨z.1.1, z.2⟩⟩
        invFun := fun s => ⟨(s.2.1, s.1), s.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_sigma]
  have hP'_sum : rectHits ht P' Q = ∑ y : Q, Nat.card {x : P' // hitsAt ht x.1 y.1} := by
    unfold rectHits
    have e : {z : P' × Q // hitsAt ht z.1.1 z.2.1} ≃ Σ y : Q, {x : P' // hitsAt ht x.1 y.1} :=
      { toFun := fun z => ⟨z.1.2, ⟨z.1.1, z.2⟩⟩
        invFun := fun s => ⟨(s.2.1, s.1), s.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_sigma]
  rw [hP_sum, hP'_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  let Ly : Submodule F P :=
    { carrier := {x : P | hitsAt ht x.1 y.1}, add_mem' := by
        intro a b ha hb i
        constructor
        · change (a.1 i + b.1 i) * y.1 i = 0
          rw [add_mul, (ha i).1, (hb i).1, add_zero]
        · change (a.1 (nx ht i) + b.1 (nx ht i)) * y.1 i = 0
          rw [add_mul, (ha i).2, (hb i).2, add_zero]
      zero_mem' := fun i => by simp
      smul_mem' := by
        intro c a ha i
        constructor
        · change (c * a.1 i) * y.1 i = 0
          rw [mul_assoc, (ha i).1, mul_zero]
        · change (c * a.1 (nx ht i)) * y.1 i = 0
          rw [mul_assoc, (ha i).2, mul_zero] }
  have hLy_le := double_ker_sub Ly r
  have eKer : {x : Ly // r x.1 = 0} ≃ {x : P' // hitsAt ht x.1 y.1} :=
    { toFun := fun x => ⟨⟨x.1.1.1, Submodule.mem_map.mpr ⟨x.1.1, x.2, rfl⟩⟩, x.1.2⟩
      invFun := fun x =>
        ⟨⟨⟨x.1.1, by obtain ⟨p, _, hp⟩ := Submodule.mem_map.mp x.1.2; rw [← hp]; exact p.2⟩, x.2⟩, by
          obtain ⟨p, hp, hpe⟩ := Submodule.mem_map.mp x.1.2
          have hpp : (⟨x.1.1, by rw [← hpe]; exact p.2⟩ : P) = p := Subtype.ext hpe.symm
          change r ⟨x.1.1, _⟩ = 0
          rw [hpp]
          exact hp⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have eLy : Ly ≃ {x : P // hitsAt ht x.1 y.1} :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr eLy, ← Nat.card_congr eKer]
  exact hLy_le

def tauIx {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : Fin (3 * t) :=
  ⟨(3 * t + 1 - i.val) % (3 * t), Nat.mod_lt _ (by omega)⟩

lemma tauIx_invol {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : tauIx ht (tauIx ht i) = i := by
  apply Fin.ext
  have hi := i.isLt
  dsimp only [tauIx]
  by_cases h0 : i.val = 0
  · rw [h0, Nat.sub_zero]
    have h1 : (3 * t + 1) % (3 * t) = 1 := by
      have : 3 * t + 1 = 1 + 3 * t := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1, Nat.add_sub_cancel, Nat.mod_self]
  · by_cases h1 : i.val = 1
    · rw [h1, Nat.add_sub_cancel, Nat.mod_self, Nat.sub_zero]
      have : 3 * t + 1 = 1 + 3 * t := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hlt : 3 * t + 1 - i.val < 3 * t := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have hback : 3 * t + 1 - (3 * t + 1 - i.val) = i.val := by omega
      rw [hback, Nat.mod_eq_of_lt hi]

lemma tauIx_nx_nat (t m : ℕ) (ht : 0 < t) (hi : m < 3 * t) :
    (3 * t + 1 - (if m + 1 = 3 * t then 0 else m + 1)) % (3 * t) =
      if (3 * t + 1 - m) % (3 * t) = 0 then 3 * t - 1 else (3 * t + 1 - m) % (3 * t) - 1 := by
  have hmod1 : (3 * t + 1) % (3 * t) = 1 := by
    have : 3 * t + 1 = 1 + 3 * t := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  by_cases h0 : m = 0
  · subst h0
    have hne1 : 0 + 1 ≠ 3 * t := by omega
    simp only [hne1, ↓reduceIte, Nat.sub_zero, hmod1, Nat.one_ne_zero, Nat.add_sub_cancel, Nat.mod_self]
  · by_cases htop : m + 1 = 3 * t
    · have h2 : 3 * t + 1 - m = 2 := by omega
      have h2mod : 2 % (3 * t) = 2 := Nat.mod_eq_of_lt (by omega)
      simp only [htop, ↓reduceIte, Nat.sub_zero, hmod1, h2, h2mod]
      simp
    · have ha : 3 * t + 1 - (m + 1) < 3 * t := by omega
      simp only [htop, ↓reduceIte]
      by_cases h1 : m = 1
      · subst h1
        simp only [Nat.add_sub_cancel, Nat.mod_self, ↓reduceIte]
        have : 3 * t + 1 - (1 + 1) = 3 * t - 1 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
      · have hb : 3 * t + 1 - m < 3 * t := by omega
        rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
        simp only [show 3 * t + 1 - m ≠ 0 by omega, ↓reduceIte]
        omega

lemma tauIx_nx {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : tauIx ht (nx ht i) = pv ht (tauIx ht i) := by
  apply Fin.ext
  rw [pv_val]
  dsimp only [tauIx]
  rw [nx_val]
  exact tauIx_nx_nat t i.val ht i.isLt

def tauIso {t : ℕ} (ht : 0 < t) : Lane t ≃ₗ[F] Lane t where
  toFun z i := z (tauIx ht i)
  invFun z i := z (tauIx ht i)
  left_inv z := by funext i; dsimp only; rw [tauIx_invol]
  right_inv z := by funext i; dsimp only; rw [tauIx_invol]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma tauIso_codeSub {t : ℕ} (ht : 0 < t) (z : Lane t) (hz : z ∈ codeSub t) :
    tauIso ht z ∈ codeSub t := by
  rw [codeSub_iff_codeF] at hz ⊢
  have hmod : ∀ i : Fin (3 * t), (tauIx ht i).val % 3 =
      if i.val % 3 = 0 then 1 else if i.val % 3 = 1 then 0 else 2 := by
    intro i
    have hi := i.isLt
    dsimp only [tauIx]
    by_cases h0 : i.val = 0
    · rw [h0, Nat.sub_zero]
      have : (3 * t + 1) % (3 * t) = 1 := by
        have h1 : 3 * t + 1 = 1 + 3 * t := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [this]; decide
    · by_cases h1 : i.val = 1
      · rw [h1, Nat.add_sub_cancel, Nat.mod_self]; decide
      · have hlt : 3 * t + 1 - i.val < 3 * t := by omega
        rw [Nat.mod_eq_of_lt hlt]
        split_ifs <;> omega
  have heq0 : ∑ i ∈ R0 t, tauIso ht z i = ∑ j ∈ R1 t, z j := by
    refine Finset.sum_nbij (tauIx ht) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [R0, R1, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hmod i]; rcases hi with h | h <;> simp [h]
    · intro a _ b _ h
      have := congrArg (tauIx ht) h
      rwa [tauIx_invol, tauIx_invol] at this
    · intro j hj
      simp only [R0, R1, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
      refine ⟨tauIx ht j, ?_, tauIx_invol ht j⟩
      simp only [R0, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hmod j]; rcases hj with h | h <;> simp [h]
    · intro _ _; rfl
  have heq1 : ∑ i ∈ R1 t, tauIso ht z i = ∑ j ∈ R0 t, z j := by
    refine Finset.sum_nbij (tauIx ht) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [R0, R1, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [hmod i]; rcases hi with h | h <;> simp [h]
    · intro a _ b _ h
      have := congrArg (tauIx ht) h
      rwa [tauIx_invol, tauIx_invol] at this
    · intro j hj
      simp only [R0, R1, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
      refine ⟨tauIx ht j, ?_, tauIx_invol ht j⟩
      simp only [R1, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hmod j]; rcases hj with h | h <;> simp [h]
    · intro _ _; rfl
  exact ⟨heq0.trans hz.2, heq1.trans hz.1⟩

lemma hitsAt_tauIso {t : ℕ} (ht : 0 < t) (x y : Lane t) :
    hitsAt ht (tauIso ht y) (tauIso ht x) ↔ hitsAt ht x y := by
  constructor
  · intro h j
    constructor
    · have h1 := (h (tauIx ht j)).1
      dsimp only [tauIso, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at h1
      rw [tauIx_invol, mul_comm] at h1
      exact h1
    · have h2 := (h (tauIx ht (nx ht j))).2
      dsimp only [tauIso, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] at h2
      have hstep : tauIx ht (nx ht (tauIx ht (nx ht j))) = j := by
        rw [tauIx_nx, tauIx_invol, pv_nx]
      rw [hstep, tauIx_invol, mul_comm] at h2
      exact h2
  · intro h i
    constructor
    · have h1 := (h (tauIx ht i)).1
      dsimp only [tauIso, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      rw [mul_comm]; exact h1
    · have h2 := (h (pv ht (tauIx ht i))).2
      rw [nx_pv] at h2
      dsimp only [tauIso, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      rw [tauIx_nx, mul_comm]
      exact h2

lemma tauIso_invol {t : ℕ} (ht : 0 < t) (z : Lane t) : tauIso ht (tauIso ht z) = z := by
  funext i; exact congrArg z (tauIx_invol ht i)

lemma rectHits_tauIso {t : ℕ} (ht : 0 < t) (P Q : Submodule F (Lane t)) :
    rectHits ht (Q.map (tauIso ht).toLinearMap) (P.map (tauIso ht).toLinearMap) = rectHits ht P Q := by
  unfold rectHits
  refine Nat.card_congr
    { toFun := fun z =>
        ⟨(⟨tauIso ht z.1.2.1, by
            obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.mp z.1.2.2
            rw [← hxe]; dsimp only [LinearEquiv.coe_toLinearMap]; rw [tauIso_invol]; exact hx⟩,
          ⟨tauIso ht z.1.1.1, by
            obtain ⟨y, hy, hye⟩ := Submodule.mem_map.mp z.1.1.2
            rw [← hye]; dsimp only [LinearEquiv.coe_toLinearMap]; rw [tauIso_invol]; exact hy⟩), by
          have h := z.2
          rw [← tauIso_invol ht z.1.2.1, ← tauIso_invol ht z.1.1.1] at h
          exact (hitsAt_tauIso ht _ _).mp h⟩
      invFun := fun z =>
        ⟨(⟨tauIso ht z.1.2.1, Submodule.mem_map.mpr ⟨z.1.2.1, z.1.2.2, rfl⟩⟩,
          ⟨tauIso ht z.1.1.1, Submodule.mem_map.mpr ⟨z.1.1.1, z.1.1.2, rfl⟩⟩),
          (hitsAt_tauIso ht _ _).mpr z.2⟩
      left_inv := fun z => by
        apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;> exact tauIso_invol ht _
      right_inv := fun z => by
        apply Subtype.ext; apply Prod.ext <;> apply Subtype.ext <;> exact tauIso_invol ht _ }

lemma exists_nonzero_dual {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (h : 0 < Module.finrank F V) : ∃ r : V →ₗ[F] F, r ≠ 0 := by
  let b := Module.finBasis F V
  let i0 : Fin (Module.finrank F V) := ⟨0, h⟩
  refine ⟨b.coord i0, ?_⟩
  intro hz
  have h1 := DFunLike.congr_fun hz (b i0)
  simp at h1

lemma finrank_map_tauIso {t : ℕ} (ht : 0 < t) (A : Submodule F (Lane t)) :
    Module.finrank F (A.map (tauIso ht).toLinearMap) = Module.finrank F A := by
  let e : A ≃ₗ[F] A.map (tauIso ht).toLinearMap :=
    { toFun := fun x => ⟨tauIso ht x.1, Submodule.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
      invFun := fun y => ⟨tauIso ht y.1, by
        obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.mp y.2
        rw [← hxe]; dsimp only [LinearEquiv.coe_toLinearMap]; rw [tauIso_invol]; exact hx⟩
      left_inv := fun x => Subtype.ext (tauIso_invol ht x.1)
      right_inv := fun y => Subtype.ext (tauIso_invol ht y.1)
      map_add' := fun _ _ => Subtype.ext (map_add (tauIso ht) _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul (tauIso ht) _ _) }
  exact e.finrank_eq.symm

lemma rect_bound_of_eq_and_le {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t)
    (hbase : ∀ (P Q : Submodule F (Lane t)), P ≤ codeSub t → Q ≤ codeSub t →
      Module.finrank F P + Module.finrank F Q = 3 * t + 1 →
      Module.finrank F P ≤ Module.finrank F Q →
      2048 * rectHits ht P Q ≤ numVal t * (Nat.card P * Nat.card Q))
    (P Q : Submodule F (Lane t)) (hP : P ≤ codeSub t) (hQ : Q ≤ codeSub t)
    (hdim : 3 * t + 1 ≤ Module.finrank F P + Module.finrank F Q) :
    2048 * rectHits ht P Q ≤ numVal t * (Nat.card P * Nat.card Q) := by
  have hsym : ∀ (A B : Submodule F (Lane t)), A ≤ codeSub t → B ≤ codeSub t →
      Module.finrank F A + Module.finrank F B = 3 * t + 1 →
      2048 * rectHits ht A B ≤ numVal t * (Nat.card A * Nat.card B) := by
    intro A B hA hB hab
    by_cases hle : Module.finrank F A ≤ Module.finrank F B
    · exact hbase A B hA hB hab hle
    · let A' := B.map (tauIso ht).toLinearMap
      let B' := A.map (tauIso ht).toLinearMap
      have hA' : A' ≤ codeSub t := by
        rintro _ ⟨y, hy, rfl⟩; exact tauIso_codeSub ht y (hB hy)
      have hB' : B' ≤ codeSub t := by
        rintro _ ⟨x, hx, rfl⟩; exact tauIso_codeSub ht x (hA hx)
      have hdA' : Module.finrank F A' = Module.finrank F B := finrank_map_tauIso ht B
      have hdB' : Module.finrank F B' = Module.finrank F A := finrank_map_tauIso ht A
      have hres := hbase A' B' hA' hB' (by omega) (by omega)
      rw [rectHits_tauIso ht A B] at hres
      have hcA' : Nat.card A' = Nat.card B := by
        rw [Module.natCard_eq_pow_finrank (K := F) (V := A'),
          Module.natCard_eq_pow_finrank (K := F) (V := B), hdA']
      have hcB' : Nat.card B' = Nat.card A := by
        rw [Module.natCard_eq_pow_finrank (K := F) (V := B'),
          Module.natCard_eq_pow_finrank (K := F) (V := A), hdB']
      rw [hcA', hcB', mul_comm (Nat.card B)] at hres
      exact hres
  generalize hd : Module.finrank F P + Module.finrank F Q - (3 * t + 1) = gap
  induction gap generalizing P Q with
  | zero =>
    exact hsym P Q hP hQ (by omega)
  | succ k ih =>
    have hgt : 3 * t + 1 < Module.finrank F P + Module.finrank F Q := by omega
    have hPpos : 0 < Module.finrank F P := by
      have := Submodule.finrank_mono hQ
      have := codeSub_finrank ht
      omega
    obtain ⟨r, hr⟩ := exists_nonzero_dual hPpos
    obtain ⟨hrk, hcard, hhits⟩ := double_ker_hits ht P Q r hr
    set P' := (LinearMap.ker r).map P.subtype
    have hP' : P' ≤ codeSub t := by
      rintro _ ⟨x, _, rfl⟩; exact hP x.2
    have hih := ih P' Q hP' hQ (by omega) (by omega)
    calc 2048 * rectHits ht P Q ≤ 2048 * (2 * rectHits ht P' Q) :=
          Nat.mul_le_mul_left 2048 hhits
      _ = 2 * (2048 * rectHits ht P' Q) := by ring
      _ ≤ 2 * (numVal t * (Nat.card P' * Nat.card Q)) := Nat.mul_le_mul_left 2 hih
      _ = numVal t * ((2 * Nat.card P') * Nat.card Q) := by ring
      _ = numVal t * (Nat.card P * Nat.card Q) := by rw [hcard]

def ext0 {n : ℕ} (S : Finset (Fin n)) : (S → F) →ₗ[F] (Fin n → F) where
  toFun x i := if hi : i ∈ S then x ⟨i, hi⟩ else 0
  map_add' x y := by ext i; by_cases h : i ∈ S <;> simp [h]
  map_smul' c x := by ext i; by_cases h : i ∈ S <;> simp [h]

def checkOn {n : ℕ} (S : Finset (Fin n)) := (synd n).comp (ext0 S)

lemma ext0_single {n : ℕ} (S : Finset (Fin n)) (j : S) (c : F) :
    ext0 S (Pi.single j c) = Pi.single j.val c := by
  ext i
  by_cases hi : i = j.val
  · subst i; simp [ext0, j.property]
  · by_cases h : i ∈ S
    · have hne : (⟨i, h⟩ : S) ≠ j := fun h' => hi (congrArg Subtype.val h')
      simp [ext0, h, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hi]
    · simp [ext0, h, Pi.single_eq_of_ne hi]

lemma reSingle {n : ℕ} (S : Finset (Fin n)) (j : S) (c : F) (e : Fin 2) :
    checkOn S (Pi.single j c) e = if j.val.val % 3 = e.val ∨ j.val.val % 3 = 2 then c else 0 := by
  rw [checkOn, LinearMap.comp_apply, ext0_single, synd_single]

lemma supportLoss {n : ℕ} (S : Finset (Fin n)) (U : Submodule F (Fin n → F))
    (hc : U ≤ (synd n).ker) (hs : ∀ x ∈ U, ∀ i ∉ S, x i = 0) :
    Module.finrank F U + Module.finrank F (checkOn S).range ≤ S.card := by
  let f : U →ₗ[F] (checkOn S).ker :=
    { toFun := fun x => ⟨fun j => x.val j.val, by
        change synd n (ext0 S (fun j => x.val j.val)) = 0
        have eqx : ext0 S (fun j => x.val j.val) = x.val := by
          ext i
          by_cases h : i ∈ S
          · simp [ext0, h]
          · simp [ext0, h, hs x x.property i h]
        rw [eqx]
        exact hc x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have inj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · exact congrFun (congrArg Subtype.val h) ⟨i, hi⟩
    · rw [hs x x.property i hi, hs y y.property i hi]
  have h := LinearMap.finrank_le_finrank_of_injective inj
  have dim := LinearMap.finrank_range_add_finrank_ker (checkOn S)
  simp at dim
  omega

lemma color_surj : ∀ a b : Fin 3, a ≠ b → ∀ y : Fin 2 → F, ∃ u v : F, ∀ e : Fin 2,
    (if a.val = e.val ∨ a.val = 2 then u else 0) +
    (if b.val = e.val ∨ b.val = 2 then v else 0) = y e := by decide +kernel

lemma rankTwo {n : ℕ} (S : Finset (Fin n)) (j k : S)
    (hne : j.val.val % 3 ≠ k.val.val % 3) : Module.finrank F (checkOn S).range = 2 := by
  have sur : Function.Surjective (checkOn S) := by
    intro y
    let a : Fin 3 := ⟨j.val.val % 3, Nat.mod_lt _ (by decide)⟩
    let b : Fin 3 := ⟨k.val.val % 3, Nat.mod_lt _ (by decide)⟩
    obtain ⟨u, v, h⟩ := color_surj a b (fun eq => hne (congrArg Fin.val eq)) y
    refine ⟨Pi.single j u + Pi.single k v, ?_⟩
    rw [map_add]
    ext e
    simp only [Pi.add_apply, reSingle]
    exact h e
  rw [LinearMap.range_eq_top.mpr sur]
  simp

lemma rankOneLe {n : ℕ} (S : Finset (Fin n)) (j : S) : 1 ≤ Module.finrank F (checkOn S).range := by
  have ht : ∀ a : Fin 3, ∃ e : Fin 2, a.val = e.val ∨ a.val = 2 := by decide
  obtain ⟨e, h⟩ := ht ⟨j.val.val % 3, Nat.mod_lt _ (by decide)⟩
  change j.val.val % 3 = e.val ∨ j.val.val % 3 = 2 at h
  let y : (checkOn S).range := ⟨checkOn S (Pi.single j (1 : F)), ⟨_, rfl⟩⟩
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨y, fun he => ?_⟩
  have hy := congrFun (congrArg Subtype.val he) e
  change checkOn S (Pi.single j (1 : F)) e = 0 at hy
  simp [reSingle, h] at hy

def mono {t : ℕ} (S : Finset (Fin (3 * t))) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i.val % 3 = j.val % 3

lemma mono_size {t : ℕ} (S : Finset (Fin (3 * t))) (h : mono S) : S.card ≤ t := by
  let f : S → Fin t := fun i => ⟨i.val.val / 3, by have hi := i.val.isLt; omega⟩
  have inj : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply Fin.ext
    have hh := h i i.property j j.property
    have hd : i.val.val / 3 = j.val.val / 3 := congrArg Fin.val he
    omega
  simpa using Fintype.card_le_of_injective f inj

lemma nx_color {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) :
    (nx ht i).val % 3 ≠ i.val % 3 := by
  have hi := i.isLt
  rw [nx_val]
  split_ifs <;> omega

lemma triple_card {n : ℕ} (S T A : Finset (Fin n))
    (hST : Disjoint S T) (hSA : Disjoint S A) (hTA : Disjoint T A) :
    S.card + T.card + A.card ≤ n := by
  rw [← Finset.card_union_of_disjoint hST,
    ← Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hSA, hTA⟩)]
  simpa using Finset.card_le_univ (S ∪ T ∪ A)

lemma mono_gap {t : ℕ} (ht : 0 < t) (S T : Finset (Fin (3 * t))) (hST : Disjoint S T)
    (hstep : ∀ j ∈ T, nx ht j ∉ S) :
    (mono T → S.card + T.card + T.card ≤ 3 * t) ∧
    (mono S → S.card + T.card + S.card ≤ 3 * t) := by
  let f : Fin (3 * t) ↪ Fin (3 * t) := ⟨nx ht, nx_inj ht⟩
  have hSX : Disjoint S (T.map f) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨b, hbin, rfl⟩ := Finset.mem_map.mp hb
    exact hstep b hbin ha
  have avoid (R : Finset (Fin (3 * t))) (hm : mono R) : Disjoint R (R.map f) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨b, hbin, rfl⟩ := Finset.mem_map.mp hb
    exact nx_color ht b (hm _ ha _ hbin)
  constructor
  · intro hm
    simpa using triple_card S T (T.map f) hST hSX (avoid T hm)
  · intro hm
    have hTS : Disjoint (T.map f) (S.map f) := by
      rw [Finset.disjoint_left]
      intro a hb ha
      obtain ⟨b, hbin, rfl⟩ := Finset.mem_map.mp hb
      obtain ⟨c, hc, hh⟩ := Finset.mem_map.mp ha
      exact Finset.disjoint_left.mp hST hc ((f.injective hh).symm ▸ hbin)
    simpa using triple_card S (T.map f) (S.map f) hSX (avoid S hm) hTS

lemma boundary_gap {t : ℕ} (ht : 0 < t) (S T : Finset (Fin (3 * t)))
    (hs : S.Nonempty) (ht' : T.Nonempty) (hST : Disjoint S T) (hstep : ∀ j ∈ T, nx ht j ∉ S) :
    S.card + T.card + 1 ≤ 3 * t := by
  classical
  by_contra! h
  have eq : S ∪ T = Finset.univ := by
    apply Finset.eq_univ_of_card
    have H := Finset.card_le_univ (S ∪ T)
    rw [Finset.card_union_of_disjoint hST] at H ⊢
    simp only [Fintype.card_fin] at H ⊢
    omega
  have closed {i} (hi : i ∈ T) : nx ht i ∈ T := by
    have hmem : nx ht i ∈ S ∪ T := eq ▸ Finset.mem_univ _
    exact (Finset.mem_union.mp hmem).resolve_left (hstep i hi)
  obtain ⟨i, hi⟩ := ht'
  obtain ⟨j, hj⟩ := hs
  have go (k : ℕ) : (⟨(i.val + k) % (3 * t), Nat.mod_lt _ (by omega)⟩ : Fin (3 * t)) ∈ T := by
    induction k with
    | zero =>
      convert hi using 1
      apply Fin.ext
      simp [Nat.mod_eq_of_lt i.isLt]
    | succ k ih =>
      have hh := closed ih
      convert hh using 1
      apply Fin.ext
      simpa only [nx, Nat.add_assoc] using (Nat.mod_add_mod (i.val + k) (3 * t) 1).symm
  have reach := go (3 * t - i.val + j.val)
  have same : (⟨(i.val + (3 * t - i.val + j.val)) % (3 * t), Nat.mod_lt _ (by omega)⟩ : Fin (3 * t)) = j := by
    apply Fin.ext
    have hi' := i.isLt
    have hj' := j.isLt
    change (i.val + (3 * t - i.val + j.val)) % (3 * t) = j.val
    rw [show i.val + (3 * t - i.val + j.val) = j.val + 3 * t by omega]
    simp [Nat.mod_eq_of_lt hj']
  rw [same] at reach
  exact Finset.disjoint_left.mp hST hj reach

noncomputable def supp {n : ℕ} (U : Submodule F (Fin n → F)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ∃ x ∈ U, x i ≠ 0)

lemma mem_supp {n : ℕ} (U : Submodule F (Fin n → F)) (i : Fin n) :
    i ∈ supp U ↔ ∃ x ∈ U, x i ≠ 0 := by
  classical
  simp [supp]

lemma suppLoss {n : ℕ} (U : Submodule F (Fin n → F)) (hc : U ≤ (synd n).ker) :
    Module.finrank F U + Module.finrank F (checkOn (supp U)).range ≤ (supp U).card := by
  apply supportLoss _ U hc
  intro x hx i hi
  by_contra hn
  exact hi ((mem_supp U i).mpr ⟨x, hx, hn⟩)

lemma oneOrTwo {t : ℕ} (S : Finset (Fin (3 * t))) (hs : S.Nonempty) :
    1 ≤ Module.finrank F (checkOn S).range ∧
      (¬ mono S → 2 ≤ Module.finrank F (checkOn S).range) := by
  obtain ⟨j, hj⟩ := hs
  refine ⟨rankOneLe _ ⟨j, hj⟩, ?_⟩
  intro h
  unfold mono at h
  push Not at h
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact (rankTwo S ⟨a, ha⟩ ⟨b, hb⟩ hab).ge

lemma mixedBound {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t) (U V : Submodule F (Lane t))
    (hcU : U ≤ codeSub t) (hcV : V ≤ codeSub t)
    (hu : 0 < Module.finrank F U) (hv : 0 < Module.finrank F V)
    (ann : ∀ x ∈ U, ∀ y ∈ V, hitsAt ht x y) :
    Module.finrank F U + Module.finrank F V + (if t = 2 then 4 else 5) ≤ 3 * t := by
  classical
  let S := supp U
  let T := supp V
  have us : Module.finrank F U + Module.finrank F (checkOn S).range ≤ S.card := suppLoss U hcU
  have vs : Module.finrank F V + Module.finrank F (checkOn T).range ≤ T.card := suppLoss V hcV
  have sn : S.Nonempty := Finset.card_pos.mp (by omega)
  have tn : T.Nonempty := Finset.card_pos.mp (by omega)
  have dst : Disjoint S T := by
    refine Finset.disjoint_left.mpr ?_
    intro i h1 h2
    obtain ⟨x, hx, xi⟩ := (mem_supp U i).mp h1
    obtain ⟨y, hy, yi⟩ := (mem_supp V i).mp h2
    exact mul_ne_zero xi yi (ann x hx y hy i).1
  have hstep : ∀ i ∈ T, nx ht i ∉ S := by
    intro i hi hn
    obtain ⟨x, hx, xi⟩ := (mem_supp U _).mp hn
    obtain ⟨y, hy, yi⟩ := (mem_supp V _).mp hi
    exact mul_ne_zero xi yi (ann x hx y hy i).2
  obtain ⟨s1, s2⟩ := oneOrTwo S sn
  obtain ⟨t1, t2⟩ := oneOrTwo T tn
  obtain ⟨gT, gS⟩ := mono_gap ht S T dst hstep
  by_cases a : mono S
  · by_cases b : mono T
    · have hS := mono_size S a
      have hT := mono_size T b
      split_ifs <;> omega
    · have H := t2 b
      have G := gS a
      split_ifs <;> omega
  · by_cases b : mono T
    · have H := s2 a
      have G := gT b
      split_ifs <;> omega
    · have H := s2 a
      have J := t2 b
      have G := boundary_gap ht S T sn tn dst hstep
      split_ifs <;> omega

def basis2Vec (k : Fin 4) : Lane 2 :=
  match k with
  | 0 => ![1, 0, 0, 1, 0, 0]
  | 1 => ![0, 1, 0, 0, 1, 0]
  | 2 => ![0, 0, 1, 0, 0, 1]
  | 3 => ![1, 1, 1, 0, 0, 0]

def comb2 (c : Fin 4 → F) : Lane 2 := fun i =>
  c 0 * basis2Vec 0 i + c 1 * basis2Vec 1 i + c 2 * basis2Vec 2 i + c 3 * basis2Vec 3 i

def dot4 (a b : Fin 4 → F) : F := a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3

lemma case_t2_kernel_check :
    (∀ c : Fin 4 → F, codeF 2 (comb2 c)) ∧
    (∀ c1 c2 : Fin 4 → F, comb2 c1 = comb2 c2 → c1 = c2) ∧
    (∀ m : Fin 4 → F, m ≠ 0 →
      (∑ c ∈ Finset.univ.filter (fun c : Fin 4 → F => dot4 m c = 0),
        2 ^ (6 - (Nb (by decide : 0 < 2) (comb2 c)).card) *
          cvalNat 2 (Nb (by decide : 0 < 2) (comb2 c))) ≤ 104) := by
  decide +kernel

lemma rect_case_t2 (ht : 0 < 2) (P Q : Submodule F (Lane 2))
    (hP : P ≤ codeSub 2) (hQ : Q ≤ codeSub 2)
    (hsum : Module.finrank F P + Module.finrank F Q = 7)
    (hle : Module.finrank F P ≤ Module.finrank F Q) :
    2048 * rectHits ht P Q ≤ numVal 2 * (Nat.card P * Nat.card Q) := by
  classical
  have hQle := Submodule.finrank_mono hQ
  have hCdim := codeSub_finrank ht
  have hP3 : Module.finrank F P = 3 := by omega
  have hQ4 : Module.finrank F Q = 4 := by omega
  have hQeq : Q = codeSub 2 := Submodule.eq_of_le_of_finrank_eq hQ (by omega)
  subst hQeq
  let e : (Fin 4 → F) →ₗ[F] codeSub 2 :=
    { toFun := fun c => ⟨comb2 c, (codeSub_iff_codeF _).mpr (case_t2_kernel_check.1 c)⟩
      map_add' := fun a b => by
        apply Subtype.ext; funext i; simp only [comb2, Pi.add_apply, Submodule.coe_add]; ring
      map_smul' := fun r a => by
        apply Subtype.ext; funext i
        simp only [comb2, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, SetLike.val_smul]; ring }
  have he_inj : Function.Injective e := fun a b hab =>
    case_t2_kernel_check.2.1 a b (congrArg Subtype.val hab)
  have he_surj : Function.Surjective e := by
    have h1 := LinearMap.finrank_range_add_finrank_ker e
    have hker : Module.finrank F (LinearMap.ker e) = 0 := by
      rw [LinearMap.ker_eq_bot.mpr he_inj, finrank_bot]
    rw [hker, add_zero, Module.finrank_fin_fun] at h1
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by omega))
  let P4 : Submodule F (Fin 4 → F) := P.comap ((codeSub 2).subtype.comp e)
  have hP4_dim : Module.finrank F P4 = 3 := by
    let eP : P4 ≃ₗ[F] P :=
      { toFun := fun c => ⟨comb2 c.1, c.2⟩
        invFun := fun x =>
          let c := Classical.choose (he_surj ⟨x.1, hP x.2⟩)
          ⟨c, by
            have hc : comb2 c = x.1 := congrArg Subtype.val (Classical.choose_spec (he_surj ⟨x.1, hP x.2⟩))
            change comb2 c ∈ P; rw [hc]; exact x.2⟩
        left_inv := fun c => by
          dsimp only
          apply Subtype.ext
          exact he_inj (Classical.choose_spec (he_surj ⟨comb2 c.1, hP c.2⟩))
        right_inv := fun x => by
          dsimp only
          apply Subtype.ext
          exact congrArg (Subtype.val : codeSub 2 → Lane 2) (Classical.choose_spec (he_surj ⟨x.1, hP x.2⟩))
        map_add' := fun a b => by
          apply Subtype.ext; funext i; simp only [comb2, Pi.add_apply, Submodule.coe_add]; ring
        map_smul' := fun r a => by
          apply Subtype.ext; funext i
          simp only [comb2, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, SetLike.val_smul]; ring }
    rw [eP.finrank_eq, hP3]
  have hex_m : ∃ m : Fin 4 → F, m ≠ 0 ∧ ∀ c : Fin 4 → F, c ∈ P4 ↔ dot4 m c = 0 := by
    have hdual : Module.finrank F P4.dualAnnihilator = 1 := by
      have h := Subspace.finrank_add_finrank_dualAnnihilator_eq P4
      rw [hP4_dim, Module.finrank_fin_fun] at h
      omega
    have hne_bot : P4.dualAnnihilator ≠ ⊥ := by
      intro hbot; rw [hbot, finrank_bot] at hdual; omega
    obtain ⟨φ0, hφ0_mem, hφ0_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
    let φ : P4.dualAnnihilator := ⟨φ0, hφ0_mem⟩
    have hφne : φ ≠ 0 := fun h => hφ0_ne (congrArg Subtype.val h)
    let m : Fin 4 → F := fun k => φ.1 (Pi.single k 1)
    have hφ_eq : ∀ c : Fin 4 → F, φ.1 c = dot4 m c := by
      intro c
      have hc : c = c 0 • Pi.single 0 1 + c 1 • Pi.single 1 1 + c 2 • Pi.single 2 1 + c 3 • Pi.single 3 1 := by
        funext k; fin_cases k <;> simp
      conv_lhs => rw [hc]
      simp only [map_add, map_smul, smul_eq_mul, dot4, m]
      ring
    have hmne : m ≠ 0 := by
      intro hm0
      apply hφne
      apply Subtype.ext
      apply LinearMap.ext
      intro c
      rw [hφ_eq c, hm0]
      simp [dot4]
    have hker : P4 = LinearMap.ker φ.1 := by
      apply Submodule.eq_of_le_of_finrank_eq
      · intro c hc
        rw [LinearMap.mem_ker]
        exact (Submodule.mem_dualAnnihilator φ.1).mp φ.2 c hc
      · have h1 := LinearMap.finrank_range_add_finrank_ker φ.1
        have hsurj : Function.Surjective φ.1 := by
          obtain ⟨c0, hc0⟩ : ∃ c0, φ.1 c0 ≠ 0 := by
            by_contra h; push Not at h; exact hφne (Subtype.ext (LinearMap.ext h))
          intro z
          rcases F_cases z with rfl | rfl
          · exact ⟨0, map_zero _⟩
          · exact ⟨c0, (F_cases _).resolve_left hc0⟩
        rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
        omega
    refine ⟨m, hmne, fun c => ?_⟩
    rw [hker, LinearMap.mem_ker, hφ_eq c]
  obtain ⟨m, hmne, hm_iff⟩ := hex_m
  rw [rectHits_codeSub_eq ht, card_codeSub]
  have hPcard : Nat.card P = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := P), Nat.card_zmod, hP3]; norm_num
  have hCcard : cntS 2 ∅ = 16 := by
    have h := cnt_formula_nat 2 ∅
    have hc1 : cvalNat 2 ∅ = 1 := by decide
    rw [hc1] at h; simp at h; omega
  have hsum_eq : 4 * ∑ p ∈ Finset.univ.filter (fun p => p ∈ P), cntS 2 (Nb ht p) =
      ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → F => dot4 m c = 0),
        2 ^ (6 - (Nb (by decide : 0 < 2) (comb2 c)).card) *
          cvalNat 2 (Nb (by decide : 0 < 2) (comb2 c)) := by
    rw [Finset.mul_sum]
    have hbij : ∑ p ∈ Finset.univ.filter (fun p => p ∈ P), 4 * cntS 2 (Nb ht p) =
        ∑ c ∈ Finset.univ.filter (fun c : Fin 4 → F => dot4 m c = 0), 4 * cntS 2 (Nb ht (comb2 c)) := by
      symm
      refine Finset.sum_nbij comb2 ?_ ?_ ?_ ?_
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        exact (hm_iff c).mpr hc
      · intro a _ b _ h; exact case_t2_kernel_check.2.1 a b h
      · intro p hp
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp
        obtain ⟨c, hc⟩ := he_surj ⟨p, hP hp⟩
        have hcp : comb2 c = p := congrArg Subtype.val hc
        refine ⟨c, ?_, hcp⟩
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hm_iff c).mp (by change comb2 c ∈ P; rw [hcp]; exact hp)
      · intro _ _; rfl
    rw [hbij]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact cnt_formula_nat 2 (Nb ht (comb2 c))
  have hle104 := case_t2_kernel_check.2.2 m hmne
  rw [hPcard, hCcard]
  simp only [numVal, ↓reduceIte]
  omega

def isPair {t : ℕ} (w : Lane t) : Prop :=
  ∃ j k : Fin (3 * t), j ≠ k ∧ j.val % 3 = k.val % 3 ∧ ∀ i, w i ≠ 0 ↔ i = j ∨ i = k

def isRun3 {t : ℕ} (ht : 0 < t) (w : Lane t) : Prop :=
  ∃ j : Fin (3 * t), ∀ i, w i ≠ 0 ↔ i = j ∨ i = nx ht j ∨ i = nx ht (nx ht j)

def shape {t : ℕ} (ht : 0 < t) (w : Lane t) : Prop := isPair w ∨ isRun3 ht w

def parityCol (e : Fin 2) (j : Fin 3) : F :=
  if j.val = e.val ∨ j.val = 2 then 1 else 0

def colour {n : ℕ} (i : Fin n) : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩

lemma column_nonzero : ∀ j : Fin 3, ∃ e : Fin 2, parityCol e j ≠ 0 := by decide +kernel

lemma column_pair : ∀ i j : Fin 3, (∀ e : Fin 2, parityCol e i + parityCol e j = 0) ↔ i = j := by
  decide +kernel

lemma support_checks_code {t : ℕ} (x : Lane t) (hc : x ∈ codeSub t) :
    ∀ e : Fin 2, ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), parityCol e (colour i) = 0 := by
  classical
  intro e
  have hce : (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0 :=
    congrFun hc e
  apply Eq.trans _ hce
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : x i = 0
  · simp [h]
  · have h1 : x i = 1 := (F_cases _).resolve_left h
    by_cases test : i.val % 3 = e.val ∨ i.val % 3 = 2 <;>
      simp [h1, parityCol, colour, test]

lemma nx_growth {t : ℕ} (ht : 0 < t) (S : Finset (Fin (3 * t))) (hS : S.Nonempty)
    (hproper : S ≠ Finset.univ) :
    S.card < (S ∪ S.map ⟨nx ht, nx_inj ht⟩).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.subset_union_left, ?_⟩
  intro heq
  apply hproper
  obtain ⟨x, hx⟩ := hS
  have hclosed : ∀ y ∈ S, nx ht y ∈ S := fun y hy => by
    rw [heq]; exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨y, hy, rfl⟩)
  have hit : ∀ k : ℕ, (⟨(x.val + k) % (3 * t), Nat.mod_lt _ (by omega)⟩ : Fin (3 * t)) ∈ S := by
    intro k
    induction k with
    | zero => convert hx using 1; apply Fin.ext; simp [Nat.mod_eq_of_lt x.isLt]
    | succ k ih =>
      have h1 := hclosed _ ih
      convert h1 using 1
      apply Fin.ext
      simpa only [nx, Nat.add_assoc] using (Nat.mod_add_mod (x.val + k) (3 * t) 1).symm
  apply Finset.eq_univ_of_forall
  intro y
  have hy := hit (3 * t - x.val + y.val)
  have hsame : (⟨(x.val + (3 * t - x.val + y.val)) % (3 * t), Nat.mod_lt _ (by omega)⟩ : Fin (3 * t)) = y := by
    apply Fin.ext
    have hxlt := x.isLt; have hylt := y.isLt
    change (x.val + (3 * t - x.val + y.val)) % (3 * t) = y.val
    rw [show x.val + (3 * t - x.val + y.val) = y.val + 3 * t by omega]
    simp [Nat.mod_eq_of_lt hylt]
  rwa [hsame] at hy

lemma Nb_card_eq_union {t : ℕ} (ht : 0 < t) (w : Lane t) :
    let S := Finset.univ.filter (fun i : Fin (3 * t) => w i ≠ 0)
    (Nb ht w).card = (S ∪ S.map ⟨nx ht, nx_inj ht⟩).card := by
  classical
  intro S
  let pvEmb : Fin (3 * t) ↪ Fin (3 * t) :=
    ⟨pv ht, fun a b h => by have := congrArg (nx ht) h; rwa [nx_pv, nx_pv] at this⟩
  have hpvEmb : ∀ j, pvEmb j = pv ht j := fun _ => rfl
  have h1 : Nb ht w = S ∪ S.map pvEmb := by
    ext i
    simp only [Nb, S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_map, hpvEmb]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨nx ht i, h, pv_nx ht i⟩
    · rintro (h | ⟨j, hj, rfl⟩)
      · exact Or.inl h
      · exact Or.inr (by rwa [nx_pv])
  rw [h1]
  refine Finset.card_bij (fun i _ => nx ht i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_union, Finset.mem_map, hpvEmb] at hi ⊢
    rcases hi with h | ⟨j, hj, rfl⟩
    · exact Or.inr ⟨i, h, rfl⟩
    · exact Or.inl (by rwa [nx_pv])
  · intro a _ b _ h; exact nx_inj ht h
  · intro y hy
    simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk] at hy
    refine ⟨pv ht y, ?_, nx_pv ht y⟩
    simp only [Finset.mem_union, Finset.mem_map, hpvEmb]
    rcases hy with h | ⟨j, hj, rfl⟩
    · exact Or.inr ⟨y, h, rfl⟩
    · exact Or.inl (by rwa [pv_nx])

lemma nx_ne_self {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : nx ht i ≠ i := by
  intro h
  have h1 := congrArg Fin.val h
  have hi := i.isLt
  rw [nx_val] at h1
  split_ifs at h1 <;> omega

lemma nx_nx_ne_self {t : ℕ} (ht : 0 < t) (i : Fin (3 * t)) : nx ht (nx ht i) ≠ i := by
  intro h
  have h1 := congrArg Fin.val h
  have hi := i.isLt
  rw [nx_val, nx_val] at h1
  split_ifs at h1 <;> omega

lemma nx_three_ne_self {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t) (i : Fin (3 * t)) :
    nx ht (nx ht (nx ht i)) ≠ i := by
  intro h
  have h1 := congrArg Fin.val h
  have hi := i.isLt
  rw [nx_val, nx_val, nx_val] at h1
  split_ifs at h1 <;> omega

lemma isPair_iff_wt2 {t : ℕ} (w : Lane t) (hc : w ∈ codeSub t) :
    isPair w ↔ wt w = 2 := by
  classical
  constructor
  · rintro ⟨j, k, hjk, _, hw⟩
    unfold wt
    have hS : Finset.univ.filter (fun i => w i ≠ 0) = {j, k} := by
      ext i; simp [hw]
    rw [hS, Finset.card_pair hjk]
  · intro hwt
    unfold wt at hwt
    obtain ⟨j, k, hjk, hS⟩ := Finset.card_eq_two.mp hwt
    have hchk := support_checks_code w hc
    have hcol : colour j = colour k := by
      apply (column_pair _ _).mp
      intro e
      have he := hchk e
      rw [hS, Finset.sum_pair hjk] at he
      exact he
    refine ⟨j, k, hjk, congrArg Fin.val hcol, fun i => ?_⟩
    have := Finset.ext_iff.mp hS i
    simpa using this

lemma footprint_classify {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) (w : Lane t)
    (hw : w ≠ 0) (hc : w ∈ codeSub t) :
    4 ≤ (Nb ht w).card ∧ ((Nb ht w).card = 4 ↔ shape ht w) ∧ ((Nb ht w).card = 5 → wt w = 3) := by
  classical
  let S := Finset.univ.filter (fun i : Fin (3 * t) => w i ≠ 0)
  let f : Fin (3 * t) ↪ Fin (3 * t) := ⟨nx ht, nx_inj ht⟩
  have hf : ∀ x, f x = nx ht x := fun _ => rfl
  have hNb : (Nb ht w).card = (S ∪ S.map f).card := Nb_card_eq_union ht w
  have hSne : S.Nonempty := by
    by_contra h
    apply hw
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hSpos : 0 < S.card := Finset.card_pos.mpr hSne
  have hno1 : S.card ≠ 1 := no_wt_one ((codeSub_iff_codeF w).mp hc)
  have hge4 : 4 ≤ (S ∪ S.map f).card := by
    by_contra! hlt
    have hproper : S ≠ Finset.univ := by
      intro he; rw [he] at hlt
      have hle : (Finset.univ : Finset (Fin (3 * t))).card ≤ (Finset.univ ∪ Finset.univ.map f).card :=
        Finset.card_le_card Finset.subset_union_left
      rw [Finset.card_univ, Fintype.card_fin] at hle
      omega
    have hgr : S.card < (S ∪ S.map f).card := nx_growth ht S hSne hproper
    have hS2 : S.card = 2 := by omega
    obtain ⟨j, k, hjk, hSeq⟩ := Finset.card_eq_two.mp hS2
    have hcol : j.val % 3 = k.val % 3 := by
      have hp := (isPair_iff_wt2 w hc).mpr hS2
      obtain ⟨j', k', hjk', hcol', hiff⟩ := hp
      have heq : ({j, k} : Finset (Fin (3 * t))) = {j', k'} := by
        ext i; rw [← hSeq]; simp [S, hiff]
      have hjmem : j ∈ ({j', k'} : Finset (Fin (3 * t))) := heq ▸ Finset.mem_insert_self j {k}
      have hkmem : k ∈ ({j', k'} : Finset (Fin (3 * t))) := heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self k)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hjmem hkmem
      rcases hjmem with rfl | rfl <;> rcases hkmem with rfl | rfl
      · exact absurd rfl hjk
      · exact hcol'
      · exact hcol'.symm
      · exact absurd rfl hjk
    have h1 : f j ≠ f k := f.injective.ne hjk
    have h2 : f j ≠ j := nx_ne_self ht j
    have h3 : f k ≠ k := nx_ne_self ht k
    have h4 : f j ≠ k := fun h => nx_color ht j ((congrArg (fun z : Fin (3 * t) => z.val % 3) h).trans hcol.symm)
    have h5 : f k ≠ j := fun h => nx_color ht k ((congrArg (fun z : Fin (3 * t) => z.val % 3) h).trans hcol)
    rw [hSeq] at hlt
    have h4card : ({j, k} ∪ ({j, k} : Finset (Fin (3 * t))).map f).card = 4 := by
      simp [Finset.map_insert, Finset.map_singleton, Finset.insert_union, Finset.singleton_union,
        hjk, h1, h2, h3, h4, h5, h2.symm, h3.symm, h5.symm]
    omega
  refine ⟨hNb ▸ hge4, ?_, ?_⟩
  · rw [hNb]
    constructor
    · intro h4
      have hproper : S ≠ Finset.univ := by
        intro he
        have hle : (Finset.univ : Finset (Fin (3 * t))).card ≤ (S ∪ S.map f).card := by
          rw [he]; exact Finset.card_le_card Finset.subset_union_left
        rw [Finset.card_univ, Fintype.card_fin] at hle
        omega
      have hgr : S.card < (S ∪ S.map f).card := nx_growth ht S hSne hproper
      have h23 : S.card = 2 ∨ S.card = 3 := by omega
      rcases h23 with h2 | h3
      · exact Or.inl ((isPair_iff_wt2 w hc).mpr h2)
      · right
        have hcount := Finset.card_union_add_card_inter S (S.map f)
        rw [Finset.card_map, h3, h4] at hcount
        have hinter : 1 < (S ∩ S.map f).card := by omega
        obtain ⟨v, hv, z, hz, hvz⟩ := Finset.one_lt_card.mp hinter
        obtain ⟨hvS, hvf⟩ := Finset.mem_inter.mp hv
        obtain ⟨hzS, hzf⟩ := Finset.mem_inter.mp hz
        obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hvf
        obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hzf
        have huq : u ≠ q := fun h => hvz (congrArg f h)
        have hcross : f u = q ∨ f q = u := by
          by_contra! h
          have hsub : ({u, f u, q, f q} : Finset (Fin (3 * t))) ⊆ S := by
            simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨hu, hvS, hq, hzS⟩
          have hcard := Finset.card_le_card hsub
          have hne_u : u ≠ f u := (nx_ne_self ht u).symm
          have hne_q : q ≠ f q := (nx_ne_self ht q).symm
          have hne_ufq : u ≠ f q := h.2.symm
          have h4c : ({u, f u, q, f q} : Finset (Fin (3 * t))).card = 4 := by
            rw [Finset.card_insert_of_notMem (by simp [hne_u, huq, hne_ufq]),
              Finset.card_insert_of_notMem (by simp [h.1, hvz]),
              Finset.card_pair hne_q]
          omega
        have mk3 : ∀ a : Fin (3 * t), a ∈ S → f a ∈ S → f (f a) ∈ S → isRun3 ht w := by
          intro a ha hb hc'
          have hSeq : S = {a, f a, f (f a)} := by
            symm
            apply Finset.eq_of_subset_of_card_le
            · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨ha, hb, hc'⟩
            · have h1 : a ≠ f a := (nx_ne_self ht a).symm
              have h2 : a ≠ f (f a) := (nx_nx_ne_self ht a).symm
              have h3' : f a ≠ f (f a) := (nx_ne_self ht (f a)).symm
              rw [Finset.card_insert_of_notMem (by simp [h1, h2]), Finset.card_pair h3', h3]
          refine ⟨a, fun i => ?_⟩
          have := Finset.ext_iff.mp hSeq i
          simpa [S, hf] using this
        rcases hcross with rfl | h
        · exact mk3 u hu hvS hzS
        · exact mk3 q hq hzS (h ▸ hvS)
    · intro hs
      apply le_antisymm _ hge4
      rcases hs with ⟨j, k, _, _, hiff⟩ | ⟨j, hiff⟩
      · have hSeq : S = {j, k} := by ext i; simp [S, hiff]
        rw [hSeq]
        have hu := Finset.card_union_le ({j, k} : Finset (Fin (3 * t))) (({j, k} : Finset (Fin (3 * t))).map f)
        rw [Finset.card_map] at hu
        have hh := Finset.card_insert_le j ({k} : Finset (Fin (3 * t)))
        simp only [Finset.card_singleton] at hh
        omega
      · have hSeq : S = {j, f j, f (f j)} := by ext i; simp [S, f, hiff]
        rw [hSeq]
        have hsub : ({j, f j, f (f j)} ∪ ({j, f j, f (f j)} : Finset (Fin (3 * t))).map f) ⊆
            ({j, f j, f (f j), f (f (f j))} : Finset (Fin (3 * t))) := by
          intro x hx
          simp only [Finset.map_insert, Finset.map_singleton, Finset.mem_union,
            Finset.mem_insert, Finset.mem_singleton] at *
          tauto
        have hu := Finset.card_le_card hsub
        have h1 := Finset.card_insert_le j ({f j, f (f j), f (f (f j))} : Finset (Fin (3 * t)))
        have h2 := Finset.card_insert_le (f j) ({f (f j), f (f (f j))} : Finset (Fin (3 * t)))
        have h3 := Finset.card_insert_le (f (f j)) ({f (f (f j))} : Finset (Fin (3 * t)))
        simp only [Finset.card_singleton] at h3
        omega
  · rw [hNb]
    intro h5
    have hproper : S ≠ Finset.univ := by
      intro he
      have hle : (Finset.univ : Finset (Fin (3 * t))).card ≤ (S ∪ S.map f).card := by
        rw [he]; exact Finset.card_le_card Finset.subset_union_left
      rw [Finset.card_univ, Fintype.card_fin] at hle
      omega
    have hgr : S.card < (S ∪ S.map f).card := nx_growth ht S hSne hproper
    have hle4 : S.card ≤ 4 := by omega
    have hne2 : S.card ≠ 2 := by
      intro h2
      have hu := Finset.card_union_le S (S.map f)
      rw [Finset.card_map] at hu
      omega
    have hne4 : S.card ≠ 4 := by
      intro h4
      have hcount := Finset.card_union_add_card_inter S (S.map f)
      rw [Finset.card_map, h4, h5] at hcount
      have hdiff : (S \ S.map f).card = 1 := by
        have := Finset.card_sdiff_add_card_inter S (S.map f)
        omega
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hdiff
      have haS : a ∈ S := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).1
      have ha_not_in : a ∉ S.map f := (Finset.mem_sdiff.mp (ha ▸ Finset.mem_singleton_self a)).2
      have hprev_out : pv ht a ∉ S := fun hp => ha_not_in (Finset.mem_map.mpr ⟨pv ht a, hp, nx_pv ht a⟩)
      have hstep : ∀ x ∈ S, x ≠ a → pv ht x ∈ S := by
        intro x hx hne
        have hxin : x ∈ S.map f := by
          by_contra hnot
          have : x ∈ S \ S.map f := Finset.mem_sdiff.mpr ⟨hx, hnot⟩
          rw [ha, Finset.mem_singleton] at this
          exact hne this
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hxin
        rw [hf, pv_nx]; exact hy
      have hchain : ∀ m : ℕ, (∀ k < m, (nx ht)^[k] a ∈ S) → m < 4 → (nx ht)^[m] a ∈ S := by
        intro m hlt hm
        by_contra hnot
        have hmpos : 0 < m := by
          by_contra hm0; have : m = 0 := by omega
          subst this; exact hnot haS
        have hsub : (Finset.range m).image (fun k => (nx ht)^[k] a) ⊆ S := by
          intro x hx
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
          exact hlt k (Finset.mem_range.mp hk)
        have hcard_lt : ((Finset.range m).image (fun k => (nx ht)^[k] a)).card < S.card := by
          have := Finset.card_image_le (s := Finset.range m) (f := fun k => (nx ht)^[k] a)
          rw [Finset.card_range] at this
          omega
        obtain ⟨b, hbS, hbnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
        have hiter : ∀ k : ℕ, (pv ht)^[k] b ∈ S ∧ (pv ht)^[k] b ∉ (Finset.range m).image (fun j => (nx ht)^[j] a) := by
          intro k
          induction k with
          | zero => exact ⟨hbS, hbnot⟩
          | succ k ih =>
            rw [Function.iterate_succ_apply']
            have hne_a : (pv ht)^[k] b ≠ a := fun he =>
              ih.2 (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hmpos, by simpa using he.symm⟩)
            have hpin : pv ht ((pv ht)^[k] b) ∈ S := hstep _ ih.1 hne_a
            refine ⟨hpin, fun him => ?_⟩
            obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp him
            have hjlt : j < m := Finset.mem_range.mp hj
            have hnext : (pv ht)^[k] b = (nx ht)^[j + 1] a := by
              rw [Function.iterate_succ_apply', hjeq, nx_pv]
            by_cases hjtop : j + 1 < m
            · exact ih.2 (Finset.mem_image.mpr ⟨j + 1, Finset.mem_range.mpr hjtop, hnext.symm⟩)
            · have hjeq' : j + 1 = m := by omega
              rw [hjeq'] at hnext
              exact hnot (hnext ▸ ih.1)
        have hreach : ∃ k : ℕ, (pv ht)^[k] b = a := by
          have hpn : ∀ k : ℕ, (pv ht)^[k] ((nx ht)^[k] a) = a := by
            intro k
            induction k with
            | zero => rfl
            | succ k ih' =>
              rw [Function.iterate_succ_apply' (nx ht), Function.iterate_succ_apply (pv ht), pv_nx, ih']
          have hiter_nx : ∀ k : ℕ, ((nx ht)^[k] a).val = (a.val + k) % (3 * t) := by
            intro k
            induction k with
            | zero => simp [Nat.mod_eq_of_lt a.isLt]
            | succ k ih' =>
              rw [Function.iterate_succ_apply']
              change (((nx ht)^[k] a).val + 1) % (3 * t) = _
              rw [ih', Nat.mod_add_mod, add_assoc]
          let k0 : ℕ := (b.val + 3 * t - a.val) % (3 * t)
          have hnx_eq : (nx ht)^[k0] a = b := by
            apply Fin.ext
            rw [hiter_nx k0]
            have ha' := a.isLt; have hb' := b.isLt
            dsimp only [k0]
            rw [Nat.add_mod_mod]
            have hsum : a.val + (b.val + 3 * t - a.val) = b.val + 3 * t := by omega
            rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hb']
          exact ⟨k0, hnx_eq ▸ hpn k0⟩
        obtain ⟨k, hk⟩ := hreach
        exact (hiter k).2 (Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hmpos, by simpa using hk.symm⟩)
      have h0 : a ∈ S := haS
      have h1 : f a ∈ S := hchain 1 (fun k hk => by interval_cases k; exact h0) (by omega)
      have h2 : f (f a) ∈ S := hchain 2 (fun k hk => by interval_cases k; exact h0; exact h1) (by omega)
      have h3 : f (f (f a)) ∈ S := hchain 3 (fun k hk => by interval_cases k; exact h0; exact h1; exact h2) (by omega)
      have hne01 : a ≠ f a := (nx_ne_self ht a).symm
      have hne02 : a ≠ f (f a) := (nx_nx_ne_self ht a).symm
      have hne03 : a ≠ f (f (f a)) := (nx_three_ne_self ht (by omega) a).symm
      have hne12 : f a ≠ f (f a) := (nx_ne_self ht (f a)).symm
      have hne13 : f a ≠ f (f (f a)) := (nx_nx_ne_self ht (f a)).symm
      have hne23 : f (f a) ≠ f (f (f a)) := (nx_ne_self ht (f (f a))).symm
      have hSeq : S = {a, f a, f (f a), f (f (f a))} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]; exact ⟨h0, h1, h2, h3⟩
        · rw [Finset.card_insert_of_notMem (by simp [hne01, hne02, hne03]),
            Finset.card_insert_of_notMem (by simp [hne12, hne13]),
            Finset.card_pair hne23, h4]
      have hchk := support_checks_code w hc
      have hmod1 : (f a).val % 3 = (a.val + 1) % 3 := by
        have := a.isLt; rw [hf, nx_val]; split_ifs <;> omega
      have hmod2 : (f (f a)).val % 3 = (a.val + 2) % 3 := by
        have := (f a).isLt; rw [hf, nx_val]; split_ifs <;> omega
      have hmod3 : (f (f (f a))).val % 3 = a.val % 3 := by
        have := (f (f a)).isLt; rw [hf, nx_val]; split_ifs <;> omega
      obtain ⟨e, hene⟩ := column_nonzero (colour a)
      have he0 := hchk e
      rw [show Finset.univ.filter (fun i => w i ≠ 0) = S from rfl, hSeq] at he0
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, hne01, hne02, hne03,
        hne12, hne13, hne23, or_self, not_false_eq_true, Finset.sum_singleton] at he0
      have h3sum : ∀ (e' : Fin 2) (c : Fin 3), parityCol e' c +
          parityCol e' ⟨(c.val + 1) % 3, Nat.mod_lt _ (by decide)⟩ +
          parityCol e' ⟨(c.val + 2) % 3, Nat.mod_lt _ (by decide)⟩ = 0 := by
        decide +kernel
      have hc1 : colour (f a) = ⟨((colour a).val + 1) % 3, Nat.mod_lt _ (by decide)⟩ := by
        apply Fin.ext; dsimp only [colour]; rw [hmod1]; omega
      have hc2 : colour (f (f a)) = ⟨((colour a).val + 2) % 3, Nat.mod_lt _ (by decide)⟩ := by
        apply Fin.ext; dsimp only [colour]; rw [hmod2]; omega
      have hc3 : colour (f (f (f a))) = colour a := by
        apply Fin.ext; dsimp only [colour]; exact hmod3
      rw [hc1, hc2, hc3] at he0
      have h00 := h3sum e (colour a)
      apply hene
      linear_combination he0 - h00
    change S.card = 3
    omega

lemma wfib_bounds {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) (w : Lane t) (hw : w ≠ 0) (hc : w ∈ codeSub t) :
    ((Nb ht w).card = 4 → 64 * (cntS t (Nb ht w) : ℚ) = 4 * (cntS t ∅ : ℚ)) ∧
    ((Nb ht w).card = 5 → 64 * (cntS t (Nb ht w) : ℚ) = 2 * (cntS t ∅ : ℚ)) ∧
    (6 ≤ (Nb ht w).card → 64 * (cntS t (Nb ht w) : ℚ) ≤ (cntS t ∅ : ℚ)) := by
  have hpos : (0 : ℚ) ≤ cntS t ∅ := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · intro h4
    rw [cntS_ratio ht, h4, cval_one (by rw [h4]; omega)]
    ring
  · intro h5
    rw [cntS_ratio ht, h5, cval_one (by rw [h5]; omega)]
    ring
  · intro h6
    rw [cntS_ratio ht]
    by_cases h8 : 8 ≤ (Nb ht w).card
    · have hpow : (1 / 2 : ℚ) ^ (Nb ht w).card ≤ (1 / 2) ^ 8 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h8
      have hc4 := cval_le t (Nb ht w)
      have hprod : 64 * ((1 / 2 : ℚ) ^ (Nb ht w).card * cval t (Nb ht w)) ≤ 1 := by
        calc 64 * ((1 / 2 : ℚ) ^ (Nb ht w).card * cval t (Nb ht w))
            ≤ 64 * ((1 / 2 : ℚ) ^ 8 * 4) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact mul_le_mul hpow hc4 (by unfold cval cvalNat; positivity) (by positivity)
          _ = 1 := by norm_num
      nlinarith
    · by_cases h7 : (Nb ht w).card = 7
      · rw [h7]
        have hc2 : cval t (Nb ht w) ≤ 2 := cval_le_two_of_lt (by rw [h7]; omega)
        nlinarith
      · have heq6 : (Nb ht w).card = 6 := by omega
        by_cases ht4 : 4 ≤ t
        · rw [heq6, cval_one (by rw [heq6]; omega)]
          linarith
        · have ht3eq : t = 3 := by omega
          subst ht3eq
          have hc1 : cval 3 (Nb ht w) = 1 := by
            have hnotR : ∀ R : Finset (Fin 9), R = R0 3 ∨ R = R1 3 ∨ R = R2 3 → ¬ R ⊆ Nb ht w := by
              intro R hR hsub
              have hRcard : R.card = 6 := by
                rcases hR with rfl | rfl | rfl <;> decide
              have hReq : R = Nb ht w := Finset.eq_of_subset_of_card_le hsub (by omega)
              have hmono : ∀ i : Fin 9, w i ≠ 0 →
                  (R = R0 3 → i.val % 3 = 0) ∧ (R = R1 3 → i.val % 3 = 2) ∧ (R = R2 3 → i.val % 3 = 1) := by
                intro i hi
                have hin1 : i ∈ Nb ht w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hi⟩
                have hin2 : pv ht i ∈ Nb ht w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by rwa [nx_pv])⟩
                rw [← hReq] at hin1 hin2
                have hilt := i.isLt
                have hpv := pv_val ht i
                refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> subst h
                · simp only [R0, Finset.mem_filter, Finset.mem_univ, true_and] at hin1 hin2
                  by_cases hi0 : i.val = 0 <;> simp only [hpv, hi0, ↓reduceIte] at hin2 <;> omega
                · simp only [R1, Finset.mem_filter, Finset.mem_univ, true_and] at hin1 hin2
                  by_cases hi0 : i.val = 0 <;> simp only [hpv, hi0, ↓reduceIte] at hin2 <;> omega
                · simp only [R2, Finset.mem_filter, Finset.mem_univ, true_and] at hin1 hin2
                  by_cases hi0 : i.val = 0 <;> simp only [hpv, hi0, ↓reduceIte] at hin2 <;> omega
              have hsupp_sub : ∃ a : ℕ, ∀ i : Fin 9, w i ≠ 0 → i.val % 3 = a := by
                rcases hR with h | h | h
                · exact ⟨0, fun i hi => (hmono i hi).1 h⟩
                · exact ⟨2, fun i hi => (hmono i hi).2.1 h⟩
                · exact ⟨1, fun i hi => (hmono i hi).2.2 h⟩
              obtain ⟨a, ha⟩ := hsupp_sub
              have hsep : ∀ i : Fin 9, ¬ (w i ≠ 0 ∧ w (nx ht i) ≠ 0) := by
                intro i ⟨h1, h2⟩
                exact nx_color ht i ((ha _ h2).trans (ha _ h1).symm)
              have hnb2 := card_Nb ht w hsep
              have hwt3 : wt w = 3 := by omega
              have hchk := support_checks_code w hc
              obtain ⟨e, hene⟩ := column_nonzero ⟨a % 3, Nat.mod_lt _ (by decide)⟩
              have he0 := hchk e
              have hconst : ∀ i ∈ Finset.univ.filter (fun i : Fin 9 => w i ≠ 0),
                  parityCol e (colour i) = parityCol e ⟨a % 3, Nat.mod_lt _ (by decide)⟩ := by
                intro i hi
                have hm := ha i (Finset.mem_filter.mp hi).2
                refine congrArg (parityCol e) (Fin.ext ?_)
                dsimp only [colour]; omega
              rw [Finset.sum_congr rfl hconst, Finset.sum_const, show (Finset.univ.filter (fun i : Fin 9 => w i ≠ 0)).card = wt w from rfl, hwt3] at he0
              have h3eq : (3 : ℕ) • parityCol e ⟨a % 3, Nat.mod_lt _ (by decide)⟩ =
                  parityCol e ⟨a % 3, Nat.mod_lt _ (by decide)⟩ := by
                rcases F_cases (parityCol e ⟨a % 3, Nat.mod_lt _ (by decide)⟩) with h | h <;> rw [h] <;> decide
              rw [h3eq] at he0
              exact hene he0
            unfold cval cvalNat
            simp [hnotR (R0 3) (Or.inl rfl), hnotR (R1 3) (Or.inr (Or.inl rfl)),
              hnotR (R2 3) (Or.inr (Or.inr rfl))]
          rw [heq6, hc1]
          linarith

open Classical in
lemma cntS_le_of_nonzero {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) (w : Lane t)
    (hw : w ≠ 0) (hc : w ∈ codeSub t) :
    64 * (cntS t (Nb ht w) : ℚ) ≤
      (if shape ht w then 4 else if (Nb ht w).card = 5 then 2 else 1) * (cntS t ∅ : ℚ) := by
  have hfc := footprint_classify ht ht3 w hw hc
  have hwb := wfib_bounds ht ht3 w hw hc
  split_ifs with hs h5
  · rw [hwb.1 (hfc.2.1.mpr hs)]
  · rw [hwb.2.1 h5]
  · have h6 : 6 ≤ (Nb ht w).card := by
      have hne4 : (Nb ht w).card ≠ 4 := fun h => hs (hfc.2.1.mp h)
      omega
    simpa using hwb.2.2 h6

def parityL (n : ℕ) : (Fin n → F) →ₗ[F] F where
  toFun x := ∑ i : Fin n, x i
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]

lemma parityL_eq_wt {n : ℕ} (x : Fin n → F) : parityL n x = (wt x : F) := by
  classical
  change (∑ i : Fin n, x i) = ((Finset.univ.filter (fun i => x i ≠ 0)).card : F)
  rw [← Finset.sum_filter_ne_zero]
  have h1 : ∀ i ∈ Finset.univ.filter (fun i => x i ≠ 0), x i = 1 :=
    fun i hi => (F_cases _).resolve_left (Finset.mem_filter.mp hi).2
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma wt_pair_eq_two {t : ℕ} {w : Lane t} (h : isPair w) : wt w = 2 := by
  classical
  obtain ⟨j, k, hjk, _, hiff⟩ := h
  unfold wt
  have hS : Finset.univ.filter (fun i => w i ≠ 0) = {j, k} := by ext i; simp [hiff]
  rw [hS, Finset.card_pair hjk]

lemma wt_run3_eq_three {t : ℕ} (ht : 0 < t) {w : Lane t} (h : isRun3 ht w) : wt w = 3 := by
  classical
  obtain ⟨j, hiff⟩ := h
  unfold wt
  have hS : Finset.univ.filter (fun i => w i ≠ 0) = {j, nx ht j, nx ht (nx ht j)} := by
    ext i; simp [hiff]
  rw [hS]
  have h1 : j ≠ nx ht j := (nx_ne_self ht j).symm
  have h2 : j ≠ nx ht (nx ht j) := (nx_nx_ne_self ht j).symm
  have h3 : nx ht j ≠ nx ht (nx ht j) := (nx_ne_self ht (nx ht j)).symm
  simp [h1, h2, h3]

lemma parityL_pair {t : ℕ} {w : Lane t} (h : isPair w) : parityL (3 * t) w = 0 := by
  rw [parityL_eq_wt, wt_pair_eq_two h]; decide

lemma parityL_run3 {t : ℕ} (ht : 0 < t) {w : Lane t} (h : isRun3 ht w) : parityL (3 * t) w = 1 := by
  rw [parityL_eq_wt, wt_run3_eq_three ht h]; decide

lemma parityL_nb5 {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) {w : Lane t} (hw : w ≠ 0) (hc : w ∈ codeSub t)
    (h5 : (Nb ht w).card = 5) : parityL (3 * t) w = 1 := by
  rw [parityL_eq_wt, (footprint_classify ht ht3 w hw hc).2.2 h5]; decide

def pairVec {n : ℕ} (i j : Fin n) : Fin n → F := Pi.single i 1 + Pi.single j 1

lemma pairVec_apply {n : ℕ} {i j : Fin n} (hij : i ≠ j) (a : Fin n) :
    pairVec i j a = if a = i ∨ a = j then 1 else 0 := by
  by_cases h1 : a = i
  · subst h1; simp [pairVec, hij]
  · by_cases h2 : a = j
    · subst h2; simp [pairVec, Ne.symm hij]
    · simp [pairVec, h1, h2]

lemma pairVec_comm {n : ℕ} (i j : Fin n) : pairVec i j = pairVec j i := add_comm _ _

lemma pairVec_add_cancel {n : ℕ} (i j k : Fin n) :
    pairVec i j + pairVec j k = pairVec i k := by
  funext a
  simp only [pairVec, Pi.add_apply]
  have hz := z2_add_self ((Pi.single (M := fun _ => F) j (1 : F)) a)
  linear_combination hz

lemma isPair_eq_pairVec {t : ℕ} {w : Lane t} (h : isPair w) :
    ∃ j k : Fin (3 * t), j ≠ k ∧ j.val % 3 = k.val % 3 ∧ w = pairVec j k := by
  obtain ⟨j, k, hjk, hcol, hiff⟩ := h
  refine ⟨j, k, hjk, hcol, ?_⟩
  funext i
  by_cases hi : i = j
  · subst hi; simp [pairVec, hjk, (F_cases _).resolve_left ((hiff i).mpr (Or.inl rfl))]
  · by_cases hk : i = k
    · subst hk; simp [pairVec, Ne.symm hjk, (F_cases _).resolve_left ((hiff i).mpr (Or.inr rfl))]
    · have h0 : w i = 0 := by by_contra hn; rcases (hiff i).mp hn with rfl | rfl <;> contradiction
      simp [pairVec, h0, hi, hk]

lemma pairVec_isPair {t : ℕ} {j k : Fin (3 * t)} (hjk : j ≠ k) (hcol : j.val % 3 = k.val % 3) :
    isPair (pairVec j k) := by
  refine ⟨j, k, hjk, hcol, fun i => ?_⟩
  by_cases hi : i = j
  · subst hi; simp [pairVec, hjk]
  · by_cases hk : i = k
    · subst hk; simp [pairVec, Ne.symm hjk]
    · simp [pairVec, hi, hk]

open Classical in
lemma pair_clique_decomp {t : ℕ} (E : Submodule F (Lane t)) (hE : E ≤ codeSub t) :
    ∃ cs : Finset (Finset (Fin (3 * t))),
      (∀ C ∈ cs, 2 ≤ C.card ∧ mono C) ∧
      (∀ C1 ∈ cs, ∀ C2 ∈ cs, C1 ≠ C2 → Disjoint C1 C2) ∧
      (∑ C ∈ cs, (C.card - 1)) ≤ Module.finrank F E ∧
      (Finset.univ.filter (fun x : Lane t => x ∈ E ∧ isPair x)).card =
        ∑ C ∈ cs, C.card * (C.card - 1) / 2 ∧
      (∀ C ∈ cs, ∀ i ∈ C, ∀ j ∈ C, i ≠ j → pairVec i j ∈ E) ∧
      (∀ x ∈ E, isPair x → ∃ C ∈ cs, ∃ i ∈ C, ∃ j ∈ C, i ≠ j ∧ x = pairVec i j) := by
  let cls (i : Fin (3 * t)) : Finset (Fin (3 * t)) :=
    Finset.univ.filter (fun j => j = i ∨ pairVec i j ∈ E)
  have hmem_self : ∀ i, i ∈ cls i := fun i => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
  have hsym : ∀ i j, j ∈ cls i → i ∈ cls j := by
    intro i j hj
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases hj with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (by rwa [pairVec_comm])
  have htrans : ∀ i j k, j ∈ cls i → k ∈ cls j → k ∈ cls i := by
    intro i j k hij hjk
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hij hjk ⊢
    rcases hij with rfl | h1
    · exact hjk
    · rcases hjk with rfl | h2
      · exact Or.inr h1
      · by_cases hik : k = i
        · exact Or.inl hik
        · right
          rw [← pairVec_add_cancel i j k]
          exact E.add_mem h1 h2
  have hcls_eq : ∀ i j, j ∈ cls i → cls j = cls i := by
    intro i j hj
    ext k
    exact ⟨fun hk => htrans i j k hj hk, fun hk => htrans j i k (hsym i j hj) hk⟩
  have hcls_mono : ∀ i, mono (cls i) := by
    intro i a ha b hb
    have hab : b ∈ cls a := by rw [hcls_eq i a ha]; exact hb
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hab
    rcases hab with rfl | hp
    · rfl
    · by_cases hne : a = b
      · rw [hne]
      · have hwt2 : wt (pairVec a b) = 2 := by
          unfold wt
          have hS : Finset.univ.filter (fun z : Fin (3 * t) => pairVec a b z ≠ 0) = {a, b} := by
            ext z
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton, pairVec_apply hne]
            split_ifs with h <;> simp [h]
          rw [hS, Finset.card_pair hne]
        obtain ⟨j, k, hjk, hcol, hiff⟩ := (isPair_iff_wt2 _ (hE hp)).mpr hwt2
        have ha1 : a = j ∨ a = k := (hiff a).mp (by rw [pairVec_apply hne]; simp)
        have hb1 : b = j ∨ b = k := (hiff b).mp (by rw [pairVec_apply hne]; simp)
        rcases ha1 with rfl | rfl <;> rcases hb1 with rfl | rfl <;> omega
  let cs : Finset (Finset (Fin (3 * t))) :=
    (Finset.univ.image cls).filter (fun C => 2 ≤ C.card)
  have hcs_prop : ∀ C ∈ cs, 2 ≤ C.card ∧ mono C := by
    intro C hC
    obtain ⟨hCim, hC2⟩ := Finset.mem_filter.mp hC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hCim
    exact ⟨hC2, hcls_mono i⟩
  have hcs_disj : ∀ C1 ∈ cs, ∀ C2 ∈ cs, C1 ≠ C2 → Disjoint C1 C2 := by
    intro C1 h1 C2 h2 hne
    obtain ⟨i1, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h1).1
    obtain ⟨i2, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h2).1
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    exact hne ((hcls_eq i1 k hk1).symm.trans (hcls_eq i2 k hk2))
  have hcs_pair : ∀ C ∈ cs, ∀ i ∈ C, ∀ j ∈ C, i ≠ j → pairVec i j ∈ E := by
    intro C hC i hi j hj hij
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hC).1
    have hji : j ∈ cls i := by rw [hcls_eq a i hi]; exact hj
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hji
    exact hji.resolve_left (Ne.symm hij)
  have hcs_cov : ∀ x ∈ E, isPair x → ∃ C ∈ cs, ∃ i ∈ C, ∃ j ∈ C, i ≠ j ∧ x = pairVec i j := by
    intro x hx hp
    obtain ⟨i, j, hij, _, rfl⟩ := isPair_eq_pairVec hp
    have hj : j ∈ cls i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hx⟩
    have hcard2 : 2 ≤ (cls i).card := by
      have hsub : ({i, j} : Finset (Fin (3 * t))) ⊆ cls i := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hmem_self _
        · exact hj
      calc 2 = ({i, j} : Finset (Fin (3 * t))).card := (Finset.card_pair hij).symm
        _ ≤ (cls i).card := Finset.card_le_card hsub
    exact ⟨cls i, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hcard2⟩,
      i, hmem_self i, j, hj, hij, rfl⟩
  have hrank : (∑ C ∈ cs, (C.card - 1)) ≤ Module.finrank F E := by
    let rep : ∀ C ∈ cs, Fin (3 * t) := fun C hC =>
      Classical.choose (Finset.card_pos.mp (show 0 < C.card by have := (hcs_prop C hC).1; omega))
    have hrep_mem : ∀ C (hC : C ∈ cs), rep C hC ∈ C := fun C hC =>
      Classical.choose_spec (Finset.card_pos.mp (show 0 < C.card by have := (hcs_prop C hC).1; omega))
    let idx := Σ C : cs, {i : Fin (3 * t) // i ∈ C.1 ∧ i ≠ rep C.1 C.2}
    let vec : idx → E := fun s =>
      ⟨pairVec (rep s.1.1 s.1.2) s.2.1, hcs_pair s.1.1 s.1.2 _ (hrep_mem s.1.1 s.1.2) s.2.1 s.2.2.1 (Ne.symm s.2.2.2)⟩
    have hlin : LinearIndependent F vec := by
      rw [Fintype.linearIndependent_iff]
      intro g hg s
      have hval := congrFun (congrArg Subtype.val hg) s.2.1
      simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        ZeroMemClass.coe_zero, Pi.zero_apply] at hval
      rw [Finset.sum_eq_single s] at hval
      · have hone : (vec s).1 s.2.1 = 1 := by
          change pairVec (rep s.1.1 s.1.2) s.2.1 s.2.1 = 1
          rw [pairVec_apply (Ne.symm s.2.2.2)]; simp
        rw [hone, mul_one] at hval
        exact hval
      · intro s' _ hsne
        have hzero : (vec s').1 s.2.1 = 0 := by
          change pairVec (rep s'.1.1 s'.1.2) s'.2.1 s.2.1 = 0
          rw [pairVec_apply (Ne.symm s'.2.2.2)]
          by_cases hCeq : s'.1 = s.1
          · have hneq : s.2.1 ≠ s'.2.1 := fun heq => hsne (by
              cases s; cases s'; dsimp only at hCeq heq; subst hCeq
              congr 1; exact Subtype.ext heq.symm)
            have hne_rep : s.2.1 ≠ rep s'.1.1 s'.1.2 := by rw [hCeq]; exact s.2.2.2
            simp [hneq, hne_rep]
          · have hdisj := hcs_disj s'.1.1 s'.1.2 s.1.1 s.1.2 (fun h => hCeq (Subtype.ext h))
            have h1 : s.2.1 ≠ rep s'.1.1 s'.1.2 := fun h =>
              Finset.disjoint_left.mp hdisj (h ▸ hrep_mem s'.1.1 s'.1.2) s.2.2.1
            have h2 : s.2.1 ≠ s'.2.1 := fun h =>
              Finset.disjoint_left.mp hdisj (h ▸ s'.2.2.1) s.2.2.1
            simp [h1, h2]
        rw [hzero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ s) h
    have hcard_idx : Fintype.card idx = ∑ C ∈ cs, (C.card - 1) := by
      rw [Fintype.card_sigma, ← Finset.sum_coe_sort cs (fun C => C.card - 1)]
      refine Finset.sum_congr rfl fun C _ => ?_
      have he : {i : Fin (3 * t) // i ∈ C.1 ∧ i ≠ rep C.1 C.2} ≃ (C.1.erase (rep C.1 C.2)) :=
        { toFun := fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2.2, x.2.1⟩⟩
          invFun := fun x => ⟨x.1, (Finset.mem_erase.mp x.2).2, (Finset.mem_erase.mp x.2).1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr he, Fintype.card_coe, Finset.card_erase_of_mem (hrep_mem C.1 C.2)]
    rw [← hcard_idx]
    exact hlin.fintype_card_le_finrank
  have hcount : (Finset.univ.filter (fun x : Lane t => x ∈ E ∧ isPair x)).card =
      ∑ C ∈ cs, C.card * (C.card - 1) / 2 := by
    let pairOf (C : Finset (Fin (3 * t))) : Finset (Lane t) :=
      (C.powersetCard 2).image (fun s => fun i => if i ∈ s then (1 : F) else 0)
    have hpair_card : ∀ C ∈ cs, (pairOf C).card = C.card * (C.card - 1) / 2 := by
      intro C _
      rw [Finset.card_image_of_injOn, Finset.card_powersetCard, Nat.choose_two_right]
      intro s1 hs1 s2 hs2 heq
      ext i
      have h1 := congrFun heq i
      by_cases hi1 : i ∈ s1 <;> by_cases hi2 : i ∈ s2 <;> simp [hi1, hi2] at h1 ⊢
    have hbi : Finset.univ.filter (fun x : Lane t => x ∈ E ∧ isPair x) = cs.biUnion pairOf := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · rintro ⟨hx, hp⟩
        obtain ⟨C, hC, i, hi, j, hj, hij, rfl⟩ := hcs_cov x hx hp
        refine ⟨C, hC, Finset.mem_image.mpr ⟨{i, j}, Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hij⟩, ?_⟩⟩
        · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        · funext z; rw [pairVec_apply hij]; simp only [Finset.mem_insert, Finset.mem_singleton]
      · rintro ⟨C, hC, hx⟩
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨hsub, hcard2⟩ := Finset.mem_powersetCard.mp hs
        obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard2
        have hi : i ∈ C := hsub (Finset.mem_insert_self i {j})
        have hj : j ∈ C := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self j))
        have heq : (fun z => if z ∈ ({i, j} : Finset (Fin (3 * t))) then (1 : F) else 0) = pairVec i j := by
          funext z; rw [pairVec_apply hij]; simp only [Finset.mem_insert, Finset.mem_singleton]
        rw [heq]
        exact ⟨hcs_pair C hC i hi j hj hij, pairVec_isPair hij ((hcs_prop C hC).2 i hi j hj)⟩
    have hdisj_p : (cs : Set (Finset (Fin (3 * t)))).PairwiseDisjoint pairOf := by
      intro C1 h1 C2 h2 hne
      change Disjoint (pairOf C1) (pairOf C2)
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨s1, hs1, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨s2, hs2, hseq⟩ := Finset.mem_image.mp hx2
      obtain ⟨hsub1, hc1⟩ := Finset.mem_powersetCard.mp hs1
      obtain ⟨hsub2, _⟩ := Finset.mem_powersetCard.mp hs2
      obtain ⟨a, ha1⟩ := Finset.card_pos.mp (by omega : 0 < s1.card)
      have ha2 : a ∈ s2 := by
        have := congrFun hseq a
        simp only [ha1, ↓reduceIte] at this
        by_contra hnot
        simp [hnot] at this
      exact Finset.disjoint_left.mp (hcs_disj C1 h1 C2 h2 hne) (hsub1 ha1) (hsub2 ha2)
    rw [hbi, Finset.card_biUnion hdisj_p]
    exact Finset.sum_congr rfl hpair_card
  exact ⟨cs, hcs_prop, hcs_disj, hrank, hcount, hcs_pair, hcs_cov⟩

def run3Vec {t : ℕ} (ht : 0 < t) (j : Fin (3 * t)) : Lane t :=
  fun i => if i = j ∨ i = nx ht j ∨ i = nx ht (nx ht j) then 1 else 0

lemma isRun3_iff_run3Vec {t : ℕ} (ht : 0 < t) (w : Lane t) :
    isRun3 ht w ↔ ∃ j : Fin (3 * t), w = run3Vec ht j := by
  constructor
  · rintro ⟨j, hiff⟩
    refine ⟨j, funext fun i => ?_⟩
    unfold run3Vec
    split_ifs with h
    · exact (F_cases _).resolve_left ((hiff i).mpr h)
    · by_contra hn; exact h ((hiff i).mp hn)
  · rintro ⟨j, rfl⟩
    refine ⟨j, fun i => ?_⟩
    unfold run3Vec
    split_ifs with h <;> simp [h]

lemma run3Vec_inj {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t) : Function.Injective (run3Vec ht) := by
  intro j k hjk
  have h1 : k = j ∨ k = nx ht j ∨ k = nx ht (nx ht j) := by
    have := congrFun hjk k
    simp only [run3Vec, true_or, ↓reduceIte] at this
    by_contra hnot
    simp [hnot] at this
  have h2 : j = k ∨ j = nx ht k ∨ j = nx ht (nx ht k) := by
    have := congrFun hjk j
    simp only [run3Vec, true_or, ↓reduceIte] at this
    by_contra hnot
    simp [hnot] at this
  have hne1 := nx_ne_self ht
  have hne2 := nx_nx_ne_self ht
  have hne3 := nx_three_ne_self ht ht2
  rcases h1 with rfl | rfl | rfl
  · rfl
  · rcases h2 with h | h | h
    · exact h
    · exact absurd h.symm (hne2 j)
    · exact absurd h.symm (hne3 j)
  · rcases h2 with h | h | h
    · exact h
    · exact absurd h.symm (hne3 j)
    · have h4 : nx ht (nx ht (nx ht (nx ht j))) = j := h.symm
      have hj := j.isLt
      have hval := congrArg Fin.val h4
      rw [nx_val, nx_val, nx_val, nx_val] at hval
      split_ifs at hval <;> omega

lemma run3_sum_zero {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) (J : Finset (Fin (3 * t)))
    (hJ : J.Nonempty) (hsum : ∑ j ∈ J, run3Vec ht j = 0) :
    ∃ a : Fin 3, J = Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 ≠ a.val) := by
  classical
  let c : Fin (3 * t) → F := fun j => if j ∈ J then 1 else 0
  have hrec : ∀ i : Fin (3 * t), c i + c (pv ht i) + c (pv ht (pv ht i)) = 0 := by
    intro i
    have hi := congrFun hsum i
    simp only [Finset.sum_apply, Pi.zero_apply] at hi
    have hsplit : ∑ j ∈ J, run3Vec ht j i =
        ∑ j : Fin (3 * t), if j ∈ J then run3Vec ht j i else 0 := by
      rw [← Finset.sum_filter]
      congr 1; ext j; simp
    rw [hsplit] at hi
    have hsupp : ∀ j : Fin (3 * t), (if j ∈ J then run3Vec ht j i else 0) =
        if j = i ∨ j = pv ht i ∨ j = pv ht (pv ht i) then c j else 0 := by
      intro j
      have hiff : (i = j ∨ i = nx ht j ∨ i = nx ht (nx ht j)) ↔
          (j = i ∨ j = pv ht i ∨ j = pv ht (pv ht i)) := by
        constructor
        · rintro (rfl | rfl | rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (pv_nx ht j).symm)
          · exact Or.inr (Or.inr (by rw [pv_nx, pv_nx]))
        · rintro (rfl | rfl | rfl)
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (nx_pv ht i).symm)
          · exact Or.inr (Or.inr (by rw [nx_pv, nx_pv]))
      by_cases hj : j ∈ J <;> by_cases h1 : j = i ∨ j = pv ht i ∨ j = pv ht (pv ht i)
      · simp [hj, c, run3Vec, hiff.mpr h1, h1]
      · have hn := mt hiff.mp h1; simp [hj, c, run3Vec, hn, h1]
      · simp [hj, c, h1]
      · simp [hj, c, h1]
    rw [Finset.sum_congr rfl (fun j _ => hsupp j), ← Finset.sum_filter] at hi
    have h3 : Finset.univ.filter (fun j : Fin (3 * t) => j = i ∨ j = pv ht i ∨ j = pv ht (pv ht i)) =
        {i, pv ht i, pv ht (pv ht i)} := by ext j; simp
    have hne1 : i ≠ pv ht i := fun h => nx_ne_self ht (pv ht i) (by rw [nx_pv]; exact h)
    have hne2 : i ≠ pv ht (pv ht i) := fun h => nx_nx_ne_self ht (pv ht (pv ht i)) (by rw [nx_pv, nx_pv]; exact h)
    have hne3 : pv ht i ≠ pv ht (pv ht i) := fun h => nx_ne_self ht (pv ht (pv ht i)) (by rw [nx_pv]; exact h)
    rw [h3, Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_insert (by simp [hne3]),
      Finset.sum_singleton] at hi
    linear_combination hi
  have hper3 : ∀ k : ℕ, (hk : k + 3 < 3 * t) →
      c ⟨k + 3, hk⟩ = c ⟨k, by omega⟩ := by
    intro k hk
    have h1 := hrec ⟨k + 3, hk⟩
    have h2 := hrec ⟨k + 2, by omega⟩
    have hp1 : pv ht ⟨k + 3, hk⟩ = ⟨k + 2, by omega⟩ := by
      apply Fin.ext; rw [pv_val]; dsimp only; simp only [show k + 3 ≠ 0 by omega, ↓reduceIte]; omega
    have hp2 : pv ht ⟨k + 2, by omega⟩ = ⟨k + 1, by omega⟩ := by
      apply Fin.ext; rw [pv_val]; dsimp only; simp only [show k + 2 ≠ 0 by omega, ↓reduceIte]; omega
    have hp3 : pv ht ⟨k + 1, by omega⟩ = ⟨k, by omega⟩ := by
      apply Fin.ext; rw [pv_val]; dsimp only; simp only [show k + 1 ≠ 0 by omega, ↓reduceIte]; omega
    rw [hp1, hp2] at h1
    rw [hp2, hp3] at h2
    have hsum2 : c ⟨k + 3, hk⟩ + c ⟨k, by omega⟩ = 0 := by
      have hz1 := z2_add_self (c ⟨k + 2, by omega⟩)
      have hz2 := z2_add_self (c ⟨k + 1, by omega⟩)
      linear_combination h1 + h2 - hz1 - hz2
    have hneg := eq_neg_of_add_eq_zero_left hsum2
    rwa [CharTwo.neg_eq] at hneg
  have hmod : ∀ j : Fin (3 * t), c j = c ⟨j.val % 3, by omega⟩ := by
    intro j
    rcases j with ⟨m, hm⟩
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm3 : m < 3
      · exact congrArg c (Fin.ext (Nat.mod_eq_of_lt hm3).symm)
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
        rw [hper3 k hm, ih k (by omega) (by omega)]
        exact congrArg c (Fin.ext (by dsimp only; omega))
  have h012 : c ⟨2, by omega⟩ + c ⟨1, by omega⟩ + c ⟨0, by omega⟩ = 0 := by
    have h := hrec ⟨2, by omega⟩
    have hp1 : pv ht ⟨2, by omega⟩ = ⟨1, by omega⟩ := by
      apply Fin.ext; rw [pv_val]; dsimp only; simp only [show (2 : ℕ) ≠ 0 by decide, ↓reduceIte]
    have hp2 : pv ht ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
      apply Fin.ext; rw [pv_val]; dsimp only; simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
    rwa [hp1, hp2] at h
  have hnz : ∃ j : Fin (3 * t), c j = 1 := by
    obtain ⟨j, hj⟩ := hJ
    exact ⟨j, by simp [c, hj]⟩
  have hnot0 : ¬ (c ⟨0, by omega⟩ = 0 ∧ c ⟨1, by omega⟩ = 0 ∧ c ⟨2, by omega⟩ = 0) := by
    rintro ⟨h0, h1, h2⟩
    obtain ⟨j, hj⟩ := hnz
    rw [hmod j] at hj
    have h3 : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
    rcases h3 with hm | hm | hm
    · have : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨0, by omega⟩ := Fin.ext hm
      rw [this, h0] at hj; exact zero_ne_one hj
    · have : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨1, by omega⟩ := Fin.ext hm
      rw [this, h1] at hj; exact zero_ne_one hj
    · have : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨2, by omega⟩ := Fin.ext hm
      rw [this, h2] at hj; exact zero_ne_one hj
  rcases F_cases (c ⟨0, by omega⟩) with h0 | h0 <;>
    rcases F_cases (c ⟨1, by omega⟩) with h1 | h1 <;>
    rcases F_cases (c ⟨2, by omega⟩) with h2 | h2
  · exact absurd ⟨h0, h1, h2⟩ hnot0
  · rw [h0, h1, h2] at h012; exact absurd h012 (by decide)
  · rw [h0, h1, h2] at h012; exact absurd h012 (by decide)
  · refine ⟨0, ?_⟩
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero]
    have hm := hmod j
    have h3 : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
    rcases h3 with h | h | h
    · have he : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨0, by omega⟩ := Fin.ext h
      rw [he, h0] at hm; simp [c] at hm; simp [h, hm]
    · have he : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨1, by omega⟩ := Fin.ext h
      rw [he, h1] at hm; simp [c] at hm; simp [h, hm]
    · have he : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨2, by omega⟩ := Fin.ext h
      rw [he, h2] at hm; simp [c] at hm; simp [h, hm]
  · rw [h0, h1, h2] at h012; exact absurd h012 (by decide)
  · refine ⟨1, ?_⟩
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_one]
    have hm := hmod j
    have h3 : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
    rcases h3 with h | h | h
    · have he : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨0, by omega⟩ := Fin.ext h
      rw [he, h0] at hm; simp [c] at hm; simp [h, hm]
    · have he : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨1, by omega⟩ := Fin.ext h
      rw [he, h1] at hm; simp [c] at hm; simp [h, hm]
    · have he : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨2, by omega⟩ := Fin.ext h
      rw [he, h2] at hm; simp [c] at hm; simp [h, hm]
  · refine ⟨2, ?_⟩
    ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hm := hmod j
    have h3 : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
    rcases h3 with h | h | h
    · have he : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨0, by omega⟩ := Fin.ext h
      rw [he, h0] at hm; simp [c] at hm; simp [h, hm]
    · have he : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨1, by omega⟩ := Fin.ext h
      rw [he, h1] at hm; simp [c] at hm; simp [h, hm]
    · have he : (⟨j.val % 3, by omega⟩ : Fin (3 * t)) = ⟨2, by omega⟩ := Fin.ext h
      rw [he, h2] at hm; simp [c] at hm; simp [h, hm]
  · rw [h0, h1, h2] at h012; exact absurd h012 (by decide)

lemma card_filter_mod3_ne (t : ℕ) (a : Fin 3) :
    (Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 ≠ a.val)).card = 2 * t := by
  have ha : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 := by omega
  have h1 : ∀ c : ℕ, c < 3 → (Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 = c)).card = t := by
    intro c hc
    calc (Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 = c)).card
        = (Finset.univ : Finset (Fin t)).card := by
          refine Finset.card_bij (fun j _ => (⟨j.val / 3, by have := j.isLt; omega⟩ : Fin t)) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro x hx y hy hxy
            have hx' := (Finset.mem_filter.mp hx).2
            have hy' := (Finset.mem_filter.mp hy).2
            have hdiv := congrArg Fin.val hxy
            dsimp only at hdiv
            exact Fin.ext (by omega)
          · intro q _
            refine ⟨⟨3 * q.val + c, by have := q.isLt; omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            omega
      _ = t := by simp
  have hdisj : Disjoint (Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 = a.val))
      (Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 ≠ a.val)) := by
    rw [Finset.disjoint_filter]; intro j _ h1' h2'; exact h2' h1'
  have hun : Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 = a.val) ∪
      Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 ≠ a.val) = Finset.univ := by
    ext j; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
  have htot := Finset.card_union_of_disjoint hdisj
  rw [hun, Finset.card_univ, Fintype.card_fin, h1 a.val a.isLt] at htot
  omega

open Classical in
lemma run3_card_le_of_lt {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t) (P : Submodule F (Lane t))
    (hsmall : Module.finrank F P + 1 < 2 * t) :
    (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ isRun3 ht x)).card ≤ Module.finrank F P := by
  let J : Finset (Fin (3 * t)) := Finset.univ.filter (fun j => run3Vec ht j ∈ P)
  have hcard_eq : (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ isRun3 ht x)).card = J.card := by
    symm
    refine Finset.card_bij (fun j _ => run3Vec ht j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, J] at hj ⊢
      exact ⟨hj, (isRun3_iff_run3Vec ht _).mpr ⟨j, rfl⟩⟩
    · intro a _ b _ h; exact run3Vec_inj ht (by omega) h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨j, rfl⟩ := (isRun3_iff_run3Vec ht x).mp hx.2
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1⟩, rfl⟩
  rw [hcard_eq]
  by_contra hgt
  push Not at hgt
  obtain ⟨K, hKJ, hKcard⟩ := Finset.exists_subset_card_eq (show Module.finrank F P + 1 ≤ J.card by omega)
  let f : K → P := fun j => ⟨run3Vec ht j.1, (Finset.mem_filter.mp (hKJ j.2)).2⟩
  have hlin : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let S : Finset (Fin (3 * t)) := (Finset.univ.filter (fun j : K => g j ≠ 0)).image Subtype.val
    have hSsum : ∑ j ∈ S, run3Vec ht j = 0 := by
      have h1 := congrArg Subtype.val hg
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero] at h1
      rw [← h1]
      rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)]
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases F_cases (g j) with h | h <;> simp [h, f]
    by_cases hSne : S.Nonempty
    · obtain ⟨a, ha⟩ := run3_sum_zero ht ht3 S hSne hSsum
      have hScard : S.card = 2 * t := ha ▸ card_filter_mod3_ne t a
      have hSle : S.card ≤ K.card := by
        calc S.card ≤ (Finset.univ : Finset K).card := Finset.card_image_le.trans (Finset.card_filter_le _ _)
          _ = K.card := by simp
      omega
    · intro j
      by_contra hne
      exact hSne ⟨j.1, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩⟩
  have hle := hlin.fintype_card_le_finrank
  rw [Fintype.card_coe, hKcard] at hle
  omega

lemma t3_inter_card (a1 a2 : Fin 3) (h : a1 ≠ a2) :
    (Finset.univ.filter (fun j : Fin 9 => j.val % 3 ≠ a1.val) ∩
      Finset.univ.filter (fun j : Fin 9 => j.val % 3 ≠ a2.val)).card = 3 := by
  revert a1 a2 h; decide +kernel

lemma t3_run3_adj (a : Fin 3) (j : Fin 9) (k : Fin 3) (hja : j.val % 3 ≠ a.val) :
    run3Vec (by decide : 0 < 3) j ⟨(3 * k.val + (a.val + 2)) % 9, Nat.mod_lt _ (by decide)⟩ =
    run3Vec (by decide : 0 < 3) j ⟨(3 * k.val + (a.val + 3)) % 9, Nat.mod_lt _ (by decide)⟩ := by
  revert a j k hja; decide +kernel

lemma t3_other_coord (a : Fin 3) (i : Fin 9) (hne : i.val % 3 ≠ (a.val + 1) % 3) :
    ∃ k : Fin 3,
      i = ⟨(3 * k.val + (a.val + 2)) % 9, Nat.mod_lt _ (by decide)⟩ ∨
      i = ⟨(3 * k.val + (a.val + 3)) % 9, Nat.mod_lt _ (by decide)⟩ := by
  revert a i hne; decide +kernel

lemma t3_adj_col_ne (a k : Fin 3) :
    (⟨(3 * k.val + (a.val + 2)) % 9, Nat.mod_lt _ (by decide)⟩ : Fin 9).val % 3 ≠
    (⟨(3 * k.val + (a.val + 3)) % 9, Nat.mod_lt _ (by decide)⟩ : Fin 9).val % 3 := by
  revert a k; decide +kernel

lemma t3_mod3_card (c : ℕ) (hc : c < 3) :
    (Finset.univ.filter (fun i : Fin 9 => i.val % 3 = c)).card = 3 := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide

open Classical in
lemma run3_card_t3_dim5 (ht : 0 < 3) (P : Submodule F (Lane 3)) (_hP : P ≤ codeSub 3)
    (hdim : Module.finrank F P = 5) :
    (Finset.univ.filter (fun x : Lane 3 => x ∈ P ∧ isRun3 ht x)).card ≤ 6 ∧
    ((Finset.univ.filter (fun x : Lane 3 => x ∈ P ∧ isRun3 ht x)).card = 6 →
      (Finset.univ.filter (fun x : Lane 3 => x ∈ P ∧ isPair x)).card ≤ 3) := by
  let J : Finset (Fin 9) := Finset.univ.filter (fun j => run3Vec ht j ∈ P)
  have hcard_eq : (Finset.univ.filter (fun x : Lane 3 => x ∈ P ∧ isRun3 ht x)).card = J.card := by
    symm
    refine Finset.card_bij (fun j _ => run3Vec ht j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, J] at hj ⊢
      exact ⟨hj, (isRun3_iff_run3Vec ht _).mpr ⟨j, rfl⟩⟩
    · intro a _ b _ h; exact run3Vec_inj ht (by omega) h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨j, rfl⟩ := (isRun3_iff_run3Vec ht x).mp hx.2
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1⟩, rfl⟩
  rw [hcard_eq]
  have hdep : ∀ K : Finset (Fin 9), K ⊆ J → K.card = 6 →
      ∃ a : Fin 3, K = Finset.univ.filter (fun j : Fin 9 => j.val % 3 ≠ a.val) := by
    intro K hKJ hKcard
    let f : K → P := fun j => ⟨run3Vec ht j.1, (Finset.mem_filter.mp (hKJ j.2)).2⟩
    have hnotlin : ¬ LinearIndependent F f := fun hlin => by
      have := hlin.fintype_card_le_finrank
      rw [Fintype.card_coe, hKcard, hdim] at this; omega
    rw [Fintype.linearIndependent_iff] at hnotlin
    push Not at hnotlin
    obtain ⟨g, hg, j0, hj0⟩ := hnotlin
    let S : Finset (Fin 9) := (Finset.univ.filter (fun j : K => g j ≠ 0)).image Subtype.val
    have hSsum : ∑ j ∈ S, run3Vec ht j = 0 := by
      have h1 := congrArg Subtype.val hg
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero] at h1
      rw [← h1, Finset.sum_image (fun a _ b _ h => Subtype.ext h), Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases F_cases (g j) with h | h <;> simp [h, f]
    have hSne : S.Nonempty := ⟨j0.1, Finset.mem_image.mpr ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0⟩, rfl⟩⟩
    obtain ⟨a, ha⟩ := run3_sum_zero ht (by omega) S hSne hSsum
    have hSK : S ⊆ K := by
      intro x hx; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx; exact j.2
    have hScard : S.card = 6 := ha ▸ card_filter_mod3_ne 3 a
    have hSeqK : S = K := Finset.eq_of_subset_of_card_le hSK (by omega)
    exact ⟨a, hSeqK ▸ ha⟩
  have hle6 : J.card ≤ 6 := by
    by_contra hgt
    push Not at hgt
    obtain ⟨K1, hK1J, hK1c⟩ := Finset.exists_subset_card_eq (show 6 ≤ J.card by omega)
    obtain ⟨a1, ha1⟩ := hdep K1 hK1J hK1c
    obtain ⟨j_out, hj_out_J, hj_out_not⟩ := Finset.exists_mem_notMem_of_card_lt_card (show K1.card < J.card by omega)
    obtain ⟨j_in, hj_in⟩ := Finset.card_pos.mp (by omega : 0 < K1.card)
    let K2 : Finset (Fin 9) := insert j_out (K1.erase j_in)
    have hK2J : K2 ⊆ J := Finset.insert_subset hj_out_J ((Finset.erase_subset _ _).trans hK1J)
    have hK2c : K2.card = 6 := by
      rw [Finset.card_insert_of_notMem (fun h => hj_out_not (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hj_in, hK1c]
    obtain ⟨a2, ha2⟩ := hdep K2 hK2J hK2c
    have hne_a : a1 ≠ a2 := by
      intro heq; subst heq
      have : j_out ∈ K1 := by rw [ha1, ← ha2]; exact Finset.mem_insert_self _ _
      exact hj_out_not this
    have hcard_inter : (K1 ∩ K2).card = 5 := by
      have he : K1 ∩ K2 = K1.erase j_in := by
        ext x; simp only [K2, Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨hx1, rfl | hx2⟩
          · exact absurd hx1 hj_out_not
          · exact hx2
        · rintro ⟨hne, hx1⟩; exact ⟨hx1, Or.inr ⟨hne, hx1⟩⟩
      rw [he, Finset.card_erase_of_mem hj_in, hK1c]
    have hcard_inter3 : (Finset.univ.filter (fun j : Fin 9 => j.val % 3 ≠ a1.val) ∩
        Finset.univ.filter (fun j : Fin 9 => j.val % 3 ≠ a2.val)).card = 3 := by
      convert t3_inter_card a1 a2 hne_a
    rw [ha1, ha2] at hcard_inter
    omega
  refine ⟨hle6, fun hJ6 => ?_⟩
  obtain ⟨a, ha⟩ := hdep J (Finset.Subset.refl J) hJ6
  let Sspan : Submodule F (Lane 3) := Submodule.span F (J.image (run3Vec ht) : Set (Lane 3))
  have hSspan_le : Sspan ≤ P := by
    rw [Submodule.span_le]
    intro x hx
    rw [Finset.mem_coe] at hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hj).2
  have hSspan_dim : Module.finrank F Sspan = 5 := by
    obtain ⟨j0, hj0⟩ := Finset.card_pos.mp (by omega : 0 < J.card)
    let K := J.erase j0
    have hKc : K.card = 5 := by rw [Finset.card_erase_of_mem hj0, hJ6]
    let f : K → Sspan := fun j =>
      ⟨run3Vec ht j.1, Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨j.1, Finset.mem_of_mem_erase j.2, rfl⟩))⟩
    have hlin : LinearIndependent F f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      let S : Finset (Fin 9) := (Finset.univ.filter (fun j : K => g j ≠ 0)).image Subtype.val
      have hSsum : ∑ j ∈ S, run3Vec ht j = 0 := by
        have h1 := congrArg Subtype.val hg
        simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero] at h1
        rw [← h1, Finset.sum_image (fun x _ y _ h => Subtype.ext h), Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        rcases F_cases (g j) with h | h <;> simp [h, f]
      by_cases hSne : S.Nonempty
      · obtain ⟨b, hb⟩ := run3_sum_zero ht (by omega) S hSne hSsum
        have hSc : S.card = 6 := hb ▸ card_filter_mod3_ne 3 b
        have hSle : S.card ≤ 5 := by
          calc S.card ≤ (Finset.univ : Finset K).card := Finset.card_image_le.trans (Finset.card_filter_le _ _)
            _ = 5 := by simp [hKc]
        omega
      · intro j; by_contra hne
        exact hSne ⟨j.1, Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩⟩
    have hge5 := hlin.fintype_card_le_finrank
    rw [Fintype.card_coe, hKc] at hge5
    have hle5 := Submodule.finrank_mono hSspan_le
    omega
  have hPeq : Sspan = P := Submodule.eq_of_le_of_finrank_eq hSspan_le (by omega)
  have heq_adj : ∀ x ∈ P, ∀ k : Fin 3,
      x ⟨(3 * k.val + (a.val + 2)) % 9, Nat.mod_lt _ (by decide)⟩ =
      x ⟨(3 * k.val + (a.val + 3)) % 9, Nat.mod_lt _ (by decide)⟩ := by
    intro x hx
    rw [← hPeq] at hx
    refine Submodule.span_induction ?_ (fun _ => rfl)
      (fun u v _ _ hu hv k => by simp only [Pi.add_apply, hu k, hv k])
      (fun r u _ hu k => by simp only [Pi.smul_apply, smul_eq_mul, hu k]) hx
    intro y hy k
    rw [Finset.mem_coe] at hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    rw [ha] at hj
    have hja : j.val % 3 ≠ a.val := (Finset.mem_filter.mp hj).2
    exact t3_run3_adj a j k hja
  have hsupp_pair : ∀ x ∈ P, isPair x → ∀ i : Fin 9, x i ≠ 0 → i.val % 3 = (a.val + 1) % 3 := by
    intro x hx hp i hi
    by_contra hne
    obtain ⟨k, hkeq⟩ := t3_other_coord a i hne
    let i1 : Fin 9 := ⟨(3 * k.val + (a.val + 2)) % 9, Nat.mod_lt _ (by decide)⟩
    let i2 : Fin 9 := ⟨(3 * k.val + (a.val + 3)) % 9, Nat.mod_lt _ (by decide)⟩
    have h12 : x i1 = x i2 := heq_adj x hx k
    have hcol_ne : i1.val % 3 ≠ i2.val % 3 := t3_adj_col_ne a k
    have hboth : x i1 ≠ 0 ∧ x i2 ≠ 0 := by
      rcases hkeq with rfl | rfl
      · exact ⟨hi, h12 ▸ hi⟩
      · exact ⟨h12.symm ▸ hi, hi⟩
    obtain ⟨u, v, huv, hcol, hiff⟩ := hp
    have hu1 := (hiff i1).mp hboth.1
    have hu2 := (hiff i2).mp hboth.2
    rcases hu1 with h1 | h1 <;> rcases hu2 with h2 | h2
    · exact hcol_ne (by rw [h1, h2])
    · exact hcol_ne (by rw [h1, h2]; exact hcol)
    · exact hcol_ne (by rw [h1, h2]; exact hcol.symm)
    · exact hcol_ne (by rw [h1, h2])
  have hsub_pair : Finset.univ.filter (fun x : Lane 3 => x ∈ P ∧ isPair x) ⊆
      ((Finset.univ.filter (fun i : Fin 9 => i.val % 3 = (a.val + 1) % 3)).powersetCard 2).image
        (fun s => fun i => if i ∈ s then (1 : F) else 0) := by
    intro x hx
    obtain ⟨hxP, hp⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨u, v, huv, _, rfl⟩ := isPair_eq_pairVec hp
    refine Finset.mem_image.mpr ⟨{u, v}, Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair huv⟩, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupp_pair _ hxP hp z (by rw [pairVec_apply huv]; simp)⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsupp_pair _ hxP hp z (by rw [pairVec_apply huv]; simp)⟩
    · funext z; rw [pairVec_apply huv]; simp only [Finset.mem_insert, Finset.mem_singleton]
  have hcard_cls : (Finset.univ.filter (fun i : Fin 9 => i.val % 3 = (a.val + 1) % 3)).card = 3 := by
    convert t3_mod3_card ((a.val + 1) % 3) (Nat.mod_lt _ (by decide))
  calc (Finset.univ.filter (fun x : Lane 3 => x ∈ P ∧ isPair x)).card
      ≤ (((Finset.univ.filter (fun i : Fin 9 => i.val % 3 = (a.val + 1) % 3)).powersetCard 2).image
          (fun s => fun i => if i ∈ s then (1 : F) else 0)).card := Finset.card_le_card hsub_pair
    _ ≤ ((Finset.univ.filter (fun i : Fin 9 => i.val % 3 = (a.val + 1) % 3)).powersetCard 2).card := Finset.card_image_le
    _ = 3 := by rw [Finset.card_powersetCard, hcard_cls]; decide

def isSep {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t)) : Prop :=
  ∀ p ∈ P, ∀ i : Fin (3 * t), ¬ (p i ≠ 0 ∧ p (nx ht i) ≠ 0)

lemma isSep_iff_supp {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t)) :
    isSep ht P ↔ ∀ i ∈ supp P, nx ht i ∉ supp P := by
  constructor
  · intro hsep i hi hnx
    obtain ⟨p, hp, hpi⟩ := (mem_supp P i).mp hi
    obtain ⟨q, hq, hqi⟩ := (mem_supp P (nx ht i)).mp hnx
    by_cases hpn : p (nx ht i) ≠ 0
    · exact hsep p hp i ⟨hpi, hpn⟩
    · by_cases hqi0 : q i ≠ 0
      · exact hsep q hq i ⟨hqi0, hqi⟩
      · push Not at hpn hqi0
        have hpq := P.add_mem hp hq
        exact hsep (p + q) hpq i ⟨by simp [hqi0, hpi], by simp [hpn, hqi]⟩
  · intro h p hp i ⟨h1, h2⟩
    exact h i ((mem_supp P i).mpr ⟨p, hp, h1⟩) ((mem_supp P (nx ht i)).mpr ⟨p, hp, h2⟩)

lemma card_supp_le_of_isSep {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t))
    (hsep : isSep ht P) : 2 * (supp P).card ≤ 3 * t := by
  classical
  have hdisj : Disjoint (supp P) ((supp P).image (nx ht)) := by
    rw [Finset.disjoint_left]
    intro x hx him
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp him
    exact (isSep_iff_supp ht P).mp hsep y hy hx
  have himc : ((supp P).image (nx ht)).card = (supp P).card :=
    Finset.card_image_of_injective _ (nx_inj ht)
  have hle : (supp P ∪ (supp P).image (nx ht)).card ≤ 3 * t :=
    (Finset.card_le_univ _).trans (by simp)
  rw [Finset.card_union_of_disjoint hdisj, himc] at hle
  omega

lemma not_mono_of_not_isSep {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t))
    (hnsep : ¬ isSep ht P) : ¬ mono (supp P) := by
  intro hm
  apply hnsep
  rw [isSep_iff_supp]
  intro i hi hnx
  exact nx_color ht i (hm (nx ht i) hnx i hi)

lemma not_isSep_of_small {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t)) (hP : P ≤ codeSub t)
    (hsmall : (t = 3 ∧ 3 ≤ Module.finrank F P) ∨ (t = 4 ∧ 5 ≤ Module.finrank F P)) :
    ¬ isSep ht P := by
  intro hsep
  have h2 := card_supp_le_of_isSep ht P hsep
  have hloss : Module.finrank F P + Module.finrank F (checkOn (supp P)).range ≤ (supp P).card :=
    suppLoss P hP
  have hne : (supp P).Nonempty := Finset.card_pos.mp (show 0 < (supp P).card by rcases hsmall with ⟨_, h⟩ | ⟨_, h⟩ <;> omega)
  obtain ⟨r1, r2⟩ := oneOrTwo (supp P) hne
  by_cases hm : mono (supp P)
  · have hms := mono_size (supp P) hm
    rcases hsmall with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega
  · have hr2 := r2 hm
    rcases hsmall with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> omega

lemma numVal_ge_348 {t : ℕ} (ht3 : 3 ≤ t) : 348 ≤ numVal t := by
  unfold numVal
  split_ifs <;> omega

noncomputable def shapeCnt {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ shape ht x)).card

noncomputable def pairCnt {t : ℕ} (P : Submodule F (Lane t)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ isPair x)).card

noncomputable def run3Cnt {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ isRun3 ht x)).card

noncomputable def nb5Cnt {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ (Nb ht x).card = 5)).card

noncomputable def wt3Cnt {t : ℕ} (P : Submodule F (Lane t)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ wt x = 3)).card

lemma shapeCnt_eq_add {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t)) :
    shapeCnt ht P = pairCnt P + run3Cnt ht P := by
  classical
  unfold shapeCnt pairCnt run3Cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp [shape, and_or_left]
  · rw [Finset.disjoint_left]
    intro x h1 h2
    have w2 := wt_pair_eq_two (Finset.mem_filter.mp h1).2.2
    have w3 := wt_run3_eq_three ht (Finset.mem_filter.mp h2).2.2
    omega

lemma run3_add_nb5_le_wt3 {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    (P : Submodule F (Lane t)) (hP : P ≤ codeSub t) :
    run3Cnt ht P + nb5Cnt ht P ≤ wt3Cnt P := by
  classical
  unfold run3Cnt nb5Cnt wt3Cnt
  have hdisj : Disjoint (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ isRun3 ht x))
      (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ (Nb ht x).card = 5)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have hxP := (Finset.mem_filter.mp h1).2.1
    have hr := (Finset.mem_filter.mp h1).2.2
    have h5 := (Finset.mem_filter.mp h2).2.2
    have hnz : x ≠ 0 := by intro hz; subst hz; have := wt_run3_eq_three ht hr; rw [wt_zero] at this; omega
    have h4 := (footprint_classify ht ht3 x hnz (hP hxP)).2.1.mpr (Or.inr hr)
    omega
  rw [← Finset.card_union_of_disjoint hdisj]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  rcases hx with ⟨hxP, hr⟩ | ⟨hxP, h5⟩
  · exact ⟨hxP, wt_run3_eq_three ht hr⟩
  · have hnz : x ≠ 0 := by
      intro hz; subst hz
      have hemp : Nb ht (0 : Lane t) = ∅ := by ext i; simp [Nb]
      rw [hemp, Finset.card_empty] at h5; omega
    exact ⟨hxP, (footprint_classify ht ht3 x hnz (hP hxP)).2.2 h5⟩

open Classical in
lemma hits_master_le {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    (P Q : Submodule F (Lane t)) (hP : P ≤ codeSub t) (hQ : Q ≤ codeSub t) :
    64 * (rectHits ht P Q : ℚ) ≤
      64 * (Nat.card Q : ℚ) +
        ((Nat.card P - 1 + 3 * shapeCnt ht P + nb5Cnt ht P : ℕ) : ℚ) * (cntS t ∅ : ℚ) := by
  have h1 := rectHits_le_sum_cntS ht P Q hQ
  have h1q : 64 * (rectHits ht P Q : ℚ) ≤ 64 * (Nat.card Q : ℚ) +
      ∑ x ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, 64 * (cntS t (Nb ht x) : ℚ) := by
    have hcast : (rectHits ht P Q : ℚ) ≤ (Nat.card Q : ℚ) +
        ∑ x ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, (cntS t (Nb ht x) : ℚ) := by
      exact_mod_cast h1
    rw [← Finset.mul_sum]; linarith
  have hsum_le : ∑ x ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, 64 * (cntS t (Nb ht x) : ℚ) ≤
      (∑ x ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0,
        (if shape ht x then (4 : ℚ) else if (Nb ht x).card = 5 then 2 else 1)) * (cntS t ∅ : ℚ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun x hx => ?_
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
    exact cntS_le_of_nonzero ht ht3 x hne (hP (Finset.mem_filter.mp hmem).2)
  have hS_eq : ∑ x ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0,
      (if shape ht x then (4 : ℚ) else if (Nb ht x).card = 5 then 2 else 1) =
      ((Nat.card P - 1 + 3 * shapeCnt ht P + nb5Cnt ht P : ℕ) : ℚ) := by
    have hsplit : ∀ x ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0,
        (if shape ht x then (4 : ℚ) else if (Nb ht x).card = 5 then 2 else 1) =
        1 + (if shape ht x then 3 else 0) + (if (Nb ht x).card = 5 then 1 else 0) := by
      intro x hx
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
      by_cases hs : shape ht x
      · have h4 := (footprint_classify ht ht3 x hne (hP (Finset.mem_filter.mp hmem).2)).2.1.mpr hs
        have hne5 : (Nb ht x).card ≠ 5 := by omega
        simp [hs, hne5]; norm_num
      · by_cases h5 : (Nb ht x).card = 5 <;> simp [hs, h5]
        norm_num
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h0mem : (0 : Lane t) ∈ Finset.univ.filter (fun p => p ∈ P) := by simp
    have hPcard : (Finset.univ.filter (fun p => p ∈ P)).card = Nat.card P := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h1s : ∑ _x ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, (1 : ℚ) = ((Nat.card P - 1 : ℕ) : ℚ) := by
      rw [Finset.sum_const, Finset.card_erase_of_mem h0mem, hPcard, nsmul_eq_mul, mul_one]
    have h0ns : ¬ shape ht (0 : Lane t) := by
      rintro (h | h)
      · have := wt_pair_eq_two h; rw [wt_zero] at this; omega
      · have := wt_run3_eq_three ht h; rw [wt_zero] at this; omega
    have h0n5 : (Nb ht (0 : Lane t)).card ≠ 5 := by
      have hemp : Nb ht (0 : Lane t) = ∅ := by ext i; simp [Nb]
      rw [hemp, Finset.card_empty]; decide
    have h2s : ∑ x ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, (if shape ht x then (3 : ℚ) else 0) =
        3 * (shapeCnt ht P : ℚ) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hf : ((Finset.univ.filter (fun p => p ∈ P)).erase 0).filter (fun x => shape ht x) =
          Finset.univ.filter (fun x : Lane t => x ∈ P ∧ shape ht x) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
        exact ⟨fun ⟨⟨_, hp⟩, hs⟩ => ⟨hp, hs⟩, fun ⟨hp, hs⟩ => ⟨⟨fun hz => h0ns (hz ▸ hs), hp⟩, hs⟩⟩
      rw [hf]; unfold shapeCnt; ring
    have h3s : ∑ x ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, (if (Nb ht x).card = 5 then (1 : ℚ) else 0) =
        (nb5Cnt ht P : ℚ) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hf : ((Finset.univ.filter (fun p => p ∈ P)).erase 0).filter (fun x => (Nb ht x).card = 5) =
          Finset.univ.filter (fun x : Lane t => x ∈ P ∧ (Nb ht x).card = 5) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
        exact ⟨fun ⟨⟨_, hp⟩, h5⟩ => ⟨hp, h5⟩, fun ⟨hp, h5⟩ => ⟨⟨fun hz => h0n5 (hz ▸ h5), hp⟩, h5⟩⟩
      rw [hf]; rfl
    rw [h1s, h2s, h3s]
    push_cast; ring
  rw [hS_eq] at hsum_le
  linarith

open Classical in
lemma hits_shape_le {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    (P Q : Submodule F (Lane t)) (hP : P ≤ codeSub t) (hQ : Q ≤ codeSub t) :
    64 * (rectHits ht P Q : ℚ) ≤
      64 * (Nat.card Q : ℚ) +
        ((2 * (Nat.card P - 1) + 2 * shapeCnt ht P : ℕ) : ℚ) * (cntS t ∅ : ℚ) := by
  have hm := hits_master_le ht ht3 P Q hP hQ
  have hnb_le : shapeCnt ht P + nb5Cnt ht P ≤ Nat.card P - 1 := by
    have h0mem : (0 : Lane t) ∈ Finset.univ.filter (fun p => p ∈ P) := by simp
    have hPcard : (Finset.univ.filter (fun p => p ∈ P)).card = Nat.card P := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hdisj : Disjoint (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ shape ht x))
        (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ (Nb ht x).card = 5)) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      have h5 := (Finset.mem_filter.mp h2).2.2
      have hnz : x ≠ 0 := by
        intro hz; subst hz; have hemp : Nb ht (0 : Lane t) = ∅ := by ext i; simp [Nb]
        rw [hemp, Finset.card_empty] at h5; omega
      have h4 := (footprint_classify ht ht3 x hnz (hP (Finset.mem_filter.mp h1).2.1)).2.1.mpr
        (Finset.mem_filter.mp h1).2.2
      omega
    have hsub : Finset.univ.filter (fun x : Lane t => x ∈ P ∧ shape ht x) ∪
        Finset.univ.filter (fun x : Lane t => x ∈ P ∧ (Nb ht x).card = 5) ⊆
        (Finset.univ.filter (fun p => p ∈ P)).erase 0 := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hx ⊢
      rcases hx with ⟨hp, hs⟩ | ⟨hp, h5⟩
      · refine ⟨?_, hp⟩
        intro hz; subst hz
        rcases hs with h | h
        · have := wt_pair_eq_two h; rw [wt_zero] at this; omega
        · have := wt_run3_eq_three ht h; rw [wt_zero] at this; omega
      · refine ⟨?_, hp⟩
        intro hz; subst hz
        have hemp : Nb ht (0 : Lane t) = ∅ := by ext i; simp [Nb]
        rw [hemp, Finset.card_empty] at h5; omega
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem h0mem, hPcard] at hc
    exact hc
  have hle : ((Nat.card P - 1 + 3 * shapeCnt ht P + nb5Cnt ht P : ℕ) : ℚ) ≤
      ((2 * (Nat.card P - 1) + 2 * shapeCnt ht P : ℕ) : ℚ) := by
    exact_mod_cast (show Nat.card P - 1 + 3 * shapeCnt ht P + nb5Cnt ht P ≤
      2 * (Nat.card P - 1) + 2 * shapeCnt ht P by omega)
  have hpos : (0 : ℚ) ≤ cntS t ∅ := Nat.cast_nonneg _
  nlinarith

def cliqueSpan {t : ℕ} (C : Finset (Fin (3 * t))) : Submodule F (Lane t) :=
  Submodule.span F {w : Lane t | ∃ i ∈ C, ∃ j ∈ C, i ≠ j ∧ w = pairVec i j}

lemma cliqueSpan_supp {t : ℕ} (C : Finset (Fin (3 * t))) (u : Lane t)
    (hu : u ∈ cliqueSpan C) : ∀ i, i ∉ C → u i = 0 := by
  refine Submodule.span_induction ?_ (fun _ _ => rfl)
    (fun a b _ _ ha hb i hi => by simp [ha i hi, hb i hi])
    (fun r a _ ha i hi => by simp [ha i hi]) hu
  rintro _ ⟨a, ha, b, hb, hab, rfl⟩ i hi
  have h1 : i ≠ a := fun h => hi (h ▸ ha)
  have h2 : i ≠ b := fun h => hi (h ▸ hb)
  rw [pairVec_apply hab]; simp [h1, h2]

lemma cliqueSpan_le_of_pairs {t : ℕ} (E : Submodule F (Lane t)) (C : Finset (Fin (3 * t)))
    (hp : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → pairVec i j ∈ E) : cliqueSpan C ≤ E := by
  rw [cliqueSpan, Submodule.span_le]
  rintro _ ⟨i, hi, j, hj, hij, rfl⟩
  exact hp i hi j hj hij

open Classical in
lemma cliqueSpan_finrank {t : ℕ} (C : Finset (Fin (3 * t))) (hC : C.Nonempty) :
    Module.finrank F (cliqueSpan C) = C.card - 1 := by
  obtain ⟨r, hr⟩ := hC
  let B : (C.erase r) → cliqueSpan C := fun x =>
    ⟨pairVec r x.1, Submodule.subset_span ⟨r, hr, x.1, Finset.mem_of_mem_erase x.2,
      (Finset.mem_erase.mp x.2).1.symm, rfl⟩⟩
  have hlin : LinearIndependent F B := by
    rw [Fintype.linearIndependent_iff]
    intro g hg x
    have hv := congrFun (congrArg Subtype.val hg) x.1
    simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ZeroMemClass.coe_zero, Pi.zero_apply] at hv
    rw [Finset.sum_eq_single x] at hv
    · have hne : x.1 ≠ r := (Finset.mem_erase.mp x.2).1
      have h1 : (B x).1 x.1 = 1 := by change pairVec r x.1 x.1 = 1; rw [pairVec_apply hne.symm]; simp
      rw [h1, mul_one] at hv; exact hv
    · intro y _ hyx
      have hne1 : x.1 ≠ r := (Finset.mem_erase.mp x.2).1
      have hne2 : x.1 ≠ y.1 := fun h => hyx (Subtype.ext h.symm)
      have hney : r ≠ y.1 := (Finset.mem_erase.mp y.2).1.symm
      have h0 : (B y).1 x.1 = 0 := by change pairVec r y.1 x.1 = 0; rw [pairVec_apply hney]; simp [hne1, hne2]
      rw [h0, mul_zero]
    · intro h; exact absurd (Finset.mem_univ x) h
  let φ : (C.erase r → F) →ₗ[F] cliqueSpan C :=
    { toFun := fun g => ∑ x : C.erase r, g x • B x
      map_add' := fun f g => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun s g => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hφ_inj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro g hg
    funext x
    exact (Fintype.linearIndependent_iff.mp hlin) g hg x
  have hφ_surj : Function.Surjective φ := by
    intro u
    have hmem : u.1 ∈ Submodule.span F (Set.range (fun x : C.erase r => pairVec r x.1)) := by
      refine Submodule.span_induction ?_ (Submodule.zero_mem _)
        (fun a b _ _ ha hb => Submodule.add_mem _ ha hb)
        (fun s a _ ha => Submodule.smul_mem _ s ha) u.2
      rintro _ ⟨i, hi, j, hj, hij, rfl⟩
      by_cases hir : i = r
      · subst hir
        exact Submodule.subset_span ⟨⟨j, Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩⟩, rfl⟩
      · by_cases hjr : j = r
        · subst hjr
          rw [pairVec_comm]
          exact Submodule.subset_span ⟨⟨i, Finset.mem_erase.mpr ⟨hir, hi⟩⟩, rfl⟩
        · rw [← pairVec_add_cancel i r j, pairVec_comm i r]
          exact Submodule.add_mem _
            (Submodule.subset_span ⟨⟨i, Finset.mem_erase.mpr ⟨hir, hi⟩⟩, rfl⟩)
            (Submodule.subset_span ⟨⟨j, Finset.mem_erase.mpr ⟨hjr, hj⟩⟩, rfl⟩)
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
    obtain ⟨c, hc⟩ := hmem
    refine ⟨fun x => c x, Subtype.ext ?_⟩
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, SetLike.val_smul, B]
    rw [← hc, Finsupp.sum_fintype]
    intro x; simp
  have heq := (LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).finrank_eq
  rw [← heq, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Finset.card_erase_of_mem hr]

lemma clique_le_finrank_of_not_isSep {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t))
    (hnsep : ¬ isSep ht P) (C : Finset (Fin (3 * t))) (hC : C.Nonempty) (hmono : mono C)
    (hp : ∀ i ∈ C, ∀ j ∈ C, i ≠ j → pairVec i j ∈ P) : C.card ≤ Module.finrank F P := by
  by_contra hgt
  push Not at hgt
  have hle := cliqueSpan_le_of_pairs P C hp
  have hdim := cliqueSpan_finrank C hC
  have hle2 := Submodule.finrank_mono hle
  have heq : cliqueSpan C = P := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  apply hnsep
  intro p hpP i ⟨h1, h2⟩
  rw [← heq] at hpP
  have hiC : i ∈ C := by by_contra h; exact h1 (cliqueSpan_supp C p hpP i h)
  have hnxC : nx ht i ∈ C := by by_contra h; exact h2 (cliqueSpan_supp C p hpP (nx ht i) h)
  exact nx_color ht i (hmono (nx ht i) hnxC i hiC)

open Classical in
lemma wt3_colors {t : ℕ} (w : Lane t) (hc : w ∈ codeSub t) (hw : wt w = 3) :
    ∀ a : Fin 3, ∃! i : Fin (3 * t), w i ≠ 0 ∧ i.val % 3 = a.val := by
  let S : Finset (Fin (3 * t)) := Finset.univ.filter (fun i => w i ≠ 0)
  have hSc : S.card = 3 := hw
  obtain ⟨i1, i2, i3, h12, h13, h23, hSeq⟩ := Finset.card_eq_three.mp hSc
  have hchk := support_checks_code w hc
  have hsum : ∀ e : Fin 2, parityCol e (colour i1) + parityCol e (colour i2) + parityCol e (colour i3) = 0 := by
    intro e
    have he := hchk e
    change ∑ i ∈ S, parityCol e (colour i) = 0 at he
    rw [hSeq, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton] at he
    linear_combination he
  have hne12 : colour i1 ≠ colour i2 := by
    intro heq
    obtain ⟨e, hene⟩ := column_nonzero (colour i3)
    have h0 := hsum e
    rw [heq, z2_add_self, zero_add] at h0
    exact hene h0
  have hne13 : colour i1 ≠ colour i3 := by
    intro heq
    obtain ⟨e, hene⟩ := column_nonzero (colour i2)
    have h0 := hsum e
    have hz := z2_add_self (parityCol e (colour i3))
    rw [heq] at h0
    apply hene; linear_combination h0 - hz
  have hne23 : colour i2 ≠ colour i3 := by
    intro heq
    obtain ⟨e, hene⟩ := column_nonzero (colour i1)
    have h0 := hsum e
    have hz := z2_add_self (parityCol e (colour i3))
    rw [heq] at h0
    apply hene; linear_combination h0 - hz
  have hSmem : ∀ i, w i ≠ 0 ↔ i = i1 ∨ i = i2 ∨ i = i3 := by
    intro i
    have hiff : i ∈ S ↔ i ∈ ({i1, i2, i3} : Finset (Fin (3 * t))) := by rw [hSeq]
    simpa [S] using hiff
  have him : ({colour i1, colour i2, colour i3} : Finset (Fin 3)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem (by simp [hne12, hne13]),
      Finset.card_insert_of_notMem (by simp [hne23]), Finset.card_singleton]
    decide
  intro a
  have ha : a ∈ ({colour i1, colour i2, colour i3} : Finset (Fin 3)) := by rw [him]; exact Finset.mem_univ a
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · refine ⟨i1, ⟨(hSmem i1).mpr (Or.inl rfl), rfl⟩, fun j ⟨hj, hcol⟩ => ?_⟩
    rcases (hSmem j).mp hj with rfl | rfl | rfl
    · rfl
    · exfalso; exact hne12 (Fin.ext hcol.symm)
    · exfalso; exact hne13 (Fin.ext hcol.symm)
  · refine ⟨i2, ⟨(hSmem i2).mpr (Or.inr (Or.inl rfl)), rfl⟩, fun j ⟨hj, hcol⟩ => ?_⟩
    rcases (hSmem j).mp hj with rfl | rfl | rfl
    · exfalso; exact hne12 (Fin.ext hcol)
    · rfl
    · exfalso; exact hne23 (Fin.ext hcol.symm)
  · refine ⟨i3, ⟨(hSmem i3).mpr (Or.inr (Or.inr rfl)), rfl⟩, fun j ⟨hj, hcol⟩ => ?_⟩
    rcases (hSmem j).mp hj with rfl | rfl | rfl
    · exfalso; exact hne13 (Fin.ext hcol)
    · exfalso; exact hne23 (Fin.ext hcol)
    · rfl

lemma run3_through_pair_le_two {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    (b1 b2 : Fin (3 * t)) (hb : b1 ≠ b2) :
    (Finset.univ.filter (fun j : Fin (3 * t) =>
      run3Vec ht j b1 ≠ 0 ∧ run3Vec ht j b2 ≠ 0)).card ≤ 2 := by
  have hsub : Finset.univ.filter (fun j : Fin (3 * t) =>
      run3Vec ht j b1 ≠ 0 ∧ run3Vec ht j b2 ≠ 0) ⊆ {b1, pv ht b1, pv ht (pv ht b1)} := by
    intro j hj
    have h1 := (Finset.mem_filter.mp hj).2.1
    simp only [run3Vec] at h1
    split_ifs at h1 with h
    · rcases h with rfl | h | h
      · exact Finset.mem_insert_self _ _
      · rw [show j = pv ht b1 by rw [h, pv_nx]]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      · rw [show j = pv ht (pv ht b1) by rw [h, pv_nx, pv_nx]]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    · exact absurd rfl h1
  have hnot_both : ¬ (b1 ∈ Finset.univ.filter (fun j : Fin (3 * t) =>
        run3Vec ht j b1 ≠ 0 ∧ run3Vec ht j b2 ≠ 0) ∧
      pv ht (pv ht b1) ∈ Finset.univ.filter (fun j : Fin (3 * t) =>
        run3Vec ht j b1 ≠ 0 ∧ run3Vec ht j b2 ≠ 0)) := by
    rintro ⟨hA, hB⟩
    have hA2 := (Finset.mem_filter.mp hA).2.2
    have hB2 := (Finset.mem_filter.mp hB).2.2
    simp only [run3Vec] at hA2 hB2
    have hA' : b2 = b1 ∨ b2 = nx ht b1 ∨ b2 = nx ht (nx ht b1) := by
      by_contra h; simp [h] at hA2
    have hB' : b2 = pv ht (pv ht b1) ∨ b2 = pv ht b1 ∨ b2 = b1 := by
      have h1 : nx ht (pv ht (pv ht b1)) = pv ht b1 := nx_pv ht _
      rw [h1, nx_pv] at hB2
      by_contra h; simp [h] at hB2
    rcases hA' with rfl | h1 | h1
    · exact hb rfl
    · rcases hB' with h2 | h2 | h2
      · have heq := h1.symm.trans h2
        have h3 := congrArg (fun z => nx ht (nx ht z)) heq
        rw [nx_pv, nx_pv] at h3
        exact nx_three_ne_self ht (by omega) b1 h3
      · have heq := h1.symm.trans h2
        have h3 := congrArg (nx ht) heq
        rw [nx_pv] at h3
        exact nx_nx_ne_self ht b1 h3
      · exact hb h2.symm
    · rcases hB' with h2 | h2 | h2
      · have heq := h1.symm.trans h2
        have h3 := congrArg (fun z => nx ht (nx ht z)) heq
        rw [nx_pv, nx_pv] at h3
        have hv := congrArg Fin.val h3
        have hb1 := b1.isLt
        rw [nx_val, nx_val, nx_val, nx_val] at hv
        split_ifs at hv <;> omega
      · have heq := h1.symm.trans h2
        have h3 := congrArg (nx ht) heq
        rw [nx_pv] at h3
        exact nx_three_ne_self ht (by omega) b1 h3
      · exact hb h2.symm
  by_cases hA : b1 ∈ Finset.univ.filter (fun j : Fin (3 * t) =>
      run3Vec ht j b1 ≠ 0 ∧ run3Vec ht j b2 ≠ 0)
  · have hB : pv ht (pv ht b1) ∉ Finset.univ.filter (fun j : Fin (3 * t) =>
        run3Vec ht j b1 ≠ 0 ∧ run3Vec ht j b2 ≠ 0) := fun h => hnot_both ⟨hA, h⟩
    have hsub2 : Finset.univ.filter (fun j : Fin (3 * t) =>
        run3Vec ht j b1 ≠ 0 ∧ run3Vec ht j b2 ≠ 0) ⊆ {b1, pv ht b1} := by
      intro j hj
      have hm := hsub hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      rcases hm with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd hj hB
    exact (Finset.card_le_card hsub2).trans (Finset.card_le_two)
  · have hsub2 : Finset.univ.filter (fun j : Fin (3 * t) =>
        run3Vec ht j b1 ≠ 0 ∧ run3Vec ht j b2 ≠ 0) ⊆ {pv ht b1, pv ht (pv ht b1)} := by
      intro j hj
      have hm := hsub hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm ⊢
      rcases hm with rfl | rfl | rfl
      · exact absurd hj hA
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact (Finset.card_le_card hsub2).trans (Finset.card_le_two)

open Classical in
lemma coset_wt3_run3_bound {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    (y0 : Lane t) (hy0 : y0 ∈ codeSub t)
    (C : Finset (Fin (3 * t))) (hC2 : 2 ≤ C.card) (hmono : mono C)
    (hCle : cliqueSpan C ≤ codeSub t) :
    (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ wt (y0 + u) = 3)).card ≤ C.card ∧
    (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ isRun3 ht (y0 + u))).card ≤ 2 := by
  by_cases hex : (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ wt (y0 + u) = 3)).Nonempty
  · obtain ⟨u0, hu0⟩ := hex
    obtain ⟨hu0S, hwt0⟩ := (Finset.mem_filter.mp hu0).2
    let y1 : Lane t := y0 + u0
    have hy1 : y1 ∈ codeSub t := (codeSub t).add_mem hy0 (hCle hu0S)
    have hshift1 : (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ wt (y0 + u) = 3)).card =
        (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ wt (y1 + u) = 3)).card := by
      refine Finset.card_bij (fun u _ => u + u0) ?_ ?_ ?_
      · intro u hu
        obtain ⟨huS, hwu⟩ := (Finset.mem_filter.mp hu).2
        have heq : y1 + (u + u0) = y0 + u := by
          funext i; simp only [y1, Pi.add_apply]; have := z2_add_self (u0 i); linear_combination this
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (cliqueSpan C).add_mem huS hu0S, heq.symm ▸ hwu⟩
      · intro a _ b _ hab
        funext i; have := congrFun hab i; simp only [Pi.add_apply] at this
        have hz := z2_add_self (u0 i); linear_combination this - hz + hz
      · intro v hv
        obtain ⟨hvS, hwv⟩ := (Finset.mem_filter.mp hv).2
        refine ⟨v + u0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (cliqueSpan C).add_mem hvS hu0S, ?_⟩, ?_⟩
        · have heq : y0 + (v + u0) = y1 + v := by funext i; simp only [y1, Pi.add_apply]; ring
          rwa [heq]
        · funext i; simp only [Pi.add_apply]; have := z2_add_self (u0 i); linear_combination this
    have hshift2 : (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ isRun3 ht (y0 + u))).card =
        (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ isRun3 ht (y1 + u))).card := by
      refine Finset.card_bij (fun u _ => u + u0) ?_ ?_ ?_
      · intro u hu
        obtain ⟨huS, hru⟩ := (Finset.mem_filter.mp hu).2
        have heq : y1 + (u + u0) = y0 + u := by
          funext i; simp only [y1, Pi.add_apply]; have := z2_add_self (u0 i); linear_combination this
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (cliqueSpan C).add_mem huS hu0S, heq.symm ▸ hru⟩
      · intro a _ b _ hab
        funext i; have := congrFun hab i; simp only [Pi.add_apply] at this
        linear_combination this
      · intro v hv
        obtain ⟨hvS, hrv⟩ := (Finset.mem_filter.mp hv).2
        refine ⟨v + u0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (cliqueSpan C).add_mem hvS hu0S, ?_⟩, ?_⟩
        · have heq : y0 + (v + u0) = y1 + v := by funext i; simp only [y1, Pi.add_apply]; ring
          rwa [heq]
        · funext i; simp only [Pi.add_apply]; have := z2_add_self (u0 i); linear_combination this
    rw [hshift1, hshift2]
    obtain ⟨c0, hc0⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
    let a0 : Fin 3 := colour c0
    have hCcol : ∀ i ∈ C, i.val % 3 = a0.val := fun i hi => hmono i hi c0 hc0
    have hu_off : ∀ u ∈ cliqueSpan C, ∀ i : Fin (3 * t), i.val % 3 ≠ a0.val → u i = 0 := by
      intro u hu i hne
      exact cliqueSpan_supp C u hu i (fun hiC => hne (hCcol i hiC))
    obtain ⟨i0, ⟨hi0_nz, hi0_col⟩, hi0_uniq⟩ := wt3_colors y1 hy1 hwt0 a0
    refine ⟨?_, ?_⟩
    · let S3 := Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ wt (y1 + u) = 3)
      have hex_i : ∀ u ∈ S3, ∃! i : Fin (3 * t), (y1 + u) i ≠ 0 ∧ i.val % 3 = a0.val := by
        intro u hu
        obtain ⟨huS, hwu⟩ := (Finset.mem_filter.mp hu).2
        exact wt3_colors (y1 + u) ((codeSub t).add_mem hy1 (hCle huS)) hwu a0
      let pick : Lane t → Fin (3 * t) := fun u =>
        if h : u ∈ S3 then Classical.choose (hex_i u h) else c0
      have hpick_spec : ∀ u (h : u ∈ S3), (y1 + u) (pick u) ≠ 0 ∧ (pick u).val % 3 = a0.val := by
        intro u h; simp only [pick, h, ↓reduceDIte]; exact (Classical.choose_spec (hex_i u h)).1
      have hpick_uniq : ∀ u (h : u ∈ S3) i, (y1 + u) i ≠ 0 → i.val % 3 = a0.val → i = pick u := by
        intro u h i h1 h2; simp only [pick, h, ↓reduceDIte]; exact (Classical.choose_spec (hex_i u h)).2 i ⟨h1, h2⟩
      have hpick_inj : Set.InjOn pick S3 := by
        intro u1 hu1 u2 hu2 heq
        have hu1' : u1 ∈ S3 := Finset.mem_coe.mp hu1
        have hu2' : u2 ∈ S3 := Finset.mem_coe.mp hu2
        obtain ⟨hu1S, _⟩ := (Finset.mem_filter.mp hu1').2
        obtain ⟨hu2S, _⟩ := (Finset.mem_filter.mp hu2').2
        have h1s := hpick_spec u1 hu1'
        have h2s := hpick_spec u2 hu2'
        funext i
        by_cases hcol : i.val % 3 = a0.val
        · have hyu1 : (y1 + u1) i = if i = pick u1 then 1 else 0 := by
            by_cases hi : i = pick u1
            · subst hi; simp [(F_cases _).resolve_left h1s.1]
            · simp only [hi, ↓reduceIte]
              by_contra hnz
              exact hi (hpick_uniq u1 hu1' i hnz hcol)
          have hyu2 : (y1 + u2) i = if i = pick u2 then 1 else 0 := by
            by_cases hi : i = pick u2
            · subst hi; simp [(F_cases _).resolve_left h2s.1]
            · simp only [hi, ↓reduceIte]
              by_contra hnz
              exact hi (hpick_uniq u2 hu2' i hnz hcol)
          have h12 : (y1 + u1) i = (y1 + u2) i := by rw [hyu1, hyu2, heq]
          simp only [Pi.add_apply] at h12
          have hz := z2_add_self (y1 i)
          linear_combination h12 - hz + hz
        · rw [hu_off u1 hu1S i hcol, hu_off u2 hu2S i hcol]
      by_cases hi0C : i0 ∈ C
      · have him : Set.MapsTo pick S3 C := by
          intro u hu
          have hu' : u ∈ S3 := Finset.mem_coe.mp hu
          have hps := hpick_spec u hu'
          by_cases he : pick u = i0
          · rw [he]; exact hi0C
          · have hy1p : y1 (pick u) = 0 := by
              by_contra hnz; exact he (hi0_uniq (pick u) ⟨hnz, hps.2⟩)
            have hup : u (pick u) ≠ 0 := by
              have := hps.1; simp only [Pi.add_apply, hy1p, zero_add] at this; exact this
            by_contra hnot
            exact hup (cliqueSpan_supp C u (Finset.mem_filter.mp hu').2.1 (pick u) hnot)
        exact Finset.card_le_card_of_injOn pick him hpick_inj
      · have him : Set.MapsTo pick S3 ({i0} : Finset (Fin (3 * t))) := by
          intro u hu
          have hu' : u ∈ S3 := Finset.mem_coe.mp hu
          simp only [Finset.mem_coe, Finset.mem_singleton]
          by_contra hne
          have huS := (Finset.mem_filter.mp hu').2.1
          have hui0 : u i0 = 0 := cliqueSpan_supp C u huS i0 hi0C
          have hyu_i0 : (y1 + u) i0 ≠ 0 := by simp [hui0, hi0_nz]
          exact hne (hpick_uniq u hu' i0 hyu_i0 hi0_col).symm
        exact (Finset.card_le_card_of_injOn pick him hpick_inj).trans (by rw [Finset.card_singleton]; omega)
    · let a1 : Fin 3 := ⟨(a0.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
      let a2 : Fin 3 := ⟨(a0.val + 2) % 3, Nat.mod_lt _ (by decide)⟩
      have ha1 : a1.val ≠ a0.val := by have := a0.isLt; dsimp [a1]; omega
      have ha2 : a2.val ≠ a0.val := by have := a0.isLt; dsimp [a2]; omega
      have ha12 : a1.val ≠ a2.val := by have := a0.isLt; dsimp [a1, a2]; omega
      obtain ⟨b1, ⟨hb1_nz, hb1_col⟩, _⟩ := wt3_colors y1 hy1 hwt0 a1
      obtain ⟨b2, ⟨hb2_nz, hb2_col⟩, _⟩ := wt3_colors y1 hy1 hwt0 a2
      have hb12 : b1 ≠ b2 := fun h => ha12 (hb1_col.symm.trans ((congrArg (fun z : Fin (3 * t) => z.val % 3) h).trans hb2_col))
      let SR := Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ isRun3 ht (y1 + u))
      let J := Finset.univ.filter (fun j : Fin (3 * t) => run3Vec ht j b1 ≠ 0 ∧ run3Vec ht j b2 ≠ 0)
      have hex_j : ∀ u ∈ SR, ∃ j : Fin (3 * t), y1 + u = run3Vec ht j :=
        fun u hu => (isRun3_iff_run3Vec ht _).mp (Finset.mem_filter.mp hu).2.2
      let pickJ : Lane t → Fin (3 * t) := fun u =>
        if h : u ∈ SR then Classical.choose (hex_j u h) else b1
      have hmaps : Set.MapsTo pickJ SR J := by
        intro u hu
        have hu' : u ∈ SR := Finset.mem_coe.mp hu
        have hspec : y1 + u = run3Vec ht (pickJ u) := by
          simp only [pickJ, hu', ↓reduceDIte]; exact Classical.choose_spec (hex_j u hu')
        have huS := (Finset.mem_filter.mp hu').2.1
        have h1 : (y1 + u) b1 ≠ 0 := by
          simp only [Pi.add_apply, hu_off u huS b1 (hb1_col.symm ▸ ha1), add_zero]; exact hb1_nz
        have h2 : (y1 + u) b2 ≠ 0 := by
          simp only [Pi.add_apply, hu_off u huS b2 (hb2_col.symm ▸ ha2), add_zero]; exact hb2_nz
        rw [hspec] at h1 h2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩
      have hinj : Set.InjOn pickJ SR := by
        intro u1 hu1 u2 hu2 heq
        have hu1' : u1 ∈ SR := Finset.mem_coe.mp hu1
        have hu2' : u2 ∈ SR := Finset.mem_coe.mp hu2
        have h1 : y1 + u1 = run3Vec ht (pickJ u1) := by
          simp only [pickJ, hu1', ↓reduceDIte]; exact Classical.choose_spec (hex_j u1 hu1')
        have h2 : y1 + u2 = run3Vec ht (pickJ u2) := by
          simp only [pickJ, hu2', ↓reduceDIte]; exact Classical.choose_spec (hex_j u2 hu2')
        have h12 : y1 + u1 = y1 + u2 := h1.trans ((congrArg (run3Vec ht) heq).trans h2.symm)
        funext i; have := congrFun h12 i; simp only [Pi.add_apply] at this
        linear_combination this
      exact (Finset.card_le_card_of_injOn pickJ hmaps hinj).trans (run3_through_pair_le_two ht ht3 b1 b2 hb12)
  · rw [Finset.not_nonempty_iff_eq_empty] at hex
    have hrun_emp : Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ isRun3 ht (y0 + u)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      obtain ⟨huS, hru⟩ := (Finset.mem_filter.mp hu).2
      have hmem : u ∈ Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ wt (y0 + u) = 3) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, huS, wt_run3_eq_three ht hru⟩
      rw [hex] at hmem; exact Finset.notMem_empty u hmem
    rw [hex, hrun_emp]; simp

open Classical in
lemma two_clique_wt3_run3_bound {t : ℕ} (ht : 0 < t) (_ht3 : 3 ≤ t)
    (y0 : Lane t) (hy0 : y0 ∈ codeSub t)
    (C1 C2 : Finset (Fin (3 * t))) (hC1 : C1.card = 3) (hC2 : C2.card = 3)
    (hm1 : mono C1) (hm2 : mono C2)
    (hSle : cliqueSpan C1 ⊔ cliqueSpan C2 ≤ codeSub t) :
    (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C1 ⊔ cliqueSpan C2 ∧ wt (y0 + u) = 3)).card ≤ 9 ∧
    (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C1 ⊔ cliqueSpan C2 ∧ isRun3 ht (y0 + u))).card ≤ 3 := by
  let S := cliqueSpan C1 ⊔ cliqueSpan C2
  by_cases hex : (Finset.univ.filter (fun u : Lane t => u ∈ S ∧ wt (y0 + u) = 3)).Nonempty
  · obtain ⟨u0, hu0⟩ := hex
    obtain ⟨hu0S, hwt0⟩ := (Finset.mem_filter.mp hu0).2
    let y1 : Lane t := y0 + u0
    have hy1 : y1 ∈ codeSub t := (codeSub t).add_mem hy0 (hSle hu0S)
    have hshift1 : (Finset.univ.filter (fun u : Lane t => u ∈ S ∧ wt (y0 + u) = 3)).card =
        (Finset.univ.filter (fun u : Lane t => u ∈ S ∧ wt (y1 + u) = 3)).card := by
      refine Finset.card_bij (fun u _ => u + u0) ?_ ?_ ?_
      · intro u hu
        obtain ⟨huS, hwu⟩ := (Finset.mem_filter.mp hu).2
        have heq : y1 + (u + u0) = y0 + u := by
          funext i; simp only [y1, Pi.add_apply]; have := z2_add_self (u0 i); linear_combination this
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.add_mem huS hu0S, heq.symm ▸ hwu⟩
      · intro a _ b _ hab
        funext i; have := congrFun hab i; simp only [Pi.add_apply] at this; linear_combination this
      · intro v hv
        obtain ⟨hvS, hwv⟩ := (Finset.mem_filter.mp hv).2
        refine ⟨v + u0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.add_mem hvS hu0S, ?_⟩, ?_⟩
        · have heq : y0 + (v + u0) = y1 + v := by funext i; simp only [y1, Pi.add_apply]; ring
          rwa [heq]
        · funext i; simp only [Pi.add_apply]; have := z2_add_self (u0 i); linear_combination this
    have hshift2 : (Finset.univ.filter (fun u : Lane t => u ∈ S ∧ isRun3 ht (y0 + u))).card =
        (Finset.univ.filter (fun u : Lane t => u ∈ S ∧ isRun3 ht (y1 + u))).card := by
      refine Finset.card_bij (fun u _ => u + u0) ?_ ?_ ?_
      · intro u hu
        obtain ⟨huS, hru⟩ := (Finset.mem_filter.mp hu).2
        have heq : y1 + (u + u0) = y0 + u := by
          funext i; simp only [y1, Pi.add_apply]; have := z2_add_self (u0 i); linear_combination this
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.add_mem huS hu0S, heq.symm ▸ hru⟩
      · intro a _ b _ hab
        funext i; have := congrFun hab i; simp only [Pi.add_apply] at this; linear_combination this
      · intro v hv
        obtain ⟨hvS, hrv⟩ := (Finset.mem_filter.mp hv).2
        refine ⟨v + u0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.add_mem hvS hu0S, ?_⟩, ?_⟩
        · have heq : y0 + (v + u0) = y1 + v := by funext i; simp only [y1, Pi.add_apply]; ring
          rwa [heq]
        · funext i; simp only [Pi.add_apply]; have := z2_add_self (u0 i); linear_combination this
    rw [hshift1, hshift2]
    obtain ⟨c1, hc1⟩ := Finset.card_pos.mp (by omega : 0 < C1.card)
    obtain ⟨c2, hc2⟩ := Finset.card_pos.mp (by omega : 0 < C2.card)
    let a1 : Fin 3 := colour c1
    let a2 : Fin 3 := colour c2
    have hC1col : ∀ i ∈ C1, i.val % 3 = a1.val := fun i hi => hm1 i hi c1 hc1
    have hC2col : ∀ i ∈ C2, i.val % 3 = a2.val := fun i hi => hm2 i hi c2 hc2
    have hSsupp : ∀ u ∈ S, ∀ i, i ∉ C1 → i ∉ C2 → u i = 0 := by
      intro u hu i h1 h2
      obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Submodule.mem_sup.mp hu
      simp [cliqueSpan_supp C1 u1 hu1 i h1, cliqueSpan_supp C2 u2 hu2 i h2]
    by_cases hsame : a1 = a2
    · have hu_off : ∀ u ∈ S, ∀ i : Fin (3 * t), i.val % 3 ≠ a1.val → u i = 0 := by
        intro u hu i hne
        exact hSsupp u hu i (fun h => hne (hC1col i h)) (fun h => hne ((hC2col i h).trans (congrArg Fin.val hsame.symm)))
      obtain ⟨i0, ⟨hi0_nz, hi0_col⟩, hi0_uniq⟩ := wt3_colors y1 hy1 hwt0 a1
      refine ⟨?_, ?_⟩
      · let S3 := Finset.univ.filter (fun u : Lane t => u ∈ S ∧ wt (y1 + u) = 3)
        have hex_i : ∀ u ∈ S3, ∃! i : Fin (3 * t), (y1 + u) i ≠ 0 ∧ i.val % 3 = a1.val := by
          intro u hu
          obtain ⟨huS, hwu⟩ := (Finset.mem_filter.mp hu).2
          exact wt3_colors (y1 + u) ((codeSub t).add_mem hy1 (hSle huS)) hwu a1
        let pick : Lane t → Fin (3 * t) := fun u =>
          if h : u ∈ S3 then Classical.choose (hex_i u h) else c1
        have hpick_spec : ∀ u (h : u ∈ S3), (y1 + u) (pick u) ≠ 0 ∧ (pick u).val % 3 = a1.val := by
          intro u h; simp only [pick, h, ↓reduceDIte]; exact (Classical.choose_spec (hex_i u h)).1
        have hpick_uniq : ∀ u (h : u ∈ S3) i, (y1 + u) i ≠ 0 → i.val % 3 = a1.val → i = pick u := by
          intro u h i h1 h2; simp only [pick, h, ↓reduceDIte]; exact (Classical.choose_spec (hex_i u h)).2 i ⟨h1, h2⟩
        have hpick_inj : Set.InjOn pick S3 := by
          intro u1 hu1 u2 hu2 heq
          have hu1' : u1 ∈ S3 := Finset.mem_coe.mp hu1
          have hu2' : u2 ∈ S3 := Finset.mem_coe.mp hu2
          obtain ⟨hu1S, _⟩ := (Finset.mem_filter.mp hu1').2
          obtain ⟨hu2S, _⟩ := (Finset.mem_filter.mp hu2').2
          have h1s := hpick_spec u1 hu1'
          have h2s := hpick_spec u2 hu2'
          funext i
          by_cases hcol : i.val % 3 = a1.val
          · have hyu1 : (y1 + u1) i = if i = pick u1 then 1 else 0 := by
              by_cases hi : i = pick u1
              · subst hi; simp [(F_cases _).resolve_left h1s.1]
              · simp only [hi, ↓reduceIte]
                by_contra hnz
                exact hi (hpick_uniq u1 hu1' i hnz hcol)
            have hyu2 : (y1 + u2) i = if i = pick u2 then 1 else 0 := by
              by_cases hi : i = pick u2
              · subst hi; simp [(F_cases _).resolve_left h2s.1]
              · simp only [hi, ↓reduceIte]
                by_contra hnz
                exact hi (hpick_uniq u2 hu2' i hnz hcol)
            have h12 : (y1 + u1) i = (y1 + u2) i := by rw [hyu1, hyu2, heq]
            simp only [Pi.add_apply] at h12; linear_combination h12
          · rw [hu_off u1 hu1S i hcol, hu_off u2 hu2S i hcol]
        have hmaps : Set.MapsTo pick S3 (insert i0 (C1 ∪ C2) : Finset (Fin (3 * t))) := by
          intro u hu
          have hu' : u ∈ S3 := Finset.mem_coe.mp hu
          have hps := hpick_spec u hu'
          simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_union]
          by_cases he : pick u = i0
          · exact Or.inl he
          · right
            have hy1p : y1 (pick u) = 0 := by
              by_contra hnz; exact he (hi0_uniq (pick u) ⟨hnz, hps.2⟩)
            have hup : u (pick u) ≠ 0 := by
              have := hps.1; simp only [Pi.add_apply, hy1p, zero_add] at this; exact this
            by_contra hnot; push Not at hnot
            exact hup (hSsupp u (Finset.mem_filter.mp hu').2.1 (pick u) hnot.1 hnot.2)
        calc S3.card ≤ (insert i0 (C1 ∪ C2)).card := Finset.card_le_card_of_injOn pick hmaps hpick_inj
          _ ≤ (C1 ∪ C2).card + 1 := Finset.card_insert_le _ _
          _ ≤ C1.card + C2.card + 1 := by have := Finset.card_union_le C1 C2; omega
          _ ≤ 9 := by omega
      · let b_col : Fin 3 := ⟨(a1.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
        have hbcol : b_col.val ≠ a1.val := by have := a1.isLt; dsimp [b_col]; omega
        obtain ⟨b, ⟨hb_nz, hb_c⟩, _⟩ := wt3_colors y1 hy1 hwt0 b_col
        let SR := Finset.univ.filter (fun u : Lane t => u ∈ S ∧ isRun3 ht (y1 + u))
        have hex_j : ∀ u ∈ SR, ∃ j : Fin (3 * t), y1 + u = run3Vec ht j :=
          fun u hu => (isRun3_iff_run3Vec ht _).mp (Finset.mem_filter.mp hu).2.2
        let pickJ : Lane t → Fin (3 * t) := fun u =>
          if h : u ∈ SR then Classical.choose (hex_j u h) else b
        have hmaps : Set.MapsTo pickJ SR ({b, pv ht b, pv ht (pv ht b)} : Finset (Fin (3 * t))) := by
          intro u hu
          have hu' : u ∈ SR := Finset.mem_coe.mp hu
          have hspec : y1 + u = run3Vec ht (pickJ u) := by
            simp only [pickJ, hu', ↓reduceDIte]; exact Classical.choose_spec (hex_j u hu')
          have h1 : (y1 + u) b ≠ 0 := by
            simp only [Pi.add_apply, hu_off u (Finset.mem_filter.mp hu').2.1 b (hb_c.symm ▸ hbcol), add_zero]
            exact hb_nz
          rw [hspec] at h1
          simp only [run3Vec] at h1
          split_ifs at h1 with h
          · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
            rcases h with h | h | h
            · exact Or.inl h.symm
            · exact Or.inr (Or.inl (by rw [h, pv_nx]))
            · exact Or.inr (Or.inr (by rw [h, pv_nx, pv_nx]))
          · exact absurd rfl h1
        have hinj : Set.InjOn pickJ SR := by
          intro u1 hu1 u2 hu2 heq
          have hu1' : u1 ∈ SR := Finset.mem_coe.mp hu1
          have hu2' : u2 ∈ SR := Finset.mem_coe.mp hu2
          have h1 : y1 + u1 = run3Vec ht (pickJ u1) := by
            simp only [pickJ, hu1', ↓reduceDIte]; exact Classical.choose_spec (hex_j u1 hu1')
          have h2 : y1 + u2 = run3Vec ht (pickJ u2) := by
            simp only [pickJ, hu2', ↓reduceDIte]; exact Classical.choose_spec (hex_j u2 hu2')
          have h12 : y1 + u1 = y1 + u2 := h1.trans ((congrArg (run3Vec ht) heq).trans h2.symm)
          funext i; have := congrFun h12 i; simp only [Pi.add_apply] at this; linear_combination this
        exact (Finset.card_le_card_of_injOn pickJ hmaps hinj).trans (by
          calc ({b, pv ht b, pv ht (pv ht b)} : Finset (Fin (3 * t))).card
              ≤ ({pv ht b, pv ht (pv ht b)} : Finset (Fin (3 * t))).card + 1 := Finset.card_insert_le _ _
            _ ≤ 2 + 1 := Nat.add_le_add_right Finset.card_le_two 1
            _ = 3 := rfl)
    · let a3 : Fin 3 := ⟨3 - a1.val - a2.val, by have := a1.isLt; have := a2.isLt; have : a1.val ≠ a2.val := fun h => hsame (Fin.ext h); omega⟩
      have ha31 : a3.val ≠ a1.val := by have := a1.isLt; have := a2.isLt; have : a1.val ≠ a2.val := fun h => hsame (Fin.ext h); dsimp [a3]; omega
      have ha32 : a3.val ≠ a2.val := by have := a1.isLt; have := a2.isLt; have : a1.val ≠ a2.val := fun h => hsame (Fin.ext h); dsimp [a3]; omega
      have hu_off3 : ∀ u ∈ S, ∀ i : Fin (3 * t), i.val % 3 = a3.val → u i = 0 := by
        intro u hu i hi
        exact hSsupp u hu i (fun h => ha31 (hi.symm.trans (hC1col i h)))
          (fun h => ha32 (hi.symm.trans (hC2col i h)))
      obtain ⟨i1_0, ⟨hi1_nz, hi1_col⟩, hi1_uniq⟩ := wt3_colors y1 hy1 hwt0 a1
      obtain ⟨i2_0, ⟨hi2_nz, hi2_col⟩, hi2_uniq⟩ := wt3_colors y1 hy1 hwt0 a2
      obtain ⟨b, ⟨hb_nz, hb_col⟩, _⟩ := wt3_colors y1 hy1 hwt0 a3
      refine ⟨?_, ?_⟩
      · let S3 := Finset.univ.filter (fun u : Lane t => u ∈ S ∧ wt (y1 + u) = 3)
        have hex1 : ∀ u ∈ S3, ∃! i : Fin (3 * t), (y1 + u) i ≠ 0 ∧ i.val % 3 = a1.val := fun u hu =>
          wt3_colors (y1 + u) ((codeSub t).add_mem hy1 (hSle (Finset.mem_filter.mp hu).2.1))
            (Finset.mem_filter.mp hu).2.2 a1
        have hex2 : ∀ u ∈ S3, ∃! i : Fin (3 * t), (y1 + u) i ≠ 0 ∧ i.val % 3 = a2.val := fun u hu =>
          wt3_colors (y1 + u) ((codeSub t).add_mem hy1 (hSle (Finset.mem_filter.mp hu).2.1))
            (Finset.mem_filter.mp hu).2.2 a2
        let p1 : Lane t → Fin (3 * t) := fun u => if h : u ∈ S3 then Classical.choose (hex1 u h) else c1
        let p2 : Lane t → Fin (3 * t) := fun u => if h : u ∈ S3 then Classical.choose (hex2 u h) else c2
        let T1 : Finset (Fin (3 * t)) := if i1_0 ∈ C1 then C1 else {i1_0}
        let T2 : Finset (Fin (3 * t)) := if i2_0 ∈ C2 then C2 else {i2_0}
        have hT1c : T1.card ≤ 3 := by dsimp [T1]; split_ifs; omega; simp
        have hT2c : T2.card ≤ 3 := by dsimp [T2]; split_ifs; omega; simp
        have hp1_mem : ∀ u ∈ S3, p1 u ∈ T1 := by
          intro u hu
          have hspec : (y1 + u) (p1 u) ≠ 0 ∧ (p1 u).val % 3 = a1.val := by
            simp only [p1, hu, ↓reduceDIte]; exact (Classical.choose_spec (hex1 u hu)).1
          dsimp [T1]
          split_ifs with hin
          · by_cases he : p1 u = i1_0
            · exact he ▸ hin
            · have hy0' : y1 (p1 u) = 0 := by by_contra hn; exact he (hi1_uniq _ ⟨hn, hspec.2⟩)
              have hu' : u (p1 u) ≠ 0 := by have := hspec.1; simp only [Pi.add_apply, hy0', zero_add] at this; exact this
              by_contra hnot
              exact hu' (hSsupp u (Finset.mem_filter.mp hu).2.1 (p1 u) hnot
                (fun hC2m => hsame (Fin.ext (hspec.2.symm.trans (hC2col _ hC2m)))))
          · simp only [Finset.mem_singleton]
            by_contra hne
            have hui : u i1_0 = 0 := hSsupp u (Finset.mem_filter.mp hu).2.1 i1_0 hin
              (fun hC2m => hsame (Fin.ext (hi1_col.symm.trans (hC2col _ hC2m))))
            have hyu : (y1 + u) i1_0 ≠ 0 := by simp [hui, hi1_nz]
            have h1 := (Classical.choose_spec (hex1 u hu)).2 i1_0 ⟨hyu, hi1_col⟩
            exact hne (by simp only [p1, hu, ↓reduceDIte]; exact h1.symm)
        have hp2_mem : ∀ u ∈ S3, p2 u ∈ T2 := by
          intro u hu
          have hspec : (y1 + u) (p2 u) ≠ 0 ∧ (p2 u).val % 3 = a2.val := by
            simp only [p2, hu, ↓reduceDIte]; exact (Classical.choose_spec (hex2 u hu)).1
          dsimp [T2]
          split_ifs with hin
          · by_cases he : p2 u = i2_0
            · exact he ▸ hin
            · have hy0' : y1 (p2 u) = 0 := by by_contra hn; exact he (hi2_uniq _ ⟨hn, hspec.2⟩)
              have hu' : u (p2 u) ≠ 0 := by have := hspec.1; simp only [Pi.add_apply, hy0', zero_add] at this; exact this
              by_contra hnot
              exact hu' (hSsupp u (Finset.mem_filter.mp hu).2.1 (p2 u)
                (fun hC1m => hsame (Fin.ext ((hC1col _ hC1m).symm.trans hspec.2))) hnot)
          · simp only [Finset.mem_singleton]
            by_contra hne
            have hui : u i2_0 = 0 := hSsupp u (Finset.mem_filter.mp hu).2.1 i2_0
              (fun hC1m => hsame (Fin.ext ((hC1col _ hC1m).symm.trans hi2_col))) hin
            have hyu : (y1 + u) i2_0 ≠ 0 := by simp [hui, hi2_nz]
            have h2 := (Classical.choose_spec (hex2 u hu)).2 i2_0 ⟨hyu, hi2_col⟩
            exact hne (by simp only [p2, hu, ↓reduceDIte]; exact h2.symm)
        have hmaps : Set.MapsTo (fun u => (p1 u, p2 u)) S3 (T1 ×ˢ T2 : Finset (Fin (3 * t) × Fin (3 * t))) :=
          fun u hu => Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hp1_mem u (Finset.mem_coe.mp hu), hp2_mem u (Finset.mem_coe.mp hu)⟩)
        have hp1_uniq : ∀ u (h : u ∈ S3) i, (y1 + u) i ≠ 0 → i.val % 3 = a1.val → i = p1 u := by
          intro u h i h1 h2; simp only [p1, h, ↓reduceDIte]; exact (Classical.choose_spec (hex1 u h)).2 i ⟨h1, h2⟩
        have hp2_uniq : ∀ u (h : u ∈ S3) i, (y1 + u) i ≠ 0 → i.val % 3 = a2.val → i = p2 u := by
          intro u h i h1 h2; simp only [p2, h, ↓reduceDIte]; exact (Classical.choose_spec (hex2 u h)).2 i ⟨h1, h2⟩
        have hinj : Set.InjOn (fun u => (p1 u, p2 u)) S3 := by
          intro u1 hu1 u2 hu2 heq
          have hu1' : u1 ∈ S3 := Finset.mem_coe.mp hu1
          have hu2' : u2 ∈ S3 := Finset.mem_coe.mp hu2
          have he1 : p1 u1 = p1 u2 := congrArg Prod.fst heq
          have he2 : p2 u1 = p2 u2 := congrArg Prod.snd heq
          funext i
          have h3 : i.val % 3 = a1.val ∨ i.val % 3 = a2.val ∨ i.val % 3 = a3.val := by
            have := a1.isLt; have := a2.isLt; have : a1.val ≠ a2.val := fun h => hsame (Fin.ext h); dsimp [a3]; omega
          rcases h3 with hc | hc | hc
          · have h1s : (y1 + u1) (p1 u1) ≠ 0 := by simp only [p1, hu1', ↓reduceDIte]; exact (Classical.choose_spec (hex1 u1 hu1')).1.1
            have h2s : (y1 + u2) (p1 u2) ≠ 0 := by simp only [p1, hu2', ↓reduceDIte]; exact (Classical.choose_spec (hex1 u2 hu2')).1.1
            have hyu1 : (y1 + u1) i = if i = p1 u1 then 1 else 0 := by
              by_cases hi : i = p1 u1
              · subst hi; simp [(F_cases _).resolve_left h1s]
              · simp only [hi, ↓reduceIte]; by_contra hn
                exact hi (hp1_uniq u1 hu1' i hn hc)
            have hyu2 : (y1 + u2) i = if i = p1 u2 then 1 else 0 := by
              by_cases hi : i = p1 u2
              · subst hi; simp [(F_cases _).resolve_left h2s]
              · simp only [hi, ↓reduceIte]; by_contra hn
                exact hi (hp1_uniq u2 hu2' i hn hc)
            have h12 : (y1 + u1) i = (y1 + u2) i := by rw [hyu1, hyu2, he1]
            simp only [Pi.add_apply] at h12; linear_combination h12
          · have h1s : (y1 + u1) (p2 u1) ≠ 0 := by simp only [p2, hu1', ↓reduceDIte]; exact (Classical.choose_spec (hex2 u1 hu1')).1.1
            have h2s : (y1 + u2) (p2 u2) ≠ 0 := by simp only [p2, hu2', ↓reduceDIte]; exact (Classical.choose_spec (hex2 u2 hu2')).1.1
            have hyu1 : (y1 + u1) i = if i = p2 u1 then 1 else 0 := by
              by_cases hi : i = p2 u1
              · subst hi; simp [(F_cases _).resolve_left h1s]
              · simp only [hi, ↓reduceIte]; by_contra hn
                exact hi (hp2_uniq u1 hu1' i hn hc)
            have hyu2 : (y1 + u2) i = if i = p2 u2 then 1 else 0 := by
              by_cases hi : i = p2 u2
              · subst hi; simp [(F_cases _).resolve_left h2s]
              · simp only [hi, ↓reduceIte]; by_contra hn
                exact hi (hp2_uniq u2 hu2' i hn hc)
            have h12 : (y1 + u1) i = (y1 + u2) i := by rw [hyu1, hyu2, he2]
            simp only [Pi.add_apply] at h12; linear_combination h12
          · rw [hu_off3 u1 (Finset.mem_filter.mp hu1').2.1 i hc, hu_off3 u2 (Finset.mem_filter.mp hu2').2.1 i hc]
        calc S3.card ≤ (T1 ×ˢ T2).card := Finset.card_le_card_of_injOn _ hmaps hinj
          _ = T1.card * T2.card := Finset.card_product T1 T2
          _ ≤ 3 * 3 := Nat.mul_le_mul hT1c hT2c
          _ = 9 := rfl
      · let SR := Finset.univ.filter (fun u : Lane t => u ∈ S ∧ isRun3 ht (y1 + u))
        have hex_j : ∀ u ∈ SR, ∃ j : Fin (3 * t), y1 + u = run3Vec ht j :=
          fun u hu => (isRun3_iff_run3Vec ht _).mp (Finset.mem_filter.mp hu).2.2
        let pickJ : Lane t → Fin (3 * t) := fun u =>
          if h : u ∈ SR then Classical.choose (hex_j u h) else b
        have hmaps : Set.MapsTo pickJ SR ({b, pv ht b, pv ht (pv ht b)} : Finset (Fin (3 * t))) := by
          intro u hu
          have hu' : u ∈ SR := Finset.mem_coe.mp hu
          have hspec : y1 + u = run3Vec ht (pickJ u) := by
            simp only [pickJ, hu', ↓reduceDIte]; exact Classical.choose_spec (hex_j u hu')
          have h1 : (y1 + u) b ≠ 0 := by
            simp only [Pi.add_apply, hu_off3 u (Finset.mem_filter.mp hu').2.1 b hb_col, add_zero]
            exact hb_nz
          rw [hspec] at h1
          simp only [run3Vec] at h1
          split_ifs at h1 with h
          · simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
            rcases h with h | h | h
            · exact Or.inl h.symm
            · exact Or.inr (Or.inl (by rw [h, pv_nx]))
            · exact Or.inr (Or.inr (by rw [h, pv_nx, pv_nx]))
          · exact absurd rfl h1
        have hinj : Set.InjOn pickJ SR := by
          intro u1 hu1 u2 hu2 heq
          have hu1' : u1 ∈ SR := Finset.mem_coe.mp hu1
          have hu2' : u2 ∈ SR := Finset.mem_coe.mp hu2
          have h1 : y1 + u1 = run3Vec ht (pickJ u1) := by
            simp only [pickJ, hu1', ↓reduceDIte]; exact Classical.choose_spec (hex_j u1 hu1')
          have h2 : y1 + u2 = run3Vec ht (pickJ u2) := by
            simp only [pickJ, hu2', ↓reduceDIte]; exact Classical.choose_spec (hex_j u2 hu2')
          have h12 : y1 + u1 = y1 + u2 := h1.trans ((congrArg (run3Vec ht) heq).trans h2.symm)
          funext i; have := congrFun h12 i; simp only [Pi.add_apply] at this; linear_combination this
        exact (Finset.card_le_card_of_injOn pickJ hmaps hinj).trans (by
          calc ({b, pv ht b, pv ht (pv ht b)} : Finset (Fin (3 * t))).card
              ≤ ({pv ht b, pv ht (pv ht b)} : Finset (Fin (3 * t))).card + 1 := Finset.card_insert_le _ _
            _ ≤ 2 + 1 := Nat.add_le_add_right Finset.card_le_two 1
            _ = 3 := rfl)
  · rw [Finset.not_nonempty_iff_eq_empty] at hex
    have hrun_emp : Finset.univ.filter (fun u : Lane t => u ∈ S ∧ isRun3 ht (y0 + u)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro u hu
      obtain ⟨huS, hru⟩ := (Finset.mem_filter.mp hu).2
      have hmem : u ∈ Finset.univ.filter (fun u : Lane t => u ∈ S ∧ wt (y0 + u) = 3) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, huS, wt_run3_eq_three ht hru⟩
      rw [hex] at hmem; exact Finset.notMem_empty u hmem
    rw [hex, hrun_emp]; simp

open Classical in
lemma subspace_coset_bound {t : ℕ} (P E S : Submodule F (Lane t)) (hSE : S ≤ E) (hEP : E ≤ P)
    (x0 : Lane t) (hx0 : x0 ∈ P) (pred : Lane t → Prop) (M : ℕ)
    (hM : ∀ y0 ∈ P, (Finset.univ.filter (fun u : Lane t => u ∈ S ∧ pred (y0 + u))).card ≤ M) :
    (Finset.univ.filter (fun u : Lane t => u ∈ E ∧ pred (x0 + u))).card ≤
      2 ^ (Module.finrank F E - Module.finrank F S) * M := by
  let S' : Submodule F E := S.comap E.subtype
  obtain ⟨K', hK'⟩ := Submodule.exists_isCompl S'
  let K : Submodule F (Lane t) := K'.map E.subtype
  have hS'_dim : Module.finrank F S' = Module.finrank F S := by
    have heq : S'.map E.subtype = S := by
      rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hSE]
    rw [← heq, Submodule.finrank_map_subtype_eq]
  have hK_dim : Module.finrank F K = Module.finrank F E - Module.finrank F S := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq S' K'
    rw [hK'.sup_eq_top, hK'.inf_eq_bot, finrank_top, finrank_bot, add_zero, hS'_dim] at hsum
    have hK'd : Module.finrank F K = Module.finrank F K' := Submodule.finrank_map_subtype_eq E K'
    omega
  have hKcard : (Finset.univ.filter (fun k : Lane t => k ∈ K)).card =
      2 ^ (Module.finrank F E - Module.finrank F S) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := F) (V := K), Nat.card_eq_fintype_card, ZMod.card, hK_dim]
  have hbi : Finset.univ.filter (fun u : Lane t => u ∈ E ∧ pred (x0 + u)) ⊆
      (Finset.univ.filter (fun k : Lane t => k ∈ K)).biUnion (fun k =>
        (Finset.univ.filter (fun s : Lane t => s ∈ S ∧ pred ((x0 + k) + s))).image (fun s => k + s)) := by
    intro u hu
    obtain ⟨huE, hpred⟩ := (Finset.mem_filter.mp hu).2
    have hmem_sup : (⟨u, huE⟩ : E) ∈ S' ⊔ K' := by rw [hK'.sup_eq_top]; trivial
    obtain ⟨s', hs', k', hk', heq⟩ := Submodule.mem_sup.mp hmem_sup
    have hu_eq : k'.1 + s'.1 = u := by
      have := congrArg Subtype.val heq; simp only [Submodule.coe_add] at this; rw [add_comm]; exact this
    refine Finset.mem_biUnion.mpr ⟨k'.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨k', hk', rfl⟩⟩,
      Finset.mem_image.mpr ⟨s'.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs', ?_⟩, hu_eq⟩⟩
    rwa [add_assoc, hu_eq]
  calc (Finset.univ.filter (fun u : Lane t => u ∈ E ∧ pred (x0 + u))).card
      ≤ ((Finset.univ.filter (fun k : Lane t => k ∈ K)).biUnion (fun k =>
          (Finset.univ.filter (fun s : Lane t => s ∈ S ∧ pred ((x0 + k) + s))).image (fun s => k + s))).card :=
        Finset.card_le_card hbi
    _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Lane t => k ∈ K),
          ((Finset.univ.filter (fun s : Lane t => s ∈ S ∧ pred ((x0 + k) + s))).image (fun s => k + s)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.univ.filter (fun k : Lane t => k ∈ K), M := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkK : k ∈ K := (Finset.mem_filter.mp hk).2
        obtain ⟨k', _, rfl⟩ := hkK
        exact Finset.card_image_le.trans (hM (x0 + k'.1) (P.add_mem hx0 (hEP k'.2)))
    _ = 2 ^ (Module.finrank F E - Module.finrank F S) * M := by
        rw [Finset.sum_const, smul_eq_mul, hKcard]

open Classical in
lemma odd_coset_iff {t : ℕ} (P : Submodule F (Lane t)) (x0 : Lane t)
    (hx0 : x0 ∈ P) (hodd : parityL (3 * t) x0 = 1) :
    let Pe := P ⊓ LinearMap.ker (parityL (3 * t))
    (Module.finrank F Pe + 1 = Module.finrank F P) ∧
    (∀ pred : Lane t → Prop, (∀ x ∈ P, pred x → parityL (3 * t) x = 1) →
      (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ pred x)).card =
      (Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ pred (x0 + u))).card) := by
  intro Pe
  let φ : P →ₗ[F] F := (parityL (3 * t)).comp P.subtype
  have hsurj : LinearMap.range φ = ⊤ := by
    rw [eq_top_iff]; intro a _
    rcases F_cases a with rfl | rfl
    · exact ⟨0, map_zero φ⟩
    · exact ⟨⟨x0, hx0⟩, hodd⟩
  have hker_eq : (LinearMap.ker φ).map P.subtype = Pe := by
    ext x; simp only [Pe, Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, φ,
      LinearMap.comp_apply, Submodule.coe_subtype]
    exact ⟨fun ⟨y, hy, hye⟩ => hye ▸ ⟨y.2, hy⟩, fun ⟨hxP, hx0⟩ => ⟨⟨x, hxP⟩, hx0, rfl⟩⟩
  have hdim : Module.finrank F Pe + 1 = Module.finrank F P := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hsurj, finrank_top, Module.finrank_self, ← Submodule.finrank_map_subtype_eq P (LinearMap.ker φ),
      hker_eq] at h1
    omega
  refine ⟨hdim, fun pred hpred => ?_⟩
  refine Finset.card_bij (fun x _ => x + x0) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxP, hpx⟩ := (Finset.mem_filter.mp hx).2
    have hpar : parityL (3 * t) (x + x0) = 0 := by
      rw [map_add, hpred x hxP hpx, hodd]; decide
    have heq : x0 + (x + x0) = x := by
      funext i; simp only [Pi.add_apply]; have := z2_add_self (x0 i); linear_combination this
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨P.add_mem hxP hx0, hpar⟩, heq.symm ▸ hpx⟩
  · intro a _ b _ hab
    funext i; have := congrFun hab i; simp only [Pi.add_apply] at this; linear_combination this
  · intro u hu
    obtain ⟨⟨huP, hupar⟩, hpu⟩ := (Finset.mem_filter.mp hu).2
    refine ⟨x0 + u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, P.add_mem hx0 huP, hpu⟩, ?_⟩
    funext i; simp only [Pi.add_apply]; have := z2_add_self (x0 i); linear_combination this

open Classical in
lemma wt3_le_15_of_run3_pos {t : ℕ} (ht : 0 < t) (P : Submodule F (Lane t))
    (hP : P ≤ codeSub t) (hdim : Module.finrank F P = 5) (hRpos : 0 < run3Cnt ht P) :
    wt3Cnt P ≤ 15 := by
  let Pe := P ⊓ LinearMap.ker (parityL (3 * t))
  obtain ⟨r0, hr0⟩ := Finset.card_pos.mp hRpos
  obtain ⟨hr0P, hr0_run⟩ := (Finset.mem_filter.mp hr0).2
  have hodd0 : parityL (3 * t) r0 = 1 := parityL_run3 ht hr0_run
  obtain ⟨hPedim, hcoset⟩ := odd_coset_iff P r0 hr0P hodd0
  let Podd := Finset.univ.filter (fun x : Lane t => x ∈ P ∧ parityL (3 * t) x = 1)
  have hPodd_card : Podd.card = 16 := by
    have h1 := hcoset (fun x => parityL (3 * t) x = 1) (fun _ _ h => h)
    have h2 : Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ parityL (3 * t) (r0 + u) = 1) =
        Finset.univ.filter (fun u : Lane t => u ∈ Pe) := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      intro hu; rw [map_add, hodd0, hu.2, add_zero]
    have h1' : Podd.card = (Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ parityL (3 * t) (r0 + u) = 1)).card := by
      convert h1
    rw [h1', h2, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := F) (V := Pe), Nat.card_eq_fintype_card, ZMod.card]
    have hPe4 : Module.finrank F Pe = 4 := by
      change Module.finrank F (↥(P ⊓ LinearMap.ker (parityL (3 * t)))) = 4; omega
    rw [hPe4]; decide
  have hwt3_sub : Finset.univ.filter (fun x : Lane t => x ∈ P ∧ wt x = 3) ⊆ Podd := by
    intro x hx
    obtain ⟨hxP, hwx⟩ := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxP, ?_⟩
    rw [parityL_eq_wt, hwx]; decide
  by_contra hgt
  push Not at hgt
  have heq_odd : Finset.univ.filter (fun x : Lane t => x ∈ P ∧ wt x = 3) = Podd :=
    Finset.eq_of_subset_of_card_le hwt3_sub (by unfold wt3Cnt at hgt; omega)
  have hall3 : ∀ x ∈ Podd, wt x = 3 := fun x hx => by
    rw [← heq_odd] at hx; exact (Finset.mem_filter.mp hx).2.2
  have hsum_wt : ∑ x ∈ Podd, wt x = 48 := by
    rw [Finset.sum_congr rfl hall3, Finset.sum_const, hPodd_card]; rfl
  have hswap : ∑ x ∈ Podd, wt x = ∑ i : Fin (3 * t), (Podd.filter (fun x => x i ≠ 0)).card := by
    simp only [wt, Finset.card_filter]
    rw [Finset.sum_comm]
  have hge8 : ∀ i ∈ supp P, 8 ≤ (Podd.filter (fun x => x i ≠ 0)).card := by
    intro i hi
    obtain ⟨v, hvP, hvi⟩ := (mem_supp P i).mp hi
    by_cases hve : parityL (3 * t) v = 0
    · have hbij : (Podd.filter (fun x => x i ≠ 0)).card = (Podd.filter (fun x => x i = 0)).card := by
        refine Finset.card_bij (fun x _ => x + v) ?_ ?_ ?_
        · intro x hx
          obtain ⟨hxO, hxi⟩ := Finset.mem_filter.mp hx
          obtain ⟨hxP, hx1⟩ := (Finset.mem_filter.mp hxO).2
          have h1 : x i = 1 := (F_cases _).resolve_left hxi
          have h2 : v i = 1 := (F_cases _).resolve_left hvi
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            P.add_mem hxP hvP, by rw [map_add, hx1, hve, add_zero]⟩, by simp [h1, h2, z2_add_self]⟩
        · intro a _ b _ hab
          funext k; have := congrFun hab k; simp only [Pi.add_apply] at this; linear_combination this
        · intro y hy
          obtain ⟨hyO, hyi⟩ := Finset.mem_filter.mp hy
          obtain ⟨hyP, hy1⟩ := (Finset.mem_filter.mp hyO).2
          refine ⟨y + v, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            P.add_mem hyP hvP, by rw [map_add, hy1, hve, add_zero]⟩, by simp [hyi, hvi]⟩, ?_⟩
          funext k; simp only [Pi.add_apply]; have := z2_add_self (v k); linear_combination this
      have hdisj : Disjoint (Podd.filter (fun x => x i ≠ 0)) (Podd.filter (fun x => x i = 0)) := by
        rw [Finset.disjoint_filter]; intro x _ h1 h2; exact h1 h2
      have hun : Podd.filter (fun x => x i ≠ 0) ∪ Podd.filter (fun x => x i = 0) = Podd := by
        ext x; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      have htot := Finset.card_union_of_disjoint hdisj
      rw [hun, ← hbij, hPodd_card] at htot
      omega
    · have hv1 : parityL (3 * t) v = 1 := (F_cases _).resolve_left hve
      by_cases hall1 : ∀ x ∈ Podd, x i ≠ 0
      · have : Podd.filter (fun x => x i ≠ 0) = Podd := Finset.filter_true_of_mem hall1
        rw [this, hPodd_card]; decide
      · push Not at hall1
        obtain ⟨x1, hx1O, hx1i⟩ := hall1
        obtain ⟨hx1P, hx1_1⟩ := (Finset.mem_filter.mp hx1O).2
        let w := v + x1
        have hwP : w ∈ P := P.add_mem hvP hx1P
        have hwe : parityL (3 * t) w = 0 := by rw [map_add, hv1, hx1_1]; decide
        have hwi : w i ≠ 0 := by simp [w, hx1i, hvi]
        have hbij : (Podd.filter (fun x => x i ≠ 0)).card = (Podd.filter (fun x => x i = 0)).card := by
          refine Finset.card_bij (fun x _ => x + w) ?_ ?_ ?_
          · intro x hx
            obtain ⟨hxO, hxi⟩ := Finset.mem_filter.mp hx
            obtain ⟨hxP, hx1⟩ := (Finset.mem_filter.mp hxO).2
            have h1 : x i = 1 := (F_cases _).resolve_left hxi
            have h2 : w i = 1 := (F_cases _).resolve_left hwi
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              P.add_mem hxP hwP, by rw [map_add, hx1, hwe, add_zero]⟩, by simp [h1, h2, z2_add_self]⟩
          · intro a _ b _ hab
            funext k; have := congrFun hab k; simp only [Pi.add_apply] at this; linear_combination this
          · intro y hy
            obtain ⟨hyO, hyi⟩ := Finset.mem_filter.mp hy
            obtain ⟨hyP, hy1⟩ := (Finset.mem_filter.mp hyO).2
            refine ⟨y + w, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              P.add_mem hyP hwP, by rw [map_add, hy1, hwe, add_zero]⟩, by simp [hyi, hwi]⟩, ?_⟩
            funext k; simp only [Pi.add_apply]; have := z2_add_self (w k); linear_combination this
        have hdisj : Disjoint (Podd.filter (fun x => x i ≠ 0)) (Podd.filter (fun x => x i = 0)) := by
          rw [Finset.disjoint_filter]; intro x _ h1 h2; exact h1 h2
        have hun : Podd.filter (fun x => x i ≠ 0) ∪ Podd.filter (fun x => x i = 0) = Podd := by
          ext x; simp only [Finset.mem_union, Finset.mem_filter]; tauto
        have htot := Finset.card_union_of_disjoint hdisj
        rw [hun, ← hbij, hPodd_card] at htot
        omega
  have h8le : 8 * (supp P).card ≤ 48 := by
    calc 8 * (supp P).card = ∑ _i ∈ supp P, 8 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ supp P, (Podd.filter (fun x => x i ≠ 0)).card := Finset.sum_le_sum hge8
      _ ≤ ∑ i : Fin (3 * t), (Podd.filter (fun x => x i ≠ 0)).card :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = 48 := by rw [← hswap, hsum_wt]
  have hnmono : ¬ mono (supp P) := by
    intro hm
    obtain ⟨j, hrun⟩ := hr0_run
    have hj : j ∈ supp P := (mem_supp P j).mpr ⟨r0, hr0P, (hrun j).mpr (Or.inl rfl)⟩
    have hnx : nx ht j ∈ supp P := (mem_supp P (nx ht j)).mpr ⟨r0, hr0P, (hrun (nx ht j)).mpr (Or.inr (Or.inl rfl))⟩
    exact nx_color ht j (hm (nx ht j) hnx j hj)
  have hloss : Module.finrank F P + Module.finrank F (checkOn (supp P)).range ≤ (supp P).card :=
    suppLoss P hP
  have hne : (supp P).Nonempty := Finset.card_pos.mp (by omega)
  have hr2 := (oneOrTwo (supp P) hne).2 hnmono
  omega

open Classical in
lemma shape_card_dim3_le_six {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    (H : Submodule F (Lane t)) (hH : H ≤ codeSub t) (hdim : Module.finrank F H = 3) :
    shapeCnt ht H ≤ 6 := by
  rw [shapeCnt_eq_add]
  by_cases hodd : ∃ x0 ∈ H, parityL (3 * t) x0 = 1
  · obtain ⟨x0, hx0, hpar⟩ := hodd
    let He := H ⊓ LinearMap.ker (parityL (3 * t))
    obtain ⟨hHedim, _⟩ := odd_coset_iff H x0 hx0 hpar
    have hHe2 : Module.finrank F He = 2 := by
      change Module.finrank F (↥(H ⊓ LinearMap.ker (parityL (3 * t)))) = 2; omega
    have hpair_eq : pairCnt H = pairCnt He := by
      unfold pairCnt; congr 1; ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, He, Submodule.mem_inf, LinearMap.mem_ker]
      exact ⟨fun ⟨hxH, hp⟩ => ⟨⟨hxH, parityL_pair hp⟩, hp⟩, fun ⟨⟨hxH, _⟩, hp⟩ => ⟨hxH, hp⟩⟩
    obtain ⟨cs, hcs_prop, _, hrank, hcount, _, _⟩ := pair_clique_decomp He (inf_le_left.trans hH)
    have h2pair : 2 * pairCnt He ≤ 6 := by
      change 2 * (Finset.univ.filter (fun x : Lane t => x ∈ He ∧ isPair x)).card ≤ 6
      rw [hcount, Finset.mul_sum]
      have hterm : ∀ C ∈ cs, 2 * (C.card * (C.card - 1) / 2) ≤ 3 * (C.card - 1) := by
        intro C hC
        have hC2 := (hcs_prop C hC).1
        have hCle : C.card - 1 ≤ ∑ D ∈ cs, (D.card - 1) :=
          Finset.single_le_sum (f := fun D : Finset (Fin (3 * t)) => D.card - 1) (fun _ _ => Nat.zero_le _) hC
        have hC3 : C.card ≤ 3 := by omega
        have heven : 2 ∣ C.card * (C.card - 1) := by
          rcases Nat.even_or_odd C.card with ⟨m, hm⟩ | ⟨m, hm⟩
          · exact ⟨m * (C.card - 1), by rw [hm]; ring⟩
          · exact ⟨C.card * m, by rw [show C.card - 1 = 2 * m by omega]; ring⟩
        rw [Nat.mul_div_cancel' heven]
        exact Nat.mul_le_mul_right _ hC3
      calc ∑ C ∈ cs, 2 * (C.card * (C.card - 1) / 2)
          ≤ ∑ C ∈ cs, 3 * (C.card - 1) := Finset.sum_le_sum hterm
        _ = 3 * ∑ C ∈ cs, (C.card - 1) := (Finset.mul_sum _ _ _).symm
        _ ≤ 3 * Module.finrank F He := Nat.mul_le_mul_left 3 hrank
        _ = 6 := by omega
    have hRle : run3Cnt ht H ≤ 3 := by
      have h1 := run3_card_le_of_lt ht ht3 H (by omega)
      have h2 : run3Cnt ht H = (Finset.univ.filter (fun x : Lane t => x ∈ H ∧ isRun3 ht x)).card := by
        unfold run3Cnt; congr 1
      omega
    omega
  · push Not at hodd
    have hR0 : run3Cnt ht H = 0 := by
      unfold run3Cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ ⟨hxH, hr⟩
      exact hodd x hxH (parityL_run3 ht hr)
    obtain ⟨cs, hcs_prop, _, hrank, hcount, _, _⟩ := pair_clique_decomp H hH
    have h2pair : 2 * pairCnt H ≤ 12 := by
      change 2 * (Finset.univ.filter (fun x : Lane t => x ∈ H ∧ isPair x)).card ≤ 12
      rw [hcount, Finset.mul_sum]
      have hterm : ∀ C ∈ cs, 2 * (C.card * (C.card - 1) / 2) ≤ 4 * (C.card - 1) := by
        intro C hC
        have hC2 := (hcs_prop C hC).1
        have hCle : C.card - 1 ≤ ∑ D ∈ cs, (D.card - 1) :=
          Finset.single_le_sum (f := fun D : Finset (Fin (3 * t)) => D.card - 1) (fun _ _ => Nat.zero_le _) hC
        have hC4 : C.card ≤ 4 := by omega
        have heven : 2 ∣ C.card * (C.card - 1) := by
          rcases Nat.even_or_odd C.card with ⟨m, hm⟩ | ⟨m, hm⟩
          · exact ⟨m * (C.card - 1), by rw [hm]; ring⟩
          · exact ⟨C.card * m, by rw [show C.card - 1 = 2 * m by omega]; ring⟩
        rw [Nat.mul_div_cancel' heven]
        exact Nat.mul_le_mul_right _ hC4
      calc ∑ C ∈ cs, 2 * (C.card * (C.card - 1) / 2)
          ≤ ∑ C ∈ cs, 4 * (C.card - 1) := Finset.sum_le_sum hterm
        _ = 4 * ∑ C ∈ cs, (C.card - 1) := (Finset.mul_sum _ _ _).symm
        _ ≤ 4 * Module.finrank F H := Nat.mul_le_mul_left 4 hrank
        _ = 12 := by omega
    omega

lemma mono_even_wt_of_codeSub {t : ℕ} (w : Lane t) (hc : w ∈ codeSub t)
    (a : ℕ) (hmono : ∀ i : Fin (3 * t), w i ≠ 0 → i.val % 3 = a) : Even (wt w) := by
  classical
  have hchk := support_checks_code w hc
  obtain ⟨e, hene⟩ := column_nonzero ⟨a % 3, Nat.mod_lt _ (by decide)⟩
  have he0 := hchk e
  have hconst : ∀ i ∈ Finset.univ.filter (fun i : Fin (3 * t) => w i ≠ 0),
      parityCol e (colour i) = parityCol e ⟨a % 3, Nat.mod_lt _ (by decide)⟩ := by
    intro i hi
    have hm := hmono i (Finset.mem_filter.mp hi).2
    refine congrArg (parityCol e) (Fin.ext ?_)
    dsimp only [colour]; omega
  rw [Finset.sum_congr rfl hconst, Finset.sum_const,
    show (Finset.univ.filter (fun i : Fin (3 * t) => w i ≠ 0)).card = wt w from rfl,
    nsmul_eq_mul] at he0
  have h1 : parityCol e ⟨a % 3, Nat.mod_lt _ (by decide)⟩ = 1 := (F_cases _).resolve_left hene
  rw [h1, mul_one] at he0
  exact even_iff_two_dvd.mpr ((ZMod.natCast_eq_zero_iff (wt w) 2).mp he0)

lemma mono_of_Ra_eq_Nb {t : ℕ} (ht : 0 < t) (w : Lane t) (R : Finset (Fin (3 * t)))
    (hR : R = R0 t ∨ R = R1 t ∨ R = R2 t) (hReq : R = Nb ht w) :
    ∃ a : ℕ, a < 3 ∧ ∀ i : Fin (3 * t), w i ≠ 0 → i.val % 3 = a := by
  have hmono : ∀ i : Fin (3 * t), w i ≠ 0 →
      (R = R0 t → i.val % 3 = 0) ∧ (R = R1 t → i.val % 3 = 2) ∧ (R = R2 t → i.val % 3 = 1) := by
    intro i hi
    have hin1 : i ∈ Nb ht w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hi⟩
    have hin2 : pv ht i ∈ Nb ht w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by rwa [nx_pv])⟩
    rw [← hReq] at hin1 hin2
    have hilt := i.isLt
    have hpv := pv_val ht i
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> subst h
    · simp only [R0, Finset.mem_filter, Finset.mem_univ, true_and] at hin1 hin2
      by_cases hi0 : i.val = 0 <;> simp only [hpv, hi0, ↓reduceIte] at hin2 <;> omega
    · simp only [R1, Finset.mem_filter, Finset.mem_univ, true_and] at hin1 hin2
      by_cases hi0 : i.val = 0 <;> simp only [hpv, hi0, ↓reduceIte] at hin2 <;> omega
    · simp only [R2, Finset.mem_filter, Finset.mem_univ, true_and] at hin1 hin2
      by_cases hi0 : i.val = 0 <;> simp only [hpv, hi0, ↓reduceIte] at hin2 <;> omega
  rcases hR with h | h | h
  · exact ⟨0, by decide, fun i hi => (hmono i hi).1 h⟩
  · exact ⟨2, by decide, fun i hi => (hmono i hi).2.1 h⟩
  · exact ⟨1, by decide, fun i hi => (hmono i hi).2.2 h⟩

lemma t4_mod3_card (a : ℕ) (ha : a < 3) :
    (Finset.univ.filter (fun i : Fin 12 => i.val % 3 = a)).card = 4 := by
  rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2) with rfl | rfl | rfl <;> decide

lemma card_Ra_eq (t : ℕ) (R : Finset (Fin (3 * t)))
    (hR : R = R0 t ∨ R = R1 t ∨ R = R2 t) : R.card = 2 * t := by
  rcases hR with rfl | rfl | rfl
  · have heq : R0 t = Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 ≠ (1 : Fin 3).val) := by
      ext j; simp only [R0, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_one]; omega
    rw [heq]; exact card_filter_mod3_ne t 1
  · have heq : R1 t = Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 ≠ (0 : Fin 3).val) := by
      ext j; simp only [R1, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero]; omega
    rw [heq]; exact card_filter_mod3_ne t 0
  · have heq : R2 t = Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 ≠ (2 : Fin 3).val) := by
      ext j; simp only [R2, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [heq]; exact card_filter_mod3_ne t 2

open Classical in
set_option maxHeartbeats 800000 in
lemma rect_case_3A {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    (P Q : Submodule F (Lane t)) (hP : P ≤ codeSub t) (hQ : Q ≤ codeSub t)
    (hP3 : Module.finrank F P = 3) (hsum : Module.finrank F P + Module.finrank F Q = 3 * t + 1) :
    2048 * rectHits ht P Q ≤ numVal t * (Nat.card P * Nat.card Q) := by
  have hCdim := codeSub_finrank ht
  have hQeq : Q = codeSub t := Submodule.eq_of_le_of_finrank_eq hQ (by omega)
  subst hQeq
  have hPcard : Nat.card P = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := P), Nat.card_eq_fintype_card, ZMod.card, hP3]; decide
  have hQcard : Nat.card (codeSub t) = cntS t ∅ := card_codeSub
  by_cases hsep : isSep ht P
  · by_cases ht3eq : t = 3
    · exact absurd hsep (not_isSep_of_small ht P hP (Or.inl ⟨ht3eq, by omega⟩))
    · rw [rectHits_codeSub_eq ht, hPcard, hQcard]
      have hterm : ∀ p ∈ Finset.univ.filter (fun p : Lane t => p ∈ P),
          (cntS t (Nb ht p) : ℚ) = (cntS t ∅ : ℚ) * ((1 / 4 : ℚ) ^ wt p * cval t (Nb ht p)) := by
        intro p hp
        have hpP : p ∈ P := (Finset.mem_filter.mp hp).2
        rw [cntS_ratio ht, card_Nb ht p (hsep p hpP), pow_mul]
        norm_num
      have hsumQ : (∑ p ∈ Finset.univ.filter (fun p : Lane t => p ∈ P), (cntS t (Nb ht p) : ℚ)) =
          (cntS t ∅ : ℚ) * ∑ p ∈ Finset.univ.filter (fun p : Lane t => p ∈ P),
            (1 / 4 : ℚ) ^ wt p * cval t (Nb ht p) := by
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      by_cases ht4 : t = 4
      · subst ht4
        have hmain : (∑ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P), (1 / 4 : ℚ) ^ wt p) ≤ 353 / 256 := by
          have h := mainQ_le 3 (Fin 12) P (fun _ => 1) hP3 (by simp)
            (fun p hp => no_wt_one ((codeSub_iff_codeF p).mp (hP hp)))
            (fun _ => by norm_num) (fun _ _ => rfl)
          have hB : Bfun 3 = 353 / 256 := by unfold Bfun; norm_num
          rw [hB] at h
          refine le_trans (le_of_eq ?_) h
          refine Finset.sum_congr (by ext p; simp) fun p _ => by ring
        have hexcess : ∑ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P),
            (1 / 4 : ℚ) ^ wt p * (cval 4 (Nb ht p) - 1) ≤ 1 / 256 := by
          have hsupp6 : (supp P).card ≤ 6 := by have := card_supp_le_of_isSep ht P hsep; omega
          have hwt_le6 : ∀ p ∈ P, wt p ≤ 6 := fun p hp => by
            have hsub : Finset.univ.filter (fun i => p i ≠ 0) ⊆ supp P :=
              fun i hi => (mem_supp P i).mpr ⟨p, hp, (Finset.mem_filter.mp hi).2⟩
            exact (Finset.card_le_card hsub).trans hsupp6
          have hcval_eq1 : ∀ p ∈ P, wt p ≤ 3 → cval 4 (Nb ht p) = 1 := fun p hp hw =>
            cval_one (by rw [card_Nb ht p (hsep p hp)]; omega)
          by_cases h4 : ∃ p0 ∈ P, wt p0 = 4 ∧ 1 < cval 4 (Nb ht p0)
          · obtain ⟨p0, hp0P, hwt0, hcgt⟩ := h4
            have hnb8 : (Nb ht p0).card = 8 := by rw [card_Nb ht p0 (hsep p0 hp0P), hwt0]
            have hRsub : R0 4 ⊆ Nb ht p0 ∨ R1 4 ⊆ Nb ht p0 ∨ R2 4 ⊆ Nb ht p0 := by
              by_contra hnot; push Not at hnot
              have : cval 4 (Nb ht p0) = 1 := by unfold cval cvalNat; simp [hnot.1, hnot.2.1, hnot.2.2]
              linarith
            have hmono0 : ∃ a : ℕ, a < 3 ∧ ∀ i : Fin 12, p0 i ≠ 0 → i.val % 3 = a := by
              rcases hRsub with h | h | h
              · exact mono_of_Ra_eq_Nb ht p0 (R0 4) (Or.inl rfl)
                  (Finset.eq_of_subset_of_card_le h (by rw [hnb8, card_Ra_eq 4 _ (Or.inl rfl)]))
              · exact mono_of_Ra_eq_Nb ht p0 (R1 4) (Or.inr (Or.inl rfl))
                  (Finset.eq_of_subset_of_card_le h (by rw [hnb8, card_Ra_eq 4 _ (Or.inr (Or.inl rfl))]))
              · exact mono_of_Ra_eq_Nb ht p0 (R2 4) (Or.inr (Or.inr rfl))
                  (Finset.eq_of_subset_of_card_le h (by rw [hnb8, card_Ra_eq 4 _ (Or.inr (Or.inr rfl))]))
            obtain ⟨a, ha3, hma⟩ := hmono0
            have hfull : ∀ i : Fin 12, i.val % 3 = a → p0 i ≠ 0 := by
              have hsub : Finset.univ.filter (fun i : Fin 12 => p0 i ≠ 0) ⊆
                  Finset.univ.filter (fun i : Fin 12 => i.val % 3 = a) :=
                fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hma i (Finset.mem_filter.mp hi).2⟩
              have hc4 : (Finset.univ.filter (fun i : Fin 12 => i.val % 3 = a)).card = 4 := by
                convert t4_mod3_card a ha3
              have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc4]; exact hwt0.ge)
              intro i hi
              have hm : i ∈ Finset.univ.filter (fun i : Fin 12 => p0 i ≠ 0) := by
                rw [heq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
              exact (Finset.mem_filter.mp hm).2
            have hsupp_sub : ∀ i ∈ supp P, i.val % 3 = a := by
              intro i hi
              by_contra hne
              have hi12 := i.isLt
              have hnx_or_pv : (nx ht i).val % 3 = a ∨ (pv ht i).val % 3 = a := by
                rw [nx_val, pv_val]; split_ifs <;> omega
              rcases hnx_or_pv with hnx | hpv
              · exact (isSep_iff_supp ht P).mp hsep i hi
                  ((mem_supp P _).mpr ⟨p0, hp0P, hfull _ hnx⟩)
              · exact (isSep_iff_supp ht P).mp hsep (pv ht i)
                  ((mem_supp P _).mpr ⟨p0, hp0P, hfull _ hpv⟩) (by rwa [nx_pv])
            have honly : ∀ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P), p ≠ p0 →
                (1 / 4 : ℚ) ^ wt p * (cval 4 (Nb ht p) - 1) = 0 := by
              intro p hp hne
              have hpP : p ∈ P := (Finset.mem_filter.mp hp).2
              have hsub : Finset.univ.filter (fun i : Fin 12 => p i ≠ 0) ⊆
                  Finset.univ.filter (fun i : Fin 12 => p0 i ≠ 0) :=
                fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                  hfull i (hsupp_sub i ((mem_supp P i).mpr ⟨p, hpP, (Finset.mem_filter.mp hi).2⟩))⟩
              have hlt : wt p < 4 := by
                by_contra hge; push Not at hge
                have heq := Finset.eq_of_subset_of_card_le hsub (by change wt p0 ≤ wt p; omega)
                apply hne; funext i
                have hiff : p i ≠ 0 ↔ p0 i ≠ 0 := by
                  have := Finset.ext_iff.mp heq i; simpa using this
                rcases F_cases (p i) with h1 | h1 <;> rcases F_cases (p0 i) with h2 | h2
                · rw [h1, h2]
                · exfalso; exact absurd (hiff.mpr (by simp [h2])) (by simp [h1])
                · exfalso; exact absurd (hiff.mp (by simp [h1])) (by simp [h2])
                · rw [h1, h2]
              rw [hcval_eq1 p hpP (by omega), sub_self, mul_zero]
            rw [Finset.sum_eq_single p0 (fun p hp hne => honly p hp hne)
              (fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0P⟩) h)]
            have hc2 : cval 4 (Nb ht p0) ≤ 2 := cval_le_two_of_lt (by omega)
            rw [hwt0]; linarith
          · push Not at h4
            by_cases h6 : ∃ p0 ∈ P, wt p0 = 6
            · obtain ⟨p0, hp0P, hwt0⟩ := h6
              have hsupp_eq : supp P = Finset.univ.filter (fun i : Fin 12 => p0 i ≠ 0) := by
                symm
                apply Finset.eq_of_subset_of_card_le
                · intro i hi
                  exact (mem_supp P i).mpr ⟨p0, hp0P, (Finset.mem_filter.mp hi).2⟩
                · change (supp P).card ≤ wt p0; omega
              have honly : ∀ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P), p ≠ p0 →
                  (1 / 4 : ℚ) ^ wt p * (cval 4 (Nb ht p) - 1) = 0 := by
                intro p hp hne
                have hpP : p ∈ P := (Finset.mem_filter.mp hp).2
                have hsub : Finset.univ.filter (fun i : Fin 12 => p i ≠ 0) ⊆
                    Finset.univ.filter (fun i : Fin 12 => p0 i ≠ 0) := by
                  rw [← hsupp_eq]; intro i hi; exact (mem_supp P i).mpr ⟨p, hpP, (Finset.mem_filter.mp hi).2⟩
                have hne6 : wt p ≠ 6 := by
                  intro hw6
                  have heq := Finset.eq_of_subset_of_card_le hsub (by change wt p0 ≤ wt p; omega)
                  apply hne; funext i
                  have hiff : p i ≠ 0 ↔ p0 i ≠ 0 := by have := Finset.ext_iff.mp heq i; simpa using this
                  rcases F_cases (p i) with h1 | h1 <;> rcases F_cases (p0 i) with h2 | h2
                  · rw [h1, h2]
                  · exfalso; exact absurd (hiff.mpr (by simp [h2])) (by simp [h1])
                  · exfalso; exact absurd (hiff.mp (by simp [h1])) (by simp [h2])
                  · rw [h1, h2]
                have hne5 : wt p ≠ 5 := by
                  intro hw5
                  have hdiff : Finset.univ.filter (fun i : Fin 12 => (p0 + p) i ≠ 0) =
                      Finset.univ.filter (fun i : Fin 12 => p0 i ≠ 0) \
                      Finset.univ.filter (fun i : Fin 12 => p i ≠ 0) := by
                    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Pi.add_apply]
                    constructor
                    · intro hne'
                      by_cases hp0i : p0 i = 0
                      · exfalso
                        have hpi : p i ≠ 0 := by simp [hp0i] at hne'; exact hne'
                        have := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi⟩)
                        exact (Finset.mem_filter.mp this).2 hp0i
                      · refine ⟨hp0i, fun hpi => ?_⟩
                        have h1 := (F_cases _).resolve_left hp0i
                        have h2 := (F_cases _).resolve_left hpi
                        exact hne' (by simp [h1, h2, z2_add_self])
                    · rintro ⟨h1, h2⟩; push Not at h2; simp [h2, h1]
                  have hwt1 : wt (p0 + p) = 1 := by
                    unfold wt; rw [hdiff, Finset.card_sdiff_of_subset hsub]
                    change wt p0 - wt p = 1; omega
                  exact no_wt_one ((codeSub_iff_codeF _).mp (hP (P.add_mem hp0P hpP))) hwt1
                have hwle4 : wt p ≤ 4 := by have := hwt_le6 p hpP; omega
                by_cases hw4 : wt p = 4
                · have hle1 := h4 p hpP hw4
                  have hge1 : 1 ≤ cval 4 (Nb ht p) := by unfold cval cvalNat; split_ifs <;> norm_num
                  have : cval 4 (Nb ht p) = 1 := le_antisymm hle1 hge1
                  rw [this, sub_self, mul_zero]
                · rw [hcval_eq1 p hpP (by omega), sub_self, mul_zero]
              rw [Finset.sum_eq_single p0 (fun p hp hne => honly p hp hne)
                (fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0P⟩) h)]
              have hc4 := cval_le 4 (Nb ht p0)
              rw [hwt0]; linarith
            · push Not at h6
              have hterm_le : ∀ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P),
                  (1 / 4 : ℚ) ^ wt p * (cval 4 (Nb ht p) - 1) ≤
                  if parityL 12 p = 1 then (1 / 1024 : ℚ) else 0 := by
                intro p hp
                have hpP : p ∈ P := (Finset.mem_filter.mp hp).2
                have hwle5 : wt p ≤ 5 := by have := hwt_le6 p hpP; have := h6 p hpP; omega
                by_cases hw5 : wt p = 5
                · have hpar1 : parityL 12 p = 1 := by rw [parityL_eq_wt, hw5]; decide
                  have hc2 : cval 4 (Nb ht p) ≤ 2 := cval_le_two_of_lt (by rw [card_Nb ht p (hsep p hpP), hw5]; decide)
                  simp only [hpar1, ↓reduceIte, hw5]; linarith
                · have hc1 : cval 4 (Nb ht p) = 1 := by
                    by_cases hw4 : wt p = 4
                    · have hle1 := h4 p hpP hw4
                      have hge1 : 1 ≤ cval 4 (Nb ht p) := by unfold cval cvalNat; split_ifs <;> norm_num
                      exact le_antisymm hle1 hge1
                    · exact hcval_eq1 p hpP (by omega)
                  rw [hc1, sub_self, mul_zero]
                  split_ifs <;> norm_num
              have hodd_le : (Finset.univ.filter (fun p : Lane 4 => p ∈ P ∧ parityL 12 p = 1)).card ≤ 4 := by
                by_cases hex : ∃ x0 ∈ P, parityL 12 x0 = 1
                · obtain ⟨x0, hx0, hpar⟩ := hex
                  obtain ⟨hPedim, hcoset⟩ := odd_coset_iff P x0 hx0 hpar
                  have hPedim' : Module.finrank F (↥(P ⊓ LinearMap.ker (parityL 12))) + 1 = Module.finrank F P := hPedim
                  have hc_eq : (Finset.univ.filter (fun p : Lane 4 => p ∈ P ∧ parityL 12 p = 1)).card =
                      (Finset.univ.filter (fun u : Lane 4 => u ∈ P ⊓ LinearMap.ker (parityL 12) ∧
                        parityL 12 (x0 + u) = 1)).card := by
                    convert hcoset (fun x => parityL 12 x = 1) (fun _ _ h => h)
                  rw [hc_eq]
                  have hsub : Finset.univ.filter (fun u : Lane 4 => u ∈ P ⊓ LinearMap.ker (parityL 12) ∧
                      parityL 12 (x0 + u) = 1) ⊆ Finset.univ.filter (fun u : Lane 4 => u ∈ P ⊓ LinearMap.ker (parityL 12)) :=
                    fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.1⟩
                  refine (Finset.card_le_card hsub).trans ?_
                  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
                    Module.natCard_eq_pow_finrank (K := F) (V := (P ⊓ LinearMap.ker (parityL 12) : Submodule F (Lane 4))),
                    Nat.card_eq_fintype_card, ZMod.card]
                  have : Module.finrank F (↥(P ⊓ LinearMap.ker (parityL 12))) = 2 := by omega
                  rw [this]; decide
                · push Not at hex
                  have : Finset.univ.filter (fun p : Lane 4 => p ∈ P ∧ parityL 12 p = 1) = ∅ := by
                    rw [Finset.filter_eq_empty_iff]; intro p _ ⟨hpP, h1⟩; exact hex p hpP h1
                  rw [this]; simp
              calc ∑ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P),
                      (1 / 4 : ℚ) ^ wt p * (cval 4 (Nb ht p) - 1)
                  ≤ ∑ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P),
                      (if parityL 12 p = 1 then (1 / 1024 : ℚ) else 0) := Finset.sum_le_sum hterm_le
                _ = ((Finset.univ.filter (fun p : Lane 4 => p ∈ P ∧ parityL 12 p = 1)).card : ℚ) * (1 / 1024) := by
                    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
                    refine congrArg (fun n : ℕ => (n : ℚ) * (1 / 1024)) (congrArg Finset.card ?_)
                    ext p; simp
                _ ≤ 4 * (1 / 1024 : ℚ) := by
                    have : ((Finset.univ.filter (fun p : Lane 4 => p ∈ P ∧ parityL 12 p = 1)).card : ℚ) ≤ 4 := by
                      exact_mod_cast hodd_le
                    linarith
                _ = 1 / 256 := by norm_num
        have htot : ∑ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P),
            (1 / 4 : ℚ) ^ wt p * cval 4 (Nb ht p) ≤ 354 / 256 := by
          have hadd : ∑ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P),
              (1 / 4 : ℚ) ^ wt p * cval 4 (Nb ht p) =
              (∑ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P), (1 / 4 : ℚ) ^ wt p) +
              (∑ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P),
                (1 / 4 : ℚ) ^ wt p * (cval 4 (Nb ht p) - 1)) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ => by ring
          linarith
        have hq : (2048 : ℚ) * (∑ p ∈ Finset.univ.filter (fun p : Lane 4 => p ∈ P), (cntS 4 (Nb ht p) : ℚ)) ≤
            354 * (8 * (cntS 4 ∅ : ℚ)) := by
          rw [hsumQ]
          have hpos : (0 : ℚ) ≤ cntS 4 ∅ := Nat.cast_nonneg _
          have hmul := mul_le_mul_of_nonneg_left htot hpos
          linarith
        have hnum : numVal 4 = 354 := by decide
        rw [hnum]
        exact_mod_cast hq
      · have ht5 : 5 ≤ t := by omega
        let cfun : Lane t → ℚ := fun p => if p ∈ P then cval t (Nb ht p) else 1
        have hcfun4 : ∀ p, cfun p ≤ 4 := fun p => by dsimp [cfun]; split_ifs; exact cval_le t _; norm_num
        have hcfun1 : ∀ p, wt p ≤ 5 → cfun p = 1 := by
          intro p hwp
          dsimp [cfun]
          split_ifs with hpP
          · by_cases hlt : 2 * wt p < 2 * t
            · exact cval_one (by rw [card_Nb ht p (hsep p hpP)]; exact hlt)
            · have ht5eq : t = 5 := by omega
              have hwp5 : wt p = 5 := by omega
              subst ht5eq
              have hnb10 : (Nb ht p).card = 10 := by rw [card_Nb ht p (hsep p hpP), hwp5]
              have hnotR : ∀ R : Finset (Fin 15), R = R0 5 ∨ R = R1 5 ∨ R = R2 5 → ¬ R ⊆ Nb ht p := by
                intro R hR hsub
                have hR10 : R.card = 10 := card_Ra_eq 5 R hR
                have hReq : R = Nb ht p := Finset.eq_of_subset_of_card_le hsub (by omega)
                obtain ⟨a, _, hma⟩ := mono_of_Ra_eq_Nb ht p R hR hReq
                have hev := mono_even_wt_of_codeSub p (hP hpP) a hma
                rw [hwp5] at hev
                exact absurd hev (by decide)
              unfold cval cvalNat
              simp [hnotR (R0 5) (Or.inl rfl), hnotR (R1 5) (Or.inr (Or.inl rfl)),
                hnotR (R2 5) (Or.inr (Or.inr rfl))]
          · rfl
        have hmain := mainQ_le 3 (Fin (3 * t)) P cfun hP3 (by simp; omega)
          (fun p hp => no_wt_one ((codeSub_iff_codeF p).mp (hP hp))) hcfun4 hcfun1
        have hB : Bfun 3 = 353 / 256 := by unfold Bfun; norm_num
        have hcongr : ∑ p ∈ Finset.univ.filter (fun p : Lane t => p ∈ P),
            (1 / 4 : ℚ) ^ wt p * cval t (Nb ht p) =
            ∑ p ∈ Finset.univ.filter (fun p : Lane t => p ∈ P), (1 / 4 : ℚ) ^ wt p * cfun p :=
          Finset.sum_congr rfl fun p hp => by simp [cfun, (Finset.mem_filter.mp hp).2]
        rw [hcongr] at hsumQ
        have hq : (2048 : ℚ) * (∑ p ∈ Finset.univ.filter (fun p : Lane t => p ∈ P), (cntS t (Nb ht p) : ℚ)) ≤
            353 * (8 * (cntS t ∅ : ℚ)) := by
          rw [hsumQ]
          have hpos : (0 : ℚ) ≤ cntS t ∅ := Nat.cast_nonneg _
          rw [hB] at hmain
          have hmain' : ∑ p ∈ Finset.univ.filter (fun p : Lane t => p ∈ P), (1 / 4 : ℚ) ^ wt p * cfun p ≤ 353 / 256 := by
            refine le_trans (le_of_eq ?_) hmain
            refine Finset.sum_congr (by ext p; simp) fun _ _ => rfl
          have hmul := mul_le_mul_of_nonneg_left hmain' hpos
          linarith
        have hnum : numVal t = 353 := by unfold numVal; split_ifs <;> omega
        rw [hnum]
        exact_mod_cast hq
  · have h3ST : 3 * shapeCnt ht P + nb5Cnt ht P ≤ 16 := by
      rw [shapeCnt_eq_add]
      by_cases hodd : ∃ x0 ∈ P, parityL (3 * t) x0 = 1
      · obtain ⟨x0, hx0, hpar⟩ := hodd
        let Pe := P ⊓ LinearMap.ker (parityL (3 * t))
        obtain ⟨hPedim, hcoset⟩ := odd_coset_iff P x0 hx0 hpar
        have hPe2 : Module.finrank F Pe = 2 := by
          change Module.finrank F (↥(P ⊓ LinearMap.ker (parityL (3 * t)))) = 2; omega
        have hpair_eq : pairCnt P = pairCnt Pe := by
          unfold pairCnt; congr 1; ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pe, Submodule.mem_inf, LinearMap.mem_ker]
          exact ⟨fun ⟨hxP, hp⟩ => ⟨⟨hxP, parityL_pair hp⟩, hp⟩, fun ⟨⟨hxP, _⟩, hp⟩ => ⟨hxP, hp⟩⟩
        obtain ⟨cs, hcs_prop, _, hrank, hcount, hcs_pair, _⟩ := pair_clique_decomp Pe (inf_le_left.trans hP)
        have hPe_card : (Finset.univ.filter (fun u : Lane t => u ∈ Pe)).card = 4 := by
          rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
            Module.natCard_eq_pow_finrank (K := F) (V := Pe), Nat.card_eq_fintype_card, ZMod.card, hPe2]; decide
        by_cases hC3 : ∃ C ∈ cs, C.card = 3
        · obtain ⟨C, hC, hCcard⟩ := hC3
          have hSdim := cliqueSpan_finrank C (Finset.card_pos.mp (by omega))
          have hSle : cliqueSpan C ≤ Pe := cliqueSpan_le_of_pairs Pe C (hcs_pair C hC)
          have hSeq : cliqueSpan C = Pe := Submodule.eq_of_le_of_finrank_eq hSle (by omega)
          have hcs_sing : cs = {C} := by
            ext D; simp only [Finset.mem_singleton]
            constructor
            · intro hD
              by_contra hne
              have hsum2 : (C.card - 1) + (D.card - 1) ≤ ∑ X ∈ cs, (X.card - 1) := by
                have hsub : ({C, D} : Finset (Finset (Fin (3 * t)))) ⊆ cs := by
                  intro X hX; simp only [Finset.mem_insert, Finset.mem_singleton] at hX
                  rcases hX with rfl | rfl <;> assumption
                have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
                  (f := fun X : Finset (Fin (3 * t)) => X.card - 1) (fun _ _ _ => Nat.zero_le _)
                rw [Finset.sum_pair (Ne.symm hne)] at hs; exact hs
              have hD2 := (hcs_prop D hD).1
              omega
            · rintro rfl; exact hC
          have hpair3 : pairCnt P = 3 := by
            rw [hpair_eq]; unfold pairCnt; rw [hcount, hcs_sing, Finset.sum_singleton, hCcard]
          obtain ⟨hwt3_le, hrun_le⟩ := coset_wt3_run3_bound ht ht3 x0 (hP hx0) C (by omega)
            (hcs_prop C hC).2 (hSle.trans (inf_le_left.trans hP))
          have hwt3_eq : wt3Cnt P = (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ wt (x0 + u) = 3)).card := by
            unfold wt3Cnt; rw [hSeq]; convert hcoset (fun x => wt x = 3) (fun x _ h => by rw [parityL_eq_wt, h]; decide)
          have hrun_eq : run3Cnt ht P = (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ isRun3 ht (x0 + u))).card := by
            unfold run3Cnt; rw [hSeq]; convert hcoset (fun x => isRun3 ht x) (fun x _ h => parityL_run3 ht h)
          have hRT := run3_add_nb5_le_wt3 ht ht3 P hP
          omega
        · push Not at hC3
          have hpair_le2 : pairCnt P ≤ 2 := by
            rw [hpair_eq]; unfold pairCnt; rw [hcount]
            have hterm : ∀ C ∈ cs, C.card * (C.card - 1) / 2 ≤ C.card - 1 := by
              intro C hC
              have hC2 := (hcs_prop C hC).1
              have hCle : C.card - 1 ≤ ∑ D ∈ cs, (D.card - 1) :=
                Finset.single_le_sum (f := fun D : Finset (Fin (3 * t)) => D.card - 1) (fun _ _ => Nat.zero_le _) hC
              have hCne := hC3 C hC
              have hCeq2 : C.card = 2 := by omega
              rw [hCeq2]
            calc ∑ C ∈ cs, C.card * (C.card - 1) / 2 ≤ ∑ C ∈ cs, (C.card - 1) := Finset.sum_le_sum hterm
              _ ≤ Module.finrank F Pe := hrank
              _ = 2 := by omega
          have hR_le3 : run3Cnt ht P ≤ 3 := by
            have h1 := run3_card_le_of_lt ht ht3 P (by omega)
            have h2 : run3Cnt ht P = (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ isRun3 ht x)).card := by
              unfold run3Cnt; congr 1
            omega
          have hwt3_le4 : wt3Cnt P ≤ 4 := by
            have h1 : wt3Cnt P = (Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ wt (x0 + u) = 3)).card := by
              unfold wt3Cnt; convert hcoset (fun x => wt x = 3) (fun x _ h => by rw [parityL_eq_wt, h]; decide)
            rw [h1]
            calc (Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ wt (x0 + u) = 3)).card
                ≤ (Finset.univ.filter (fun u : Lane t => u ∈ Pe)).card :=
                  Finset.card_le_card (fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.1⟩)
              _ = 4 := hPe_card
          have hRT := run3_add_nb5_le_wt3 ht ht3 P hP
          omega
      · push Not at hodd
        have hR0 : run3Cnt ht P = 0 := by
          unfold run3Cnt; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x _ ⟨hxP, hr⟩; exact hodd x hxP (parityL_run3 ht hr)
        have hT0 : nb5Cnt ht P = 0 := by
          unfold nb5Cnt; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x _ ⟨hxP, h5⟩
          have hnz : x ≠ 0 := by
            intro hz; subst hz; have hemp : Nb ht (0 : Lane t) = ∅ := by ext i; simp [Nb]
            rw [hemp, Finset.card_empty] at h5; omega
          exact hodd x hxP (parityL_nb5 ht ht3 hnz (hP hxP) h5)
        obtain ⟨cs, hcs_prop, _, hrank, hcount, hcs_pair, _⟩ := pair_clique_decomp P hP
        have h2pair : 2 * pairCnt P ≤ 9 := by
          unfold pairCnt; rw [hcount, Finset.mul_sum]
          have hterm : ∀ C ∈ cs, 2 * (C.card * (C.card - 1) / 2) ≤ 3 * (C.card - 1) := by
            intro C hC
            have hC2 := (hcs_prop C hC).1
            have hC3 : C.card ≤ 3 := by
              have := clique_le_finrank_of_not_isSep ht P hsep C (Finset.card_pos.mp (by omega))
                (hcs_prop C hC).2 (hcs_pair C hC)
              omega
            have heven : 2 ∣ C.card * (C.card - 1) := by
              rcases Nat.even_or_odd C.card with ⟨m, hm⟩ | ⟨m, hm⟩
              · exact ⟨m * (C.card - 1), by rw [hm]; ring⟩
              · exact ⟨C.card * m, by rw [show C.card - 1 = 2 * m by omega]; ring⟩
            rw [Nat.mul_div_cancel' heven]
            exact Nat.mul_le_mul_right _ hC3
          calc ∑ C ∈ cs, 2 * (C.card * (C.card - 1) / 2)
              ≤ ∑ C ∈ cs, 3 * (C.card - 1) := Finset.sum_le_sum hterm
            _ = 3 * ∑ C ∈ cs, (C.card - 1) := (Finset.mul_sum _ _ _).symm
            _ ≤ 3 * Module.finrank F P := Nat.mul_le_mul_left 3 hrank
            _ = 9 := by omega
        omega
    have hm := hits_master_le ht ht3 P (codeSub t) hP (le_refl _)
    rw [hPcard, hQcard] at hm ⊢
    have hnum := numVal_ge_348 ht3
    have hpos : (0 : ℚ) ≤ cntS t ∅ := Nat.cast_nonneg _
    have h3STq : ((8 - 1 + 3 * shapeCnt ht P + nb5Cnt ht P : ℕ) : ℚ) ≤ 23 := by
      exact_mod_cast (show 8 - 1 + 3 * shapeCnt ht P + nb5Cnt ht P ≤ 23 by omega)
    have hq : (2048 : ℚ) * (rectHits ht P (codeSub t) : ℚ) ≤
        (numVal t : ℚ) * (8 * (cntS t ∅ : ℚ)) := by
      have hnumq : (348 : ℚ) ≤ (numVal t : ℚ) := by exact_mod_cast hnum
      nlinarith
    exact_mod_cast hq

open Classical in
lemma rect_case_3B {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    (P Q : Submodule F (Lane t)) (hP : P ≤ codeSub t) (hQ : Q ≤ codeSub t)
    (hP4 : Module.finrank F P = 4) (hsum : Module.finrank F P + Module.finrank F Q = 3 * t + 1) :
    2048 * rectHits ht P Q ≤ numVal t * (Nat.card P * Nat.card Q) := by
  let b := Module.finBasisOfFinrankEq F P hP4
  let ev : (Fin 4 → F) → (P →ₗ[F] F) := fun m =>
    { toFun := fun x => ∑ i : Fin 4, m i * b.repr x i
      map_add' := fun x y => by simp only [map_add, Finsupp.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  have hev_dim : ∀ m : Fin 4 → F, m ≠ 0 →
      Module.finrank F ((LinearMap.ker (ev m)).map P.subtype) = 3 := by
    intro m hm
    have hne : ev m ≠ 0 := by
      intro hz
      apply hm; funext i
      have h1 := LinearMap.congr_fun hz (b i)
      simp only [ev, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, Module.Basis.repr_self] at h1
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj.symm])
        (fun h => absurd (Finset.mem_univ i) h)] at h1
      simpa using h1
    have hsurj : LinearMap.range (ev m) = ⊤ := by
      obtain ⟨x, hx⟩ : ∃ x, ev m x ≠ 0 := by by_contra h; push Not at h; exact hne (LinearMap.ext h)
      rw [eq_top_iff]; intro a _
      rcases F_cases a with rfl | rfl
      · exact ⟨0, map_zero _⟩
      · exact ⟨x, (F_cases _).resolve_left hx⟩
    have h1 := LinearMap.finrank_range_add_finrank_ker (ev m)
    rw [hsurj, finrank_top, Module.finrank_self, hP4, ← Submodule.finrank_map_subtype_eq P (LinearMap.ker (ev m))] at h1
    omega
  have hcount_m : ∀ x : P, x ≠ 0 →
      (Finset.univ.filter (fun m : Fin 4 → F => m ≠ 0 ∧ ev m x = 0)).card = 7 := by
    intro x hx
    have hne : ∃ i0 : Fin 4, b.repr x i0 ≠ 0 := by
      by_contra h; push Not at h
      apply hx; apply b.repr.injective; ext i; simpa using h i
    obtain ⟨i0, hi0⟩ := hne
    have hbi : (Finset.univ.filter (fun m : Fin 4 → F => ev m x = 0)).card = 8 := by
      have h1 : (Finset.univ.filter (fun m : Fin 4 → F => ev m x = 0)).card =
          (Finset.univ : Finset ({i : Fin 4 // i ≠ i0} → F)).card := by
        refine Finset.card_bij (fun m _ i => m i.1) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro m1 hm1 m2 hm2 heq
          have h10 := (Finset.mem_filter.mp hm1).2
          have h20 := (Finset.mem_filter.mp hm2).2
          have hother : ∀ i : Fin 4, i ≠ i0 → m1 i = m2 i := fun i hi => congrFun heq ⟨i, hi⟩
          funext i
          by_cases hi : i = i0
          · subst hi
            have hs1 : ∑ j ∈ Finset.univ.erase i, m1 j * b.repr x j =
                ∑ j ∈ Finset.univ.erase i, m2 j * b.repr x j :=
              Finset.sum_congr rfl fun j hj => by rw [hother j (Finset.mem_erase.mp hj).1]
            simp only [ev, LinearMap.coe_mk, AddHom.coe_mk] at h10 h20
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at h10 h20
            have hb1 : b.repr x i = 1 := (F_cases _).resolve_left hi0
            rw [hb1, mul_one] at h10 h20
            rw [hs1] at h10
            have hz := z2_add_self (∑ j ∈ Finset.univ.erase i, m2 j * b.repr x j)
            linear_combination h10 - h20
          · exact hother i hi
        · intro g _
          let m' : Fin 4 → F := fun i =>
            if hi : i = i0 then ∑ j : {j : Fin 4 // j ≠ i0}, g j * b.repr x j.1 else g ⟨i, hi⟩
          refine ⟨m', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · simp only [ev, LinearMap.coe_mk, AddHom.coe_mk]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
            have hb1 : b.repr x i0 = 1 := (F_cases _).resolve_left hi0
            have hm0 : m' i0 = ∑ j : {j : Fin 4 // j ≠ i0}, g j * b.repr x j.1 := by simp [m']
            have hrest : ∑ j ∈ Finset.univ.erase i0, m' j * b.repr x j =
                ∑ j : {j : Fin 4 // j ≠ i0}, g j * b.repr x j.1 := by
              rw [← Finset.sum_coe_sort (Finset.univ.erase i0)]
              refine Finset.sum_bij (fun j _ => ⟨j.1, (Finset.mem_erase.mp j.2).1⟩)
                (fun _ _ => Finset.mem_univ _)
                (fun a _ b _ h => Subtype.ext (congrArg (Subtype.val : {j : Fin 4 // j ≠ i0} → Fin 4) h))
                (fun j _ => ⟨⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩⟩, Finset.mem_univ _, rfl⟩)
                (fun j _ => by simp [m', (Finset.mem_erase.mp j.2).1])
            rw [hm0, hb1, mul_one, hrest, z2_add_self]
          · funext j; simp [m', j.2]
      rw [h1, Finset.card_univ, Fintype.card_fun, ZMod.card]
      have hc3 : Fintype.card {i : Fin 4 // i ≠ i0} = 3 := by
        rw [Fintype.card_subtype]
        have : Finset.univ.filter (fun i : Fin 4 => i ≠ i0) = Finset.univ.erase i0 := by ext i; simp
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ i0)]; decide
      rw [hc3]; decide
    have h0in : (0 : Fin 4 → F) ∈ Finset.univ.filter (fun m : Fin 4 → F => ev m x = 0) := by
      simp [ev]
    have heq : Finset.univ.filter (fun m : Fin 4 → F => m ≠ 0 ∧ ev m x = 0) =
        (Finset.univ.filter (fun m : Fin 4 → F => ev m x = 0)).erase 0 := by
      ext m; simp [and_comm]
    rw [heq, Finset.card_erase_of_mem h0in, hbi]
  let Mnz : Finset (Fin 4 → F) := Finset.univ.filter (fun m : Fin 4 → F => m ≠ 0)
  have hMnz_card : Mnz.card = 15 := by
    have heq : Mnz = Finset.univ.erase 0 := by ext m; simp [Mnz]
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]; decide
  have h7S : 7 * shapeCnt ht P ≤ 90 := by
    have hdbl : ∑ x : P, (if shape ht x.1 then (Mnz.filter (fun m => ev m x = 0)).card else 0) =
        ∑ m ∈ Mnz, shapeCnt ht ((LinearMap.ker (ev m)).map P.subtype) := by
      have hlhs : ∑ x : P, (if shape ht x.1 then (Mnz.filter (fun m => ev m x = 0)).card else 0) =
          ∑ x : P, ∑ m ∈ Mnz, if shape ht x.1 ∧ ev m x = 0 then 1 else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hs : shape ht x.1
        · simp only [hs, true_and, ↓reduceIte, Finset.card_filter]
        · simp only [hs, false_and, ↓reduceIte, Finset.sum_const_zero]
      rw [hlhs, Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.card_filter]
      unfold shapeCnt
      refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
      · intro x hx
        obtain ⟨hs, hm0⟩ := (Finset.mem_filter.mp hx).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x, hm0, rfl⟩, hs⟩
      · intro a _ b _ h; exact Subtype.ext h
      · intro y hy
        obtain ⟨⟨x, hm0, rfl⟩, hs⟩ := (Finset.mem_filter.mp hy).2
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, hm0⟩, rfl⟩
    have h7eq : ∑ x : P, (if shape ht x.1 then (Mnz.filter (fun m => ev m x = 0)).card else 0) =
        7 * shapeCnt ht P := by
      have hterm : ∀ x : P, (if shape ht x.1 then (Mnz.filter (fun m => ev m x = 0)).card else 0) =
          if shape ht x.1 then 7 else 0 := by
        intro x
        split_ifs with hs
        · have hxne : x ≠ 0 := by
            intro hz; rw [hz] at hs
            rcases hs with h | h
            · have := wt_pair_eq_two h; simp only [ZeroMemClass.coe_zero, wt_zero] at this; omega
            · have := wt_run3_eq_three ht h; simp only [ZeroMemClass.coe_zero, wt_zero] at this; omega
          have heq : Mnz.filter (fun m => ev m x = 0) =
              Finset.univ.filter (fun m : Fin 4 → F => m ≠ 0 ∧ ev m x = 0) := by
            ext m; simp [Mnz]
          rw [heq, hcount_m x hxne]
        · rfl
      rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, smul_eq_mul, mul_comm]
      congr 1
      unfold shapeCnt
      refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
      · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2, (Finset.mem_filter.mp hx).2⟩
      · intro a _ b _ h; exact Subtype.ext h
      · intro y hy
        obtain ⟨hyP, hs⟩ := (Finset.mem_filter.mp hy).2
        exact ⟨⟨y, hyP⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, rfl⟩
    rw [← h7eq, hdbl]
    calc ∑ m ∈ Mnz, shapeCnt ht ((LinearMap.ker (ev m)).map P.subtype)
        ≤ ∑ _m ∈ Mnz, 6 := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hmne : m ≠ 0 := (Finset.mem_filter.mp hm).2
          have hsub : (LinearMap.ker (ev m)).map P.subtype ≤ codeSub t := by
            rintro _ ⟨x, _, rfl⟩; exact hP x.2
          exact shape_card_dim3_le_six ht ht3 _ hsub (hev_dim m hmne)
      _ = 90 := by rw [Finset.sum_const, smul_eq_mul, hMnz_card]
  have hS12 : shapeCnt ht P ≤ 12 := by omega
  have hPcard : Nat.card P = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := P), Nat.card_eq_fintype_card, ZMod.card, hP4]; decide
  have hCdim := codeSub_finrank ht
  have hQcard : 2 * Nat.card Q = cntS t ∅ := by
    rw [← card_codeSub, Module.natCard_eq_pow_finrank (K := F) (V := Q),
      Module.natCard_eq_pow_finrank (K := F) (V := codeSub t), Nat.card_eq_fintype_card, ZMod.card,
      hCdim, show Module.finrank F Q = 3 * t - 3 by omega, ← pow_succ']
    congr 1; omega
  have hm := hits_shape_le ht ht3 P Q hP hQ
  rw [hPcard] at hm ⊢
  have hnum := numVal_ge_348 ht3
  have hpos : (0 : ℚ) ≤ cntS t ∅ := Nat.cast_nonneg _
  have hQq : (2 : ℚ) * (Nat.card Q : ℚ) = (cntS t ∅ : ℚ) := by exact_mod_cast hQcard
  have hSq : ((2 * (16 - 1) + 2 * shapeCnt ht P : ℕ) : ℚ) ≤ 54 := by
    exact_mod_cast (show 2 * (16 - 1) + 2 * shapeCnt ht P ≤ 54 by omega)
  have hq : (2048 : ℚ) * (rectHits ht P Q : ℚ) ≤
      (numVal t : ℚ) * (16 * (Nat.card Q : ℚ)) := by
    have hnumq : (348 : ℚ) ≤ (numVal t : ℚ) := by exact_mod_cast hnum
    nlinarith
  exact_mod_cast hq

open Classical in
set_option maxHeartbeats 800000 in
lemma rect_case_3D {t : ℕ} (ht : 0 < t) (ht3 : 3 ≤ t)
    (P Q : Submodule F (Lane t)) (hP : P ≤ codeSub t) (hQ : Q ≤ codeSub t)
    (hP5 : Module.finrank F P = 5) (hsum : Module.finrank F P + Module.finrank F Q = 3 * t + 1) :
    2048 * rectHits ht P Q ≤ numVal t * (Nat.card P * Nat.card Q) := by
  have hPcard : Nat.card P = 32 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := P), Nat.card_eq_fintype_card, ZMod.card, hP5]; decide
  have hCdim := codeSub_finrank ht
  have hQcard : 4 * Nat.card Q = cntS t ∅ := by
    rw [← card_codeSub, Module.natCard_eq_pow_finrank (K := F) (V := Q),
      Module.natCard_eq_pow_finrank (K := F) (V := codeSub t), Nat.card_eq_fintype_card, ZMod.card,
      hCdim, show Module.finrank F Q = 3 * t - 4 by omega, show (4 : ℕ) = 2 ^ 2 by decide, ← pow_add]
    congr 1; omega
  have hnum := numVal_ge_348 ht3
  have hpos : (0 : ℚ) ≤ cntS t ∅ := Nat.cast_nonneg _
  have hQq : (4 : ℚ) * (Nat.card Q : ℚ) = (cntS t ∅ : ℚ) := by exact_mod_cast hQcard
  by_cases hsep : isSep ht P
  · by_cases ht34 : t = 3 ∨ t = 4
    · rcases ht34 with rfl | rfl
      · exact absurd hsep (not_isSep_of_small ht P hP (Or.inl ⟨rfl, by omega⟩))
      · exact absurd hsep (not_isSep_of_small ht P hP (Or.inr ⟨rfl, by omega⟩))
    · have ht5 : 5 ≤ t := by omega
      have h1 := rectHits_le_sum_cntS ht P Q hQ
      have h1q : (rectHits ht P Q : ℚ) ≤ (Nat.card Q : ℚ) +
          ∑ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, (cntS t (Nb ht p) : ℚ) := by
        exact_mod_cast h1
      have hmain : ∑ p ∈ Finset.univ.filter (fun p : Lane t => p ∈ P), (1 / 4 : ℚ) ^ wt p ≤ Bfun 5 := by
        have h := mainQ_le 5 (Fin (3 * t)) P (fun _ => 1) hP5 (by simp; omega)
          (fun p hp => no_wt_one ((codeSub_iff_codeF p).mp (hP hp)))
          (fun _ => by norm_num) (fun _ _ => rfl)
        refine le_trans (le_of_eq ?_) h
        refine Finset.sum_congr (by ext p; simp) fun p _ => by ring
      have hB5 : Bfun 5 = 8177 / 4096 := by unfold Bfun; norm_num
      have h0mem : (0 : Lane t) ∈ Finset.univ.filter (fun p => p ∈ P) := by simp
      have hnz_sum : ∑ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, (1 / 4 : ℚ) ^ wt p ≤ 4081 / 4096 := by
        have hs := Finset.add_sum_erase (Finset.univ.filter (fun p : Lane t => p ∈ P))
          (fun p => (1 / 4 : ℚ) ^ wt p) h0mem
        rw [wt_zero, pow_zero] at hs
        linarith
      have hex_term : ∀ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0,
          (1 / 4 : ℚ) ^ wt p * (cval t (Nb ht p) - 1) ≤ 3 / 1024 := by
        intro p hp
        have hpP : p ∈ P := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2
        by_cases hw4 : wt p ≤ 4
        · have hc1 : cval t (Nb ht p) = 1 := cval_one (by rw [card_Nb ht p (hsep p hpP)]; omega)
          rw [hc1, sub_self, mul_zero]; norm_num
        · have hw5 : 5 ≤ wt p := by omega
          have hpow : (1 / 4 : ℚ) ^ wt p ≤ (1 / 4) ^ 5 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hw5
          have hc4 := cval_le t (Nb ht p)
          have hge1 : 0 ≤ cval t (Nb ht p) - 1 := by unfold cval cvalNat; split_ifs <;> norm_num
          calc (1 / 4 : ℚ) ^ wt p * (cval t (Nb ht p) - 1)
              ≤ (1 / 4) ^ 5 * 3 := mul_le_mul hpow (by linarith) hge1 (by positivity)
            _ = 3 / 1024 := by norm_num
      have hex_sum : ∑ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0,
          (1 / 4 : ℚ) ^ wt p * (cval t (Nb ht p) - 1) ≤ 93 / 1024 := by
        have hPce : ((Finset.univ.filter (fun p : Lane t => p ∈ P)).erase 0).card = 31 := by
          rw [Finset.card_erase_of_mem h0mem, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, hPcard]
        calc ∑ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0,
                (1 / 4 : ℚ) ^ wt p * (cval t (Nb ht p) - 1)
            ≤ ∑ _p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, (3 / 1024 : ℚ) :=
              Finset.sum_le_sum hex_term
          _ = 93 / 1024 := by rw [Finset.sum_const, hPce, nsmul_eq_mul]; norm_num
      have hcnt_sum : ∑ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, (cntS t (Nb ht p) : ℚ) =
          (cntS t ∅ : ℚ) * ((∑ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0, (1 / 4 : ℚ) ^ wt p) +
            (∑ p ∈ (Finset.univ.filter (fun p => p ∈ P)).erase 0,
              (1 / 4 : ℚ) ^ wt p * (cval t (Nb ht p) - 1))) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        have hpP : p ∈ P := (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2
        rw [cntS_ratio ht, card_Nb ht p (hsep p hpP), pow_mul, show (1 / 2 : ℚ) ^ 2 = 1 / 4 by norm_num]
        ring
      rw [hPcard]
      have hq : (2048 : ℚ) * (rectHits ht P Q : ℚ) ≤ (numVal t : ℚ) * (32 * (Nat.card Q : ℚ)) := by
        have hnumq : (348 : ℚ) ≤ (numVal t : ℚ) := by exact_mod_cast hnum
        nlinarith
      exact_mod_cast hq
  · have h3ST : 3 * shapeCnt ht P + nb5Cnt ht P ≤ 40 := by
      rw [shapeCnt_eq_add]
      by_cases hodd : ∃ x0 ∈ P, parityL (3 * t) x0 = 1
      · obtain ⟨x0, hx0, hpar⟩ := hodd
        let Pe := P ⊓ LinearMap.ker (parityL (3 * t))
        obtain ⟨hPedim, hcoset⟩ := odd_coset_iff P x0 hx0 hpar
        have hPe4 : Module.finrank F Pe = 4 := by
          change Module.finrank F (↥(P ⊓ LinearMap.ker (parityL (3 * t)))) = 4; omega
        have hPe_card : (Finset.univ.filter (fun u : Lane t => u ∈ Pe)).card = 16 := by
          rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
            Module.natCard_eq_pow_finrank (K := F) (V := Pe), Nat.card_eq_fintype_card, ZMod.card, hPe4]; decide
        have hpair_eq : pairCnt P = pairCnt Pe := by
          unfold pairCnt; congr 1; ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pe, Submodule.mem_inf, LinearMap.mem_ker]
          exact ⟨fun ⟨hxP, hp⟩ => ⟨⟨hxP, parityL_pair hp⟩, hp⟩, fun ⟨⟨hxP, _⟩, hp⟩ => ⟨hxP, hp⟩⟩
        obtain ⟨cs, hcs_prop, hcs_disj, hrank, hcount, hcs_pair, _⟩ := pair_clique_decomp Pe (inf_le_left.trans hP)
        have hRT := run3_add_nb5_le_wt3 ht ht3 P hP
        by_cases hC5 : ∃ C ∈ cs, C.card = 5
        · obtain ⟨C, hC, hCcard⟩ := hC5
          have hSdim := cliqueSpan_finrank C (Finset.card_pos.mp (by omega))
          have hSle : cliqueSpan C ≤ Pe := cliqueSpan_le_of_pairs Pe C (hcs_pair C hC)
          have hSeq : cliqueSpan C = Pe := Submodule.eq_of_le_of_finrank_eq hSle (by omega)
          have hcs_sing : cs = {C} := by
            ext D; simp only [Finset.mem_singleton]
            constructor
            · intro hD; by_contra hne
              have hsub : ({C, D} : Finset (Finset (Fin (3 * t)))) ⊆ cs := by
                intro X hX; simp only [Finset.mem_insert, Finset.mem_singleton] at hX
                rcases hX with rfl | rfl <;> assumption
              have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
                (f := fun X : Finset (Fin (3 * t)) => X.card - 1) (fun _ _ _ => Nat.zero_le _)
              rw [Finset.sum_pair (Ne.symm hne)] at hs
              have hD2 := (hcs_prop D hD).1; omega
            · rintro rfl; exact hC
          have hpair10 : pairCnt P = 10 := by
            rw [hpair_eq]; unfold pairCnt; rw [hcount, hcs_sing, Finset.sum_singleton, hCcard]
          obtain ⟨hwt3_le, hrun_le⟩ := coset_wt3_run3_bound ht ht3 x0 (hP hx0) C (by omega)
            (hcs_prop C hC).2 (hSle.trans (inf_le_left.trans hP))
          have hwt3_eq : wt3Cnt P = (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ wt (x0 + u) = 3)).card := by
            unfold wt3Cnt; rw [hSeq]; convert hcoset (fun x => wt x = 3) (fun x _ h => by rw [parityL_eq_wt, h]; decide)
          have hrun_eq : run3Cnt ht P = (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ isRun3 ht (x0 + u))).card := by
            unfold run3Cnt; rw [hSeq]; convert hcoset (fun x => isRun3 ht x) (fun x _ h => parityL_run3 ht h)
          omega
        · by_cases hC4 : ∃ C ∈ cs, C.card = 4
          · obtain ⟨C, hC, hCcard⟩ := hC4
            have hSdim := cliqueSpan_finrank C (Finset.card_pos.mp (by omega))
            have hSle : cliqueSpan C ≤ Pe := cliqueSpan_le_of_pairs Pe C (hcs_pair C hC)
            have hrest_sum : ∑ D ∈ cs.erase C, (D.card - 1) ≤ 1 := by
              have hs := Finset.add_sum_erase cs (fun D => D.card - 1) hC
              omega
            have hpair_le7 : pairCnt P ≤ 7 := by
              rw [hpair_eq]; unfold pairCnt; rw [hcount, ← Finset.add_sum_erase _ _ hC]
              have hterm : ∀ D ∈ cs.erase C, D.card * (D.card - 1) / 2 ≤ D.card - 1 := by
                intro D hD
                have hD2 := (hcs_prop D (Finset.mem_erase.mp hD).2).1
                have hDle : D.card - 1 ≤ ∑ X ∈ cs.erase C, (X.card - 1) :=
                  Finset.single_le_sum (f := fun X : Finset (Fin (3 * t)) => X.card - 1) (fun _ _ => Nat.zero_le _) hD
                have hDeq : D.card = 2 := by omega
                rw [hDeq]
              have hsum_rest := Finset.sum_le_sum hterm
              rw [hCcard] at *
              omega
            have hwt3_le8 : wt3Cnt P ≤ 8 := by
              have h1 : wt3Cnt P = (Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ wt (x0 + u) = 3)).card := by
                unfold wt3Cnt; convert hcoset (fun x => wt x = 3) (fun x _ h => by rw [parityL_eq_wt, h]; decide)
              rw [h1]
              have hb := subspace_coset_bound P Pe (cliqueSpan C) hSle inf_le_left x0 hx0
                (fun x => wt x = 3) 4 (fun y0 hy0 => by
                  have hc := (coset_wt3_run3_bound ht ht3 y0 (hP hy0) C (by omega)
                    (hcs_prop C hC).2 (hSle.trans (inf_le_left.trans hP))).1
                  have heq : (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ wt (y0 + u) = 3)).card =
                      (Finset.univ.filter (fun u : Lane t => u ∈ cliqueSpan C ∧ wt (y0 + u) = 3)).card := rfl
                  rw [← hCcard]; convert hc)
              rw [hPe4, hSdim, hCcard] at hb
              have hb' : (Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ wt (x0 + u) = 3)).card ≤
                  2 ^ (4 - (4 - 1)) * 4 := by convert hb
              omega
            have hrun_le4 : run3Cnt ht P ≤ 4 := by
              have h1 : run3Cnt ht P = (Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ isRun3 ht (x0 + u))).card := by
                unfold run3Cnt; convert hcoset (fun x => isRun3 ht x) (fun x _ h => parityL_run3 ht h)
              rw [h1]
              have hb := subspace_coset_bound P Pe (cliqueSpan C) hSle inf_le_left x0 hx0
                (fun x => isRun3 ht x) 2 (fun y0 hy0 => by
                  convert (coset_wt3_run3_bound ht ht3 y0 (hP hy0) C (by omega)
                    (hcs_prop C hC).2 (hSle.trans (inf_le_left.trans hP))).2)
              rw [hPe4, hSdim, hCcard] at hb
              have hb' : (Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ isRun3 ht (x0 + u))).card ≤
                  2 ^ (4 - (4 - 1)) * 2 := by convert hb
              omega
            omega
          · by_cases hC33 : ∃ C1 ∈ cs, ∃ C2 ∈ cs, C1 ≠ C2 ∧ C1.card = 3 ∧ C2.card = 3
            · obtain ⟨C1, hC1, C2, hC2, hne12, hcard1, hcard2⟩ := hC33
              have hS1le : cliqueSpan C1 ≤ Pe := cliqueSpan_le_of_pairs Pe C1 (hcs_pair C1 hC1)
              have hS2le : cliqueSpan C2 ≤ Pe := cliqueSpan_le_of_pairs Pe C2 (hcs_pair C2 hC2)
              have hS12le : cliqueSpan C1 ⊔ cliqueSpan C2 ≤ Pe := sup_le hS1le hS2le
              have hdisjS : Disjoint (cliqueSpan C1) (cliqueSpan C2) := by
                rw [Submodule.disjoint_def]
                intro x hx1 hx2
                funext i
                by_cases hi1 : i ∈ C1
                · exact cliqueSpan_supp C2 x hx2 i (Finset.disjoint_left.mp (hcs_disj C1 hC1 C2 hC2 hne12) hi1)
                · exact cliqueSpan_supp C1 x hx1 i hi1
              have hS12dim : Module.finrank F (↥(cliqueSpan C1 ⊔ cliqueSpan C2)) = 4 := by
                have hs := Submodule.finrank_sup_add_finrank_inf_eq (cliqueSpan C1) (cliqueSpan C2)
                rw [disjoint_iff.mp hdisjS, finrank_bot, add_zero,
                  cliqueSpan_finrank C1 (Finset.card_pos.mp (by omega)),
                  cliqueSpan_finrank C2 (Finset.card_pos.mp (by omega)), hcard1, hcard2] at hs
                exact hs
              have hS12eq : cliqueSpan C1 ⊔ cliqueSpan C2 = Pe :=
                Submodule.eq_of_le_of_finrank_eq hS12le (by omega)
              have hcs_pair2 : cs = {C1, C2} := by
                ext D; simp only [Finset.mem_insert, Finset.mem_singleton]
                constructor
                · intro hD; by_contra hnot; push Not at hnot
                  have hsub : ({C1, C2, D} : Finset (Finset (Fin (3 * t)))) ⊆ cs := by
                    intro X hX; simp only [Finset.mem_insert, Finset.mem_singleton] at hX
                    rcases hX with rfl | rfl | rfl <;> assumption
                  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
                    (f := fun X : Finset (Fin (3 * t)) => X.card - 1) (fun _ _ _ => Nat.zero_le _)
                  rw [Finset.sum_insert (by simp [hne12, Ne.symm hnot.1]),
                    Finset.sum_pair (Ne.symm hnot.2)] at hs
                  have hD2 := (hcs_prop D hD).1; omega
                · rintro (rfl | rfl) <;> assumption
              have hpair6 : pairCnt P = 6 := by
                rw [hpair_eq]; unfold pairCnt; rw [hcount, hcs_pair2, Finset.sum_pair hne12, hcard1, hcard2]
              obtain ⟨hwt3_le, hrun_le⟩ := two_clique_wt3_run3_bound ht ht3 x0 (hP hx0) C1 C2 hcard1 hcard2
                (hcs_prop C1 hC1).2 (hcs_prop C2 hC2).2 (hS12le.trans (inf_le_left.trans hP))
              have hwt3_eq : wt3Cnt P = (Finset.univ.filter (fun u : Lane t =>
                  u ∈ cliqueSpan C1 ⊔ cliqueSpan C2 ∧ wt (x0 + u) = 3)).card := by
                unfold wt3Cnt; rw [hS12eq]; convert hcoset (fun x => wt x = 3) (fun x _ h => by rw [parityL_eq_wt, h]; decide)
              have hrun_eq : run3Cnt ht P = (Finset.univ.filter (fun u : Lane t =>
                  u ∈ cliqueSpan C1 ⊔ cliqueSpan C2 ∧ isRun3 ht (x0 + u))).card := by
                unfold run3Cnt; rw [hS12eq]; convert hcoset (fun x => isRun3 ht x) (fun x _ h => parityL_run3 ht h)
              omega
            · push Not at hC5 hC4 hC33
              have hC_le3 : ∀ C ∈ cs, C.card ≤ 3 := by
                intro C hC
                have hCle : C.card - 1 ≤ ∑ D ∈ cs, (D.card - 1) :=
                  Finset.single_le_sum (f := fun D : Finset (Fin (3 * t)) => D.card - 1) (fun _ _ => Nat.zero_le _) hC
                have h5 := hC5 C hC; have h4 := hC4 C hC
                omega
              have hpair_le5 : pairCnt P ≤ 5 := by
                rw [hpair_eq]; unfold pairCnt; rw [hcount]
                by_cases hhas3 : ∃ C0 ∈ cs, C0.card = 3
                · obtain ⟨C0, hC0, hC0c⟩ := hhas3
                  rw [← Finset.add_sum_erase _ _ hC0]
                  have hrest : ∀ D ∈ cs.erase C0, D.card * (D.card - 1) / 2 ≤ D.card - 1 := by
                    intro D hD
                    obtain ⟨hne, hDm⟩ := Finset.mem_erase.mp hD
                    have hD2 := (hcs_prop D hDm).1
                    have hDle3 := hC_le3 D hDm
                    have hDne3 : D.card ≠ 3 := hC33 C0 hC0 D hDm (Ne.symm hne) hC0c
                    have hDeq2 : D.card = 2 := by omega
                    rw [hDeq2]
                  have hsum_er := Finset.add_sum_erase cs (fun D => D.card - 1) hC0
                  have hle_er := Finset.sum_le_sum hrest
                  rw [hC0c] at *
                  omega
                · push Not at hhas3
                  have hterm : ∀ C ∈ cs, C.card * (C.card - 1) / 2 ≤ C.card - 1 := by
                    intro C hC
                    have hC2 := (hcs_prop C hC).1
                    have hC3 := hC_le3 C hC
                    have hne3 := hhas3 C hC
                    have hCeq2 : C.card = 2 := by omega
                    rw [hCeq2]
                  calc ∑ C ∈ cs, C.card * (C.card - 1) / 2 ≤ ∑ C ∈ cs, (C.card - 1) := Finset.sum_le_sum hterm
                    _ ≤ Module.finrank F Pe := hrank
                    _ ≤ 5 := by omega
              have hwt3_le16 : wt3Cnt P ≤ 16 := by
                have h1 : wt3Cnt P = (Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ wt (x0 + u) = 3)).card := by
                  unfold wt3Cnt; convert hcoset (fun x => wt x = 3) (fun x _ h => by rw [parityL_eq_wt, h]; decide)
                rw [h1]
                calc (Finset.univ.filter (fun u : Lane t => u ∈ Pe ∧ wt (x0 + u) = 3)).card
                    ≤ (Finset.univ.filter (fun u : Lane t => u ∈ Pe)).card :=
                      Finset.card_le_card (fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2.1⟩)
                  _ = 16 := hPe_card
              by_cases hR4 : run3Cnt ht P ≤ 4
              · omega
              · have hwt3_le15 : wt3Cnt P ≤ 15 := wt3_le_15_of_run3_pos ht P hP hP5 (by omega)
                by_cases hR5 : run3Cnt ht P = 5
                · omega
                · by_cases ht3eq : t = 3
                  · subst ht3eq
                    obtain ⟨hRle6, hR6imp⟩ := run3_card_t3_dim5 ht P hP hP5
                    have hR_eq : run3Cnt ht P = (Finset.univ.filter (fun x : Lane 3 => x ∈ P ∧ isRun3 ht x)).card := by
                      unfold run3Cnt; congr 1
                    have hP_eq : pairCnt P = (Finset.univ.filter (fun x : Lane 3 => x ∈ P ∧ isPair x)).card := by
                      unfold pairCnt; congr 1
                    have hR6 : (Finset.univ.filter (fun x : Lane 3 => x ∈ P ∧ isRun3 ht x)).card = 6 := by omega
                    have hP3 := hR6imp hR6
                    omega
                  · have hRle5 : run3Cnt ht P ≤ 5 := by
                      have h1 := run3_card_le_of_lt ht ht3 P (by omega)
                      have h2 : run3Cnt ht P = (Finset.univ.filter (fun x : Lane t => x ∈ P ∧ isRun3 ht x)).card := by
                        unfold run3Cnt; congr 1
                      omega
                    omega
      · push Not at hodd
        have hR0 : run3Cnt ht P = 0 := by
          unfold run3Cnt; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x _ ⟨hxP, hr⟩; exact hodd x hxP (parityL_run3 ht hr)
        have hT0 : nb5Cnt ht P = 0 := by
          unfold nb5Cnt; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x _ ⟨hxP, h5⟩
          have hnz : x ≠ 0 := by
            intro hz; subst hz; have hemp : Nb ht (0 : Lane t) = ∅ := by ext i; simp [Nb]
            rw [hemp, Finset.card_empty] at h5; omega
          exact hodd x hxP (parityL_nb5 ht ht3 hnz (hP hxP) h5)
        obtain ⟨cs, hcs_prop, _, hrank, hcount, hcs_pair, _⟩ := pair_clique_decomp P hP
        have h2pair : 2 * pairCnt P ≤ 25 := by
          unfold pairCnt; rw [hcount, Finset.mul_sum]
          have hterm : ∀ C ∈ cs, 2 * (C.card * (C.card - 1) / 2) ≤ 5 * (C.card - 1) := by
            intro C hC
            have hC2 := (hcs_prop C hC).1
            have hC5 : C.card ≤ 5 := by
              have := clique_le_finrank_of_not_isSep ht P hsep C (Finset.card_pos.mp (by omega))
                (hcs_prop C hC).2 (hcs_pair C hC)
              omega
            have heven : 2 ∣ C.card * (C.card - 1) := by
              rcases Nat.even_or_odd C.card with ⟨m, hm⟩ | ⟨m, hm⟩
              · exact ⟨m * (C.card - 1), by rw [hm]; ring⟩
              · exact ⟨C.card * m, by rw [show C.card - 1 = 2 * m by omega]; ring⟩
            rw [Nat.mul_div_cancel' heven]
            exact Nat.mul_le_mul_right _ hC5
          calc ∑ C ∈ cs, 2 * (C.card * (C.card - 1) / 2)
              ≤ ∑ C ∈ cs, 5 * (C.card - 1) := Finset.sum_le_sum hterm
            _ = 5 * ∑ C ∈ cs, (C.card - 1) := (Finset.mul_sum _ _ _).symm
            _ ≤ 5 * Module.finrank F P := Nat.mul_le_mul_left 5 hrank
            _ = 25 := by omega
        omega
    have hm := hits_master_le ht ht3 P Q hP hQ
    rw [hPcard] at hm ⊢
    have h3STq : ((32 - 1 + 3 * shapeCnt ht P + nb5Cnt ht P : ℕ) : ℚ) ≤ 71 := by
      exact_mod_cast (show 32 - 1 + 3 * shapeCnt ht P + nb5Cnt ht P ≤ 71 by omega)
    have hq : (2048 : ℚ) * (rectHits ht P Q : ℚ) ≤ (numVal t : ℚ) * (32 * (Nat.card Q : ℚ)) := by
      have hnumq : (348 : ℚ) ≤ (numVal t : ℚ) := by exact_mod_cast hnum
      nlinarith
    exact_mod_cast hq

open Classical in
lemma finrank_span_image_le {E U : Type*} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    (f : E → U) (S : Finset E) :
    Module.finrank F (Submodule.span F (f '' (S : Set E))) ≤ S.card := by
  let φ : (S → F) →ₗ[F] U :=
    { toFun := fun g => ∑ e : S, g e • f e.1
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hle : Submodule.span F (f '' (S : Set E)) ≤ LinearMap.range φ := by
    rw [Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    refine ⟨fun x => if x.1 = e then 1 else 0, ?_⟩
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single ⟨e, Finset.mem_coe.mp he⟩]
    · simp
    · intro b _ hbe; simp [show b.1 ≠ e from fun h => hbe (Subtype.ext h)]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.finrank_range_le φ
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
  exact h1.trans h2

open Classical in
lemma mem_span_finset_iff {E U : Type*} [AddCommGroup U] [Module F U]
    (f : E → U) (S : Finset E) (y : U) :
    y ∈ Submodule.span F (f '' (S : Set E)) ↔ ∃ c : S → F, y = ∑ e : S, c e • f e.1 := by
  constructor
  · intro hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨e, he, rfl⟩
      refine ⟨fun x => if x.1 = e then 1 else 0, ?_⟩
      rw [Finset.sum_eq_single ⟨e, Finset.mem_coe.mp he⟩]
      · simp
      · intro b _ hbe; simp [show b.1 ≠ e from fun h => hbe (Subtype.ext h)]
      · intro h; exact absurd (Finset.mem_univ _) h
    · exact ⟨0, by simp⟩
    · rintro a b _ _ ⟨ca, rfl⟩ ⟨cb, rfl⟩
      exact ⟨ca + cb, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
    · rintro r a _ ⟨ca, rfl⟩
      exact ⟨r • ca, by simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]⟩
  · rintro ⟨c, rfl⟩
    exact Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ (c e)
      (Submodule.subset_span ⟨e.1, Finset.mem_coe.mpr e.2, rfl⟩)

open Classical in
lemma mem_span_subset_of_mem_erase {E U : Type*} [AddCommGroup U] [Module F U]
    (f : E → U) (I S : Finset E) (hSI : S ⊆ I)
    (hI : LinearIndependent F (fun e : I => f e.1))
    (y : U) (hy : y ∈ Submodule.span F (f '' (I : Set E)))
    (her : ∀ a ∈ I \ S, y ∈ Submodule.span F (f '' ((I.erase a : Finset E) : Set E))) :
    y ∈ Submodule.span F (f '' (S : Set E)) := by
  obtain ⟨c, hc⟩ := (mem_span_finset_iff f I y).mp hy
  have hzero : ∀ e : I, e.1 ∉ S → c e = 0 := by
    intro e heS
    obtain ⟨d, hd⟩ := (mem_span_finset_iff f (I.erase e.1) y).mp
      (her e.1 (Finset.mem_sdiff.mpr ⟨e.2, heS⟩))
    let d' : I → F := fun x => if hx : x.1 = e.1 then 0 else d ⟨x.1, Finset.mem_erase.mpr ⟨hx, x.2⟩⟩
    have hd'_sum : ∑ x : I, d' x • f x.1 = y := by
      rw [hd]
      have h1 : ∑ x : I, d' x • f x.1 = ∑ x ∈ (Finset.univ : Finset I).erase e, d' x • f x.1 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e)]
        have : d' e = 0 := by simp [d']
        rw [this, zero_smul, zero_add]
      rw [h1]
      refine Finset.sum_bij (fun x hx => ⟨x.1, Finset.mem_erase.mpr
        ⟨fun heq => (Finset.mem_erase.mp hx).1 (Subtype.ext heq), x.2⟩⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact Subtype.ext (Subtype.mk.inj h)
      · intro b _
        refine ⟨⟨b.1, Finset.mem_of_mem_erase b.2⟩,
          Finset.mem_erase.mpr ⟨fun heq => (Finset.mem_erase.mp b.2).1 (congrArg (Subtype.val : I → E) heq), Finset.mem_univ _⟩,
          Subtype.ext rfl⟩
      · intro x hx
        have hne : x.1 ≠ e.1 := fun heq => (Finset.mem_erase.mp hx).1 (Subtype.ext heq)
        simp only [d', hne, ↓reduceDIte]
    have hdiff : ∑ x : I, (c x - d' x) • f x.1 = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hc, hd'_sum, sub_self]
    have hce := (Fintype.linearIndependent_iff.mp hI) (fun x => c x - d' x) hdiff e
    have hde : d' e = 0 := by simp [d']
    rw [hde, sub_zero] at hce
    exact hce
  rw [mem_span_finset_iff]
  refine ⟨fun x => c ⟨x.1, hSI x.2⟩, ?_⟩
  rw [hc]
  have h1 : ∑ e : I, c e • f e.1 = ∑ e ∈ (Finset.univ : Finset I).filter (fun e => e.1 ∈ S), c e • f e.1 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : e.1 ∈ S
    · simp [h]
    · simp [h, hzero e h]
  rw [h1]
  refine Finset.sum_bij (fun e he => ⟨e.1, (Finset.mem_filter.mp he).2⟩) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro a _ b _ h; exact Subtype.ext (Subtype.mk.inj h)
  · intro b _
    exact ⟨⟨b.1, hSI b.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, Subtype.ext rfl⟩
  · intro _ _; rfl

def ReachIn {E : Type*} (X1 : Finset E) (adj : E → E → Prop) : ℕ → E → Prop
  | 0, x => x ∈ X1
  | n + 1, b => ∃ a, ReachIn X1 adj n a ∧ adj a b

lemma reachIn_path {E : Type*} (X1 : Finset E) (adj : E → E → Prop) :
    ∀ (m : ℕ) (y : E), ReachIn X1 adj m y →
      ∃ p : Fin (m + 1) → E, p ⟨0, Nat.zero_lt_succ m⟩ ∈ X1 ∧
        p ⟨m, Nat.lt_succ_self m⟩ = y ∧
        ∀ i : Fin m, adj (p ⟨i.1, by omega⟩) (p ⟨i.1 + 1, by omega⟩)
  | 0, y, hy => ⟨fun _ => y, hy, rfl, fun i => i.elim0⟩
  | m + 1, y, ⟨a, ha, hab⟩ => by
    obtain ⟨p0, h0, hm, hadj⟩ := reachIn_path X1 adj m a ha
    let p : Fin (m + 2) → E := fun i =>
      if h : i.1 ≤ m then p0 ⟨i.1, Nat.lt_succ_of_le h⟩ else y
    refine ⟨p, ?_, ?_, ?_⟩
    · simp only [p, Nat.zero_le, ↓reduceDIte]; exact h0
    · simp only [p, show ¬ (m + 1 ≤ m) by omega, ↓reduceDIte]
    · intro i
      have hilt := i.isLt
      by_cases htop : i.1 = m
      · have h1 : p ⟨i.1, by omega⟩ = a := by
          simp only [p, show i.1 ≤ m by omega, ↓reduceDIte]
          rw [← hm]; congr 1; exact Fin.ext htop
        have h2 : p ⟨i.1 + 1, by omega⟩ = y := by
          simp only [p, show ¬ (i.1 + 1 ≤ m) by omega, ↓reduceDIte]
        rw [h1, h2]; exact hab
      · have h1 : p ⟨i.1, by omega⟩ = p0 ⟨i.1, by omega⟩ := by simp [p, show i.1 ≤ m by omega]
        have h2 : p ⟨i.1 + 1, by omega⟩ = p0 ⟨i.1 + 1, by omega⟩ := by simp [p, show i.1 + 1 ≤ m by omega]
        rw [h1, h2]; exact hadj ⟨i.1, by omega⟩

lemma reachIn_parity {E : Type*} (I X1 : Finset E) (adj : E → E → Prop)
    (hX1 : ∀ x ∈ X1, x ∉ I)
    (hadj : ∀ a b, adj a b → (a ∈ I ∧ b ∉ I) ∨ (a ∉ I ∧ b ∈ I)) :
    ∀ (n : ℕ) (x : E), ReachIn X1 adj n x → (n % 2 = 0 → x ∉ I) ∧ (n % 2 = 1 → x ∈ I)
  | 0, x, hx => ⟨fun _ => hX1 x hx, fun h => by omega⟩
  | n + 1, b, ⟨a, ha, hab⟩ => by
    have ih := reachIn_parity I X1 adj hX1 hadj n a ha
    rcases hadj a b hab with ⟨haI, hbI⟩ | ⟨haI, hbI⟩
    · refine ⟨fun _ => hbI, fun h => ?_⟩
      have : n % 2 = 0 := by omega
      exact absurd haI (ih.1 this)
    · refine ⟨fun h => ?_, fun _ => hbI⟩
      have : n % 2 = 1 := by omega
      exact absurd (ih.2 this) haI

lemma reachIn_shift {E : Type*} (X1 : Finset E) (adj : E → E → Prop) {m : ℕ}
    (p : Fin (m + 1) → E)
    (hadj : ∀ i : Fin m, adj (p ⟨i.1, by omega⟩) (p ⟨i.1 + 1, by omega⟩))
    (n i : ℕ) (hi : i ≤ m) (hstart : ReachIn X1 adj n (p ⟨i, by omega⟩)) :
    ∀ d : ℕ, (hd : i + d ≤ m) → ReachIn X1 adj (n + d) (p ⟨i + d, by omega⟩)
  | 0, _ => hstart
  | d + 1, hd =>
    ⟨p ⟨i + d, by omega⟩, reachIn_shift X1 adj p hadj n i hi hstart d (by omega),
      hadj ⟨i + d, by omega⟩⟩

open Classical in
set_option maxHeartbeats 800000 in
lemma matroid_inter {E U V : Type*} [Fintype E]
    [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (u : E → U) (v : E → V) (k : ℕ)
    (hall : ∀ (A B : Finset E), A ∪ B = Finset.univ →
      k ≤ Module.finrank F (Submodule.span F (u '' (A : Set E))) +
          Module.finrank F (Submodule.span F (v '' (B : Set E)))) :
    ∃ I : Finset E, I.card = k ∧
      LinearIndependent F (fun e : I => u e.1) ∧
      LinearIndependent F (fun e : I => v e.1) := by
  let good (I : Finset E) : Prop :=
    LinearIndependent F (fun e : I => u e.1) ∧ LinearIndependent F (fun e : I => v e.1)
  have h0good : good ∅ := by
    have : IsEmpty (∅ : Finset E) := ⟨fun x => Finset.notMem_empty x.1 x.2⟩
    exact ⟨linearIndependent_empty_type, linearIndependent_empty_type⟩
  let Sgood : Finset (Finset E) := Finset.univ.filter good
  have hSne : Sgood.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0good⟩⟩
  obtain ⟨I, hIgood_mem, hImax⟩ := Finset.exists_max_image Sgood Finset.card hSne
  obtain ⟨hIu, hIv⟩ := (Finset.mem_filter.mp hIgood_mem).2
  by_cases hge : k ≤ I.card
  · obtain ⟨I0, hI0I, hI0c⟩ := Finset.exists_subset_card_eq hge
    let emb : I0 → I := fun x => ⟨x.1, hI0I x.2⟩
    have hemb : Function.Injective emb := fun a b h => Subtype.ext (Subtype.mk.inj h)
    exact ⟨I0, hI0c, hIu.comp emb hemb, hIv.comp emb hemb⟩
  · exfalso
    let SU := Submodule.span F (u '' (I : Set E))
    let SV := Submodule.span F (v '' (I : Set E))
    let X1 : Finset E := Finset.univ.filter (fun x => x ∉ I ∧ u x ∉ SU)
    let X2 : Finset E := Finset.univ.filter (fun x => x ∉ I ∧ v x ∉ SV)
    let adj : E → E → Prop := fun a b =>
      (a ∈ I ∧ b ∉ I ∧ u b ∈ SU ∧ u b ∉ Submodule.span F (u '' ((I.erase a : Finset E) : Set E))) ∨
      (a ∉ I ∧ b ∈ I ∧ v a ∈ SV ∧ v a ∉ Submodule.span F (v '' ((I.erase b : Finset E) : Set E)))
    have hX1_out : ∀ x ∈ X1, x ∉ I := fun x hx => (Finset.mem_filter.mp hx).2.1
    have hadj_bip : ∀ a b, adj a b → (a ∈ I ∧ b ∉ I) ∨ (a ∉ I ∧ b ∈ I) := by
      intro a b h; rcases h with h | h
      · exact Or.inl ⟨h.1, h.2.1⟩
      · exact Or.inr ⟨h.1, h.2.1⟩
    by_cases hreach : ∃ n : ℕ, ∃ y : E, y ∈ X2 ∧ ReachIn X1 adj n y
    · let m := Nat.find hreach
      obtain ⟨y, hyX2, hmy⟩ := Nat.find_spec hreach
      have hm_min : ∀ n < m, ∀ z : E, ReachIn X1 adj n z → z ∉ X2 := fun n hn z hnz hzX2 =>
        Nat.find_min hreach hn ⟨z, hzX2, hnz⟩
      obtain ⟨p, hp0, hpm, hadj_p⟩ := reachIn_path X1 adj m y hmy
      have hreach_p : ∀ i : Fin (m + 1), ReachIn X1 adj i.1 (p i) := fun i => by
        have h := reachIn_shift X1 adj p hadj_p 0 0 (Nat.zero_le m) hp0 i.1 (by have := i.isLt; omega)
        simpa using h
      have hpar_p : ∀ i : Fin (m + 1), (i.1 % 2 = 0 → p i ∉ I) ∧ (i.1 % 2 = 1 → p i ∈ I) := fun i =>
        reachIn_parity I X1 adj hX1_out hadj_bip i.1 (p i) (hreach_p i)
      have hm_even : m % 2 = 0 := by
        by_contra hodd
        have hm1 : m % 2 = 1 := by omega
        have hyI : y ∈ I := hpm ▸ (hpar_p ⟨m, Nat.lt_succ_self m⟩).2 hm1
        exact (Finset.mem_filter.mp hyX2).2.1 hyI
      have hno_X2 : ∀ i : Fin (m + 1), i.1 < m → p i ∉ X2 := fun i hi =>
        hm_min i.1 hi (p i) (hreach_p i)
      have hno_X1 : ∀ i : Fin (m + 1), 0 < i.1 → p i ∉ X1 := by
        intro i hi hx1
        have hsh := reachIn_shift X1 adj p hadj_p 0 i.1 (Nat.lt_succ_iff.mp i.isLt) hx1 (m - i.1) (by omega)
        have heq : (⟨i.1 + (m - i.1), by omega⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ :=
          Fin.ext (by dsimp only; omega)
        rw [heq, hpm, zero_add] at hsh
        exact hm_min (m - i.1) (by omega) y hsh hyX2
      have hno_short : ∀ i j : Fin (m + 1), i.1 + 1 < j.1 → ¬ adj (p i) (p j) := by
        intro i j hij had
        have hr1 : ReachIn X1 adj (i.1 + 1) (p j) := ⟨p i, hreach_p i, had⟩
        have hsh := reachIn_shift X1 adj p hadj_p (i.1 + 1) j.1 (Nat.lt_succ_iff.mp j.isLt) hr1 (m - j.1) (by omega)
        have heq : (⟨j.1 + (m - j.1), by omega⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ :=
          Fin.ext (by dsimp only; omega)
        rw [heq, hpm] at hsh
        exact hm_min (i.1 + 1 + (m - j.1)) (by omega) y hsh hyX2
      have hp_inj : Function.Injective p := by
        have hgo : ∀ a b : Fin (m + 1), p a = p b → a.1 < b.1 → False := by
          intro a b hab hlt
          have hr : ReachIn X1 adj a.1 (p b) := hab ▸ hreach_p a
          have hsh := reachIn_shift X1 adj p hadj_p a.1 b.1 (Nat.lt_succ_iff.mp b.isLt) hr (m - b.1) (by omega)
          have heq : (⟨b.1 + (m - b.1), by omega⟩ : Fin (m + 1)) = ⟨m, Nat.lt_succ_self m⟩ :=
            Fin.ext (by dsimp only; omega)
          rw [heq, hpm] at hsh
          exact hm_min (a.1 + (m - b.1)) (by omega) y hsh hyX2
        intro i j hij
        by_contra hne
        have hval := Fin.val_ne_of_ne hne
        rcases (by omega : i.1 < j.1 ∨ j.1 < i.1) with hlt | hlt
        · exact hgo i j hij hlt
        · exact hgo j i hij.symm hlt
      let EvIdx : Finset (Fin (m + 1)) := Finset.univ.filter (fun i => i.1 % 2 = 0)
      let OdIdx : Finset (Fin (m + 1)) := Finset.univ.filter (fun i => i.1 % 2 = 1)
      let EvenP : Finset E := EvIdx.image p
      let OddP : Finset E := OdIdx.image p
      have hOdSub : OddP ⊆ I := by
        intro e he; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
        exact (hpar_p i).2 (Finset.mem_filter.mp hi).2
      have hEvDisj : Disjoint EvenP I := by
        rw [Finset.disjoint_left]
        intro e he heI; obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
        exact (hpar_p i).1 (Finset.mem_filter.mp hi).2 heI
      have hEvCard : EvenP.card = m / 2 + 1 := by
        rw [Finset.card_image_of_injective _ hp_inj]
        calc EvIdx.card = (Finset.univ : Finset (Fin (m / 2 + 1))).card := by
              refine Finset.card_bij (fun i _ => (⟨i.1 / 2, by have := i.isLt; omega⟩ : Fin (m / 2 + 1))) ?_ ?_ ?_
              · intro _ _; exact Finset.mem_univ _
              · intro a ha b hb hab
                have ha2 := (Finset.mem_filter.mp ha).2
                have hb2 := (Finset.mem_filter.mp hb).2
                have hd := congrArg Fin.val hab; dsimp only at hd
                exact Fin.ext (by omega)
              · intro q _
                refine ⟨⟨2 * q.1, by have := q.isLt; omega⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩,
                  Fin.ext (by dsimp only; omega)⟩
          _ = m / 2 + 1 := by simp
      have hOdCard : OddP.card = m / 2 := by
        rw [Finset.card_image_of_injective _ hp_inj]
        calc OdIdx.card = (Finset.univ : Finset (Fin (m / 2))).card := by
              refine Finset.card_bij (fun i hi => (⟨i.1 / 2, by
                have := i.isLt; have := (Finset.mem_filter.mp hi).2; omega⟩ : Fin (m / 2))) ?_ ?_ ?_
              · intro _ _; exact Finset.mem_univ _
              · intro a ha b hb hab
                have ha2 := (Finset.mem_filter.mp ha).2
                have hb2 := (Finset.mem_filter.mp hb).2
                have hd := congrArg Fin.val hab; dsimp only at hd
                exact Fin.ext (by omega)
              · intro q _
                refine ⟨⟨2 * q.1 + 1, by have := q.isLt; omega⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩,
                  Fin.ext (by dsimp only; omega)⟩
          _ = m / 2 := by simp
      let I' : Finset E := (I \ OddP) ∪ EvenP
      have hI'card : I'.card = I.card + 1 := by
        have hd : Disjoint (I \ OddP) EvenP := Finset.disjoint_of_subset_left Finset.sdiff_subset hEvDisj.symm
        rw [Finset.card_union_of_disjoint hd, Finset.card_sdiff_of_subset hOdSub, hEvCard, hOdCard]
        have hle : m / 2 ≤ I.card := hOdCard ▸ Finset.card_le_card hOdSub
        omega
      have hI'u : LinearIndependent F (fun e : I' => u e.1) := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        by_contra hne_all
        push Not at hne_all
        let EvMem : ∀ i : Fin (m + 1), i.1 % 2 = 0 → p i ∈ I' := fun i hi =>
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
        let Nz : Finset (Fin (m + 1)) := Finset.univ.filter (fun i =>
          ∃ hi : i.1 % 2 = 0, g ⟨p i, EvMem i hi⟩ ≠ 0)
        by_cases hNz : Nz.Nonempty
        · let j0 := Nz.min' hNz
          have hj0_mem : j0 ∈ Nz := Finset.min'_mem Nz hNz
          obtain ⟨hj0_ev, hj0_nz⟩ := (Finset.mem_filter.mp hj0_mem).2
          have hg1 : g ⟨p j0, EvMem j0 hj0_ev⟩ = 1 := (F_cases _).resolve_left hj0_nz
          have hsum_j0 : u (p j0) = ∑ e ∈ (Finset.univ : Finset I').erase ⟨p j0, EvMem j0 hj0_ev⟩,
              g e • u e.1 := by
            have h1 := hg
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨p j0, EvMem j0 hj0_ev⟩), hg1, one_smul] at h1
            have h2 := eq_neg_of_add_eq_zero_left h1
            have hneg : ∀ x : U, -x = x := fun x => by
              have h0 : x + x = 0 := by
                have := add_smul (1 : F) (1 : F) x
                rw [z2_add_self, zero_smul, one_smul] at this
                exact this.symm
              exact (eq_neg_of_add_eq_zero_left h0).symm
            rwa [hneg] at h2
          by_cases hj0_zero : j0.1 = 0
          · have hpj0_eq : p j0 = p ⟨0, Nat.zero_lt_succ m⟩ := congrArg p (Fin.ext hj0_zero)
            have hin_SU : u (p j0) ∈ SU := by
              rw [hsum_j0]
              refine Submodule.sum_mem SU fun e he => ?_
              by_cases hge0 : g e = 0
              · rw [hge0, zero_smul]; exact SU.zero_mem
              · apply Submodule.smul_mem SU
                rcases Finset.mem_union.mp e.2 with heI | heE
                · exact Submodule.subset_span ⟨e.1, Finset.mem_coe.mpr (Finset.mem_sdiff.mp heI).1, rfl⟩
                · obtain ⟨j, hjEv, hjeq⟩ := Finset.mem_image.mp heE
                  have hj2 : j.1 % 2 = 0 := (Finset.mem_filter.mp hjEv).2
                  have hj_ne0 : 0 < j.1 := by
                    by_contra h0
                    have hj0' : j = j0 := Fin.ext (by omega)
                    exact (Finset.mem_erase.mp he).1 (Subtype.ext (hjeq.symm.trans (congrArg p hj0')))
                  have hjnotX1 := hno_X1 j hj_ne0
                  have hjnotI := (hpar_p j).1 hj2
                  simp only [X1, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hjnotX1
                  rw [← hjeq]; exact hjnotX1 hjnotI
            rw [hpj0_eq] at hin_SU
            exact (Finset.mem_filter.mp hp0).2.2 hin_SU
          · let jprev : Fin (m + 1) := ⟨j0.1 - 1, by have := j0.isLt; omega⟩
            have hadj_prev : adj (p jprev) (p j0) := by
              have h := hadj_p ⟨j0.1 - 1, by have := j0.isLt; omega⟩
              have e1 : (⟨j0.1 - 1 + 1, by have := j0.isLt; omega⟩ : Fin (m + 1)) = j0 :=
                Fin.ext (by dsimp only; omega)
              rwa [e1] at h
            have hjp_inI : p jprev ∈ I := (hpar_p jprev).2 (by dsimp [jprev]; omega)
            have hjp_not_span : u (p j0) ∉ Submodule.span F (u '' ((I.erase (p jprev) : Finset E) : Set E)) := by
              rcases hadj_prev with h | h
              · exact h.2.2.2
              · exact absurd hjp_inI h.1
            have hin_er : u (p j0) ∈ Submodule.span F (u '' ((I.erase (p jprev) : Finset E) : Set E)) := by
              rw [hsum_j0]
              refine Submodule.sum_mem _ fun e he => ?_
              by_cases hge0 : g e = 0
              · rw [hge0, zero_smul]; exact Submodule.zero_mem _
              · apply Submodule.smul_mem
                rcases Finset.mem_union.mp e.2 with heI | heE
                · obtain ⟨heI1, heNotOd⟩ := Finset.mem_sdiff.mp heI
                  have hne_prev : e.1 ≠ p jprev := fun heq =>
                    heNotOd (heq ▸ Finset.mem_image.mpr ⟨jprev, Finset.mem_filter.mpr
                      ⟨Finset.mem_univ _, by dsimp [jprev]; omega⟩, rfl⟩)
                  exact Submodule.subset_span ⟨e.1, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne_prev, heI1⟩), rfl⟩
                · obtain ⟨j, hjEv, hjeq⟩ := Finset.mem_image.mp heE
                  have hj2 : j.1 % 2 = 0 := (Finset.mem_filter.mp hjEv).2
                  have hj_in_Nz : j ∈ Nz := by
                    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2, ?_⟩
                    have : (⟨p j, EvMem j hj2⟩ : I') = e := Subtype.ext hjeq
                    rwa [this]
                  have hj_ge : j0 ≤ j := Finset.min'_le Nz j hj_in_Nz
                  have hj_ne : j ≠ j0 := fun heq =>
                    (Finset.mem_erase.mp he).1 (Subtype.ext (hjeq.symm.trans (congrArg p heq)))
                  have hj_gt : j0.1 < j.1 := by have := Fin.val_ne_of_ne hj_ne; change j0.1 ≤ j.1 at hj_ge; omega
                  have hshort := hno_short jprev j (by dsimp [jprev]; omega)
                  have hjnotX1 := hno_X1 j (by omega)
                  have hjnotI := (hpar_p j).1 hj2
                  simp only [X1, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hjnotX1
                  have hjuSU : u (p j) ∈ SU := hjnotX1 hjnotI
                  rw [← hjeq]
                  by_contra hnot
                  exact hshort (Or.inl ⟨hjp_inI, hjnotI, hjuSU, hnot⟩)
            exact hjp_not_span hin_er
        · rw [Finset.not_nonempty_iff_eq_empty] at hNz
          let gI : I → F := fun e => if h : e.1 ∈ I' then g ⟨e.1, h⟩ else 0
          have hgI_sum : ∑ e : I, gI e • u e.1 = 0 := by
            rw [← hg]
            have hsplit : ∑ e : I', g e • u e.1 = ∑ e ∈ (Finset.univ : Finset I').filter (fun e => e.1 ∈ I), g e • u e.1 := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun e _ => ?_
              by_cases heI : e.1 ∈ I
              · simp [heI]
              · simp only [heI, ↓reduceIte]
                have heEv : e.1 ∈ EvenP := (Finset.mem_union.mp e.2).resolve_left (fun h => heI (Finset.mem_sdiff.mp h).1)
                obtain ⟨j, hjEv, hjeq⟩ := Finset.mem_image.mp heEv
                have hj2 : j.1 % 2 = 0 := (Finset.mem_filter.mp hjEv).2
                have hg0 : g e = 0 := by
                  by_contra hne
                  have hmem : j ∈ Nz := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2, by
                    have : (⟨p j, EvMem j hj2⟩ : I') = e := Subtype.ext hjeq; rwa [this]⟩
                  rw [hNz] at hmem; exact Finset.notMem_empty j hmem
                rw [hg0, zero_smul]
            rw [hsplit]
            have hI_filt : ∑ e : I, gI e • u e.1 = ∑ e ∈ (Finset.univ : Finset I).filter (fun e => e.1 ∈ I'), gI e • u e.1 := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun e _ => ?_
              by_cases h : e.1 ∈ I'
              · simp [h]
              · simp [gI, h]
            rw [hI_filt]
            refine Finset.sum_bij (fun e he => ⟨e.1, (Finset.mem_filter.mp he).2⟩) ?_ ?_ ?_ ?_
            · intro e _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩
            · intro a _ b _ h; exact Subtype.ext (Subtype.mk.inj h)
            · intro b hb
              exact ⟨⟨b.1, (Finset.mem_filter.mp hb).2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, Subtype.ext rfl⟩
            · intro e he; simp [gI, (Finset.mem_filter.mp he).2]
          have hgI0 := (Fintype.linearIndependent_iff.mp hIu) gI hgI_sum
          obtain ⟨e, hene⟩ := hne_all
          rcases Finset.mem_union.mp e.2 with heI | heEv
          · have heI1 := (Finset.mem_sdiff.mp heI).1
            have := hgI0 ⟨e.1, heI1⟩
            simp [gI, e.2] at this
            exact hene this
          · obtain ⟨j, hjEv, hjeq⟩ := Finset.mem_image.mp heEv
            have hj2 : j.1 % 2 = 0 := (Finset.mem_filter.mp hjEv).2
            have hmem : j ∈ Nz := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2, by
              have : (⟨p j, EvMem j hj2⟩ : I') = e := Subtype.ext hjeq; rwa [this]⟩
            rw [hNz] at hmem; exact Finset.notMem_empty j hmem
      have hI'v : LinearIndependent F (fun e : I' => v e.1) := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        by_contra hne_all
        push Not at hne_all
        let EvMem : ∀ i : Fin (m + 1), i.1 % 2 = 0 → p i ∈ I' := fun i hi =>
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
        let Nz : Finset (Fin (m + 1)) := Finset.univ.filter (fun i =>
          ∃ hi : i.1 % 2 = 0, g ⟨p i, EvMem i hi⟩ ≠ 0)
        by_cases hNz : Nz.Nonempty
        · let j0 := Nz.max' hNz
          have hj0_mem : j0 ∈ Nz := Finset.max'_mem Nz hNz
          obtain ⟨hj0_ev, hj0_nz⟩ := (Finset.mem_filter.mp hj0_mem).2
          have hg1 : g ⟨p j0, EvMem j0 hj0_ev⟩ = 1 := (F_cases _).resolve_left hj0_nz
          have hsum_j0 : v (p j0) = ∑ e ∈ (Finset.univ : Finset I').erase ⟨p j0, EvMem j0 hj0_ev⟩,
              g e • v e.1 := by
            have h1 := hg
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨p j0, EvMem j0 hj0_ev⟩), hg1, one_smul] at h1
            have h2 := eq_neg_of_add_eq_zero_left h1
            have hneg : ∀ x : V, -x = x := fun x => by
              have h0 : x + x = 0 := by
                have := add_smul (1 : F) (1 : F) x
                rw [z2_add_self, zero_smul, one_smul] at this
                exact this.symm
              exact (eq_neg_of_add_eq_zero_left h0).symm
            rwa [hneg] at h2
          by_cases hj0_top : j0.1 = m
          · have hpj0_eq : p j0 = y := by rw [← hpm]; exact congrArg p (Fin.ext hj0_top)
            have hin_SV : v (p j0) ∈ SV := by
              rw [hsum_j0]
              refine Submodule.sum_mem SV fun e he => ?_
              by_cases hge0 : g e = 0
              · rw [hge0, zero_smul]; exact SV.zero_mem
              · apply Submodule.smul_mem SV
                rcases Finset.mem_union.mp e.2 with heI | heE
                · exact Submodule.subset_span ⟨e.1, Finset.mem_coe.mpr (Finset.mem_sdiff.mp heI).1, rfl⟩
                · obtain ⟨j, hjEv, hjeq⟩ := Finset.mem_image.mp heE
                  have hj2 : j.1 % 2 = 0 := (Finset.mem_filter.mp hjEv).2
                  have hj_ltm : j.1 < m := by
                    have := j.isLt
                    by_contra hge'
                    have hjm : j = j0 := Fin.ext (by omega)
                    exact (Finset.mem_erase.mp he).1 (Subtype.ext (hjeq.symm.trans (congrArg p hjm)))
                  have hjnotX2 := hno_X2 j hj_ltm
                  have hjnotI := (hpar_p j).1 hj2
                  simp only [X2, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hjnotX2
                  rw [← hjeq]; exact hjnotX2 hjnotI
            rw [hpj0_eq] at hin_SV
            exact (Finset.mem_filter.mp hyX2).2.2 hin_SV
          · let jnext : Fin (m + 1) := ⟨j0.1 + 1, by have := j0.isLt; omega⟩
            have hadj_next : adj (p j0) (p jnext) := hadj_p ⟨j0.1, by have := j0.isLt; omega⟩
            have hjn_inI : p jnext ∈ I := (hpar_p jnext).2 (by dsimp [jnext]; omega)
            have hjn_not_span : v (p j0) ∉ Submodule.span F (v '' ((I.erase (p jnext) : Finset E) : Set E)) := by
              rcases hadj_next with h | h
              · exact absurd hjn_inI h.2.1
              · exact h.2.2.2
            have hin_er : v (p j0) ∈ Submodule.span F (v '' ((I.erase (p jnext) : Finset E) : Set E)) := by
              rw [hsum_j0]
              refine Submodule.sum_mem _ fun e he => ?_
              by_cases hge0 : g e = 0
              · rw [hge0, zero_smul]; exact Submodule.zero_mem _
              · apply Submodule.smul_mem
                rcases Finset.mem_union.mp e.2 with heI | heE
                · obtain ⟨heI1, heNotOd⟩ := Finset.mem_sdiff.mp heI
                  have hne_next : e.1 ≠ p jnext := fun heq =>
                    heNotOd (heq ▸ Finset.mem_image.mpr ⟨jnext, Finset.mem_filter.mpr
                      ⟨Finset.mem_univ _, by dsimp [jnext]; omega⟩, rfl⟩)
                  exact Submodule.subset_span ⟨e.1, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne_next, heI1⟩), rfl⟩
                · obtain ⟨j, hjEv, hjeq⟩ := Finset.mem_image.mp heE
                  have hj2 : j.1 % 2 = 0 := (Finset.mem_filter.mp hjEv).2
                  have hj_in_Nz : j ∈ Nz := by
                    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2, ?_⟩
                    have : (⟨p j, EvMem j hj2⟩ : I') = e := Subtype.ext hjeq
                    rwa [this]
                  have hj_le : j ≤ j0 := Finset.le_max' Nz j hj_in_Nz
                  have hj_ne : j ≠ j0 := fun heq =>
                    (Finset.mem_erase.mp he).1 (Subtype.ext (hjeq.symm.trans (congrArg p heq)))
                  have hj_lt : j.1 < j0.1 := by have := Fin.val_ne_of_ne hj_ne; change j.1 ≤ j0.1 at hj_le; omega
                  have hshort := hno_short j jnext (by dsimp [jnext]; omega)
                  have hjnotX2 := hno_X2 j (by have := j0.isLt; omega)
                  have hjnotI := (hpar_p j).1 hj2
                  simp only [X2, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hjnotX2
                  have hjvSV : v (p j) ∈ SV := hjnotX2 hjnotI
                  rw [← hjeq]
                  by_contra hnot
                  exact hshort (Or.inr ⟨hjnotI, hjn_inI, hjvSV, hnot⟩)
            exact hjn_not_span hin_er
        · rw [Finset.not_nonempty_iff_eq_empty] at hNz
          let gI : I → F := fun e => if h : e.1 ∈ I' then g ⟨e.1, h⟩ else 0
          have hgI_sum : ∑ e : I, gI e • v e.1 = 0 := by
            rw [← hg]
            have hsplit : ∑ e : I', g e • v e.1 = ∑ e ∈ (Finset.univ : Finset I').filter (fun e => e.1 ∈ I), g e • v e.1 := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun e _ => ?_
              by_cases heI : e.1 ∈ I
              · simp [heI]
              · simp only [heI, ↓reduceIte]
                have heEv : e.1 ∈ EvenP := (Finset.mem_union.mp e.2).resolve_left (fun h => heI (Finset.mem_sdiff.mp h).1)
                obtain ⟨j, hjEv, hjeq⟩ := Finset.mem_image.mp heEv
                have hj2 : j.1 % 2 = 0 := (Finset.mem_filter.mp hjEv).2
                have hg0 : g e = 0 := by
                  by_contra hne
                  have hmem : j ∈ Nz := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2, by
                    have : (⟨p j, EvMem j hj2⟩ : I') = e := Subtype.ext hjeq; rwa [this]⟩
                  rw [hNz] at hmem; exact Finset.notMem_empty j hmem
                rw [hg0, zero_smul]
            rw [hsplit]
            have hI_filt : ∑ e : I, gI e • v e.1 = ∑ e ∈ (Finset.univ : Finset I).filter (fun e => e.1 ∈ I'), gI e • v e.1 := by
              rw [Finset.sum_filter]
              refine Finset.sum_congr rfl fun e _ => ?_
              by_cases h : e.1 ∈ I'
              · simp [h]
              · simp [gI, h]
            rw [hI_filt]
            refine Finset.sum_bij (fun e he => ⟨e.1, (Finset.mem_filter.mp he).2⟩) ?_ ?_ ?_ ?_
            · intro e _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩
            · intro a _ b _ h; exact Subtype.ext (Subtype.mk.inj h)
            · intro b hb
              exact ⟨⟨b.1, (Finset.mem_filter.mp hb).2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, Subtype.ext rfl⟩
            · intro e he; simp [gI, (Finset.mem_filter.mp he).2]
          have hgI0 := (Fintype.linearIndependent_iff.mp hIv) gI hgI_sum
          obtain ⟨e, hene⟩ := hne_all
          rcases Finset.mem_union.mp e.2 with heI | heEv
          · have heI1 := (Finset.mem_sdiff.mp heI).1
            have := hgI0 ⟨e.1, heI1⟩
            simp [gI, e.2] at this
            exact hene this
          · obtain ⟨j, hjEv, hjeq⟩ := Finset.mem_image.mp heEv
            have hj2 : j.1 % 2 = 0 := (Finset.mem_filter.mp hjEv).2
            have hmem : j ∈ Nz := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj2, by
              have : (⟨p j, EvMem j hj2⟩ : I') = e := Subtype.ext hjeq; rwa [this]⟩
            rw [hNz] at hmem; exact Finset.notMem_empty j hmem
      have hI'mem : I' ∈ Sgood := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI'u, hI'v⟩
      have hle := hImax I' hI'mem
      omega
    · push Not at hreach
      let B : Finset E := Finset.univ.filter (fun e => ∃ n : ℕ, ReachIn X1 adj n e)
      let A : Finset E := Finset.univ.filter (fun e => ¬ ∃ n : ℕ, ReachIn X1 adj n e)
      have hAB : A ∪ B = Finset.univ := by
        ext e; simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
      have hdisjAB : Disjoint (I ∩ A) (I ∩ B) := by
        rw [Finset.disjoint_left]
        intro e h1 h2
        exact (Finset.mem_filter.mp (Finset.mem_inter.mp h1).2).2 (Finset.mem_filter.mp (Finset.mem_inter.mp h2).2).2
      have hunAB : (I ∩ A) ∪ (I ∩ B) = I := by
        rw [← Finset.inter_union_distrib_left, hAB, Finset.inter_univ]
      have hspanA : Submodule.span F (u '' (A : Set E)) ≤ Submodule.span F (u '' ((I ∩ A : Finset E) : Set E)) := by
        rw [Submodule.span_le]
        rintro _ ⟨b, hb, rfl⟩
        have hbA : b ∈ A := Finset.mem_coe.mp hb
        by_cases hbI : b ∈ I
        · exact Submodule.subset_span ⟨b, Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨hbI, hbA⟩), rfl⟩
        · have hbnotX1 : b ∉ X1 := fun hx1 => (Finset.mem_filter.mp hbA).2 ⟨0, hx1⟩
          simp only [X1, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hbnotX1
          have hbuSU : u b ∈ SU := hbnotX1 hbI
          apply mem_span_subset_of_mem_erase u I (I ∩ A) Finset.inter_subset_left hIu (u b) hbuSU
          intro a ha
          obtain ⟨haI, haNotIA⟩ := Finset.mem_sdiff.mp ha
          have haReach : ∃ n : ℕ, ReachIn X1 adj n a := by
            by_contra hnot
            exact haNotIA (Finset.mem_inter.mpr ⟨haI, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩⟩)
          obtain ⟨n, hna⟩ := haReach
          by_contra hnot
          exact (Finset.mem_filter.mp hbA).2 ⟨n + 1, a, hna, Or.inl ⟨haI, hbI, hbuSU, hnot⟩⟩
      have hspanB : Submodule.span F (v '' (B : Set E)) ≤ Submodule.span F (v '' ((I ∩ B : Finset E) : Set E)) := by
        rw [Submodule.span_le]
        rintro _ ⟨a, ha, rfl⟩
        have haB : a ∈ B := Finset.mem_coe.mp ha
        obtain ⟨n, hna⟩ := (Finset.mem_filter.mp haB).2
        by_cases haI : a ∈ I
        · exact Submodule.subset_span ⟨a, Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨haI, haB⟩), rfl⟩
        · have hanotX2 : a ∉ X2 := fun hx2 => hreach n a hx2 hna
          simp only [X2, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hanotX2
          have havSV : v a ∈ SV := hanotX2 haI
          apply mem_span_subset_of_mem_erase v I (I ∩ B) Finset.inter_subset_left hIv (v a) havSV
          intro b hb
          obtain ⟨hbI, hbNotIB⟩ := Finset.mem_sdiff.mp hb
          have hbNotB : b ∉ B := fun hbB => hbNotIB (Finset.mem_inter.mpr ⟨hbI, hbB⟩)
          by_contra hnot
          exact hbNotB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, n + 1, a, hna, Or.inr ⟨haI, hbI, havSV, hnot⟩⟩)
      have hrA := (Submodule.finrank_mono hspanA).trans (finrank_span_image_le u (I ∩ A))
      have hrB := (Submodule.finrank_mono hspanB).trans (finrank_span_image_le v (I ∩ B))
      have htot := hall A B hAB
      have hsumI : (I ∩ A).card + (I ∩ B).card = I.card := by
        rw [← Finset.card_union_of_disjoint hdisjAB, hunAB]
      omega

lemma card_filter_mod_three_eq_1080 (t : ℕ) (a : ℕ) :
    (Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a)).card ≤ t := by
  by_cases ha : a < 3
  · have hsub : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a) ⊆
        (Finset.univ : Finset (Fin t)).image (fun q : Fin t =>
          (⟨3 * q.val + a, by omega⟩ : Fin (3 * t))) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      refine ⟨⟨i.val / 3, by omega⟩, ?_⟩
      apply Fin.ext; dsimp; omega
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  · have hemp : Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]; omega
    simp [hemp]

lemma exists_orth_zmod2_1080 (S : Submodule F (Fin 2 → F))
    (hlt : Module.finrank F S < 2) :
    ∃ α0 α1 : F, (α0 ≠ 0 ∨ α1 ≠ 0) ∧ ∀ z ∈ S, α0 * z 0 + α1 * z 1 = 0 := by
  have hnot_top : S ≠ ⊤ := by
    intro htop; rw [htop, finrank_top] at hlt
    have h2 : Module.finrank F (Fin 2 → F) = 2 := by simp
    omega
  by_cases h0 : ∀ z ∈ S, z 0 = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, fun z hz => by simp [h0 z hz]⟩
  · by_cases h1 : ∀ z ∈ S, z 1 = 0
    · exact ⟨0, 1, Or.inr one_ne_zero, fun z hz => by simp [h1 z hz]⟩
    · by_cases h01 : ∀ z ∈ S, z 0 + z 1 = 0
      · exact ⟨1, 1, Or.inl one_ne_zero, fun z hz => by simpa using h01 z hz⟩
      · exfalso
        push Not at h0 h1 h01
        rcases h0 with ⟨z0, hz0S, hz0⟩
        rcases h1 with ⟨z1, hz1S, hz1⟩
        rcases h01 with ⟨z2, hz2S, hz2⟩
        apply hnot_top; rw [eq_top_iff]; intro w _
        let e0 : Fin 2 → F := fun e => if e = 0 then 1 else 0
        let e1 : Fin 2 → F := fun e => if e = 1 then 1 else 0
        have hz : ∀ x : F, x = 0 ∨ x = 1 := F_cases
        have h11 : (1 : F) + 1 = 0 := by decide
        have h10_01 : e0 ∈ S ∧ e1 ∈ S := by
          have hz0_0 : z0 0 = 1 := (hz (z0 0)).resolve_left hz0
          have hz1_1 : z1 1 = 1 := (hz (z1 1)).resolve_left hz1
          rcases hz (z2 0) with h2a | h2a <;> rcases hz (z2 1) with h2b | h2b
          · exfalso; apply hz2; simp [h2a, h2b]
          · have hz2_e1 : z2 = e1 := by ext e; fin_cases e <;> simp [e1, h2a, h2b]
            have he1 : e1 ∈ S := hz2_e1 ▸ hz2S
            refine ⟨?_, he1⟩
            rcases hz (z0 1) with h0b | h0b
            · have : z0 = e0 := by ext e; fin_cases e <;> simp [e0, hz0_0, h0b]
              exact this ▸ hz0S
            · have : z0 + z2 = e0 := by ext e; fin_cases e <;> simp [e0, hz0_0, h0b, h2a, h2b, h11]
              exact this ▸ S.add_mem hz0S hz2S
          · have hz2_e0 : z2 = e0 := by ext e; fin_cases e <;> simp [e0, h2a, h2b]
            have he0 : e0 ∈ S := hz2_e0 ▸ hz2S
            refine ⟨he0, ?_⟩
            rcases hz (z1 0) with h1a | h1a
            · have : z1 = e1 := by ext e; fin_cases e <;> simp [e1, h1a, hz1_1]
              exact this ▸ hz1S
            · have : z1 + z2 = e1 := by ext e; fin_cases e <;> simp [e1, h1a, hz1_1, h2a, h2b, h11]
              exact this ▸ S.add_mem hz1S hz2S
          · exfalso; apply hz2; simp [h2a, h2b, h11]
        have hw_eq : w = w 0 • e0 + w 1 • e1 := by ext e; fin_cases e <;> simp [e0, e1]
        rw [hw_eq]
        exact S.add_mem (S.smul_mem _ h10_01.1) (S.smul_mem _ h10_01.2)

lemma finrank_le_card_add_k_sub_syndrome_1080
    (t k : ℕ) (P : Submodule F (Lane t))
    (hcode : ∀ x ∈ P, ∀ e : Fin 2,
      (∑ i : Fin (3 * t), if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0)
    (ZP AL IL : Finset (Fin (3 * t)))
    (hpart1 : Disjoint ZP AL) (hpart2 : Disjoint ZP IL) (hpart3 : Disjoint AL IL)
    (hcov : ZP ∪ AL ∪ IL = Finset.univ)
    (hZP : ∀ i ∈ ZP, ∀ x ∈ P, x i = 0)
    (rep : Fin k → Fin (3 * t))
    (cL : Fin (3 * t) → Fin k)
    (hrep : ∀ c : Fin k, rep c ∈ AL ∧ cL (rep c) = c)
    (hAL : ∀ i ∈ AL, ∀ x ∈ P, x i = x (rep (cL i))) :
    ∃ rP : ℕ, rP ≤ 2 ∧
      Module.finrank F P + rP ≤ IL.card + k ∧
      (rP = 0 → ∀ c : Fin k, 2 ≤ (AL.filter (fun i => cL i = c)).card) ∧
      (rP = 1 → (∀ c : Fin k, (AL.filter (fun i => cL i = c)).card = 1) →
        ∃ a : ℕ, ∀ i ∈ AL ∪ IL, i.val % 3 = a) := by
  classical
  let n := 3 * t
  let V := (IL → F) × (Fin k → F)
  let φ : P →ₗ[F] V :=
    { toFun := fun x => (fun i => x.1 i.1, fun c => x.1 (rep c))
      map_add' := fun x y => by ext <;> rfl
      map_smul' := fun a x => by ext <;> rfl }
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext; funext i
    have hi : i ∈ ZP ∪ AL ∪ IL := hcov ▸ Finset.mem_univ i
    simp only [Finset.mem_union] at hi
    rcases hi with (hi | hi) | hi
    · rw [hZP i hi x.1 x.2, hZP i hi y.1 y.2]
    · rw [hAL i hi x.1 x.2, hAL i hi y.1 y.2]; exact congrFun (congrArg Prod.snd hxy) (cL i)
    · exact congrFun (congrArg Prod.fst hxy) ⟨i, hi⟩
  let wtC (c : Fin k) (e : Fin 2) : F :=
    ∑ i ∈ AL.filter (fun i => cL i = c), if i.val % 3 = e.val ∨ i.val % 3 = 2 then (1 : F) else 0
  let σ : V →ₗ[F] (Fin 2 → F) :=
    { toFun := fun v e =>
        (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) +
        (∑ c : Fin k, wtC c e * v.2 c)
      map_add' := fun u v => by
        ext e
        change (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i + v.1 i else (0 : F)) +
            (∑ c : Fin k, wtC c e * (u.2 c + v.2 c)) =
          ((∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i else 0) +
            (∑ c : Fin k, wtC c e * u.2 c)) +
          ((∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) +
            (∑ c : Fin k, wtC c e * v.2 c))
        have h1 : ∀ i : IL, (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i + v.1 i else (0 : F)) =
            (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then u.1 i else 0) +
            (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) := by
          intro i; split_ifs <;> simp
        simp only [h1, Finset.sum_add_distrib, mul_add]; ring
      map_smul' := fun a v => by
        ext e
        change (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then a * v.1 i else (0 : F)) +
            (∑ c : Fin k, wtC c e * (a * v.2 c)) =
          a * ((∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) +
            (∑ c : Fin k, wtC c e * v.2 c))
        have h1 : ∀ i : IL, (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then a * v.1 i else (0 : F)) =
            a * (if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then v.1 i else 0) := by
          intro i; split_ifs <;> simp
        simp only [h1, ← Finset.mul_sum]
        have h2 : ∀ c : Fin k, wtC c e * (a * v.2 c) = a * (wtC c e * v.2 c) := fun c => by ring
        simp only [h2, ← Finset.mul_sum]; ring }
  have hcomp : σ.comp φ = 0 := by
    apply LinearMap.ext; intro x; ext e
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, σ, φ,
      LinearMap.coe_mk, AddHom.coe_mk]
    have hsum_all : (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) = 0 :=
      hcode x.1 x.2 e
    have hsplit : (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) =
        (∑ i ∈ ZP, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) +
        (∑ i ∈ AL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) +
        (∑ i ∈ IL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) := by
      rw [← Finset.sum_union hpart1, ← Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hpart2, hpart3⟩),
        hcov]
    have hZ0 : (∑ i ∈ ZP, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) = 0 := by
      apply Finset.sum_eq_zero; intro i hi; simp [hZP i hi x.1 x.2]
    have hIL_eq : (∑ i : IL, if i.1.val % 3 = e.val ∨ i.1.val % 3 = 2 then x.1 i.1 else (0 : F)) =
        ∑ i ∈ IL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F) :=
      Finset.sum_coe_sort IL (fun i => if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F))
    have hAL_eq : (∑ c : Fin k, wtC c e * x.1 (rep c)) =
        ∑ i ∈ AL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F) := by
      have hfib : ∑ c : Fin k, ∑ i ∈ AL.filter (fun i => cL i = c),
          (if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F)) =
          ∑ i ∈ AL, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x.1 i else (0 : F) := by
        rw [← Finset.sum_biUnion]
        · congr 1; ext i; simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
          exact ⟨fun ⟨_, hi, _⟩ => hi, fun hi => ⟨cL i, hi, rfl⟩⟩
        · intro c1 _ c2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
          intro i h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      rw [← hfib]
      refine Finset.sum_congr rfl fun c _ => ?_
      dsimp [wtC]; rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hci : cL i = c := (Finset.mem_filter.mp hi).2
      have hxi : x.1 i = x.1 (rep c) := hci ▸ hAL i (Finset.mem_filter.mp hi).1 x.1 x.2
      rw [hxi]; split_ifs <;> simp
    rw [hIL_eq, hAL_eq]; rw [hZ0, zero_add] at hsplit; rw [add_comm, ← hsplit, hsum_all]
  let rP := Module.finrank F (LinearMap.range σ)
  refine ⟨rP, ?_, ?_, ?_, ?_⟩
  · have hle := Submodule.finrank_le (LinearMap.range σ); simpa using hle
  · have hsub : LinearMap.range φ ≤ LinearMap.ker σ := by
      rintro _ ⟨x, rfl⟩; rw [LinearMap.mem_ker]; exact LinearMap.congr_fun hcomp x
    have h1 : Module.finrank F P = Module.finrank F (LinearMap.range φ) :=
      (LinearEquiv.ofInjective φ hφ_inj).finrank_eq
    have h2 : Module.finrank F (LinearMap.range φ) ≤ Module.finrank F (LinearMap.ker σ) :=
      Submodule.finrank_mono hsub
    have h3 : Module.finrank F (LinearMap.range σ) + Module.finrank F (LinearMap.ker σ) =
      Module.finrank F V := LinearMap.finrank_range_add_finrank_ker σ
    have hV : Module.finrank F V = IL.card + k := by simp [V, Module.finrank_prod, Fintype.card_coe]
    change Module.finrank F P + rP ≤ IL.card + k; omega
  · intro hr0 c
    have hker_all : LinearMap.range σ = ⊥ := Submodule.finrank_eq_zero.mp hr0
    have hσ0 : ∀ v : V, σ v = 0 := fun v => (Submodule.mem_bot F).mp (hker_all ▸ ⟨v, rfl⟩)
    have hwt0 : ∀ e : Fin 2, wtC c e = 0 := fun e => by
      let v : V := (0, fun c' => if c' = c then 1 else 0)
      have hv := congrFun (hσ0 v) e; simpa [σ, v] using hv
    by_contra hlt; push Not at hlt
    have hmem : rep c ∈ AL.filter (fun i => cL i = c) := Finset.mem_filter.mpr (hrep c)
    have hsing : AL.filter (fun i => cL i = c) = {rep c} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hmem, fun j hj => ?_⟩
      by_contra hne
      have h2 : ({rep c, j} : Finset (Fin n)).card ≤ (AL.filter (fun i => cL i = c)).card :=
        Finset.card_le_card (by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
      rw [Finset.card_pair (Ne.symm hne)] at h2; omega
    have h0 := hwt0 0; have h1 := hwt0 1
    dsimp [wtC] at h0 h1; rw [hsing, Finset.sum_singleton] at h0 h1
    have hmod : (rep c).val % 3 = 0 ∨ (rep c).val % 3 = 1 ∨ (rep c).val % 3 = 2 := by omega
    rcases hmod with hm | hm | hm
    · simp [hm] at h0
    · simp [hm] at h1
    · simp [hm] at h0
  · intro hr1 hcard1
    obtain ⟨α0, α1, hαne, horthS⟩ := exists_orth_zmod2_1080 (LinearMap.range σ) (by change rP < 2; omega)
    have horth : ∀ v : V, α0 * σ v 0 + α1 * σ v 1 = 0 := fun v => horthS (σ v) ⟨v, rfl⟩
    have hcoeff : ∀ i ∈ AL ∪ IL,
        α0 * (if i.val % 3 = 0 ∨ i.val % 3 = 2 then (1 : F) else 0) +
        α1 * (if i.val % 3 = 1 ∨ i.val % 3 = 2 then (1 : F) else 0) = 0 := by
      intro i hi
      rcases Finset.mem_union.mp hi with hiA | hiI
      · let c := cL i
        have hsing : AL.filter (fun j => cL j = c) = {i} := by
          have hc1 := hcard1 c
          have hmem : i ∈ AL.filter (fun j => cL j = c) := Finset.mem_filter.mpr ⟨hiA, rfl⟩
          apply Finset.eq_singleton_iff_unique_mem.mpr
          refine ⟨hmem, fun j hj => ?_⟩
          by_contra hne
          have h2 : ({i, j} : Finset (Fin n)).card ≤ (AL.filter (fun x => cL x = c)).card :=
            Finset.card_le_card (by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption)
          rw [Finset.card_pair (Ne.symm hne)] at h2; omega
        let v : V := (0, fun c' => if c' = c then 1 else 0)
        have hv := horth v
        have hσv : ∀ e : Fin 2, σ v e = if i.val % 3 = e.val ∨ i.val % 3 = 2 then (1 : F) else 0 := by
          intro e; have h1 : σ v e = wtC c e := by simp [σ, v]
          rw [h1]; dsimp [wtC]; rw [hsing, Finset.sum_singleton]
        rw [hσv 0, hσv 1] at hv; simpa using hv
      · let v : V := (fun j : IL => if j.1 = i then 1 else 0, 0)
        have hv := horth v
        have hsum_e : ∀ e : Fin 2,
            (∑ j : IL, if j.1.val % 3 = e.val ∨ j.1.val % 3 = 2 then v.1 j else (0 : F)) =
            if i.val % 3 = e.val ∨ i.val % 3 = 2 then 1 else 0 := by
          intro e
          rw [Finset.sum_eq_single ⟨i, hiI⟩]
          · simp [v]
          · intro b _ hbi; have hne : b.1 ≠ i := fun h => hbi (Subtype.ext h); simp [v, hne]
          · intro h; exact (h (Finset.mem_univ _)).elim
        simp only [σ, LinearMap.coe_mk, AddHom.coe_mk, hsum_e, v] at hv; simpa using hv
    rcases F_cases α0 with rfl | rfl <;> rcases F_cases α1 with rfl | rfl
    · simp at hαne
    · refine ⟨0, fun i hi => ?_⟩
      have hc := hcoeff i hi
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with hm | hm | hm <;> simp [hm] at hc ⊢
    · refine ⟨1, fun i hi => ?_⟩
      have hc := hcoeff i hi
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with hm | hm | hm <;> simp [hm] at hc ⊢
    · refine ⟨2, fun i hi => ?_⟩
      have hc := hcoeff i hi
      have hm : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
      rcases hm with hm | hm | hm
      · simp [hm] at hc
      · simp [hm] at hc
      · exact hm

lemma cycle_ends_bound_1080
    (n k : ℕ) (hn_pos : 0 < n) (hk : 3 ≤ k)
    (ZP ZQ AL AR IL IR : Finset (Fin n))
    (hAL_disj_ZP : Disjoint ZP AL) (hIL_disj_ZP : Disjoint ZP IL) (hIL_disj_AL : Disjoint AL IL)
    (hPcov : ZP ∪ AL ∪ IL = Finset.univ)
    (hAR_disj_ZQ : Disjoint ZQ AR) (hIR_disj_ZQ : Disjoint ZQ IR) (hIR_disj_AR : Disjoint AR IR)
    (hQcov : ZQ ∪ AR ∪ IR = Finset.univ)
    (Eact : Finset (Fin (2 * n)))
    (left right : Fin (2 * n) → Fin n)
    (hleft : ∀ e : Fin (2 * n), left e = ⟨((e.val + 1) / 2) % n, Nat.mod_lt _ hn_pos⟩)
    (hright : ∀ e : Fin (2 * n), right e = ⟨(e.val / 2) % n, Nat.mod_lt _ hn_pos⟩)
    (hEact_def : ∀ e : Fin (2 * n), e ∈ Eact ↔ left e ∉ ZP ∧ right e ∉ ZQ)
    (hAL_mem : ∀ e ∈ Eact, left e ∈ AL)
    (hAR_mem : ∀ e ∈ Eact, right e ∈ AR)
    (s : Fin k → Fin (2 * n))
    (hs_act : ∀ c : Fin k, s c ∈ Eact)
    (cL cR : Fin n → Fin k)
    (hrepL : ∀ c : Fin k, left (s c) ∈ AL ∧ cL (left (s c)) = c)
    (hedge_same_col : ∀ e ∈ Eact, cL (left e) = cR (right e)) :
    ∃ nLive nDead nEnds : ℕ,
      nLive + nDead = 2 * n ∧
      nLive = (AL.card + IL.card) + (AR.card + IR.card) ∧
      nEnds ≤ nDead ∧
      nEnds ≤ nLive ∧
      IL.card + IR.card + k ≤ nEnds := by
  classical
  have hkpos : 0 < k := by omega
  let nxt : Fin (2 * n) → Fin (2 * n) := fun v => ⟨(v.val + 1) % (2 * n), Nat.mod_lt _ (by omega)⟩
  have hnxt_inj : Function.Injective nxt := by
    intro v1 v2 heq
    have hval : (v1.val + 1) % (2 * n) = (v2.val + 1) % (2 * n) := congrArg Fin.val heq
    apply Fin.ext; have hv1 := v1.2; have hv2 := v2.2
    by_cases h1 : v1.val + 1 < 2 * n <;> by_cases h2 : v2.val + 1 < 2 * n
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hval; omega
    · have h2eq : v2.val + 1 = 2 * n := by omega
      rw [Nat.mod_eq_of_lt h1, h2eq, Nat.mod_self] at hval; omega
    · have h1eq : v1.val + 1 = 2 * n := by omega
      rw [h1eq, Nat.mod_self, Nat.mod_eq_of_lt h2] at hval; omega
    · omega
  let isLive : Fin (2 * n) → Prop := fun v =>
    if v.val % 2 = 0 then (⟨v.val / 2, by omega⟩ : Fin n) ∉ ZP
    else (⟨v.val / 2, by omega⟩ : Fin n) ∉ ZQ
  let Live : Finset (Fin (2 * n)) := Finset.univ.filter (fun v => isLive v)
  let Dead : Finset (Fin (2 * n)) := Finset.univ.filter (fun v => ¬ isLive v)
  have hLive_Dead : Live.card + Dead.card = 2 * n := by
    have hdisj : Disjoint Live Dead := by rw [Finset.disjoint_filter]; intro v _ h1 h2; exact h2 h1
    have hun : Live ∪ Dead = Finset.univ := by
      ext v; simp only [Live, Dead, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
    rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_univ, Fintype.card_fin]
  have hLive_card : Live.card = (AL.card + IL.card) + (AR.card + IR.card) := by
    let UP := AL ∪ IL; let UQ := AR ∪ IR
    have hUP : UP.card = AL.card + IL.card := Finset.card_union_of_disjoint hIL_disj_AL
    have hUQ : UQ.card = AR.card + IR.card := Finset.card_union_of_disjoint hIR_disj_AR
    have hUP_iff : ∀ i : Fin n, i ∈ UP ↔ i ∉ ZP := by
      intro i; have hi : i ∈ ZP ∪ AL ∪ IL := hPcov ▸ Finset.mem_univ i
      simp only [UP, Finset.mem_union] at hi ⊢
      constructor
      · rintro (hA | hI) hZ
        · exact Finset.disjoint_left.mp hAL_disj_ZP hZ hA
        · exact Finset.disjoint_left.mp hIL_disj_ZP hZ hI
      · intro hnotZ; rcases hi with (hZ | hA) | hI
        · exact absurd hZ hnotZ
        · exact Or.inl hA
        · exact Or.inr hI
    have hUQ_iff : ∀ j : Fin n, j ∈ UQ ↔ j ∉ ZQ := by
      intro j; have hj : j ∈ ZQ ∪ AR ∪ IR := hQcov ▸ Finset.mem_univ j
      simp only [UQ, Finset.mem_union] at hj ⊢
      constructor
      · rintro (hA | hI) hZ
        · exact Finset.disjoint_left.mp hAR_disj_ZQ hZ hA
        · exact Finset.disjoint_left.mp hIR_disj_ZQ hZ hI
      · intro hnotZ; rcases hj with (hZ | hA) | hI
        · exact absurd hZ hnotZ
        · exact Or.inl hA
        · exact Or.inr hI
    let Leven := UP.image (fun i : Fin n => (⟨2 * i.val, by omega⟩ : Fin (2 * n)))
    let Lodd := UQ.image (fun j : Fin n => (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)))
    have hLeven_card : Leven.card = UP.card :=
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
    have hLodd_card : Lodd.card = UQ.card :=
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
    have hdisj_eo : Disjoint Leven Lodd := by
      rw [Finset.disjoint_left]; intro v h1 h2
      rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨j, _, heq⟩
      have := congrArg Fin.val heq; dsimp at this; omega
    have hLive_eq : Live = Leven ∪ Lodd := by
      ext v
      simp only [Live, Leven, Lodd, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, isLive]
      by_cases hv : v.val % 2 = 0
      · simp only [hv, ↓reduceIte]
        constructor
        · intro hnotZ; left
          refine ⟨⟨v.val / 2, by omega⟩, (hUP_iff _).mpr hnotZ, Fin.ext (by dsimp; omega)⟩
        · rintro (⟨i, hi, heq⟩ | ⟨j, _, heq⟩)
          · have hval : 2 * i.val = v.val := congrArg Fin.val heq
            have hi' : (⟨v.val / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
            rw [hi']; exact (hUP_iff i).mp hi
          · have hval : 2 * j.val + 1 = v.val := congrArg Fin.val heq; omega
      · simp only [hv, ↓reduceIte]
        constructor
        · intro hnotZ; right
          refine ⟨⟨v.val / 2, by omega⟩, (hUQ_iff _).mpr hnotZ, Fin.ext (by dsimp; omega)⟩
        · rintro (⟨i, _, heq⟩ | ⟨j, hj, heq⟩)
          · have hval : 2 * i.val = v.val := congrArg Fin.val heq; omega
          · have hval : 2 * j.val + 1 = v.val := congrArg Fin.val heq
            have hj' : (⟨v.val / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
            rw [hj']; exact (hUQ_iff j).mp hj
    rw [hLive_eq, Finset.card_union_of_disjoint hdisj_eo, hLeven_card, hLodd_card, hUP, hUQ]
  have hEact_iff : ∀ e : Fin (2 * n), e ∈ Eact ↔ isLive e ∧ isLive (nxt e) := by
    intro e; rw [hEact_def e, hleft e, hright e]; simp only [isLive, nxt]
    by_cases he : e.val % 2 = 0
    · have he1 : (e.val + 1) % (2 * n) = e.val + 1 := Nat.mod_eq_of_lt (by omega)
      have he1odd : (e.val + 1) % 2 ≠ 0 := by omega
      simp only [he, he1, he1odd, ↓reduceIte]
      have hL : (⟨((e.val + 1) / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = ⟨e.val / 2, by omega⟩ :=
        Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      have hR : (⟨(e.val / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = ⟨(e.val + 1) / 2, by omega⟩ :=
        Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      rw [hL, hR]
    · have hne2 : (e.val + 1) % (2 * n) % 2 = 0 := by
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop]; omega
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
      simp only [he, hne2, ↓reduceIte]
      have hR : (⟨(e.val / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = ⟨e.val / 2, by omega⟩ :=
        Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)])
      have hmod_lt : (e.val + 1) % (2 * n) < 2 * n := Nat.mod_lt _ (by omega)
      have hL : (⟨((e.val + 1) / 2) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) =
          ⟨((e.val + 1) % (2 * n)) / 2, by omega⟩ := by
        apply Fin.ext; dsimp
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop, Nat.mod_eq_of_lt (by omega)]
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
          have : (2 * n) / 2 = n := by omega
          rw [this, Nat.mod_self]
      rw [hL, hR, and_comm]
  let Ends : Finset (Fin (2 * n)) := Live.filter (fun v => ¬ isLive (nxt v))
  have hEnds_le_Dead : Ends.card ≤ Dead.card := by
    refine Finset.card_le_card_of_injOn nxt ?_ (fun x _ y _ h => hnxt_inj h)
    intro v hv
    simp only [Finset.mem_coe, Ends, Dead, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  have hEnds_le_Live : Ends.card ≤ Live.card := Finset.card_filter_le _ _
  let isColV : Fin (2 * n) → Prop := fun v =>
    if v.val % 2 = 0 then (⟨v.val / 2, by omega⟩ : Fin n) ∈ AL
    else (⟨v.val / 2, by omega⟩ : Fin n) ∈ AR
  let vcol : Fin (2 * n) → Fin k := fun v =>
    if v.val % 2 = 0 then cL ⟨v.val / 2, by omega⟩ else cR ⟨v.val / 2, by omega⟩
  have hstep_col : ∀ e : Fin (2 * n), isLive e → isLive (nxt e) →
      isColV e ∧ isColV (nxt e) ∧ vcol e = vcol (nxt e) := by
    intro e h1 h2
    have heA : e ∈ Eact := (hEact_iff e).mpr ⟨h1, h2⟩
    have hcol := hedge_same_col e heA
    have hmemL : left e ∈ AL := hAL_mem e heA
    have hmemR : right e ∈ AR := hAR_mem e heA
    simp only [isColV, vcol, nxt]
    by_cases he : e.val % 2 = 0
    · have he1 : (e.val + 1) % (2 * n) = e.val + 1 := Nat.mod_eq_of_lt (by omega)
      have he1odd : (e.val + 1) % 2 ≠ 0 := by omega
      simp only [he, he1, he1odd, ↓reduceIte]
      have hL : left e = ⟨e.val / 2, by omega⟩ := by
        rw [hleft e]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      have hR : right e = ⟨(e.val + 1) / 2, by omega⟩ := by
        rw [hright e]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      rw [← hL, ← hR]; exact ⟨hmemL, hmemR, hcol⟩
    · have hne2 : (e.val + 1) % (2 * n) % 2 = 0 := by
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop]; omega
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
      simp only [he, hne2, ↓reduceIte]
      have hR : right e = ⟨e.val / 2, by omega⟩ := by
        rw [hright e]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)])
      have hmod_lt : (e.val + 1) % (2 * n) < 2 * n := Nat.mod_lt _ (by omega)
      have hL : left e = ⟨((e.val + 1) % (2 * n)) / 2, by omega⟩ := by
        rw [hleft e]; apply Fin.ext; dsimp
        by_cases htop : e.val + 1 < 2 * n
        · rw [Nat.mod_eq_of_lt htop, Nat.mod_eq_of_lt (by omega)]
        · have : e.val + 1 = 2 * n := by omega
          rw [this, Nat.mod_self]
          have : (2 * n) / 2 = n := by omega
          rw [this, Nat.mod_self]
      rw [← hL, ← hR]; exact ⟨hmemR, hmemL, hcol.symm⟩
  have hEnds_color : ∀ c : Fin k, ∃ v ∈ Ends, isColV v ∧ vcol v = c := by
    intro c
    let v0 : Fin (2 * n) := ⟨2 * (left (s c)).val, by omega⟩
    have hv0_live : isLive v0 := by
      simp only [isLive, v0, Nat.mul_mod_right, ↓reduceIte]
      have h1 : (⟨2 * (left (s c)).val / 2, by omega⟩ : Fin n) = left (s c) := Fin.ext (by dsimp; omega)
      rw [h1]; exact ((hEact_def (s c)).mp (hs_act c)).1
    have hv0_col : isColV v0 ∧ vcol v0 = c := by
      simp only [isColV, vcol, v0, Nat.mul_mod_right, ↓reduceIte]
      have h1 : (⟨2 * (left (s c)).val / 2, by omega⟩ : Fin n) = left (s c) := Fin.ext (by dsimp; omega)
      rw [h1]; exact hrepL c
    have hex_dead : ∃ d : ℕ, ¬ isLive (nxt^[d] v0) := by
      by_contra hall; push Not at hall
      have hsame : ∀ d : ℕ, vcol (nxt^[d] v0) = c := by
        intro d; induction d with
        | zero => exact hv0_col.2
        | succ d ih =>
          rw [Function.iterate_succ_apply']
          have hst := hstep_col (nxt^[d] v0) (hall d)
            ((Function.iterate_succ_apply' nxt d v0).symm ▸ hall (d + 1))
          rw [← hst.2.2, ih]
      have hiter_val : ∀ d : ℕ, (nxt^[d] v0).val = (v0.val + d) % (2 * n) := by
        intro d; induction d with
        | zero => simp [Nat.mod_eq_of_lt v0.2]
        | succ d ih =>
          rw [Function.iterate_succ_apply']; dsimp [nxt]; rw [ih, Nat.mod_add_mod, add_assoc]
      let c' : Fin k := ⟨(c.val + 1) % k, Nat.mod_lt _ hkpos⟩
      have hc'ne : c' ≠ c := by
        intro heq; have hv : (c.val + 1) % k = c.val := congrArg Fin.val heq; have hc2 := c.2
        by_cases htop : c.val + 1 < k
        · rw [Nat.mod_eq_of_lt htop] at hv; omega
        · have : c.val + 1 = k := by omega
          rw [this, Nat.mod_self] at hv; omega
      let w0 : Fin (2 * n) := ⟨2 * (left (s c')).val, by omega⟩
      let d0 : ℕ := (w0.val + 2 * n - v0.val) % (2 * n)
      have hhit : nxt^[d0] v0 = w0 := by
        apply Fin.ext; rw [hiter_val d0]; have hv0lt := v0.2; have hw0lt := w0.2
        dsimp [d0]; rw [Nat.add_mod_mod]
        have : v0.val + (w0.val + 2 * n - v0.val) = w0.val + 2 * n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hw0lt]
      have h1 := hsame d0; rw [hhit] at h1
      have h2 : vcol w0 = c' := by
        simp only [vcol, w0, Nat.mul_mod_right, ↓reduceIte]
        have heq : (⟨2 * (left (s c')).val / 2, by omega⟩ : Fin n) = left (s c') := Fin.ext (by dsimp; omega)
        rw [heq]; exact (hrepL c').2
      rw [h2] at h1; exact hc'ne h1
    let d0 := Nat.find hex_dead
    have hd0_spec : ¬ isLive (nxt^[d0] v0) := Nat.find_spec hex_dead
    have hd0_pos : 0 < d0 := by
      by_contra h0; have : d0 = 0 := by omega
      rw [this] at hd0_spec; exact hd0_spec hv0_live
    have hlive_lt : ∀ m < d0, isLive (nxt^[m] v0) := fun m hm =>
      by_contra fun h => Nat.find_min hex_dead hm h
    have hprop_lt : ∀ m < d0, isColV (nxt^[m] v0) ∧ vcol (nxt^[m] v0) = c := by
      intro m hm; induction m with
      | zero => exact hv0_col
      | succ m ih =>
        rw [Function.iterate_succ_apply']
        have hst := hstep_col (nxt^[m] v0) (hlive_lt m (by omega))
          ((Function.iterate_succ_apply' nxt m v0).symm ▸ hlive_lt (m + 1) hm)
        exact ⟨hst.2.1, hst.2.2.symm.trans (ih (by omega)).2⟩
    let v := nxt^[d0 - 1] v0
    have hv_live : isLive v := hlive_lt (d0 - 1) (by omega)
    have hv_nxt : ¬ isLive (nxt v) := by
      have : nxt v = nxt^[d0] v0 := by
        dsimp [v]; rw [← Function.iterate_succ_apply' nxt (d0 - 1) v0]; congr 1; omega
      rw [this]; exact hd0_spec
    have hv_col := hprop_lt (d0 - 1) (by omega)
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_live⟩, hv_nxt⟩,
      hv_col.1, hv_col.2⟩
  let E_IL := IL.image (fun i : Fin n => (⟨2 * i.val, by omega⟩ : Fin (2 * n)))
  let E_IR := IR.image (fun j : Fin n => (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)))
  let E_C := (Finset.univ : Finset (Fin k)).image (fun c => Classical.choose (hEnds_color c))
  have hEIL_sub : E_IL ⊆ Ends := by
    intro v hv; rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
    have hi_notZ : i ∉ ZP := Finset.disjoint_right.mp hIL_disj_ZP hi
    have hi_notA : i ∉ AL := Finset.disjoint_right.mp hIL_disj_AL hi
    have hlive : isLive ⟨2 * i.val, by omega⟩ := by
      simp only [isLive, Nat.mul_mod_right, ↓reduceIte]
      have : (⟨2 * i.val / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
      rw [this]; exact hi_notZ
    have hdead : ¬ isLive (nxt ⟨2 * i.val, by omega⟩) := by
      intro hl2
      have heA : (⟨2 * i.val, by omega⟩ : Fin (2 * n)) ∈ Eact := (hEact_iff _).mpr ⟨hlive, hl2⟩
      have hleft_i : left ⟨2 * i.val, by omega⟩ = i := by
        rw [hleft]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      exact hi_notA (hleft_i ▸ hAL_mem _ heA)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlive⟩, hdead⟩
  have hEIR_sub : E_IR ⊆ Ends := by
    intro v hv; rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
    have hj_notZ : j ∉ ZQ := Finset.disjoint_right.mp hIR_disj_ZQ hj
    have hj_notA : j ∉ AR := Finset.disjoint_right.mp hIR_disj_AR hj
    have hlive : isLive ⟨2 * j.val + 1, by omega⟩ := by
      have hodd : (2 * j.val + 1) % 2 ≠ 0 := by omega
      simp only [isLive, hodd, ↓reduceIte]
      have : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
      rw [this]; exact hj_notZ
    have hdead : ¬ isLive (nxt ⟨2 * j.val + 1, by omega⟩) := by
      intro hl2
      have heA : (⟨2 * j.val + 1, by omega⟩ : Fin (2 * n)) ∈ Eact := (hEact_iff _).mpr ⟨hlive, hl2⟩
      have hright_j : right ⟨2 * j.val + 1, by omega⟩ = j := by
        rw [hright]; exact Fin.ext (by dsimp; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      exact hj_notA (hright_j ▸ hAR_mem _ heA)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlive⟩, hdead⟩
  have hEC_sub : E_C ⊆ Ends := by
    intro v hv; rcases Finset.mem_image.mp hv with ⟨c, _, rfl⟩
    exact (Classical.choose_spec (hEnds_color c)).1
  have hEIL_card : E_IL.card = IL.card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
  have hEIR_card : E_IR.card = IR.card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega))
  have hEC_card : E_C.card = k := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro c1 c2 h; dsimp only at h
      have h1 := (Classical.choose_spec (hEnds_color c1)).2.2
      have h2 := (Classical.choose_spec (hEnds_color c2)).2.2
      rw [h] at h1; exact h1.symm.trans h2
  have hd1 : Disjoint E_IL E_IR := by
    rw [Finset.disjoint_left]; intro v h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨j, _, heq⟩
    have := congrArg Fin.val heq; dsimp at this; omega
  have hd2 : Disjoint E_IL E_C := by
    rw [Finset.disjoint_left]; intro v h1 h2
    rcases Finset.mem_image.mp h1 with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨c, _, heq⟩
    have hcolV := (Classical.choose_spec (hEnds_color c)).2.1
    rw [heq] at hcolV; simp only [isColV, Nat.mul_mod_right, ↓reduceIte] at hcolV
    have hi' : (⟨2 * i.val / 2, by omega⟩ : Fin n) = i := Fin.ext (by dsimp; omega)
    rw [hi'] at hcolV; exact Finset.disjoint_right.mp hIL_disj_AL hi hcolV
  have hd3 : Disjoint E_IR E_C := by
    rw [Finset.disjoint_left]; intro v h1 h2
    rcases Finset.mem_image.mp h1 with ⟨j, hj, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨c, _, heq⟩
    have hcolV := (Classical.choose_spec (hEnds_color c)).2.1
    rw [heq] at hcolV; have hodd : (2 * j.val + 1) % 2 ≠ 0 := by omega
    simp only [isColV, hodd, ↓reduceIte] at hcolV
    have hj' : (⟨(2 * j.val + 1) / 2, by omega⟩ : Fin n) = j := Fin.ext (by dsimp; omega)
    rw [hj'] at hcolV; exact Finset.disjoint_right.mp hIR_disj_AR hj hcolV
  have hEnds_ge : IL.card + IR.card + k ≤ Ends.card := by
    have hsub : E_IL ∪ E_IR ∪ E_C ⊆ Ends :=
      Finset.union_subset (Finset.union_subset hEIL_sub hEIR_sub) hEC_sub
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd2, hd3⟩),
      Finset.card_union_of_disjoint hd1, hEIL_card, hEIR_card, hEC_card] at hcard
    exact hcard
  exact ⟨Live.card, Dead.card, Ends.card, hLive_Dead, hLive_card, hEnds_le_Dead, hEnds_le_Live, hEnds_ge⟩

lemma main_1080 {t : ℕ} (ht : 0 < t) {k : ℕ} (hk : 3 ≤ k)
    (P Q : Submodule F (Lane t)) (hP : P ≤ codeSub t) (hQ : Q ≤ codeSub t)
    (s : Fin k → Fin (2 * (3 * t)))
    (hPsurj : Function.Surjective (fun x : P => fun c : Fin k => x.1 (ixn (3 * t) (by omega) (((s c).val + 1) / 2))))
    (hQsurj : Function.Surjective (fun y : Q => fun c : Fin k => y.1 (ixn (3 * t) (by omega) ((s c).val / 2))))
    (hedge : ∀ e : Fin (2 * (3 * t)),
      (∀ x : P, x.1 (ixn (3 * t) (by omega) ((e.val + 1) / 2)) = 0) ∨
      (∀ y : Q, y.1 (ixn (3 * t) (by omega) (e.val / 2)) = 0) ∨
      ∃ c : Fin k,
        (∀ x : P, x.1 (ixn (3 * t) (by omega) ((e.val + 1) / 2)) = x.1 (ixn (3 * t) (by omega) (((s c).val + 1) / 2))) ∧
        (∀ y : Q, y.1 (ixn (3 * t) (by omega) (e.val / 2)) = y.1 (ixn (3 * t) (by omega) ((s c).val / 2)))) :
    2 * (Module.finrank F P + Module.finrank F Q) + 5 ≤ 2 * (3 * t) + k := by
  classical
  let n := 3 * t
  have hn_pos : 0 < n := by omega
  let left : Fin (2 * n) → Fin n := fun e => ixn n hn_pos ((e.val + 1) / 2)
  let right : Fin (2 * n) → Fin n := fun e => ixn n hn_pos (e.val / 2)
  have hPcode : ∀ x ∈ P, ∀ e : Fin 2,
      (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then x i else 0) = 0 :=
    fun x hx e => congrFun (hP hx) e
  have hQcode : ∀ y ∈ Q, ∀ e : Fin 2,
      (∑ i : Fin n, if i.val % 3 = e.val ∨ i.val % 3 = 2 then y i else 0) = 0 :=
    fun y hy e => congrFun (hQ hy) e
  have hPdist : ∀ c1 c2 : Fin k, (∀ x : P, x.1 (left (s c1)) = x.1 (left (s c2))) → c1 = c2 := by
    intro c1 c2 heq; by_contra hne
    obtain ⟨x, hx⟩ := hPsurj (fun c => if c = c1 then (1 : F) else 0)
    have h1 : x.1 (left (s c1)) = 1 := by simpa [left] using congrFun hx c1
    have h2 : x.1 (left (s c2)) = 0 := by simpa [left, Ne.symm hne] using congrFun hx c2
    rw [heq x] at h1; rw [h1] at h2; exact one_ne_zero h2
  have hQdist : ∀ c1 c2 : Fin k, (∀ y : Q, y.1 (right (s c1)) = y.1 (right (s c2))) → c1 = c2 := by
    intro c1 c2 heq; by_contra hne
    obtain ⟨y, hy⟩ := hQsurj (fun c => if c = c1 then (1 : F) else 0)
    have h1 : y.1 (right (s c1)) = 1 := by simpa [right] using congrFun hy c1
    have h2 : y.1 (right (s c2)) = 0 := by simpa [right, Ne.symm hne] using congrFun hy c2
    rw [heq y] at h1; rw [h1] at h2; exact one_ne_zero h2
  have hPnz : ∀ c : Fin k, ¬ (∀ x : P, x.1 (left (s c)) = 0) := by
    intro c h0; obtain ⟨x, hx⟩ := hPsurj (fun _ => (1 : F))
    have h1 : x.1 (left (s c)) = 1 := congrFun hx c
    rw [h0 x] at h1; exact zero_ne_one h1
  have hQnz : ∀ c : Fin k, ¬ (∀ y : Q, y.1 (right (s c)) = 0) := by
    intro c h0; obtain ⟨y, hy⟩ := hQsurj (fun _ => (1 : F))
    have h1 : y.1 (right (s c)) = 1 := congrFun hy c
    rw [h0 y] at h1; exact zero_ne_one h1
  let ZP : Finset (Fin n) := Finset.univ.filter (fun i => ∀ x : P, x.1 i = 0)
  let ZQ : Finset (Fin n) := Finset.univ.filter (fun j => ∀ y : Q, y.1 j = 0)
  let Eact : Finset (Fin (2 * n)) := Finset.univ.filter (fun e => left e ∉ ZP ∧ right e ∉ ZQ)
  have hEact_col : ∀ e ∈ Eact,
      ∃ c : Fin k, (∀ x : P, x.1 (left e) = x.1 (left (s c))) ∧
        (∀ y : Q, y.1 (right e) = y.1 (right (s c))) := by
    intro e he
    simp only [Eact, ZP, ZQ, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases hedge e with h1 | h2 | h3
    · exact absurd h1 he.1
    · exact absurd h2 he.2
    · exact h3
  have hs_act : ∀ c : Fin k, s c ∈ Eact := fun c => by
    simp only [Eact, ZP, ZQ, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hPnz c, hQnz c⟩
  let AL : Finset (Fin n) := Finset.univ.filter (fun i => ∃ e ∈ Eact, left e = i)
  let AR : Finset (Fin n) := Finset.univ.filter (fun j => ∃ e ∈ Eact, right e = j)
  let IL : Finset (Fin n) := Finset.univ.filter (fun i => i ∉ ZP ∧ i ∉ AL)
  let IR : Finset (Fin n) := Finset.univ.filter (fun j => j ∉ ZQ ∧ j ∉ AR)
  have hAL_disj_ZP : Disjoint ZP AL := by
    rw [Finset.disjoint_left]; intro i hiZ hiA
    rcases (Finset.mem_filter.mp hiA).2 with ⟨e, he, rfl⟩; exact (Finset.mem_filter.mp he).2.1 hiZ
  have hAR_disj_ZQ : Disjoint ZQ AR := by
    rw [Finset.disjoint_left]; intro j hjZ hjA
    rcases (Finset.mem_filter.mp hjA).2 with ⟨e, he, rfl⟩; exact (Finset.mem_filter.mp he).2.2 hjZ
  have hIL_disj_ZP : Disjoint ZP IL := by
    rw [Finset.disjoint_left]; intro i hiZ hiI; exact (Finset.mem_filter.mp hiI).2.1 hiZ
  have hIL_disj_AL : Disjoint AL IL := by
    rw [Finset.disjoint_left]; intro i hiA hiI; exact (Finset.mem_filter.mp hiI).2.2 hiA
  have hIR_disj_ZQ : Disjoint ZQ IR := by
    rw [Finset.disjoint_left]; intro j hjZ hjI; exact (Finset.mem_filter.mp hjI).2.1 hjZ
  have hIR_disj_AR : Disjoint AR IR := by
    rw [Finset.disjoint_left]; intro j hjA hjI; exact (Finset.mem_filter.mp hjI).2.2 hjA
  have hPcov : ZP ∪ AL ∪ IL = Finset.univ := by
    ext i; simp only [Finset.mem_union, IL, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
  have hQcov : ZQ ∪ AR ∪ IR = Finset.univ := by
    ext j; simp only [Finset.mem_union, IR, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
  have hAL_col_ex : ∀ i ∈ AL, ∃ c : Fin k, ∀ x : P, x.1 i = x.1 (left (s c)) := by
    intro i hi; rcases (Finset.mem_filter.mp hi).2 with ⟨e, he, rfl⟩
    rcases hEact_col e he with ⟨c, hcL, _⟩; exact ⟨c, hcL⟩
  have hAR_col_ex : ∀ j ∈ AR, ∃ c : Fin k, ∀ y : Q, y.1 j = y.1 (right (s c)) := by
    intro j hj; rcases (Finset.mem_filter.mp hj).2 with ⟨e, he, rfl⟩
    rcases hEact_col e he with ⟨c, _, hcR⟩; exact ⟨c, hcR⟩
  have hkpos : 0 < k := by omega
  let c0 : Fin k := ⟨0, hkpos⟩
  let cL : Fin n → Fin k := fun i => if h : i ∈ AL then Classical.choose (hAL_col_ex i h) else c0
  let cR : Fin n → Fin k := fun j => if h : j ∈ AR then Classical.choose (hAR_col_ex j h) else c0
  have hcL_spec : ∀ i ∈ AL, ∀ x : P, x.1 i = x.1 (left (s (cL i))) := fun i hi => by
    simp only [cL, hi, ↓reduceDIte]; exact Classical.choose_spec (hAL_col_ex i hi)
  have hcR_spec : ∀ j ∈ AR, ∀ y : Q, y.1 j = y.1 (right (s (cR j))) := fun j hj => by
    simp only [cR, hj, ↓reduceDIte]; exact Classical.choose_spec (hAR_col_ex j hj)
  have hrepL : ∀ c : Fin k, left (s c) ∈ AL ∧ cL (left (s c)) = c := fun c => by
    have hmem : left (s c) ∈ AL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, s c, hs_act c, rfl⟩
    exact ⟨hmem, hPdist _ _ fun x => (hcL_spec _ hmem x).symm⟩
  have hrepR : ∀ c : Fin k, right (s c) ∈ AR ∧ cR (right (s c)) = c := fun c => by
    have hmem : right (s c) ∈ AR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, s c, hs_act c, rfl⟩
    exact ⟨hmem, hQdist _ _ fun y => (hcR_spec _ hmem y).symm⟩
  have hedge_same_col : ∀ e ∈ Eact, cL (left e) = cR (right e) := by
    intro e he; rcases hEact_col e he with ⟨c, hcL, hcR⟩
    have hmemL : left e ∈ AL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩
    have hmemR : right e ∈ AR := Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩
    have h1 : cL (left e) = c := hPdist _ _ fun x => (hcL_spec _ hmemL x).symm.trans (hcL x)
    have h2 : cR (right e) = c := hQdist _ _ fun y => (hcR_spec _ hmemR y).symm.trans (hcR y)
    rw [h1, h2]
  obtain ⟨rP, hrP2, hdimP, hrP0, hrP1⟩ :=
    finrank_le_card_add_k_sub_syndrome_1080 t k P hPcode ZP AL IL
      hAL_disj_ZP hIL_disj_ZP hIL_disj_AL hPcov
      (fun i hi x hx => (Finset.mem_filter.mp hi).2 ⟨x, hx⟩)
      (fun c => left (s c)) cL hrepL
      (fun i hi x hx => hcL_spec i hi ⟨x, hx⟩)
  obtain ⟨rQ, hrQ2, hdimQ, hrQ0, hrQ1⟩ :=
    finrank_le_card_add_k_sub_syndrome_1080 t k Q hQcode ZQ AR IR
      hAR_disj_ZQ hIR_disj_ZQ hIR_disj_AR hQcov
      (fun j hj y hy => (Finset.mem_filter.mp hj).2 ⟨y, hy⟩)
      (fun c => right (s c)) cR hrepR
      (fun j hj y hy => hcR_spec j hj ⟨y, hy⟩)
  have hAL_sum : AL.card = ∑ c : Fin k, (AL.filter (fun i => cL i = c)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext i; simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun hi => ⟨cL i, hi, rfl⟩, fun ⟨_, hi, _⟩ => hi⟩
    · intro c1 _ c2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
      intro i h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hAR_sum : AR.card = ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext j; simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun hj => ⟨cR j, hj, rfl⟩, fun ⟨_, hj, _⟩ => hj⟩
    · intro c1 _ c2 _ hne; change Disjoint _ _; rw [Finset.disjoint_left]
      intro j h1 h2; exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hAL_ge_k : k ≤ AL.card := by
    rw [hAL_sum]
    have : ∑ _c : Fin k, 1 ≤ ∑ c : Fin k, (AL.filter (fun i => cL i = c)).card :=
      Finset.sum_le_sum fun c _ => Finset.card_pos.mpr ⟨left (s c), Finset.mem_filter.mpr (hrepL c)⟩
    simpa using this
  have hAR_ge_k : k ≤ AR.card := by
    rw [hAR_sum]
    have : ∑ _c : Fin k, 1 ≤ ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card :=
      Finset.sum_le_sum fun c _ => Finset.card_pos.mpr ⟨right (s c), Finset.mem_filter.mpr (hrepR c)⟩
    simpa using this
  obtain ⟨nLive, nDead, nEnds, hLive_Dead, hLive_card, hEnds_le_Dead, hEnds_le_Live, hEnds_ge⟩ :=
    cycle_ends_bound_1080 n k hn_pos hk ZP ZQ AL AR IL IR
      hAL_disj_ZP hIL_disj_ZP hIL_disj_AL hPcov
      hAR_disj_ZQ hIR_disj_ZQ hIR_disj_AR hQcov
      Eact left right (fun _ => rfl) (fun _ => rfl)
      (fun e => by simp only [Eact, Finset.mem_filter, Finset.mem_univ, true_and])
      (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩)
      (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl⟩)
      s hs_act cL cR hrepL hedge_same_col
  have hdimP' : Module.finrank F P + rP ≤ IL.card + k := hdimP
  have hdimQ' : Module.finrank F Q + rQ ≤ IR.card + k := hdimQ
  change 2 * (Module.finrank F P + Module.finrank F Q) + 5 ≤ 2 * n + k
  have hmaster : 2 * (Module.finrank F P + Module.finrank F Q) +
      (AL.card - k) + (AR.card - k) + (nDead - nEnds) +
      (nEnds - (IL.card + IR.card + k)) + 2 * (rP + rQ) ≤ 2 * n + k := by omega
  by_cases hsum3 : 3 ≤ rP + rQ
  · omega
  · by_cases hrP0_case : rP = 0
    · have hAL_2k : 2 * k ≤ AL.card := by
        rw [hAL_sum]
        have : ∑ _c : Fin k, 2 ≤ ∑ c : Fin k, (AL.filter (fun i => cL i = c)).card :=
          Finset.sum_le_sum fun c _ => hrP0 hrP0_case c
        simpa [mul_comm] using this
      by_cases hrQ0_case : rQ = 0
      · have hAR_2k : 2 * k ≤ AR.card := by
          rw [hAR_sum]
          have : ∑ _c : Fin k, 2 ≤ ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card :=
            Finset.sum_le_sum fun c _ => hrQ0 hrQ0_case c
          simpa [mul_comm] using this
        omega
      · omega
    · by_cases hrQ0_case : rQ = 0
      · have hAR_2k : 2 * k ≤ AR.card := by
          rw [hAR_sum]
          have : ∑ _c : Fin k, 2 ≤ ∑ c : Fin k, (AR.filter (fun j => cR j = c)).card :=
            Finset.sum_le_sum fun c _ => hrQ0 hrQ0_case c
          simpa [mul_comm] using this
        omega
      · have hrP1_eq : rP = 1 := by omega
        have hrQ1_eq : rQ = 1 := by omega
        by_cases hex0 : (AL.card - k) + (AR.card - k) + (nDead - nEnds) = 0
        · exfalso
          have hAL_eq_k : AL.card = k := by omega
          have hAR_eq_k : AR.card = k := by omega
          have hDead_eq : nDead = nEnds := by omega
          have hAL_c1 : ∀ c : Fin k, (AL.filter (fun i => cL i = c)).card = 1 := by
            intro c; by_contra hne1
            have hge1 : 1 ≤ (AL.filter (fun i => cL i = c)).card :=
              Finset.card_pos.mpr ⟨left (s c), Finset.mem_filter.mpr (hrepL c)⟩
            have hge2 : 2 ≤ (AL.filter (fun i => cL i = c)).card := by omega
            have hsum_gt : k < ∑ c' : Fin k, (AL.filter (fun i => cL i = c')).card := by
              have h1 : ∑ c' : Fin k, (if c' = c then 2 else 1) ≤
                  ∑ c' : Fin k, (AL.filter (fun i => cL i = c')).card := by
                refine Finset.sum_le_sum fun c' _ => ?_
                by_cases hc' : c' = c
                · subst hc'; simpa using hge2
                · simp only [hc', ↓reduceIte]
                  exact Finset.card_pos.mpr ⟨left (s c'), Finset.mem_filter.mpr (hrepL c')⟩
              have h2 : ∑ c' : Fin k, (if c' = c then 2 else 1) = k + 1 := by
                rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
                have hf1 : (Finset.univ.filter (fun c' : Fin k => c' = c)).card = 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => c' = c) = {c} := by ext x; simp
                  rw [this, Finset.card_singleton]
                have hf2 : (Finset.univ.filter (fun c' : Fin k => ¬ c' = c)).card = k - 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => ¬ c' = c) = Finset.univ.erase c := by ext x; simp
                  rw [this, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
                rw [hf1, hf2]; simp only [smul_eq_mul]; omega
              omega
            omega
          have hAR_c1 : ∀ c : Fin k, (AR.filter (fun j => cR j = c)).card = 1 := by
            intro c; by_contra hne1
            have hge1 : 1 ≤ (AR.filter (fun j => cR j = c)).card :=
              Finset.card_pos.mpr ⟨right (s c), Finset.mem_filter.mpr (hrepR c)⟩
            have hge2 : 2 ≤ (AR.filter (fun j => cR j = c)).card := by omega
            have hsum_gt : k < ∑ c' : Fin k, (AR.filter (fun j => cR j = c')).card := by
              have h1 : ∑ c' : Fin k, (if c' = c then 2 else 1) ≤
                  ∑ c' : Fin k, (AR.filter (fun j => cR j = c')).card := by
                refine Finset.sum_le_sum fun c' _ => ?_
                by_cases hc' : c' = c
                · subst hc'; simpa using hge2
                · simp only [hc', ↓reduceIte]
                  exact Finset.card_pos.mpr ⟨right (s c'), Finset.mem_filter.mpr (hrepR c')⟩
              have h2 : ∑ c' : Fin k, (if c' = c then 2 else 1) = k + 1 := by
                rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
                have hf1 : (Finset.univ.filter (fun c' : Fin k => c' = c)).card = 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => c' = c) = {c} := by ext x; simp
                  rw [this, Finset.card_singleton]
                have hf2 : (Finset.univ.filter (fun c' : Fin k => ¬ c' = c)).card = k - 1 := by
                  have : Finset.univ.filter (fun c' : Fin k => ¬ c' = c) = Finset.univ.erase c := by ext x; simp
                  rw [this, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
                rw [hf1, hf2]; simp only [smul_eq_mul]; omega
              omega
            omega
          obtain ⟨a, ha⟩ := hrP1 hrP1_eq hAL_c1
          obtain ⟨b, hb⟩ := hrQ1 hrQ1_eq hAR_c1
          have hUP_le_t : AL.card + IL.card ≤ t := by
            rw [← Finset.card_union_of_disjoint hIL_disj_AL]
            have hsub : AL ∪ IL ⊆ Finset.univ.filter (fun i : Fin (3 * t) => i.val % 3 = a) :=
              fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha i hi⟩
            exact (Finset.card_le_card hsub).trans (card_filter_mod_three_eq_1080 t a)
          have hUQ_le_t : AR.card + IR.card ≤ t := by
            rw [← Finset.card_union_of_disjoint hIR_disj_AR]
            have hsub : AR ∪ IR ⊆ Finset.univ.filter (fun j : Fin (3 * t) => j.val % 3 = b) :=
              fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb j hj⟩
            exact (Finset.card_le_card hsub).trans (card_filter_mod_three_eq_1080 t b)
          omega
        · omega

lemma sum_two_pow_sub_wt {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∑ x : ι → F, 2 ^ (Fintype.card ι - wt x) = 3 ^ Fintype.card ι := by
  have h1 : ∀ x : ι → F, 2 ^ (Fintype.card ι - wt x) = ∏ i : ι, if x i = 0 then 2 else 1 := by
    intro x
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    congr 1
    have hdisj : Disjoint (Finset.univ.filter (fun i : ι => x i = 0))
        (Finset.univ.filter (fun i : ι => x i ≠ 0)) := by
      rw [Finset.disjoint_filter]; intro i _ h1 h2; exact h2 h1
    have hun : Finset.univ.filter (fun i : ι => x i = 0) ∪
        Finset.univ.filter (fun i : ι => x i ≠ 0) = Finset.univ := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
    have htot := Finset.card_union_of_disjoint hdisj
    rw [hun, Finset.card_univ] at htot
    have hwt : wt x = (Finset.univ.filter (fun i : ι => x i ≠ 0)).card := by unfold wt; congr 1
    omega
  rw [Finset.sum_congr rfl (fun x _ => h1 x),
    ← Fintype.prod_sum (fun (_ : ι) (z : F) => if z = 0 then (2 : ℕ) else 1)]
  have hfac : ∀ _ : ι, (∑ z : F, if z = 0 then (2 : ℕ) else 1) = 3 := fun _ => by
    rw [sum_F]; decide
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_const, Finset.card_univ]

lemma card_orth_pairs (n : ℕ) :
    (Finset.univ.filter (fun ab : (Fin n → F) × (Fin n → F) => ∀ i : Fin n, ab.1 i * ab.2 i = 0)).card = 3 ^ n := by
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have hinner : ∀ a : Fin n → F,
      (∑ b : Fin n → F, if ∀ i : Fin n, a i * b i = 0 then (1 : ℕ) else 0) = 2 ^ (n - wt a) := by
    intro a
    have hprod : ∀ b : Fin n → F,
        (if ∀ i : Fin n, a i * b i = 0 then (1 : ℕ) else 0) =
        ∏ i : Fin n, if a i * b i = 0 then 1 else 0 := by
      intro b
      by_cases h : ∀ i : Fin n, a i * b i = 0
      · simp [h]
      · simp only [h, ↓reduceIte]
        push Not at h; obtain ⟨i, hi⟩ := h
        exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
    rw [Finset.sum_congr rfl (fun b _ => hprod b),
      ← Fintype.prod_sum (fun (i : Fin n) (z : F) => if a i * z = 0 then (1 : ℕ) else 0)]
    have hfac : ∀ i : Fin n, (∑ z : F, if a i * z = 0 then (1 : ℕ) else 0) = if a i = 0 then 2 else 1 := by
      intro i; rw [sum_F]; rcases F_cases (a i) with h | h <;> simp [h]
    rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_ite, Finset.prod_const_one, mul_one,
      Finset.prod_const]
    congr 1
    have hdisj : Disjoint (Finset.univ.filter (fun i : Fin n => a i = 0))
        (Finset.univ.filter (fun i : Fin n => a i ≠ 0)) := by
      rw [Finset.disjoint_filter]; intro i _ h1 h2; exact h2 h1
    have hun : Finset.univ.filter (fun i : Fin n => a i = 0) ∪
        Finset.univ.filter (fun i : Fin n => a i ≠ 0) = Finset.univ := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; tauto
    have htot := Finset.card_union_of_disjoint hdisj
    rw [hun, Finset.card_univ, Fintype.card_fin] at htot
    have hwt : wt a = (Finset.univ.filter (fun i : Fin n => a i ≠ 0)).card := by unfold wt; congr 1
    omega
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  simpa using sum_two_pow_sub_wt (ι := Fin n)

lemma nat_card_fin_fun (n : ℕ) : Nat.card (Fin n → F) = 2 ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma card_orth_pairs_nat (n : ℕ) :
    Nat.card {ab : (Fin n → F) × (Fin n → F) // ∀ i : Fin n, ab.1 i * ab.2 i = 0} = 3 ^ n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_orth_pairs n

lemma card_orth_one_extra_nat {n : ℕ} (hn : 1 ≤ n) (α : Fin n → F) (hα : α ≠ 0) :
    Nat.card {ab : (Fin n → F) × (Fin (n + 1) → F) //
      (∀ c : Fin n, ab.1 c * ab.2 c.castSucc = 0) ∧
      (∑ c : Fin n, α c * ab.1 c) * ab.2 (Fin.last n) = 0} ≤ 2 * 3 ^ n - 3 ^ (n - 1) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  obtain ⟨c0, hc0⟩ : ∃ c0 : Fin n, α c0 ≠ 0 := by
    by_contra h; push Not at h; exact hα (funext h)
  have hc0_1 : α c0 = 1 := (F_cases _).resolve_left hc0
  let All : Finset ((Fin n → F) × (Fin (n + 1) → F)) :=
    Finset.univ.filter (fun ab => ∀ c : Fin n, ab.1 c * ab.2 c.castSucc = 0)
  let Good : Finset ((Fin n → F) × (Fin (n + 1) → F)) :=
    Finset.univ.filter (fun ab => (∀ c : Fin n, ab.1 c * ab.2 c.castSucc = 0) ∧
      (∑ c : Fin n, α c * ab.1 c) * ab.2 (Fin.last n) = 0)
  let Bad : Finset ((Fin n → F) × (Fin (n + 1) → F)) :=
    Finset.univ.filter (fun ab => (∀ c : Fin n, ab.1 c * ab.2 c.castSucc = 0) ∧
      (∑ c : Fin n, α c * ab.1 c) = 1 ∧ ab.2 (Fin.last n) = 1)
  have hAll_card : All.card = 2 * 3 ^ n := by
    have hbij : All.card = (Finset.univ.filter (fun ab : (Fin n → F) × (Fin n → F) =>
        ∀ c : Fin n, ab.1 c * ab.2 c = 0) ×ˢ (Finset.univ : Finset F)).card := by
      refine Finset.card_bij (fun ab _ => ((ab.1, fun c => ab.2 c.castSucc), ab.2 (Fin.last n))) ?_ ?_ ?_
      · intro ab hab
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hab).2⟩,
          Finset.mem_univ _⟩
      · intro x _ y _ hxy
        have h1 : x.1 = y.1 := congrArg (fun z => z.1.1) hxy
        have h2 : (fun c : Fin n => x.2 c.castSucc) = (fun c : Fin n => y.2 c.castSucc) :=
          congrArg (fun z => z.1.2) hxy
        have h3 : x.2 (Fin.last n) = y.2 (Fin.last n) := congrArg Prod.snd hxy
        refine Prod.ext h1 (funext fun i => ?_)
        refine Fin.lastCases h3 (fun c => congrFun h2 c) i
      · intro z hz
        obtain ⟨h1, _⟩ := Finset.mem_product.mp hz
        refine ⟨(z.1.1, Fin.snoc z.1.2 z.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun c => ?_⟩, ?_⟩
        · simpa using (Finset.mem_filter.mp h1).2 c
        · refine Prod.ext (Prod.ext rfl (funext fun c => by simp)) (by simp)
    rw [hbij, Finset.card_product, card_orth_pairs n, Finset.card_univ, ZMod.card, mul_comm]
  have hdisj : Disjoint Good Bad := by
    rw [Finset.disjoint_filter]
    intro ab _ hG hB; rw [hB.2.1, hB.2.2, mul_one] at hG; exact one_ne_zero hG.2
  have hsub : Good ∪ Bad ⊆ All := by
    intro ab hab
    simp only [Finset.mem_union, Good, Bad, All, Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
    rcases hab with h | h <;> exact h.1
  let T := {c : Fin n // c ≠ c0}
  have hT_card : Fintype.card T = n - 1 := by
    rw [Fintype.card_subtype]
    have : Finset.univ.filter (fun c : Fin n => c ≠ c0) = Finset.univ.erase c0 := by ext c; simp
    rw [this, Finset.card_erase_of_mem (Finset.mem_univ c0), Finset.card_univ, Fintype.card_fin]
  let mkBad : (T → F) × (T → F) → (Fin n → F) × (Fin (n + 1) → F) := fun pq =>
    let a : Fin n → F := fun c =>
      if h : c = c0 then 1 + ∑ x : T, α x.1 * pq.1 x else pq.1 ⟨c, h⟩
    let bn : Fin n → F := fun c => if h : c = c0 then 0 else pq.2 ⟨c, h⟩
    (a, Fin.snoc bn 1)
  have hBad_ge : 3 ^ (n - 1) ≤ Bad.card := by
    let Pprev := Finset.univ.filter (fun pq : (T → F) × (T → F) => ∀ x : T, pq.1 x * pq.2 x = 0)
    have hPprev_card : Pprev.card = 3 ^ (n - 1) := by
      let ePrev : T ≃ Fin (n - 1) := Fintype.equivFinOfCardEq hT_card
      have hbij : Pprev.card = (Finset.univ.filter (fun ab : (Fin (n - 1) → F) × (Fin (n - 1) → F) =>
          ∀ i : Fin (n - 1), ab.1 i * ab.2 i = 0)).card := by
        refine Finset.card_bij (fun pq _ => (pq.1 ∘ ePrev.symm, pq.2 ∘ ePrev.symm)) ?_ ?_ ?_
        · intro pq hpq
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (Finset.mem_filter.mp hpq).2 (ePrev.symm i)⟩
        · intro x _ y _ hxy
          refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
          · have := congrFun (congrArg Prod.fst hxy) (ePrev i); simpa using this
          · have := congrFun (congrArg Prod.snd hxy) (ePrev i); simpa using this
        · intro ab hab
          refine ⟨(ab.1 ∘ ePrev, ab.2 ∘ ePrev),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => (Finset.mem_filter.mp hab).2 (ePrev x)⟩,
            Prod.ext (funext fun i => by simp) (funext fun i => by simp)⟩
      rw [hbij, card_orth_pairs (n - 1)]
    have hmaps : Set.MapsTo mkBad Pprev Bad := by
      intro pq hpq
      have hperp := (Finset.mem_filter.mp (Finset.mem_coe.mp hpq)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, by simp [mkBad]⟩)
      · intro c
        simp only [mkBad, Fin.snoc_castSucc]
        by_cases hc : c = c0
        · simp [hc]
        · simp only [hc, ↓reduceDIte]; exact hperp ⟨c, hc⟩
      · simp only [mkBad]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c0)]
        have h0 : α c0 * (if h : c0 = c0 then 1 + ∑ x : T, α x.1 * pq.1 x else pq.1 ⟨c0, h⟩) =
            1 + ∑ x : T, α x.1 * pq.1 x := by simp [hc0_1]
        have hrest : ∑ c ∈ Finset.univ.erase c0,
            α c * (if h : c = c0 then 1 + ∑ x : T, α x.1 * pq.1 x else pq.1 ⟨c, h⟩) =
            ∑ x : T, α x.1 * pq.1 x := by
          rw [← Finset.sum_coe_sort (Finset.univ.erase c0)]
          refine Finset.sum_bij (fun c _ => ⟨c.1, (Finset.mem_erase.mp c.2).1⟩)
            (fun _ _ => Finset.mem_univ _)
            (fun a _ b _ h => Subtype.ext (congrArg (Subtype.val : T → Fin n) h))
            (fun x _ => ⟨⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩, Finset.mem_univ _, rfl⟩)
            (fun c _ => by simp [(Finset.mem_erase.mp c.2).1])
        rw [h0, hrest, add_assoc, z2_add_self, add_zero]
    have hinj : Set.InjOn mkBad Pprev := by
      intro x _ y _ hxy
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · have := congrFun (congrArg Prod.fst hxy) i.1; simpa [mkBad, i.2] using this
      · have := congrFun (congrArg Prod.snd hxy) i.1.castSucc; simpa [mkBad, i.2] using this
    rw [← hPprev_card]
    exact Finset.card_le_card_of_injOn mkBad hmaps hinj
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hAll_card] at hle
  change Good.card ≤ 2 * 3 ^ n - 3 ^ (n - 1)
  have _ := hn
  omega

lemma card_orth_both_in_span_nat {n : ℕ} (hn : 2 ≤ n) (α β : Fin n → F) (hα : α ≠ 0) (hβ : β ≠ 0)
    (hne : ∀ c : Fin n, ¬ (α = Pi.single c 1 ∧ β = Pi.single c 1)) :
    Nat.card {ab : (Fin n → F) × (Fin n → F) //
      (∀ c : Fin n, ab.1 c * ab.2 c = 0) ∧
      (∑ c : Fin n, α c * ab.1 c) * (∑ c : Fin n, β c * ab.2 c) = 0} ≤ 3 ^ n - 3 ^ (n - 2) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hex_ab : ∃ a0 b0 : Fin n, a0 ≠ b0 ∧ α a0 = 1 ∧ β b0 = 1 := by
    obtain ⟨a1, ha1⟩ : ∃ a1 : Fin n, α a1 ≠ 0 := by by_contra h; push Not at h; exact hα (funext h)
    obtain ⟨b1, hb1⟩ : ∃ b1 : Fin n, β b1 ≠ 0 := by by_contra h; push Not at h; exact hβ (funext h)
    have ha1_1 : α a1 = 1 := (F_cases _).resolve_left ha1
    have hb1_1 : β b1 = 1 := (F_cases _).resolve_left hb1
    by_cases hab : a1 = b1
    · subst hab
      by_cases ha_other : ∃ a2 : Fin n, a2 ≠ a1 ∧ α a2 ≠ 0
      · obtain ⟨a2, ha2ne, ha2⟩ := ha_other
        exact ⟨a2, a1, ha2ne, (F_cases _).resolve_left ha2, hb1_1⟩
      · by_cases hb_other : ∃ b2 : Fin n, b2 ≠ a1 ∧ β b2 ≠ 0
        · obtain ⟨b2, hb2ne, hb2⟩ := hb_other
          exact ⟨a1, b2, hb2ne.symm, ha1_1, (F_cases _).resolve_left hb2⟩
        · push Not at ha_other hb_other
          exfalso; apply hne a1
          constructor <;> funext c <;> by_cases hc : c = a1
          · subst hc; simp [ha1_1]
          · simp [hc, ha_other c hc]
          · subst hc; simp [hb1_1]
          · simp [hc, hb_other c hc]
    · exact ⟨a1, b1, hab, ha1_1, hb1_1⟩
  obtain ⟨a0, b0, hab, hαa, hβb⟩ := hex_ab
  let All : Finset ((Fin n → F) × (Fin n → F)) :=
    Finset.univ.filter (fun ab => ∀ c : Fin n, ab.1 c * ab.2 c = 0)
  let Good : Finset ((Fin n → F) × (Fin n → F)) :=
    Finset.univ.filter (fun ab => (∀ c : Fin n, ab.1 c * ab.2 c = 0) ∧
      (∑ c : Fin n, α c * ab.1 c) * (∑ c : Fin n, β c * ab.2 c) = 0)
  let Bad : Finset ((Fin n → F) × (Fin n → F)) :=
    Finset.univ.filter (fun ab => (∀ c : Fin n, ab.1 c * ab.2 c = 0) ∧
      (∑ c : Fin n, α c * ab.1 c) = 1 ∧ (∑ c : Fin n, β c * ab.2 c) = 1)
  have hAll_card : All.card = 3 ^ n := card_orth_pairs n
  have hdisj : Disjoint Good Bad := by
    rw [Finset.disjoint_filter]
    intro ab _ hG hB; rw [hB.2.1, hB.2.2, mul_one] at hG; exact one_ne_zero hG.2
  have hsub : Good ∪ Bad ⊆ All := by
    intro ab hab
    simp only [Finset.mem_union, Good, Bad, All, Finset.mem_filter, Finset.mem_univ, true_and] at hab ⊢
    rcases hab with h | h <;> exact h.1
  let T := {c : Fin n // c ≠ a0 ∧ c ≠ b0}
  have hT_card : Fintype.card T = n - 2 := by
    rw [Fintype.card_subtype]
    have : Finset.univ.filter (fun c : Fin n => c ≠ a0 ∧ c ≠ b0) = (Finset.univ.erase a0).erase b0 := by
      ext c; simp [and_comm]
    rw [this, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ a0), Finset.card_univ, Fintype.card_fin]
    omega
  let mkBad : (T → F) × (T → F) → (Fin n → F) × (Fin n → F) := fun pq =>
    let a : Fin n → F := fun c =>
      if h1 : c = a0 then 1 + ∑ x : T, α x.1 * pq.1 x
      else if h2 : c = b0 then 0 else pq.1 ⟨c, h1, h2⟩
    let b : Fin n → F := fun c =>
      if h1 : c = a0 then 0
      else if h2 : c = b0 then 1 + ∑ x : T, β x.1 * pq.2 x else pq.2 ⟨c, h1, h2⟩
    (a, b)
  have hBad_ge : 3 ^ (n - 2) ≤ Bad.card := by
    let Pprev := Finset.univ.filter (fun pq : (T → F) × (T → F) => ∀ x : T, pq.1 x * pq.2 x = 0)
    have hPprev_card : Pprev.card = 3 ^ (n - 2) := by
      let ePrev : T ≃ Fin (n - 2) := Fintype.equivFinOfCardEq hT_card
      have hbij : Pprev.card = (Finset.univ.filter (fun ab : (Fin (n - 2) → F) × (Fin (n - 2) → F) =>
          ∀ i : Fin (n - 2), ab.1 i * ab.2 i = 0)).card := by
        refine Finset.card_bij (fun pq _ => (pq.1 ∘ ePrev.symm, pq.2 ∘ ePrev.symm)) ?_ ?_ ?_
        · intro pq hpq
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (Finset.mem_filter.mp hpq).2 (ePrev.symm i)⟩
        · intro x _ y _ hxy
          refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
          · have := congrFun (congrArg Prod.fst hxy) (ePrev i); simpa using this
          · have := congrFun (congrArg Prod.snd hxy) (ePrev i); simpa using this
        · intro ab hab
          refine ⟨(ab.1 ∘ ePrev, ab.2 ∘ ePrev),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x => (Finset.mem_filter.mp hab).2 (ePrev x)⟩,
            Prod.ext (funext fun i => by simp) (funext fun i => by simp)⟩
      rw [hbij, card_orth_pairs (n - 2)]
    have hmaps : Set.MapsTo mkBad Pprev Bad := by
      intro pq hpq
      have hperp := (Finset.mem_filter.mp (Finset.mem_coe.mp hpq)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩)
      · intro c; simp only [mkBad]
        by_cases h1 : c = a0
        · simp [h1]
        · by_cases h2 : c = b0
          · simp only [h1, ↓reduceDIte]; simp only [h2, ↓reduceDIte, zero_mul]
          · simp only [h1, h2, ↓reduceDIte]; exact hperp ⟨c, h1, h2⟩
      · simp only [mkBad]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b0⟩)]
        have h1 : α a0 * (if h1 : a0 = a0 then 1 + ∑ x : T, α x.1 * pq.1 x
            else if h2 : a0 = b0 then 0 else pq.1 ⟨a0, h1, h2⟩) = 1 + ∑ x : T, α x.1 * pq.1 x := by
          simp [hαa]
        have h2 : α b0 * (if h1 : b0 = a0 then 1 + ∑ x : T, α x.1 * pq.1 x
            else if h2 : b0 = b0 then 0 else pq.1 ⟨b0, h1, h2⟩) = 0 := by
          simp [hab.symm]
        have hrest : ∑ c ∈ (Finset.univ.erase a0).erase b0,
            α c * (if h1 : c = a0 then 1 + ∑ x : T, α x.1 * pq.1 x
              else if h2 : c = b0 then 0 else pq.1 ⟨c, h1, h2⟩) =
            ∑ x : T, α x.1 * pq.1 x := by
          rw [← Finset.sum_coe_sort ((Finset.univ.erase a0).erase b0)]
          refine Finset.sum_bij (fun c _ => ⟨c.1, (Finset.mem_erase.mp (Finset.mem_erase.mp c.2).2).1,
              (Finset.mem_erase.mp c.2).1⟩)
            (fun _ _ => Finset.mem_univ _)
            (fun a _ b _ h => Subtype.ext (congrArg (Subtype.val : T → Fin n) h))
            (fun x _ => ⟨⟨x.1, Finset.mem_erase.mpr ⟨x.2.2, Finset.mem_erase.mpr ⟨x.2.1, Finset.mem_univ _⟩⟩⟩,
              Finset.mem_univ _, rfl⟩)
            (fun c _ => by simp [(Finset.mem_erase.mp (Finset.mem_erase.mp c.2).2).1, (Finset.mem_erase.mp c.2).1])
        rw [h1, h2, hrest, zero_add, add_assoc, z2_add_self, add_zero]
      · simp only [mkBad]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b0⟩)]
        have h1 : β a0 * (if h1 : a0 = a0 then 0
            else if h2 : a0 = b0 then 1 + ∑ x : T, β x.1 * pq.2 x else pq.2 ⟨a0, h1, h2⟩) = 0 := by simp
        have h2 : β b0 * (if h1 : b0 = a0 then 0
            else if h2 : b0 = b0 then 1 + ∑ x : T, β x.1 * pq.2 x else pq.2 ⟨b0, h1, h2⟩) =
            1 + ∑ x : T, β x.1 * pq.2 x := by simp [hab.symm, hβb]
        have hrest : ∑ c ∈ (Finset.univ.erase a0).erase b0,
            β c * (if h1 : c = a0 then 0
              else if h2 : c = b0 then 1 + ∑ x : T, β x.1 * pq.2 x else pq.2 ⟨c, h1, h2⟩) =
            ∑ x : T, β x.1 * pq.2 x := by
          rw [← Finset.sum_coe_sort ((Finset.univ.erase a0).erase b0)]
          refine Finset.sum_bij (fun c _ => ⟨c.1, (Finset.mem_erase.mp (Finset.mem_erase.mp c.2).2).1,
              (Finset.mem_erase.mp c.2).1⟩)
            (fun _ _ => Finset.mem_univ _)
            (fun a _ b _ h => Subtype.ext (congrArg (Subtype.val : T → Fin n) h))
            (fun x _ => ⟨⟨x.1, Finset.mem_erase.mpr ⟨x.2.2, Finset.mem_erase.mpr ⟨x.2.1, Finset.mem_univ _⟩⟩⟩,
              Finset.mem_univ _, rfl⟩)
            (fun c _ => by simp [(Finset.mem_erase.mp (Finset.mem_erase.mp c.2).2).1, (Finset.mem_erase.mp c.2).1])
        rw [h1, h2, hrest, zero_add, add_assoc, z2_add_self, add_zero]
    have hinj : Set.InjOn mkBad Pprev := by
      intro x _ y _ hxy
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · have := congrFun (congrArg Prod.fst hxy) i.1; simpa [mkBad, i.2.1, i.2.2] using this
      · have := congrFun (congrArg Prod.snd hxy) i.1; simpa [mkBad, i.2.1, i.2.2] using this
    rw [← hPprev_card]
    exact Finset.card_le_card_of_injOn mkBad hmaps hinj
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hAll_card] at hle
  change Good.card ≤ 3 ^ n - 3 ^ (n - 2)
  omega

open Classical in
lemma surj_of_linearIndependent_dual {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {k : ℕ} (f : Fin k → (V →ₗ[F] F)) (hlin : LinearIndependent F f) :
    Function.Surjective (LinearMap.pi f) := by
  by_contra hns
  have hne_top : LinearMap.range (LinearMap.pi f) ≠ ⊤ := fun h => hns (LinearMap.range_eq_top.mp h)
  have hlt : Module.finrank F (LinearMap.range (LinearMap.pi f)) < k := by
    have hle := Submodule.finrank_le (LinearMap.range (LinearMap.pi f))
    rw [Module.finrank_fin_fun] at hle
    have hne : Module.finrank F (LinearMap.range (LinearMap.pi f)) ≠ k := fun heq =>
      hne_top (Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; exact heq))
    omega
  have hdual : 0 < Module.finrank F (LinearMap.range (LinearMap.pi f)).dualAnnihilator := by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range (LinearMap.pi f))
    rw [Module.finrank_fin_fun] at h; omega
  have hbot : (LinearMap.range (LinearMap.pi f)).dualAnnihilator ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hdual; omega
  obtain ⟨φ, hφmem, hφne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let α : Fin k → F := fun c => φ (Pi.single c 1)
  have hα_ne : ∃ c : Fin k, α c ≠ 0 := by
    by_contra hall; push Not at hall
    apply hφne; apply LinearMap.ext; intro w
    have hw : w = ∑ c : Fin k, w c • Pi.single c (1 : F) := by
      funext i; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [Pi.single_eq_of_ne hji.symm]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hw, map_sum]
    exact Finset.sum_eq_zero fun c _ => by rw [map_smul, show φ (Pi.single c 1) = 0 from hall c, smul_zero]
  have hlin_zero : ∑ c : Fin k, α c • f c = 0 := by
    apply LinearMap.ext; intro x
    have h0 := (Submodule.mem_dualAnnihilator φ).mp hφmem (LinearMap.pi f x) ⟨x, rfl⟩
    have hw : LinearMap.pi f x = ∑ c : Fin k, f c x • Pi.single c (1 : F) := by
      funext i; simp only [LinearMap.pi_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji; simp [Pi.single_eq_of_ne hji.symm]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hw, map_sum] at h0
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply]
    rw [← h0]
    refine Finset.sum_congr rfl fun c _ => by rw [map_smul, smul_eq_mul, mul_comm]
  obtain ⟨c, hc⟩ := hα_ne
  exact hc ((Fintype.linearIndependent_iff.mp hlin) α hlin_zero c)

lemma linearIndependent_snoc_of_not_mem {V : Type*} [AddCommGroup V] [Module F V]
    {n : ℕ} (e : Fin n → (V →ₗ[F] F)) (hlin : LinearIndependent F e) (w : V →ₗ[F] F)
    (hw : w ∉ Submodule.span F (e '' (Finset.univ : Finset (Fin n)))) :
    LinearIndependent F (Fin.snoc (α := fun _ => V →ₗ[F] F) e w) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg6 : g (Fin.last n) = 0 := by
    by_contra hnz
    have h1 : g (Fin.last n) = 1 := (F_cases _).resolve_left hnz
    rw [Fin.sum_univ_castSucc, Fin.snoc_last, h1, one_smul] at hg
    have heq : w = ∑ c : Fin n, g c.castSucc • e c := by
      have h2 := eq_neg_of_add_eq_zero_right hg
      have hneg : ∀ z : V →ₗ[F] F, -z = z := fun z => by
        have h0 : z + z = 0 := by
          have := add_smul (1 : F) (1 : F) z; rw [z2_add_self, zero_smul, one_smul] at this; exact this.symm
        exact (eq_neg_of_add_eq_zero_left h0).symm
      rw [hneg] at h2
      simpa [Fin.snoc_castSucc] using h2
    apply hw
    rw [heq]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨c, Finset.mem_coe.mpr (Finset.mem_univ c), rfl⟩)
  rw [Fin.sum_univ_castSucc, Fin.snoc_last, hg6, zero_smul, add_zero] at hg
  have hrest : ∀ c : Fin n, g c.castSucc = 0 := (Fintype.linearIndependent_iff.mp hlin) (fun c => g c.castSucc) (by
    simpa [Fin.snoc_castSucc] using hg)
  intro i; exact Fin.lastCases hg6 hrest i

open Classical in
lemma six_plus_one_bound {t : ℕ} (ht : 0 < t) (P Q : Submodule F (Lane t))
    (eP : Fin 6 → (P →ₗ[F] F)) (eQ : Fin 6 → (Q →ₗ[F] F))
    (hPind : LinearIndependent F eP) (hQind : LinearIndependent F eQ)
    (u6 : P →ₗ[F] F) (v6 : Q →ₗ[F] F) (hu6 : u6 ≠ 0) (hv6 : v6 ≠ 0)
    (hne : ∀ c : Fin 6, ¬ (u6 = eP c ∧ v6 = eQ c))
    (hkill : ∀ (x : P) (y : Q), hitsAt ht x.1 y.1 →
      (∀ c : Fin 6, eP c x * eQ c y = 0) ∧ u6 x * v6 y = 0) :
    2048 * rectHits ht P Q ≤ 324 * (Nat.card P * Nat.card Q) := by
  let fP : P →ₗ[F] (Fin 6 → F) := LinearMap.pi eP
  let fQ : Q →ₗ[F] (Fin 6 → F) := LinearMap.pi eQ
  have hPsurj : Function.Surjective fP := surj_of_linearIndependent_dual eP hPind
  have hQsurj : Function.Surjective fQ := surj_of_linearIndependent_dual eQ hQind
  by_cases hu_in : u6 ∈ Submodule.span F (eP '' (Finset.univ : Finset (Fin 6)))
  · obtain ⟨α', hα'⟩ := (mem_span_finset_iff eP Finset.univ u6).mp hu_in
    let α : Fin 6 → F := fun c => α' ⟨c, Finset.mem_univ c⟩
    have hu6_eq : ∀ x : P, u6 x = ∑ c : Fin 6, α c * eP c x := by
      intro x
      have h1 := LinearMap.congr_fun hα' x
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
      rw [h1]
      exact Finset.sum_bij (fun c _ => c.1) (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ h => Subtype.ext h) (fun c _ => ⟨⟨c, Finset.mem_univ c⟩, Finset.mem_univ _, rfl⟩)
        (fun _ _ => rfl)
    have hα_ne : α ≠ 0 := by
      intro hz; apply hu6; apply LinearMap.ext; intro x
      rw [hu6_eq x, hz]; simp
    by_cases hv_in : v6 ∈ Submodule.span F (eQ '' (Finset.univ : Finset (Fin 6)))
    · obtain ⟨β', hβ'⟩ := (mem_span_finset_iff eQ Finset.univ v6).mp hv_in
      let β : Fin 6 → F := fun c => β' ⟨c, Finset.mem_univ c⟩
      have hv6_eq : ∀ y : Q, v6 y = ∑ c : Fin 6, β c * eQ c y := by
        intro y
        have h1 := LinearMap.congr_fun hβ' y
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
        rw [h1]
        exact Finset.sum_bij (fun c _ => c.1) (fun _ _ => Finset.mem_univ _)
          (fun a _ b _ h => Subtype.ext h) (fun c _ => ⟨⟨c, Finset.mem_univ c⟩, Finset.mem_univ _, rfl⟩)
          (fun _ _ => rfl)
      have hβ_ne : β ≠ 0 := by
        intro hz; apply hv6; apply LinearMap.ext; intro y
        rw [hv6_eq y, hz]; simp
      have hαβ_ne : ∀ c : Fin 6, ¬ (α = Pi.single c 1 ∧ β = Pi.single c 1) := by
        rintro c ⟨hαc, hβc⟩
        apply hne c
        refine ⟨LinearMap.ext fun x => ?_, LinearMap.ext fun y => ?_⟩
        · rw [hu6_eq x, hαc, Finset.sum_eq_single c]
          · simp
          · intro j _ hj; simp [Pi.single_eq_of_ne hj]
          · intro h; exact absurd (Finset.mem_univ c) h
        · rw [hv6_eq y, hβc, Finset.sum_eq_single c]
          · simp
          · intro j _ hj; simp [Pi.single_eq_of_ne hj]
          · intro h; exact absurd (Finset.mem_univ c) h
      let pred : (Fin 6 → F) × (Fin 6 → F) → Prop := fun ab =>
        (∀ c : Fin 6, ab.1 c * ab.2 c = 0) ∧
        (∑ c : Fin 6, α c * ab.1 c) * (∑ c : Fin 6, β c * ab.2 c) = 0
      have hsurj : Function.Surjective (fP.prodMap fQ) := hPsurj.prodMap hQsurj
      have hpull := pull_count (fP.prodMap fQ) hsurj pred
      have hhits_le : rectHits ht P Q ≤ Nat.card {z : P × Q // pred ((fP.prodMap fQ) z)} := by
        unfold rectHits
        refine Nat.card_le_card_of_injective
          (fun z => ⟨z.1, ?_⟩) (fun a b h => Subtype.ext (Subtype.mk.inj h))
        obtain ⟨h1, h2⟩ := hkill z.1.1 z.1.2 z.2
        refine ⟨h1, ?_⟩
        simp only [LinearMap.prodMap_apply, fP, fQ, LinearMap.pi_apply]
        rwa [← hu6_eq z.1.1, ← hv6_eq z.1.2]
      have hTcard : Nat.card ((Fin 6 → F) × (Fin 6 → F)) = 4096 := by
        rw [Nat.card_prod, nat_card_fin_fun]; decide
      have hpred_le : Nat.card {t : (Fin 6 → F) × (Fin 6 → F) // pred t} ≤ 648 :=
        (card_orth_both_in_span_nat (by decide : 2 ≤ 6) α β hα_ne hβ_ne hαβ_ne).trans (by decide)
      rw [hTcard, Nat.card_prod] at hpull
      have h1 : rectHits ht P Q * 4096 ≤ (Nat.card P * Nat.card Q) * 648 := by
        calc rectHits ht P Q * 4096 ≤ Nat.card {z : P × Q // pred ((fP.prodMap fQ) z)} * 4096 :=
              Nat.mul_le_mul_right 4096 hhits_le
          _ = (Nat.card P * Nat.card Q) * Nat.card {t : (Fin 6 → F) × (Fin 6 → F) // pred t} := hpull
          _ ≤ (Nat.card P * Nat.card Q) * 648 := Nat.mul_le_mul_left _ hpred_le
      omega
    · let eQ7 : Fin 7 → (Q →ₗ[F] F) := Fin.snoc (α := fun _ => Q →ₗ[F] F) eQ v6
      have hQ7surj : Function.Surjective (LinearMap.pi eQ7) :=
        surj_of_linearIndependent_dual eQ7 (linearIndependent_snoc_of_not_mem eQ hQind v6 hv_in)
      let pred : (Fin 6 → F) × (Fin 7 → F) → Prop := fun ab =>
        (∀ c : Fin 6, ab.1 c * ab.2 c.castSucc = 0) ∧
        (∑ c : Fin 6, α c * ab.1 c) * ab.2 (Fin.last 6) = 0
      have hsurj : Function.Surjective (fP.prodMap (LinearMap.pi eQ7)) := hPsurj.prodMap hQ7surj
      have hpull := pull_count (fP.prodMap (LinearMap.pi eQ7)) hsurj pred
      have hhits_le : rectHits ht P Q ≤
          Nat.card {z : P × Q // pred ((fP.prodMap (LinearMap.pi eQ7)) z)} := by
        unfold rectHits
        refine Nat.card_le_card_of_injective
          (fun z => ⟨z.1, ?_⟩) (fun a b h => Subtype.ext (Subtype.mk.inj h))
        obtain ⟨h1, h2⟩ := hkill z.1.1 z.1.2 z.2
        refine ⟨fun c => by simpa [fP, eQ7] using h1 c, ?_⟩
        simp only [LinearMap.prodMap_apply, fP, LinearMap.pi_apply, eQ7, Fin.snoc_last]
        rwa [← hu6_eq z.1.1]
      have hTcard : Nat.card ((Fin 6 → F) × (Fin 7 → F)) = 8192 := by
        rw [Nat.card_prod, nat_card_fin_fun, nat_card_fin_fun]; decide
      have hpred_le : Nat.card {t : (Fin 6 → F) × (Fin 7 → F) // pred t} ≤ 1215 :=
        (card_orth_one_extra_nat (by decide : 1 ≤ 6) α hα_ne).trans (by decide)
      rw [hTcard, Nat.card_prod] at hpull
      have h1 : rectHits ht P Q * 8192 ≤ (Nat.card P * Nat.card Q) * 1215 := by
        calc rectHits ht P Q * 8192
            ≤ Nat.card {z : P × Q // pred ((fP.prodMap (LinearMap.pi eQ7)) z)} * 8192 :=
              Nat.mul_le_mul_right 8192 hhits_le
          _ = (Nat.card P * Nat.card Q) * Nat.card {t : (Fin 6 → F) × (Fin 7 → F) // pred t} := hpull
          _ ≤ (Nat.card P * Nat.card Q) * 1215 := Nat.mul_le_mul_left _ hpred_le
      omega
  · let eP7 : Fin 7 → (P →ₗ[F] F) := Fin.snoc (α := fun _ => P →ₗ[F] F) eP u6
    have hP7surj : Function.Surjective (LinearMap.pi eP7) :=
      surj_of_linearIndependent_dual eP7 (linearIndependent_snoc_of_not_mem eP hPind u6 hu_in)
    by_cases hv_in : v6 ∈ Submodule.span F (eQ '' (Finset.univ : Finset (Fin 6)))
    · obtain ⟨β', hβ'⟩ := (mem_span_finset_iff eQ Finset.univ v6).mp hv_in
      let β : Fin 6 → F := fun c => β' ⟨c, Finset.mem_univ c⟩
      have hv6_eq : ∀ y : Q, v6 y = ∑ c : Fin 6, β c * eQ c y := by
        intro y
        have h1 := LinearMap.congr_fun hβ' y
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
        rw [h1]
        exact Finset.sum_bij (fun c _ => c.1) (fun _ _ => Finset.mem_univ _)
          (fun a _ b _ h => Subtype.ext h) (fun c _ => ⟨⟨c, Finset.mem_univ c⟩, Finset.mem_univ _, rfl⟩)
          (fun _ _ => rfl)
      have hβ_ne : β ≠ 0 := by
        intro hz; apply hv6; apply LinearMap.ext; intro y
        rw [hv6_eq y, hz]; simp
      let pred : (Fin 7 → F) × (Fin 6 → F) → Prop := fun ab =>
        (∀ c : Fin 6, ab.2 c * ab.1 c.castSucc = 0) ∧
        (∑ c : Fin 6, β c * ab.2 c) * ab.1 (Fin.last 6) = 0
      have hsurj : Function.Surjective ((LinearMap.pi eP7).prodMap fQ) := hP7surj.prodMap hQsurj
      have hpull := pull_count ((LinearMap.pi eP7).prodMap fQ) hsurj pred
      have hhits_le : rectHits ht P Q ≤
          Nat.card {z : P × Q // pred (((LinearMap.pi eP7).prodMap fQ) z)} := by
        unfold rectHits
        refine Nat.card_le_card_of_injective
          (fun z => ⟨z.1, ?_⟩) (fun a b h => Subtype.ext (Subtype.mk.inj h))
        obtain ⟨h1, h2⟩ := hkill z.1.1 z.1.2 z.2
        refine ⟨fun c => by simpa [fQ, eP7, mul_comm] using h1 c, ?_⟩
        simp only [LinearMap.prodMap_apply, fQ, LinearMap.pi_apply, eP7, Fin.snoc_last]
        rw [← hv6_eq z.1.2, mul_comm]; exact h2
      have hTcard : Nat.card ((Fin 7 → F) × (Fin 6 → F)) = 8192 := by
        rw [Nat.card_prod, nat_card_fin_fun, nat_card_fin_fun]; decide
      have hpred_le : Nat.card {t : (Fin 7 → F) × (Fin 6 → F) // pred t} ≤ 1215 := by
        have e : {t : (Fin 7 → F) × (Fin 6 → F) // pred t} ≃
            {t : (Fin 6 → F) × (Fin 7 → F) //
              (∀ c : Fin 6, t.1 c * t.2 c.castSucc = 0) ∧
              (∑ c : Fin 6, β c * t.1 c) * t.2 (Fin.last 6) = 0} :=
          { toFun := fun z => ⟨(z.1.2, z.1.1), z.2⟩
            invFun := fun z => ⟨(z.1.2, z.1.1), z.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [Nat.card_congr e]
        exact (card_orth_one_extra_nat (by decide : 1 ≤ 6) β hβ_ne).trans (by decide)
      rw [hTcard, Nat.card_prod] at hpull
      have h1 : rectHits ht P Q * 8192 ≤ (Nat.card P * Nat.card Q) * 1215 := by
        calc rectHits ht P Q * 8192
            ≤ Nat.card {z : P × Q // pred (((LinearMap.pi eP7).prodMap fQ) z)} * 8192 :=
              Nat.mul_le_mul_right 8192 hhits_le
          _ = (Nat.card P * Nat.card Q) * Nat.card {t : (Fin 7 → F) × (Fin 6 → F) // pred t} := hpull
          _ ≤ (Nat.card P * Nat.card Q) * 1215 := Nat.mul_le_mul_left _ hpred_le
      omega
    · let eQ7 : Fin 7 → (Q →ₗ[F] F) := Fin.snoc (α := fun _ => Q →ₗ[F] F) eQ v6
      have hQ7surj : Function.Surjective (LinearMap.pi eQ7) :=
        surj_of_linearIndependent_dual eQ7 (linearIndependent_snoc_of_not_mem eQ hQind v6 hv_in)
      let pred : (Fin 7 → F) × (Fin 7 → F) → Prop := fun ab => ∀ i : Fin 7, ab.1 i * ab.2 i = 0
      have hsurj : Function.Surjective ((LinearMap.pi eP7).prodMap (LinearMap.pi eQ7)) :=
        hP7surj.prodMap hQ7surj
      have hpull := pull_count ((LinearMap.pi eP7).prodMap (LinearMap.pi eQ7)) hsurj pred
      have hhits_le : rectHits ht P Q ≤
          Nat.card {z : P × Q // pred (((LinearMap.pi eP7).prodMap (LinearMap.pi eQ7)) z)} := by
        unfold rectHits
        refine Nat.card_le_card_of_injective
          (fun z => ⟨z.1, ?_⟩) (fun a b h => Subtype.ext (Subtype.mk.inj h))
        obtain ⟨h1, h2⟩ := hkill z.1.1 z.1.2 z.2
        intro i
        refine Fin.lastCases ?_ (fun c => ?_) i
        · simp only [LinearMap.prodMap_apply, LinearMap.pi_apply, eP7, eQ7, Fin.snoc_last]; exact h2
        · simp only [LinearMap.prodMap_apply, LinearMap.pi_apply, eP7, eQ7, Fin.snoc_castSucc]; exact h1 c
      have hTcard : Nat.card ((Fin 7 → F) × (Fin 7 → F)) = 16384 := by
        rw [Nat.card_prod, nat_card_fin_fun]; decide
      have hpred_eq : Nat.card {t : (Fin 7 → F) × (Fin 7 → F) // pred t} = 2187 := by
        rw [card_orth_pairs_nat 7]; decide
      rw [hTcard, hpred_eq, Nat.card_prod] at hpull
      have h1 : rectHits ht P Q * 16384 ≤ (Nat.card P * Nat.card Q) * 2187 := by
        calc rectHits ht P Q * 16384
            ≤ Nat.card {z : P × Q // pred (((LinearMap.pi eP7).prodMap (LinearMap.pi eQ7)) z)} * 16384 :=
              Nat.mul_le_mul_right 16384 hhits_le
          _ = (Nat.card P * Nat.card Q) * 2187 := hpull
      omega

open Classical in
lemma rect_case_3C {t : ℕ} (ht : 0 < t) (ht4 : 4 ≤ t)
    (P Q : Submodule F (Lane t)) (hP : P ≤ codeSub t) (hQ : Q ≤ codeSub t)
    (hP6 : 6 ≤ Module.finrank F P) (hle : Module.finrank F P ≤ Module.finrank F Q)
    (hsum : Module.finrank F P + Module.finrank F Q = 3 * t + 1) :
    2048 * rectHits ht P Q ≤ numVal t * (Nat.card P * Nat.card Q) := by
  let n := 3 * t
  have hn_pos : 0 < n := by omega
  let left : Fin (2 * n) → Fin n := fun e => ixn n hn_pos ((e.val + 1) / 2)
  let right : Fin (2 * n) → Fin n := fun e => ixn n hn_pos (e.val / 2)
  let u : Fin (2 * n) → (P →ₗ[F] F) := fun e => (LinearMap.proj (left e)).comp P.subtype
  let v : Fin (2 * n) → (Q →ₗ[F] F) := fun e => (LinearMap.proj (right e)).comp Q.subtype
  have hhits_edges : ∀ (x y : Lane t), hitsAt ht x y ↔ ∀ e : Fin (2 * n), x (left e) * y (right e) = 0 := by
    intro x y
    constructor
    · intro h e
      have he := e.isLt
      by_cases hev : e.val % 2 = 0
      · have hL : left e = ⟨e.val / 2, by omega⟩ := Fin.ext (by
          dsimp [left, ixn]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
        have hR : right e = ⟨e.val / 2, by omega⟩ := Fin.ext (by
          dsimp [right, ixn]; rw [Nat.mod_eq_of_lt (by omega)])
        rw [hL, hR]; exact (h ⟨e.val / 2, by omega⟩).1
      · have hL : left e = nx ht ⟨e.val / 2, by omega⟩ := Fin.ext (by
          dsimp [left, ixn, nx]; congr 1; omega)
        have hR : right e = ⟨e.val / 2, by omega⟩ := Fin.ext (by
          dsimp [right, ixn]; rw [Nat.mod_eq_of_lt (by omega)])
        rw [hL, hR]; exact (h ⟨e.val / 2, by omega⟩).2
    · intro h i
      have hi := i.isLt
      constructor
      · have h0 := h ⟨2 * i.val, by omega⟩
        have hL : left ⟨2 * i.val, by omega⟩ = i := Fin.ext (by
          dsimp [left, ixn]; rw [show (2 * i.val + 1) / 2 = i.val by omega, Nat.mod_eq_of_lt hi])
        have hR : right ⟨2 * i.val, by omega⟩ = i := Fin.ext (by
          dsimp [right, ixn]; rw [show 2 * i.val / 2 = i.val by omega, Nat.mod_eq_of_lt hi])
        rwa [hL, hR] at h0
      · have h1 := h ⟨2 * i.val + 1, by omega⟩
        have hL : left ⟨2 * i.val + 1, by omega⟩ = nx ht i := Fin.ext (by
          dsimp [left, ixn, nx]; rw [show (2 * i.val + 1 + 1) / 2 = i.val + 1 by omega])
        have hR : right ⟨2 * i.val + 1, by omega⟩ = i := Fin.ext (by
          dsimp [right, ixn]; rw [show (2 * i.val + 1) / 2 = i.val by omega, Nat.mod_eq_of_lt hi])
        rwa [hL, hR] at h1
  have hcodim : ∀ {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (f : Fin (2 * n) → (V →ₗ[F] F)) (A : Finset (Fin (2 * n))),
      Module.finrank F V ≤
        Module.finrank F (Submodule.span F (f '' (A : Set (Fin (2 * n))))) +
        Module.finrank F (⨅ e ∈ A, LinearMap.ker (f e) : Submodule F V) := by
    intro V _ _ _ f A
    induction A using Finset.induction_on with
    | empty =>
      have htop : (⨅ e ∈ (∅ : Finset (Fin (2 * n))), LinearMap.ker (f e) : Submodule F V) = ⊤ := by simp
      rw [htop, finrank_top]
      omega
    | @insert a s _ ih =>
      let Ws := Submodule.span F (f '' (s : Set (Fin (2 * n))))
      let W' := Submodule.span F (f '' ((insert a s : Finset (Fin (2 * n))) : Set (Fin (2 * n))))
      let Ks : Submodule F V := ⨅ e ∈ s, LinearMap.ker (f e)
      let K' : Submodule F V := ⨅ e ∈ insert a s, LinearMap.ker (f e)
      have hK'eq : K' = LinearMap.ker (f a) ⊓ Ks := by
        ext x
        simp only [K', Ks, Submodule.mem_iInf, Submodule.mem_inf, Finset.mem_insert]
        constructor
        · intro h; exact ⟨h a (Or.inl rfl), fun e he => h e (Or.inr he)⟩
        · rintro ⟨h1, h2⟩ e (rfl | he)
          · exact h1
          · exact h2 e he
      have hWle : Ws ≤ W' :=
        Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr (Finset.subset_insert a s)))
      have ih' : Module.finrank F V ≤ Module.finrank F Ws + Module.finrank F Ks := ih
      by_cases hmem : f a ∈ Ws
      · have hWeq : W' = Ws := le_antisymm (Submodule.span_le.mpr (by
          rintro _ ⟨e, he, rfl⟩
          rcases Finset.mem_insert.mp (Finset.mem_coe.mp he) with rfl | hes
          · exact hmem
          · exact Submodule.subset_span ⟨e, Finset.mem_coe.mpr hes, rfl⟩)) hWle
        have hK : Ks ≤ K' := by
          rw [hK'eq]; intro x hx; refine Submodule.mem_inf.mpr ⟨?_, hx⟩
          rw [LinearMap.mem_ker]
          obtain ⟨c, hc⟩ := (mem_span_finset_iff f s (f a)).mp hmem
          have hfx := LinearMap.congr_fun hc x
          simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hfx
          rw [hfx]
          refine Finset.sum_eq_zero fun i _ => ?_
          have hi0 : f i.1 x = 0 := by
            rw [Submodule.mem_iInf] at hx
            have hx1 := hx i.1
            rw [Submodule.mem_iInf] at hx1
            exact LinearMap.mem_ker.mp (hx1 i.2)
          rw [hi0, mul_zero]
        have hKdim : Module.finrank F Ks ≤ Module.finrank F K' := Submodule.finrank_mono hK
        change Module.finrank F V ≤ Module.finrank F W' + Module.finrank F K'
        rw [hWeq]
        omega
      · have hWmono : Module.finrank F Ws ≤ Module.finrank F W' := Submodule.finrank_mono hWle
        have hWne : Module.finrank F Ws ≠ Module.finrank F W' := fun heq => by
          have hEq : Ws = W' := Submodule.eq_of_le_of_finrank_eq hWle heq
          apply hmem; rw [hEq]
          exact Submodule.subset_span ⟨a, Finset.mem_coe.mpr (Finset.mem_insert_self a s), rfl⟩
        let g : Ks →ₗ[F] F := (f a).comp Ks.subtype
        have hmap : (LinearMap.ker g).map Ks.subtype = K' := by
          ext x
          simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype,
            hK'eq, Submodule.mem_inf]
          constructor
          · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨x, h2⟩, h1, rfl⟩
        have h1 := LinearMap.finrank_range_add_finrank_ker g
        have h2 : Module.finrank F (LinearMap.range g) ≤ 1 :=
          (Submodule.finrank_le (LinearMap.range g)).trans_eq (Module.finrank_self F)
        have h3 : Module.finrank F (LinearMap.ker g) = Module.finrank F K' := by
          rw [← hmap, Submodule.finrank_map_subtype_eq]
        change Module.finrank F V ≤ Module.finrank F W' + Module.finrank F K'
        omega
  have hall : ∀ (A B : Finset (Fin (2 * n))), A ∪ B = Finset.univ →
      6 ≤ Module.finrank F (Submodule.span F (u '' (A : Set (Fin (2 * n))))) +
          Module.finrank F (Submodule.span F (v '' (B : Set (Fin (2 * n))))) := by
    intro A B hAB
    let U0 : Submodule F P := ⨅ e ∈ A, LinearMap.ker (u e)
    let V0 : Submodule F Q := ⨅ e ∈ B, LinearMap.ker (v e)
    let U : Submodule F (Lane t) := U0.map P.subtype
    let V : Submodule F (Lane t) := V0.map Q.subtype
    have hUdim : Module.finrank F U = Module.finrank F U0 := Submodule.finrank_map_subtype_eq P U0
    have hVdim : Module.finrank F V = Module.finrank F V0 := Submodule.finrank_map_subtype_eq Q V0
    have hUcode : U ≤ codeSub t := by rintro _ ⟨x, _, rfl⟩; exact hP x.2
    have hVcode : V ≤ codeSub t := by rintro _ ⟨y, _, rfl⟩; exact hQ y.2
    have hcP : Module.finrank F P ≤
        Module.finrank F (Submodule.span F (u '' (A : Set (Fin (2 * n))))) + Module.finrank F U0 := hcodim u A
    have hcQ : Module.finrank F Q ≤
        Module.finrank F (Submodule.span F (v '' (B : Set (Fin (2 * n))))) + Module.finrank F V0 := hcodim v B
    by_cases hU0 : Module.finrank F U = 0
    · omega
    · by_cases hV0 : Module.finrank F V = 0
      · omega
      · have hann : ∀ x ∈ U, ∀ y ∈ V, hitsAt ht x y := by
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          rw [hhits_edges]
          intro e
          have he : e ∈ A ∪ B := hAB ▸ Finset.mem_univ e
          rcases Finset.mem_union.mp he with heA | heB
          · have hx0 : x.1 (left e) = 0 := by
              change x ∈ ⨅ e ∈ A, LinearMap.ker (u e) at hx
              rw [Submodule.mem_iInf] at hx
              have h1 := hx e
              rw [Submodule.mem_iInf] at h1
              exact LinearMap.mem_ker.mp (h1 heA)
            simp only [Submodule.coe_subtype, hx0, zero_mul]
          · have hy0 : y.1 (right e) = 0 := by
              change y ∈ ⨅ e ∈ B, LinearMap.ker (v e) at hy
              rw [Submodule.mem_iInf] at hy
              have h1 := hy e
              rw [Submodule.mem_iInf] at h1
              exact LinearMap.mem_ker.mp (h1 heB)
            simp only [Submodule.coe_subtype, hy0, mul_zero]
        have hmb := mixedBound ht (by omega) U V hUcode hVcode (by omega) (by omega) hann
        have hne2 : ¬ (t = 2) := by omega
        simp only [hne2, ↓reduceIte] at hmb
        omega
  obtain ⟨I, hIcard, hIu, hIv⟩ := matroid_inter u v 6 (fun A B hAB =>
    hall A B (by ext e; have := Finset.ext_iff.mp hAB e; simpa using this))
  let eI : Fin 6 ≃ I := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hIcard])).symm
  let s : Fin 6 → Fin (2 * n) := fun c => (eI c).1
  have hPind : LinearIndependent F (fun c : Fin 6 => u (s c)) := hIu.comp eI eI.injective
  have hQind : LinearIndependent F (fun c : Fin 6 => v (s c)) := hIv.comp eI eI.injective
  have hPsurj : Function.Surjective (fun x : P => fun c : Fin 6 => x.1 (left (s c))) :=
    surj_of_linearIndependent_dual (fun c => u (s c)) hPind
  have hQsurj : Function.Surjective (fun y : Q => fun c : Fin 6 => y.1 (right (s c))) :=
    surj_of_linearIndependent_dual (fun c => v (s c)) hQind
  have hex_e6 : ∃ e6 : Fin (2 * n), u e6 ≠ 0 ∧ v e6 ≠ 0 ∧
      ∀ c : Fin 6, ¬ (u e6 = u (s c) ∧ v e6 = v (s c)) := by
    by_contra hno; push Not at hno
    have hedge : ∀ e : Fin (2 * (3 * t)),
        (∀ x : P, x.1 (ixn (3 * t) (by omega) ((e.val + 1) / 2)) = 0) ∨
        (∀ y : Q, y.1 (ixn (3 * t) (by omega) (e.val / 2)) = 0) ∨
        ∃ c : Fin 6,
          (∀ x : P, x.1 (ixn (3 * t) (by omega) ((e.val + 1) / 2)) = x.1 (ixn (3 * t) (by omega) (((s c).val + 1) / 2))) ∧
          (∀ y : Q, y.1 (ixn (3 * t) (by omega) (e.val / 2)) = y.1 (ixn (3 * t) (by omega) ((s c).val / 2))) := by
      intro e
      by_cases hu0 : u e = 0
      · exact Or.inl fun x => LinearMap.congr_fun hu0 x
      · by_cases hv0 : v e = 0
        · exact Or.inr (Or.inl fun y => LinearMap.congr_fun hv0 y)
        · obtain ⟨c, hc1, hc2⟩ := hno e hu0 hv0
          exact Or.inr (Or.inr ⟨c, fun x => LinearMap.congr_fun hc1 x, fun y => LinearMap.congr_fun hc2 y⟩)
    have h1080 := main_1080 ht (by decide : 3 ≤ 6) P Q hP hQ s hPsurj hQsurj hedge
    omega
  obtain ⟨e6, hu6, hv6, hne6⟩ := hex_e6
  have h61 := six_plus_one_bound ht P Q (fun c => u (s c)) (fun c => v (s c)) hPind hQind
    (u e6) (v e6) hu6 hv6 hne6 (fun x y hxy => by
      have he := (hhits_edges x.1 y.1).mp hxy
      exact ⟨fun c => he (s c), he e6⟩)
  have hnum := numVal_ge_348 (by omega : 3 ≤ t)
  exact h61.trans (Nat.mul_le_mul_right _ (by omega))

lemma rect_bound {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t)
    (P Q : Submodule F (Lane t)) (hP : P ≤ codeSub t) (hQ : Q ≤ codeSub t)
    (hdim : 3 * t + 1 ≤ Module.finrank F P + Module.finrank F Q) :
    2048 * rectHits ht P Q ≤ numVal t * (Nat.card P * Nat.card Q) := by
  refine rect_bound_of_eq_and_le ht ht2 ?_ P Q hP hQ hdim
  intro A B hA hB hsum hle
  by_cases ht2eq : t = 2
  · subst ht2eq
    exact rect_case_t2 ht A B hA hB hsum hle
  · have ht3 : 3 ≤ t := by omega
    have hCdim := codeSub_finrank ht
    have hBle := Submodule.finrank_mono hB
    have hAge3 : 3 ≤ Module.finrank F A := by omega
    by_cases hA3 : Module.finrank F A = 3
    · exact rect_case_3A ht ht3 A B hA hB hA3 hsum
    · by_cases hA4 : Module.finrank F A = 4
      · exact rect_case_3B ht ht3 A B hA hB hA4 hsum
      · by_cases hA5 : Module.finrank F A = 5
        · exact rect_case_3D ht ht3 A B hA hB hA5 hsum
        · have hA6 : 6 ≤ Module.finrank F A := by omega
          have ht4 : 4 ≤ t := by omega
          exact rect_case_3C ht ht4 A B hA hB hA6 hle hsum

lemma coset_upper {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t)
    (name c : Word t) (K : Submodule F (Word t))
    (hK : 3 * t + 5 ≤ Module.finrank F K) (w0 : Word t)
    (A : Word t →ₗ[F] Word t) (b : Word t) :
    2048 * Nat.card {x : K // outn (6 * t) (by omega) name c (w0 + x.1) = A (w0 + x.1) + b} ≤
      numVal t * Nat.card K := by
  let L : Word t →ₗ[F] Word t :=
    (Qw ht (evenLane ht w0)).comp (oddLane ht) +
    ((Qw ht).flip (oddLane ht w0)).comp (evenLane ht) +
    Lbase ht name + A
  let d : Word t := outn (6 * t) (by omega) name c w0 + A w0 + b
  have heq : ∀ x : K, (outn (6 * t) (by omega) name c (w0 + x.1) = A (w0 + x.1) + b) ↔
      Qw ht (evenLane ht x.1) (oddLane ht x.1) = L x.1 + d := by
    intro x
    have h1 := outn_normal ht name c (w0 + x.1)
    have h0 := outn_normal ht name c w0
    have hz2 : ∀ p q : F, p = q ↔ p + q = 0 := by decide
    rw [funext_iff, funext_iff]
    refine forall_congr' fun i => ?_
    rw [h1]
    simp only [Pi.add_apply, map_add, LinearMap.add_apply, LinearMap.comp_apply,
      LinearMap.flip_apply, L, d]
    rw [h0]
    simp only [Pi.add_apply]
    rw [hz2 (_ + _), hz2 (Qw ht (evenLane ht x.1) (oddLane ht x.1) i)]
    exact Iff.of_eq (congrArg (· = 0) (by ring))
  have hcard_eq : Nat.card {x : K // outn (6 * t) (by omega) name c (w0 + x.1) = A (w0 + x.1) + b} =
      Nat.card {x : K // Qw ht (evenLane ht x.1) (oddLane ht x.1) = L x.1 + d} :=
    Nat.card_congr (Equiv.subtypeEquivRight heq)
  rw [hcard_eq]
  let KZ : Submodule F (Word t) := K ⊓ LinearMap.ker (evenLane ht)
  let fE : K →ₗ[F] Lane t := (evenLane ht).comp K.subtype
  let U : Submodule F (Lane t) := LinearMap.range fE
  let fO : KZ →ₗ[F] Lane t := (oddLane ht).comp KZ.subtype
  let V : Submodule F (Lane t) := LinearMap.range fO
  have hU : U ≤ codeSub t := by
    rintro _ ⟨x, rfl⟩
    exact evenLane_mem_codeSub ht x.1
  have hV : V ≤ codeSub t := by
    rintro _ ⟨x, rfl⟩
    exact oddLane_mem_codeSub ht x.1
  have hkerE : Module.finrank F (LinearMap.ker fE) = Module.finrank F KZ := by
    let e : LinearMap.ker fE ≃ₗ[F] KZ :=
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact e.finrank_eq
  have hkerO_le : Module.finrank F (LinearMap.ker fO) ≤ 4 := by
    let g : LinearMap.ker fO →ₗ[F] LinearMap.ker ((evenLane ht).prod (oddLane ht)) :=
      { toFun := fun x => ⟨x.1.1, by
          rw [LinearMap.mem_ker, LinearMap.prod_apply, Prod.mk_eq_zero]
          exact ⟨x.1.2.2, x.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hginj : Function.Injective g := fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun z => z.1) hab))
    exact (LinearMap.finrank_le_finrank_of_injective hginj).trans_eq (ker_lanes_finrank ht)
  have hdim_sum : 3 * t + 1 ≤ Module.finrank F U + Module.finrank F V := by
    have h1 : Module.finrank F U + Module.finrank F (LinearMap.ker fE) = Module.finrank F K :=
      LinearMap.finrank_range_add_finrank_ker fE
    have h2 : Module.finrank F V + Module.finrank F (LinearMap.ker fO) = Module.finrank F KZ :=
      LinearMap.finrank_range_add_finrank_ker fO
    rw [hkerE] at h1
    omega
  have hrect := rect_bound ht ht2 U V hU hV hdim_sum
  have hpc := pull_count (fE.rangeRestrict.prodMap fO.rangeRestrict)
    (by
      rintro ⟨y1, y2⟩
      obtain ⟨x1, hx1⟩ := y1.2
      obtain ⟨x2, hx2⟩ := y2.2
      exact ⟨(x1, x2), Prod.ext (Subtype.ext hx1) (Subtype.ext hx2)⟩)
    (fun z : U × V => hitsAt ht z.1.1 z.2.1)
  rw [Nat.card_prod, Nat.card_prod] at hpc
  have hdc := quad_double_count ht K KZ (fun x => by
    simp only [KZ, Submodule.mem_inf, LinearMap.mem_ker]) L d
  have hposU : 0 < Nat.card U := Nat.card_pos
  have hposV : 0 < Nat.card V := Nat.card_pos
  have hposKZ : 0 < Nat.card KZ := Nat.card_pos
  have hmul : (Nat.card KZ * (Nat.card U * Nat.card V)) *
      (2048 * Nat.card {x : K // Qw ht (evenLane ht x.1) (oddLane ht x.1) = L x.1 + d}) ≤
      (Nat.card KZ * (Nat.card U * Nat.card V)) * (numVal t * Nat.card K) := by
    calc (Nat.card KZ * (Nat.card U * Nat.card V)) *
          (2048 * Nat.card {x : K // Qw ht (evenLane ht x.1) (oddLane ht x.1) = L x.1 + d})
        = 2048 * ((Nat.card KZ * Nat.card {x : K // Qw ht (evenLane ht x.1) (oddLane ht x.1) = L x.1 + d}) *
            (Nat.card U * Nat.card V)) := by ring
      _ ≤ 2048 * (Nat.card {z : K × KZ // hitsAt ht (evenLane ht z.1.1) (oddLane ht z.2.1)} *
            (Nat.card U * Nat.card V)) :=
          Nat.mul_le_mul_left 2048 (Nat.mul_le_mul_right _ hdc)
      _ = 2048 * (Nat.card K * Nat.card KZ * rectHits ht U V) :=
          congrArg (2048 * ·) hpc
      _ = Nat.card K * Nat.card KZ * (2048 * rectHits ht U V) := by ring
      _ ≤ Nat.card K * Nat.card KZ * (numVal t * (Nat.card U * Nat.card V)) :=
          Nat.mul_le_mul_left _ hrect
      _ = (Nat.card KZ * (Nat.card U * Nat.card V)) * (numVal t * Nat.card K) := by ring
  exact Nat.le_of_mul_le_mul_left hmul (Nat.mul_pos hposKZ (Nat.mul_pos hposU hposV))

lemma adaptive_upper {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t)
    (name c : Word t) (ask : Fin (3 * t - 5) → ℕ → Word t →ₗ[F] F)
    (A : ℕ → Word t →ₗ[F] Word t) (b : ℕ → Word t) :
    2048 * Nat.card {w : Word t //
        outn (6 * t) (by omega) name c w =
          A (runn (6 * t) (3 * t - 5) ask w) w + b (runn (6 * t) (3 * t - 5) ask w)} ≤
      numVal t * 2 ^ (6 * t) := by
  classical
  let f : Word t → ℕ := runn (6 * t) (3 * t - 5) ask
  let P : Word t → Prop := fun w => outn (6 * t) (by omega) name c w = A (f w) w + b (f w)
  let imgs : Finset ℕ := Finset.univ.image f
  have hpart_tot : (∑ r ∈ imgs, (Finset.univ.filter (fun w : Word t => f w = r)).card) = 2 ^ (6 * t) := by
    rw [← Finset.card_biUnion]
    · have hun : imgs.biUnion (fun r => Finset.univ.filter (fun w : Word t => f w = r)) = Finset.univ := by
        ext w
        simp only [Finset.mem_biUnion, imgs, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_filter, iff_true]
        exact ⟨f w, ⟨w, rfl⟩, rfl⟩
      rw [hun, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    · intro r1 _ r2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hpart_hit : Nat.card {w : Word t // P w} =
      ∑ r ∈ imgs, (Finset.univ.filter (fun w : Word t => P w ∧ f w = r)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.card_biUnion]
    · congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, imgs,
        Finset.mem_image]
      constructor
      · intro hp; exact ⟨f w, ⟨w, rfl⟩, hp, rfl⟩
      · rintro ⟨_, _, hp, _⟩; exact hp
    · intro r1 _ r2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2)
  rw [hpart_hit, Finset.mul_sum, ← hpart_tot, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  obtain ⟨w0, _, hw0⟩ := Finset.mem_image.mp hr
  obtain ⟨K, hKcoset, hKdim⟩ := cell_coset (6 * t) (3 * t - 5) ask w0
  have hK5 : 3 * t + 5 ≤ Module.finrank F K := by omega
  have hcu := coset_upper ht ht2 name c K hK5 w0 (A r) (b r)
  have eK : (Finset.univ.filter (fun w : Word t => f w = r)).card = Nat.card K := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun w => ⟨w.1 - w0, (hKcoset w.1).mp (w.2.trans hw0.symm)⟩
        invFun := fun x => ⟨w0 + x.1, ((hKcoset (w0 + x.1)).mpr (by rw [add_sub_cancel_left]; exact x.2)).trans hw0⟩
        left_inv := fun w => Subtype.ext (add_sub_cancel _ _)
        right_inv := fun x => Subtype.ext (add_sub_cancel_left _ _) }
  have eH : (Finset.univ.filter (fun w : Word t => P w ∧ f w = r)).card =
      Nat.card {x : K // outn (6 * t) (by omega) name c (w0 + x.1) = A r (w0 + x.1) + b r} := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun w =>
          ⟨⟨w.1 - w0, (hKcoset w.1).mp (w.2.2.trans hw0.symm)⟩, by
            have h1 := w.2.1
            dsimp only [P] at h1
            rw [w.2.2] at h1
            rwa [add_sub_cancel]⟩
        invFun := fun x =>
          ⟨w0 + x.1.1, by
            have hfx : f (w0 + x.1.1) = r :=
              ((hKcoset (w0 + x.1.1)).mpr (by rw [add_sub_cancel_left]; exact x.1.2)).trans hw0
            refine ⟨?_, hfx⟩
            dsimp only [P]
            rw [hfx]
            exact x.2⟩
        left_inv := fun w => Subtype.ext (add_sub_cancel _ _)
        right_inv := fun x => Subtype.ext (Subtype.ext (add_sub_cancel_left _ _)) }
  rw [eK, eH]
  exact hcu

lemma fixed_lower {t : ℕ} (ht : 0 < t) (ht2 : 2 ≤ t) (name c : Word t) :
    ∃ (A : ℕ → Word t →ₗ[F] Word t) (b : ℕ → Word t),
      2048 * Nat.card {w : Word t //
        outn (6 * t) (by omega) name c w =
          A (runn (6 * t) (3 * t - 5) (askFix ht) w) w +
          b (runn (6 * t) (3 * t - 5) (askFix ht) w)} =
        numVal t * 2 ^ (6 * t) := by
  classical
  let f : Word t → ℕ := runn (6 * t) (3 * t - 5) (askFix ht)
  let K : Submodule F (Word t) := LinearMap.ker (LinearMap.pi (fun j => askFix ht j 0))
  have hcoset : ∀ w0 w : Word t, f w = f w0 ↔ w - w0 ∈ K := by
    intro w0 w
    obtain ⟨p, hp⟩ := runn_eq_iff (6 * t) (3 * t - 5) (askFix ht) w0
    rw [hp w, LinearMap.mem_ker]
    constructor
    · intro hj; funext j; exact hj j
    · intro hj j; exact congrFun hj j
  let rep : ℕ → Word t := fun r =>
    if h : ∃ w : Word t, f w = r then Classical.choose h else 0
  have hrep : ∀ r : ℕ, (∃ w : Word t, f w = r) → f (rep r) = r := by
    intro r h
    simp only [rep, h, ↓reduceDIte]
    exact Classical.choose_spec h
  let A : ℕ → Word t →ₗ[F] Word t := fun r =>
    (Qw ht (evenLane ht (rep r))).comp (oddLane ht) +
    ((Qw ht).flip (oddLane ht (rep r))).comp (evenLane ht) +
    Lbase ht name
  let b : ℕ → Word t := fun r => outn (6 * t) (by omega) name c (rep r) + A r (rep r)
  refine ⟨A, b, ?_⟩
  let P : Word t → Prop := fun w => outn (6 * t) (by omega) name c w = A (f w) w + b (f w)
  let imgs : Finset ℕ := Finset.univ.image f
  have hpart_tot : (∑ r ∈ imgs, (Finset.univ.filter (fun w : Word t => f w = r)).card) = 2 ^ (6 * t) := by
    rw [← Finset.card_biUnion]
    · have hun : imgs.biUnion (fun r => Finset.univ.filter (fun w : Word t => f w = r)) = Finset.univ := by
        ext w
        simp only [Finset.mem_biUnion, imgs, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.mem_filter, iff_true]
        exact ⟨f w, ⟨w, rfl⟩, rfl⟩
      rw [hun, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    · intro r1 _ r2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hpart_hit : Nat.card {w : Word t // P w} =
      ∑ r ∈ imgs, (Finset.univ.filter (fun w : Word t => P w ∧ f w = r)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.card_biUnion]
    · congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, imgs,
        Finset.mem_image]
      constructor
      · intro hp; exact ⟨f w, ⟨w, rfl⟩, hp, rfl⟩
      · rintro ⟨_, _, hp, _⟩; exact hp
    · intro r1 _ r2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2)
  let φ : K →ₗ[F] Pfix ht × codeSub t :=
    { toFun := fun x =>
        (⟨evenLane ht x.1, evenLane_mem_codeSub ht x.1, by
          rw [SetLike.mem_coe, LinearMap.mem_ker]
          funext j
          have hx := congrFun x.2 j
          change askFix ht j 0 x.1 = 0 at hx
          rwa [askFix_eq_laneFix ht ht2] at hx⟩,
         ⟨oddLane ht x.1, oddLane_mem_codeSub ht x.1⟩)
      map_add' := fun _ _ => by apply Prod.ext <;> apply Subtype.ext <;> simp
      map_smul' := fun _ _ => by apply Prod.ext <;> apply Subtype.ext <;> simp }
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨⟨u, huC, huK⟩, ⟨v, hvC⟩⟩
    obtain ⟨w, hwE, hwO⟩ := lanes_surj ht u v huC hvC
    have hwK : w ∈ K := by
      rw [LinearMap.mem_ker]
      funext j
      change askFix ht j 0 w = 0
      rw [askFix_eq_laneFix ht ht2, hwE]
      exact congrFun huK j
    refine ⟨⟨w, hwK⟩, ?_⟩
    apply Prod.ext <;> apply Subtype.ext
    · exact hwE
    · exact hwO
  have hpc := pull_count φ hφ_surj (fun z : Pfix ht × codeSub t => hitsAt ht z.1.1 z.2.1)
  rw [Nat.card_prod] at hpc
  have hKeq : 2048 * Nat.card {x : K // hitsAt ht (evenLane ht x.1) (oddLane ht x.1)} =
      numVal t * Nat.card K := by
    have hmul : (Nat.card (Pfix ht) * Nat.card (codeSub t)) *
        (2048 * Nat.card {x : K // hitsAt ht (evenLane ht x.1) (oddLane ht x.1)}) =
        (Nat.card (Pfix ht) * Nat.card (codeSub t)) * (numVal t * Nat.card K) := by
      calc (Nat.card (Pfix ht) * Nat.card (codeSub t)) *
            (2048 * Nat.card {x : K // hitsAt ht (evenLane ht x.1) (oddLane ht x.1)})
          = 2048 * (Nat.card {x : K // hitsAt ht (evenLane ht x.1) (oddLane ht x.1)} *
              (Nat.card (Pfix ht) * Nat.card (codeSub t))) := by ring
        _ = 2048 * (Nat.card K * rectHits ht (Pfix ht) (codeSub t)) :=
            congrArg (2048 * ·) hpc
        _ = Nat.card K * (2048 * rectHits ht (Pfix ht) (codeSub t)) := by ring
        _ = Nat.card K * (numVal t * (Nat.card (Pfix ht) * Nat.card (codeSub t))) := by
            rw [Pfix_hits_eq ht ht2]
        _ = (Nat.card (Pfix ht) * Nat.card (codeSub t)) * (numVal t * Nat.card K) := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos Nat.card_pos Nat.card_pos) hmul
  rw [hpart_hit, Finset.mul_sum, ← hpart_tot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨w', _, hw'⟩ := Finset.mem_image.mp hr
  have hw0 : f (rep r) = r := hrep r ⟨w', hw'⟩
  have eK : (Finset.univ.filter (fun w : Word t => f w = r)).card = Nat.card K := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun w => ⟨w.1 - rep r, (hcoset (rep r) w.1).mp (w.2.trans hw0.symm)⟩
        invFun := fun x => ⟨rep r + x.1, ((hcoset (rep r) (rep r + x.1)).mpr (by rw [add_sub_cancel_left]; exact x.2)).trans hw0⟩
        left_inv := fun w => Subtype.ext (add_sub_cancel _ _)
        right_inv := fun x => Subtype.ext (add_sub_cancel_left _ _) }
  have hquad : ∀ x : K, (outn (6 * t) (by omega) name c (rep r + x.1) = A r (rep r + x.1) + b r) ↔
      hitsAt ht (evenLane ht x.1) (oddLane ht x.1) := by
    intro x
    rw [← Qw_eq_zero_iff ht]
    have h1 := outn_normal ht name c (rep r + x.1)
    have h0 := outn_normal ht name c (rep r)
    have hz2 : ∀ p q : F, p = q ↔ p + q = 0 := by decide
    rw [funext_iff, funext_iff]
    refine forall_congr' fun i => ?_
    have hEq :
        outn (6 * t) (by omega) name c (rep r + x.1) i + (A r (rep r + x.1) + b r) i =
        Qw ht (evenLane ht x.1) (oddLane ht x.1) i := by
      rw [h1]
      simp only [Pi.add_apply, map_add, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.flip_apply, A, b]
      rw [h0]
      simp only [Pi.add_apply]
      ring_nf
      simp only [show (2 : F) = 0 by decide, show (4 : F) = 0 by decide,
        show (6 : F) = 0 by decide, mul_zero, add_zero, zero_add]
    rw [hz2, hEq]
    rfl
  have eH : (Finset.univ.filter (fun w : Word t => P w ∧ f w = r)).card =
      Nat.card {x : K // hitsAt ht (evenLane ht x.1) (oddLane ht x.1)} := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun w =>
          ⟨⟨w.1 - rep r, (hcoset (rep r) w.1).mp (w.2.2.trans hw0.symm)⟩, by
            rw [← hquad]
            have h1 := w.2.1
            dsimp only [P] at h1
            rw [w.2.2] at h1
            rwa [add_sub_cancel]⟩
        invFun := fun x =>
          ⟨rep r + x.1.1, by
            have hfx : f (rep r + x.1.1) = r :=
              ((hcoset (rep r) (rep r + x.1.1)).mpr (by rw [add_sub_cancel_left]; exact x.1.2)).trans hw0
            refine ⟨?_, hfx⟩
            dsimp only [P]
            rw [hfx]
            exact (hquad x.1).mpr x.2⟩
        left_inv := fun w => Subtype.ext (add_sub_cancel _ _)
        right_inv := fun x => Subtype.ext (Subtype.ext (add_sub_cancel_left _ _)) }
  rw [eK, eH]
  exact hKeq

theorem main_proof : ∀ (t : ℕ) (ht : 0 < t), 2 ≤ t →
  let h := 3*t-5
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 5) ht)⟩ : Fin n)
  let rot := fun (s : ℕ) (w : W) (i : Fin n) => w (ix (i.val + n - s % n))
  let out := fun (name c raw : W) (i : Fin n) =>
    let old := rot 3 raw + name
    let y := fun j : Fin n => old j + old (ix (j.val+2)) + old (ix (j.val+n-2))
    y i + (1+y (ix (i.val+1)))*y (ix (i.val+2)) + rot 4 raw i + c i
  let run := fun (ask : Fin h → ℕ → W →ₗ[F] F) (w : W) =>
    (List.finRange h).foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)
  let mix := fun (w : W) (i : Fin n) =>
    let old := rot 3 w
    old i + old (ix (i.val+2)) + old (ix (i.val+n-2))
  let site := fun j : Fin h => if t = 3 then (if j.val < 2 then j.val+4 else j.val+5) else if j.val = 0 then 2 else if j.val < 3 then j.val+3 else if j.val < 5 then j.val+4 else j.val+5
  let num := if t = 2 then 416 else if t = 3 then 348 else if t = 4 then 354 else 353
  ∀ (name c : W) (fixed : Bool) (k : ℕ),
    (∃ (ask : Fin h → ℕ → W →ₗ[F] F) (A : ℕ → W →ₗ[F] W) (b : ℕ → W),
      (fixed = true → ∀ j p w, ask j p w =
        if t = 2 then mix w (ix 0) + mix w (ix 6) else mix w (ix (2*site j))) ∧
      k ≤ Nat.card {w : W // out name c w = A (run ask w) w + b (run ask w)}) ↔ 2048*k ≤ num*2^n := by
  intro t ht ht2 h F' n W ix rot out run mix site num name c fixed k
  have hup_eq : ∀ (ask : Fin h → ℕ → W →ₗ[F'] F') (A : ℕ → W →ₗ[F'] W) (b : ℕ → W),
      Nat.card {w : W // out name c w = A (run ask w) w + b (run ask w)} =
      Nat.card {w : Word t //
        outn (6 * t) (by omega) name c w =
          A (runn (6 * t) (3 * t - 5) ask w) w + b (runn (6 * t) (3 * t - 5) ask w)} := by
    intro ask A b
    refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
    rfl
  have hnum : numVal t = num := by unfold numVal; dsimp only [num]; split_ifs <;> rfl
  have hsite : ∀ j : Fin h, siteVal t j = site j := fun j => by
    unfold siteVal; dsimp only [site]; split_ifs <;> rfl
  constructor
  · rintro ⟨ask, A, b, _, hk⟩
    have hup := adaptive_upper ht ht2 name c ask A b
    rw [hup_eq ask A b] at hk
    have hk' : 2048 * k ≤ 2048 * Nat.card {w : Word t //
        outn (6 * t) (by omega) name c w =
          A (runn (6 * t) (3 * t - 5) ask w) w + b (runn (6 * t) (3 * t - 5) ask w)} :=
      Nat.mul_le_mul_left 2048 hk
    have hres := hk'.trans hup
    rwa [hnum] at hres
  · intro hle
    obtain ⟨A, b, hlow⟩ := fixed_lower ht ht2 name c
    refine ⟨askFix ht, A, b, ?_, ?_⟩
    · intro _ j p w
      unfold askFix
      by_cases h2 : t = 2
      · simp only [h2, ↓reduceIte]; rfl
      · simp only [h2, ↓reduceIte, hsite j, mixL, LinearMap.coe_mk, AddHom.coe_mk]; rfl
    · rw [hup_eq (askFix ht) A b]
      have : 2048 * k ≤ 2048 * Nat.card {w : Word t //
          outn (6 * t) (by omega) name c w =
            A (runn (6 * t) (3 * t - 5) (askFix ht) w) w +
            b (runn (6 * t) (3 * t - 5) (askFix ht) w)} := by
        rw [hlow, hnum]
        exact hle
      exact Nat.le_of_mul_le_mul_left this (by norm_num)

end PEqualNP.Outside.L_meta_33677_aux

theorem PEqualNP.Outside.L_meta_33677 : (∀ (t : ℕ) (ht : 0 < t), 2 ≤ t →
  let h := 3*t-5
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let n := 6*t
  let W := Fin n → F
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ (Nat.mul_pos (Nat.zero_lt_succ 5) ht)⟩ : Fin n)
  let rot := fun (s : ℕ) (w : W) (i : Fin n) => w (ix (i.val + n - s % n))
  let out := fun (name c raw : W) (i : Fin n) =>
    let old := rot 3 raw + name
    let y := fun j : Fin n => old j + old (ix (j.val+2)) + old (ix (j.val+n-2))
    y i + (1+y (ix (i.val+1)))*y (ix (i.val+2)) + rot 4 raw i + c i
  let run := fun (ask : Fin h → ℕ → W →ₗ[F] F) (w : W) =>
    (List.finRange h).foldl (fun z i => 2*z + (if ask i z w = 0 then 0 else 1)) (0 : ℕ)
  let mix := fun (w : W) (i : Fin n) =>
    let old := rot 3 w
    old i + old (ix (i.val+2)) + old (ix (i.val+n-2))
  let site := fun j : Fin h => if t = 3 then (if j.val < 2 then j.val+4 else j.val+5) else if j.val = 0 then 2 else if j.val < 3 then j.val+3 else if j.val < 5 then j.val+4 else j.val+5
  let num := if t = 2 then 416 else if t = 3 then 348 else if t = 4 then 354 else 353
  ∀ (name c : W) (fixed : Bool) (k : ℕ),
    (∃ (ask : Fin h → ℕ → W →ₗ[F] F) (A : ℕ → W →ₗ[F] W) (b : ℕ → W),
      (fixed = true → ∀ j p w, ask j p w =
        if t = 2 then mix w (ix 0) + mix w (ix 6) else mix w (ix (2*site j))) ∧
      k ≤ Nat.card {w : W // out name c w = A (run ask w) w + b (run ask w)}) ↔ 2048*k ≤ num*2^n) :=
  PEqualNP.Outside.L_meta_33677_aux.main_proof
