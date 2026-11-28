import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_404_aux
open Finset

abbrev X (r : ℕ) := Fin r → Fin 3 → ZMod 2

def t (x : Fin 3 → ZMod 2) : ZMod 2 := x 2 + x 0 * x 1

def tgt {r : ℕ} (z : X r) : Fin r → ZMod 2 := fun i => t (z i)

def g1 (u : Fin 3 → ZMod 2) : ℕ := (univ.filter (fun x : Fin 3 → ZMod 2 => t (x + u) = t x)).card

theorem g1_le : ∀ u : Fin 3 → ZMod 2, g1 u ≤ 4 + 4 * (if u = 0 then 1 else 0) := by decide

theorem g1_sum : ∑ u : Fin 3 → ZMod 2, g1 u = 32 := by decide

def G {r : ℕ} (s : Finset (Fin r)) (v : X r) : ℕ := ∏ i ∈ s, g1 (v i)

def sub {r : ℕ} (K : AddSubgroup (X r)) (j : Fin r) : AddSubgroup (X r) :=
  K ⊓ (Pi.evalAddMonoidHom (fun _ : Fin r => Fin 3 → ZMod 2) j).ker

theorem mem_sub {r : ℕ} (K : AddSubgroup (X r)) (j : Fin r) (w : X r) :
    w ∈ sub K j ↔ w ∈ K ∧ w j = 0 := by
  simp [sub, AddSubgroup.mem_inf, AddMonoidHom.mem_ker]

theorem Kf_dvd {r : ℕ} (K : AddSubgroup (X r)) [DecidablePred (· ∈ K)] :
    (univ.filter (fun v => v ∈ K)).card ∣ 2 ^ (3 * r) := by
  have h1 := AddSubgroup.card_addSubgroup_dvd_card K
  have h2 : Nat.card K = (univ.filter (fun v => v ∈ K)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h3 : Nat.card (X r) = 2 ^ (3 * r) := by
    rw [Nat.card_eq_fintype_card]; simp [pow_mul]
  rw [h2, h3] at h1
  exact h1

theorem blockU (U : Finset (Fin 3 → ZMod 2)) {n : ℕ} (h : U.card ∣ 2 ^ n) :
    (∑ u ∈ U, g1 u) ^ 3 ≤ 512 * U.card ^ 2 := by
  obtain ⟨e, -, hUe⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  have h8 : U.card ≤ 8 := by simpa using U.card_le_univ
  by_cases hfull : U.card = 8
  · have : U = univ := Finset.eq_univ_of_card U (by simp [hfull])
    rw [this, g1_sum]; simp
  · have hsum : ∑ u ∈ U, g1 u ≤ 4 * U.card + 4 := by
      calc ∑ u ∈ U, g1 u ≤ ∑ u ∈ U, (4 + 4 * (if u = 0 then 1 else 0)) :=
            Finset.sum_le_sum (fun u _ => g1_le u)
        _ = 4 * U.card + 4 * ∑ u ∈ U, (if u = 0 then 1 else 0) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul]; ring
        _ ≤ 4 * U.card + 4 := by
            have : ∑ u ∈ U, (if u = 0 then 1 else 0 : ℕ) ≤ 1 := by
              rw [Finset.sum_ite_eq']; split_ifs <;> simp
            omega
    have he3 : e ≤ 2 := by
      by_contra hc0
      have hc : 3 ≤ e := by omega
      have : 2 ^ 3 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hc
      norm_num at this
      omega
    have hsum3 : (∑ u ∈ U, g1 u) ^ 3 ≤ (4 * U.card + 4) ^ 3 := Nat.pow_le_pow_left hsum 3
    rw [hUe] at hsum3 ⊢
    interval_cases e <;> norm_num at hsum3 ⊢ <;> omega

theorem tens {r : ℕ} (s : Finset (Fin r)) : ∀ (K : AddSubgroup (X r)) [DecidablePred (· ∈ K)],
    (∀ v ∈ K, ∀ i ∉ s, v i = 0) → ∀ a : X r,
    (∑ v ∈ univ.filter (fun v => v ∈ K), G s (a + v)) ^ 3
      ≤ 512 ^ s.card * (univ.filter (fun v => v ∈ K)).card ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro K _ hK a
    have e : univ.filter (fun v => v ∈ K) = {0} := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro hv; funext i; exact hK v hv i (Finset.notMem_empty i)
      · rintro rfl; exact K.zero_mem
    rw [e]; simp [G]
  | insert j s hj ih =>
    intro K _ hK a
    have hK' : ∀ v ∈ sub K j, ∀ i ∉ s, v i = 0 := by
      intro v hv i hi
      by_cases hij : i = j
      · subst hij; exact ((mem_sub K i v).1 hv).2
      · exact hK v ((mem_sub K j v).1 hv).1 i (by simp [hij, hi])
    obtain ⟨Kf, hKf⟩ : ∃ Kf, Kf = univ.filter (fun v => v ∈ K) := ⟨_, rfl⟩
    obtain ⟨Kf', hKf'⟩ : ∃ Kf', Kf' = univ.filter (fun v => v ∈ sub K j) := ⟨_, rfl⟩
    rw [← hKf]
    obtain ⟨S, hS⟩ : ∃ S : (Fin 3 → ZMod 2) → Finset (X r),
        S = fun u => Kf.filter (fun v => (a + v) j = u) := ⟨_, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x : (Fin 3 → ZMod 2) → ℕ, x = fun u => ∑ v ∈ S u, G s (a + v) := ⟨_, rfl⟩
    have memS : ∀ u v, v ∈ S u ↔ v ∈ K ∧ (a + v) j = u := by
      intro u v; simp [hS, hKf]
    have fib : ∀ u, (S u).Nonempty →
        (S u).card = Kf'.card ∧ x u ^ 3 ≤ 512 ^ s.card * Kf'.card ^ 2 := by
      intro u ⟨b, hb⟩
      have hb' := (memS u b).1 hb
      have hmem : ∀ w ∈ Kf', b + w ∈ S u := by
        intro w hw
        have hw' : w ∈ K ∧ w j = 0 := by
          rw [hKf', mem_filter] at hw; exact (mem_sub K j w).1 hw.2
        rw [memS]
        refine ⟨K.add_mem hb'.1 hw'.1, ?_⟩
        rw [← add_assoc, Pi.add_apply, hw'.2, add_zero]; exact hb'.2
      have hmem2 : ∀ v ∈ S u, v - b ∈ Kf' := by
        intro v hv
        have hv' := (memS u v).1 hv
        rw [hKf', mem_filter]
        refine ⟨mem_univ _, (mem_sub K j _).2 ⟨K.sub_mem hv'.1 hb'.1, ?_⟩⟩
        have e1 := hv'.2
        have e2 := hb'.2
        simp only [Pi.add_apply] at e1 e2
        have : v j = b j := add_left_cancel (e1.trans e2.symm)
        simp [this]
      constructor
      · exact (Finset.card_nbij' (fun w => b + w) (fun v => v - b) hmem hmem2
          (by intro w _; simp) (by intro v _; simp)).symm
      · have hxu : x u = ∑ w ∈ Kf', G s ((a + b) + w) := by
          rw [hx]
          refine Finset.sum_nbij' (fun v => v - b) (fun w => b + w) hmem2 hmem
            (by intro v _; simp) (by intro w _; simp) ?_
          intro v _
          congr 1; abel
        rw [hxu, hKf']
        exact ih (sub K j) hK' (a + b)
    have htot : ∑ v ∈ Kf, G (insert j s) (a + v) = ∑ u, g1 u * x u := by
      have e1 : ∀ v, G (insert j s) (a + v) = g1 ((a + v) j) * G s (a + v) := by
        intro v; simp [G, Finset.prod_insert hj]
      simp_rw [e1]
      rw [← Finset.sum_fiberwise Kf (fun v => (a + v) j)]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [hx, hS]
      dsimp only
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v hv => ?_)
      rw [(Finset.mem_filter.1 hv).2]
    have hcard : Kf.card = ∑ u, (S u).card := by
      rw [hS]
      exact Finset.card_eq_sum_card_fiberwise (f := fun v => (a + v) j) (t := univ) (by simp)
    obtain ⟨U, hU⟩ : ∃ U, U = univ.filter (fun u => (S u).Nonempty) := ⟨_, rfl⟩
    have hcardU : Kf.card = U.card * Kf'.card := by
      rw [hcard, ← Finset.sum_filter_add_sum_filter_not univ (fun u => (S u).Nonempty)]
      rw [Finset.sum_congr rfl (fun u hu => (fib u (Finset.mem_filter.1 hu).2).1)]
      rw [Finset.sum_eq_zero (fun u hu => Finset.card_eq_zero.2
        (Finset.not_nonempty_iff_eq_empty.1 (Finset.mem_filter.1 hu).2))]
      rw [Finset.sum_const, smul_eq_mul, add_zero, hU]
    have htot2 : ∑ u, g1 u * x u = ∑ u ∈ U, g1 u * x u := by
      rw [hU]
      refine (Finset.sum_filter_of_ne (fun u _ hne => ?_)).symm
      by_contra hc
      apply hne
      have hSe : S u = ∅ := Finset.not_nonempty_iff_eq_empty.1 hc
      simp [hx, hSe]
    have hUne : U.Nonempty := by
      refine ⟨a j, ?_⟩
      rw [hU, mem_filter]
      exact ⟨mem_univ _, ⟨0, (memS _ _).2 ⟨K.zero_mem, by simp⟩⟩⟩
    obtain ⟨u0, hu0, hmax⟩ := Finset.exists_max_image U x hUne
    have hle : ∑ u ∈ U, g1 u * x u ≤ (∑ u ∈ U, g1 u) * x u0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun u hu => Nat.mul_le_mul_left _ (hmax u hu))
    have hx0 := (fib u0 (by rw [hU] at hu0; exact (Finset.mem_filter.1 hu0).2)).2
    have hUdvd : U.card ∣ 2 ^ (3 * r) :=
      (Dvd.intro _ hcardU.symm).trans (by rw [hKf]; exact Kf_dvd K)
    have hblk := blockU U hUdvd
    calc (∑ v ∈ Kf, G (insert j s) (a + v)) ^ 3 = (∑ u ∈ U, g1 u * x u) ^ 3 := by
          rw [htot, htot2]
      _ ≤ ((∑ u ∈ U, g1 u) * x u0) ^ 3 := Nat.pow_le_pow_left hle 3
      _ = (∑ u ∈ U, g1 u) ^ 3 * x u0 ^ 3 := mul_pow _ _ _
      _ ≤ (512 * U.card ^ 2) * (512 ^ s.card * Kf'.card ^ 2) := Nat.mul_le_mul hblk hx0
      _ = 512 ^ (insert j s).card * Kf.card ^ 2 := by
          rw [Finset.card_insert_of_notMem hj, hcardU]; ring

def gg {r : ℕ} (w : X r) : ℕ := (univ.filter (fun z : X r => tgt (z + w) = tgt z)).card

theorem gg_eq {r : ℕ} (w : X r) : gg w = G univ w := by
  have : univ.filter (fun z : X r => tgt (z + w) = tgt z)
      = Fintype.piFinset (fun i => univ.filter (fun x : Fin 3 → ZMod 2 => t (x + w i) = t x)) := by
    ext z; simp [Fintype.mem_piFinset, tgt, funext_iff]
  rw [gg, this, Fintype.card_piFinset]; rfl

theorem conv (r k d : ℕ) (ask : X r →ₗ[ZMod 2] (Fin d → ZMod 2))
    (out : (Fin d → ZMod 2) → Finset (Fin r → ZMod 2))
    (h : ∀ z, (out (ask z)).card ≤ 2 ^ k ∧ tgt z ∈ out (ask z)) : 3 * r ≤ d + 3 * k := by
  classical
  obtain ⟨Kf, hKf⟩ : ∃ Kf, Kf = univ.filter (fun v : X r => ask v = 0) := ⟨_, rfl⟩
  have memK : ∀ v, v ∈ Kf ↔ ask v = 0 := by intro v; simp [hKf]
  have hm : 0 < Kf.card := Finset.card_pos.2 ⟨0, (memK 0).2 (map_zero ask)⟩

  have hD : 8 ^ r ≤ 2 ^ d * Kf.card := by
    have e1 : (univ : Finset (X r)).card
        = ∑ a ∈ univ.image ask, (univ.filter (fun z => ask z = a)).card :=
      Finset.card_eq_sum_card_image ask univ
    have e2 : ∀ a ∈ univ.image ask, (univ.filter (fun z => ask z = a)).card = Kf.card := by
      intro a ha
      obtain ⟨z0, -, rfl⟩ := Finset.mem_image.1 ha
      refine Finset.card_nbij' (fun z => z - z0) (fun v => z0 + v) ?_ ?_ ?_ ?_
      · intro z hz
        simp only [Finset.mem_coe] at hz ⊢
        rw [memK, map_sub, (Finset.mem_filter.1 hz).2, sub_self]
      · intro v hv
        simp only [Finset.mem_coe] at hv ⊢
        rw [Finset.mem_filter]
        exact ⟨mem_univ _, by rw [map_add, (memK v).1 hv, add_zero]⟩
      · intro z _; simp
      · intro v _; simp
    rw [Finset.sum_congr rfl e2, Finset.sum_const, smul_eq_mul, Finset.card_univ] at e1
    have hc : Fintype.card (X r) = 8 ^ r := by simp
    rw [hc] at e1
    rw [e1]
    refine Nat.mul_le_mul_right _ ?_
    have := (univ.image ask).card_le_univ
    simpa using this

  have hB : 8 ^ r * Kf.card ≤ 2 ^ k * ∑ w ∈ Kf, gg w := by
    have hz : ∀ z : X r, Kf.card ^ 2 ≤
        2 ^ k * ∑ v ∈ Kf, ∑ v' ∈ Kf, (if tgt (z + v') = tgt (z + v) then 1 else 0) := by
      intro z
      have hmap : ∀ v ∈ Kf, tgt (z + v) ∈ out (ask z) := by
        intro v hv
        have := (h (z + v)).2
        rwa [map_add, (memK v).1 hv, add_zero] at this
      have e1 : Kf.card = ∑ y ∈ out (ask z), (Kf.filter (fun v => tgt (z + v) = y)).card :=
        Finset.card_eq_sum_card_fiberwise hmap
      have e2 : ∑ y ∈ out (ask z), (Kf.filter (fun v => tgt (z + v) = y)).card ^ 2
          = ∑ v ∈ Kf, ∑ v' ∈ Kf, (if tgt (z + v') = tgt (z + v) then 1 else 0) := by
        rw [← Finset.sum_fiberwise_of_maps_to hmap
          (fun v => ∑ v' ∈ Kf, if tgt (z + v') = tgt (z + v) then 1 else 0)]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        calc (Kf.filter (fun v => tgt (z + v) = y)).card ^ 2
            = ∑ v ∈ Kf.filter (fun v => tgt (z + v) = y),
                (Kf.filter (fun v => tgt (z + v) = y)).card := by
              rw [Finset.sum_const, smul_eq_mul, sq]
          _ = _ := by
              refine Finset.sum_congr rfl (fun v hv => ?_)
              rw [(Finset.mem_filter.1 hv).2, Finset.card_filter]
      calc Kf.card ^ 2
          = (∑ y ∈ out (ask z), (Kf.filter (fun v => tgt (z + v) = y)).card) ^ 2 := by rw [← e1]
        _ ≤ (out (ask z)).card *
              ∑ y ∈ out (ask z), (Kf.filter (fun v => tgt (z + v) = y)).card ^ 2 :=
            sq_sum_le_card_mul_sum_sq
        _ ≤ 2 ^ k * ∑ y ∈ out (ask z), (Kf.filter (fun v => tgt (z + v) = y)).card ^ 2 :=
            Nat.mul_le_mul_right _ (h z).1
        _ = _ := by rw [e2]
    have hsum := Finset.sum_le_sum (s := (univ : Finset (X r))) (fun z _ => hz z)
    have e3 : ∀ v v' : X r,
        ∑ z : X r, (if tgt (z + v') = tgt (z + v) then 1 else 0) = gg (v' - v) := by
      intro v v'
      rw [gg, Finset.card_filter]
      refine Fintype.sum_equiv (Equiv.addRight v) _ _ (fun z => ?_)
      have e : z + v + (v' - v) = z + v' := by abel
      simp only [Equiv.coe_addRight, e]
    have e4 : ∀ v ∈ Kf, ∑ v' ∈ Kf, gg (v' - v) = ∑ w ∈ Kf, gg w := by
      intro v hv
      refine Finset.sum_nbij' (fun v' => v' - v) (fun w => w + v) ?_ ?_ ?_ ?_ ?_
      · intro v' hv'; rw [memK, map_sub, (memK _).1 hv', (memK _).1 hv, sub_self]
      · intro w hw; rw [memK, map_add, (memK _).1 hw, (memK _).1 hv, add_zero]
      · intro v' _; simp
      · intro w _; simp
      · intro v' _; rfl
    have hR : ∑ z : X r, 2 ^ k * ∑ v ∈ Kf, ∑ v' ∈ Kf,
        (if tgt (z + v') = tgt (z + v) then 1 else 0) = 2 ^ k * (Kf.card * ∑ w ∈ Kf, gg w) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun v _ => Finset.sum_comm)]
      rw [Finset.sum_congr rfl (fun v hv => (Finset.sum_congr rfl (fun v' _ => e3 v v')).trans
        (e4 v hv))]
      rw [Finset.sum_const, smul_eq_mul]
    rw [hR, Finset.sum_const, smul_eq_mul, Finset.card_univ] at hsum
    have hc : Fintype.card (X r) = 8 ^ r := by simp
    rw [hc] at hsum
    refine Nat.le_of_mul_le_mul_left ?_ hm
    calc Kf.card * (8 ^ r * Kf.card) = 8 ^ r * Kf.card ^ 2 := by ring
      _ ≤ 2 ^ k * (Kf.card * ∑ w ∈ Kf, gg w) := hsum
      _ = Kf.card * (2 ^ k * ∑ w ∈ Kf, gg w) := by ring

  have hA : (∑ w ∈ Kf, gg w) ^ 3 ≤ 512 ^ r * Kf.card ^ 2 := by
    have := tens (Finset.univ : Finset (Fin r)) (LinearMap.ker ask).toAddSubgroup
      (by intro v _ i hi; exact absurd (mem_univ i) hi) 0
    have e : univ.filter (fun v => v ∈ (LinearMap.ker ask).toAddSubgroup) = Kf := by
      ext v; rw [memK]; simp
    rw [e, Finset.card_univ, Fintype.card_fin] at this
    simpa [gg_eq] using this

  have h512 : (512 : ℕ) ^ r = (8 ^ r) ^ 3 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h8k : ((2 : ℕ) ^ k) ^ 3 = 8 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h1 : (512 ^ r * Kf.card ^ 2) * Kf.card ≤ (512 ^ r * Kf.card ^ 2) * 8 ^ k := by
    calc (512 ^ r * Kf.card ^ 2) * Kf.card = (8 ^ r * Kf.card) ^ 3 := by rw [h512]; ring
      _ ≤ (2 ^ k * ∑ w ∈ Kf, gg w) ^ 3 := Nat.pow_le_pow_left hB 3
      _ = 8 ^ k * (∑ w ∈ Kf, gg w) ^ 3 := by rw [mul_pow, h8k]
      _ ≤ 8 ^ k * (512 ^ r * Kf.card ^ 2) := Nat.mul_le_mul_left _ hA
      _ = _ := by ring
  have h2 : Kf.card ≤ 8 ^ k := Nat.le_of_mul_le_mul_left h1 (by positivity)
  have h3 : 2 ^ (3 * r) ≤ 2 ^ (d + 3 * k) := by
    calc 2 ^ (3 * r) = 8 ^ r := by rw [pow_mul]; norm_num
      _ ≤ 2 ^ d * Kf.card := hD
      _ ≤ 2 ^ d * 8 ^ k := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (d + 3 * k) := by rw [pow_add, pow_mul]; norm_num
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h3

def askL (r k d : ℕ) : X r →ₗ[ZMod 2] (Fin d → ZMod 2) :=
  LinearMap.pi (fun i : Fin d => if h : i.val < 3 * (r - k) then
    (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 3 => ZMod 2)
        (⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3)).comp
      (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin r => Fin 3 → ZMod 2)
        (⟨i.val / 3, by omega⟩ : Fin r))
    else 0)

theorem askL_apply (r k d : ℕ) (z : X r) (i : Fin d) (hi : i.val < 3 * (r - k)) (j : Fin r)
    (c : Fin 3) (hj : i.val / 3 = j.val) (hc : i.val % 3 = c.val) : askL r k d z i = z j c := by
  simp only [askL, LinearMap.pi_apply, hi, dite_true, LinearMap.comp_apply, LinearMap.proj_apply]
  have e1 : (⟨i.val / 3, by omega⟩ : Fin r) = j := Fin.ext hj
  have e2 : (⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) = c := Fin.ext hc
  rw [e1, e2]

theorem fwd (r k d : ℕ) (hk : k ≤ r) (hd : 3 * (r - k) ≤ d) :
    ∃ (ask : X r →ₗ[ZMod 2] (Fin d → ZMod 2)) (out : (Fin d → ZMod 2) → Finset (Fin r → ZMod 2)),
      ∀ z, (out (ask z)).card ≤ 2 ^ k ∧ tgt z ∈ out (ask z) := by
  classical
  refine ⟨askL r k d, fun w => univ.filter (fun y : Fin r → ZMod 2 => ∀ i : Fin r,
    ∀ hi : i.val < r - k, y i = w ⟨3 * i.val + 2, by omega⟩ + w ⟨3 * i.val, by omega⟩ *
      w ⟨3 * i.val + 1, by omega⟩), fun z => ⟨?_, ?_⟩⟩
  · have hle := Finset.card_le_card_of_injOn
      (s := univ.filter (fun y : Fin r → ZMod 2 => ∀ i : Fin r,
        ∀ hi : i.val < r - k, y i = askL r k d z ⟨3 * i.val + 2, by omega⟩ +
          askL r k d z ⟨3 * i.val, by omega⟩ * askL r k d z ⟨3 * i.val + 1, by omega⟩))
      (t := (univ : Finset (Fin k → ZMod 2)))
      (fun y : Fin r → ZMod 2 => fun j : Fin k => y ⟨r - k + j.val, by omega⟩)
      (by intro y _; simp) ?_
    · simpa using hle
    · intro y hy y' hy' heq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hy hy'
      funext i
      by_cases hi : i.val < r - k
      · rw [hy i hi, hy' i hi]
      · have := congrFun heq ⟨i.val - (r - k), by omega⟩
        have e : (⟨r - k + (i.val - (r - k)), by omega⟩ : Fin r) = i := Fin.ext (by dsimp; omega)
        simp only at this
        rw [e] at this
        exact this
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hi
    rw [askL_apply r k d z _ (by dsimp; omega) i 2 (by dsimp; omega) (by simp),
      askL_apply r k d z _ (by dsimp; omega) i 0 (by dsimp; omega) (by simp),
      askL_apply r k d z _ (by dsimp; omega) i 1 (by dsimp; omega) (by simp)]
    rfl

theorem main (r k d : ℕ) (hk : k ≤ r) :
    (∃ (ask : X r →ₗ[ZMod 2] (Fin d → ZMod 2)) (out : (Fin d → ZMod 2) → Finset (Fin r → ZMod 2)),
      ∀ z, (out (ask z)).card ≤ 2 ^ k ∧ tgt z ∈ out (ask z)) ↔ 3 * (r - k) ≤ d := by
  constructor
  · rintro ⟨ask, out, h⟩
    have := conv r k d ask out h
    omega
  · exact fwd r k d hk

end PEqualNP.Outside.L_pcx_404_aux

theorem PEqualNP.Outside.L_pcx_404 : (∀ (r k d : ℕ) (_ : k ≤ r),
  let F := ZMod 2
  let X := Fin r → Fin 3 → F
  let Y := Fin r → F
  let target := fun (z : X) (i : Fin r) => z i 2 + z i 0 * z i 1
  (∃ (ask : X →ₗ[F] (Fin d → F)) (out : (Fin d → F) → Finset Y),
    ∀ z : X, (out (ask z)).card ≤ 2^k ∧ target z ∈ out (ask z)) ↔ 3*(r-k) ≤ d) := by
  exact fun r k d hk => PEqualNP.Outside.L_pcx_404_aux.main r k d hk
