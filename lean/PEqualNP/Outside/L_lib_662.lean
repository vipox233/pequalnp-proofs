import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_662

abbrev K := ZMod 2
abbrev V (w : ℕ) := Fin (w + 1) → K
abbrev U (w : ℕ) := Fin w → K
abbrev I (w : ℕ) := V w × Fin (w + 1)

private lemma zmod2_cases (x : K) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (x : K) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma zmod2_ne_one_iff (x : K) : x ≠ 1 ↔ x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

private lemma card_U (w : ℕ) : Fintype.card (U w) = 2 ^ w := by
  simp

private lemma card_V (w : ℕ) : Fintype.card (V w) = 2 * 2 ^ w := by
  simp [pow_succ']

def prefixOf {w : ℕ} (v : V w) : U w := fun i => v i.castSucc

def lastBit {w : ℕ} (v : V w) : K := v (Fin.last w)

def combine {w : ℕ} (u : U w) (b : K) : V w := Fin.snoc u b

private lemma combine_castSucc {w : ℕ} (u : U w) (b : K) (i : Fin w) :
    combine u b i.castSucc = u i := by
  simp [combine]

private lemma combine_last {w : ℕ} (u : U w) (b : K) :
    combine u b (Fin.last w) = b := by
  simp [combine]

private lemma prefixOf_combine {w : ℕ} (u : U w) (b : K) :
    prefixOf (combine u b) = u := by
  funext i
  exact combine_castSucc u b i

private lemma lastBit_combine {w : ℕ} (u : U w) (b : K) :
    lastBit (combine u b) = b := combine_last u b

private lemma combine_prefixOf_lastBit {w : ℕ} (v : V w) :
    combine (prefixOf v) (lastBit v) = v := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · exact combine_last (prefixOf v) (lastBit v)
  · intro j
    exact combine_castSucc (prefixOf v) (lastBit v) j

def equivUV (w : ℕ) : V w ≃ U w × K where
  toFun v := (prefixOf v, lastBit v)
  invFun p := combine p.1 p.2
  left_inv := combine_prefixOf_lastBit
  right_inv p := Prod.ext (prefixOf_combine p.1 p.2) (lastBit_combine p.1 p.2)

def tau {w : ℕ} (d : U w) (f : U w → K) : Equiv.Perm (V w) where
  toFun v := combine (prefixOf v + d) (lastBit v + f (prefixOf v))
  invFun v := combine (prefixOf v + d) (lastBit v + f (prefixOf v + d))
  left_inv v := by
    simp only [prefixOf_combine, lastBit_combine]
    have h1 : prefixOf v + d + d = prefixOf v := by
      funext i
      simp only [Pi.add_apply]
      rw [add_assoc, zmod2_add_self, add_zero]
    rw [h1, add_assoc, zmod2_add_self, add_zero, combine_prefixOf_lastBit]
  right_inv v := by
    simp only [prefixOf_combine, lastBit_combine]
    have h1 : prefixOf v + d + d = prefixOf v := by
      funext i
      simp only [Pi.add_apply]
      rw [add_assoc, zmod2_add_self, add_zero]
    have h2 : lastBit v + f (prefixOf v + d) + f (prefixOf v + d) = lastBit v := by
      rw [add_assoc, zmod2_add_self, add_zero]
    rw [h1, h2, combine_prefixOf_lastBit]

private lemma tau_castSucc {w : ℕ} (d : U w) (f : U w → K) (v : V w) (i : Fin w) :
    tau d f v i.castSucc = v i.castSucc + d i := by
  change combine (prefixOf v + d) (lastBit v + f (prefixOf v)) i.castSucc = _
  rw [combine_castSucc]
  rfl

private lemma tau_last {w : ℕ} (d : U w) (f : U w → K) (v : V w) :
    tau d f v (Fin.last w) = v (Fin.last w) + f (prefixOf v) := by
  change combine (prefixOf v + d) (lastBit v + f (prefixOf v)) (Fin.last w) = _
  rw [combine_last]
  rfl

private lemma sum_const_coord_zero {w : ℕ} (k : Fin w) (F : U w → K)
    (hF : ∀ d : U w, F (d + Pi.single k 1) = F d) :
    ∑ d : U w, F d = 0 := by
  classical
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (U w))
    (fun d => d k = 0) F).symm
  rw [hsplit]
  have hbij :
      ∑ d ∈ (Finset.univ : Finset (U w)).filter (fun d => d k = 0), F d =
      ∑ d ∈ (Finset.univ : Finset (U w)).filter (fun d => ¬ d k = 0), F d := by
    refine Finset.sum_bij (fun d _ => d + Pi.single k 1) ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      simp [hd]
    · intro d1 _ d2 _ h
      have h' := congrArg (fun x => x + Pi.single k (1 : K)) h
      have hcancel : ∀ x : U w, x + Pi.single k (1 : K) + Pi.single k (1 : K) = x := by
        intro x
        funext i
        simp only [Pi.add_apply]
        rw [add_assoc, zmod2_add_self, add_zero]
      rwa [hcancel, hcancel] at h'
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      refine ⟨d + Pi.single k 1, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Pi.single_eq_same]
        rcases zmod2_cases (d k) with h0 | h1
        · exfalso; exact hd h0
        · rw [h1]; decide
      · funext i
        simp only [Pi.add_apply]
        rw [add_assoc, zmod2_add_self, add_zero]
    · intro d _
      exact (hF d).symm
  rw [← hbij]
  exact zmod2_add_self _

private lemma sum_monomial_tau_zero {w : ℕ} (p : Equiv.Perm (V w)) (f : U w → K)
    (S : Finset (I w)) (hcard : S.card ≤ w) (hlast : ∃ j ∈ S, j.2 = Fin.last w) :
    ∑ d : U w, ∏ j ∈ S, (tau d f * p) j.1 j.2 = 0 := by
  classical
  rcases hlast with ⟨j0, hj0, hj0last⟩
  have hw : 0 < w := by
    have : 0 < S.card := Finset.card_pos.mpr ⟨j0, hj0⟩
    omega
  let Spref := S.filter (fun j => j.2 ≠ Fin.last w)
  have hSpref_lt : Spref.card < w := by
    have hss : Spref ⊂ S := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
      intro heq
      have : j0 ∈ Spref := heq.symm ▸ hj0
      exact (Finset.mem_filter.mp this).2 hj0last
    exact lt_of_lt_of_le (Finset.card_lt_card hss) hcard
  let toW : Fin (w + 1) → Fin w := fun i =>
    if h : i = Fin.last w then ⟨0, hw⟩ else i.castPred h
  let T := Spref.image (fun j => toW j.2)
  have hT_lt : T.card < (Finset.univ : Finset (Fin w)).card := by
    rw [Finset.card_fin]
    exact lt_of_le_of_lt Finset.card_image_le hSpref_lt
  have hT_ne : T ≠ Finset.univ := fun h => by
    rw [h] at hT_lt
    exact (lt_irrefl _) hT_lt
  obtain ⟨k, hk⟩ : ∃ k : Fin w, k ∉ T := by
    by_contra h
    push Not at h
    exact hT_ne (Finset.eq_univ_iff_forall.mpr h)
  refine sum_const_coord_zero k _ ?_
  intro d
  refine Finset.prod_congr rfl ?_
  intro j hj
  simp only [Equiv.Perm.mul_apply]
  by_cases hjlast : j.2 = Fin.last w
  · rw [hjlast, tau_last, tau_last]
  · let m := j.2.castPred hjlast
    have hm_eq : j.2 = m.castSucc := (Fin.castSucc_castPred j.2 hjlast).symm
    have hm_ne : m ≠ k := by
      intro hmk
      apply hk
      refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hjlast⟩, ?_⟩
      dsimp only [toW]
      simp only [hjlast, ↓reduceDIte]
      exact hmk
    rw [hm_eq, tau_castSucc, tau_castSucc]
    simp only [Pi.add_apply]
    rw [Pi.single_eq_of_ne hm_ne, add_zero]

private lemma sum_monomial_tau_eq {w : ℕ} (p : Equiv.Perm (V w)) (f : U w → K)
    (S : Finset (I w)) (hcard : S.card ≤ w) :
    ∑ d : U w, ∏ j ∈ S, (tau d f * p) j.1 j.2 =
      ∑ d : U w, ∏ j ∈ S, (tau d 0 * p) j.1 j.2 := by
  by_cases hlast : ∃ j ∈ S, j.2 = Fin.last w
  · rw [sum_monomial_tau_zero p f S hcard hlast, sum_monomial_tau_zero p 0 S hcard hlast]
  · push Not at hlast
    refine Finset.sum_congr rfl fun d _ => Finset.prod_congr rfl fun j hj => ?_
    simp only [Equiv.Perm.mul_apply]
    have hjlast : j.2 ≠ Fin.last w := hlast j hj
    have hm_eq : j.2 = (j.2.castPred hjlast).castSucc := (Fin.castSucc_castPred j.2 hjlast).symm
    rw [hm_eq, tau_castSucc, tau_castSucc]

private lemma sum_pred_tau_eq {w : ℕ} (c : V w → Finset (I w) → K)
    (p : Equiv.Perm (V w)) (a : V w) (f : U w → K) :
    ∑ d : U w,
      (∑ S ∈ (Finset.univ : Finset (Finset (I w))).filter (fun S => S.card ≤ w),
        c a S * ∏ j ∈ S, (tau d f * p) j.1 j.2) =
    ∑ d : U w,
      (∑ S ∈ (Finset.univ : Finset (Finset (I w))).filter (fun S => S.card ≤ w),
        c a S * ∏ j ∈ S, (tau d 0 * p) j.1 j.2) := by
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hcard : S.card ≤ w := (Finset.mem_filter.mp hS).2
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_monomial_tau_eq p f S hcard]

private lemma sum_target_tau {w : ℕ} (p : Equiv.Perm (V w)) (a : V w) (f : U w → K) :
    ∑ d : U w, ∏ i : Fin (w + 1), (tau d f * p) a i =
      lastBit (p a) + f (prefixOf (p a)) := by
  let d0 : U w := fun k => 1 + prefixOf (p a) k
  have hterm : ∀ d : U w,
      ∏ i : Fin (w + 1), (tau d f * p) a i =
        (if d = d0 then lastBit (p a) + f (prefixOf (p a)) else 0) := by
    intro d
    rw [Fin.prod_univ_castSucc]
    simp only [Equiv.Perm.mul_apply, tau_last]
    have hcast : ∏ i : Fin w, tau d f (p a) i.castSucc = if d = d0 then 1 else 0 := by
      split_ifs with hd
      · subst hd
        refine Finset.prod_eq_one fun k _ => ?_
        rw [tau_castSucc]
        change prefixOf (p a) k + (1 + prefixOf (p a) k) = 1
        rw [add_left_comm, zmod2_add_self, add_zero]
      · have hne : ∃ k : Fin w, d k ≠ d0 k := by
          by_contra h
          push Not at h
          exact hd (funext h)
        rcases hne with ⟨k, hk⟩
        refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
        rw [tau_castSucc]
        have h1 : prefixOf (p a) k + d k ≠ 1 := by
          intro h1
          apply hk
          dsimp only [d0]
          have h2 := congrArg (fun x => prefixOf (p a) k + x) h1
          rw [← add_assoc, zmod2_add_self, zero_add] at h2
          exact h2.trans (add_comm _ _)
        exact (zmod2_ne_one_iff _).mp h1
    rw [hcast]
    split_ifs <;> simp [lastBit]
  simp_rw [hterm]
  simp

private lemma card_filter_agree {w : ℕ} (H : Finset (U w)) (g : U w → K) :
    ((Finset.univ : Finset (U w → K)).filter (fun f => ∀ u ∈ H, f u = g u)).card =
      2 ^ (2 ^ w - H.card) := by
  classical
  have hcard_eq :
      ((Finset.univ : Finset (U w → K)).filter (fun f => ∀ u ∈ H, f u = g u)).card =
        Fintype.card ({u : U w // u ∉ H} → K) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun f _ => fun u => f u.1) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro f1 hf1 f2 hf2 h
      have hf1' := (Finset.mem_filter.mp hf1).2
      have hf2' := (Finset.mem_filter.mp hf2).2
      funext u
      by_cases hu : u ∈ H
      · rw [hf1' u hu, hf2' u hu]
      · exact congrFun h ⟨u, hu⟩
    · intro h _
      refine ⟨fun u => if hu : u ∈ H then g u else h ⟨u, hu⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro u hu
        simp [hu]
      · funext u
        simp [u.2]
  rw [hcard_eq, Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl, Fintype.card_coe, card_U]

private lemma card_perm_image_eq {w : ℕ} (A M1 M2 : Finset (V w))
    (hcard : M1.card = M2.card) :
    ((Finset.univ : Finset (Equiv.Perm (V w))).filter
        (fun p : Equiv.Perm (V w) => A.image (p : V w → V w) = M1)).card =
      ((Finset.univ : Finset (Equiv.Perm (V w))).filter
        (fun p : Equiv.Perm (V w) => A.image (p : V w → V w) = M2)).card := by
  classical
  have he1 : M1 ≃ M2 := Finset.equivOfCardEq hcard
  have hcomp : (Finset.univ \ M1).card = (Finset.univ \ M2).card := by
    rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_univ, Finset.inter_univ, hcard]
  have he2 : ↥(Finset.univ \ M1) ≃ ↥(Finset.univ \ M2) := Finset.equivOfCardEq hcomp
  let σ : Equiv.Perm (V w) :=
    { toFun := fun x =>
        if hx : x ∈ M1 then (he1 ⟨x, hx⟩).1
        else (he2 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩).1
      invFun := fun y =>
        if hy : y ∈ M2 then (he1.symm ⟨y, hy⟩).1
        else (he2.symm ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩⟩).1
      left_inv := fun x => by
        by_cases hx : x ∈ M1
        · have hmem : (he1 ⟨x, hx⟩).1 ∈ M2 := (he1 ⟨x, hx⟩).2
          simp [hx, hmem]
        · have hmem : (he2 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩).1 ∉ M2 :=
            (Finset.mem_sdiff.mp (he2 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩).2).2
          simp [hx, hmem]
      right_inv := fun y => by
        by_cases hy : y ∈ M2
        · have hmem : (he1.symm ⟨y, hy⟩).1 ∈ M1 := (he1.symm ⟨y, hy⟩).2
          simp [hy, hmem]
        · have hmem : (he2.symm ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩⟩).1 ∉ M1 :=
            (Finset.mem_sdiff.mp (he2.symm ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩⟩).2).2
          simp [hy, hmem] }
  have hσ_img : M1.image σ = M2 := by
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (if hx' : x ∈ M1 then (he1 ⟨x, hx'⟩).1
        else (he2 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx'⟩⟩).1) ∈ M2
      split_ifs
      exact (he1 ⟨x, hx⟩).2
    · intro hy
      refine ⟨(he1.symm ⟨y, hy⟩).1, (he1.symm ⟨y, hy⟩).2, ?_⟩
      change (if hx' : (he1.symm ⟨y, hy⟩).1 ∈ M1 then (he1 ⟨(he1.symm ⟨y, hy⟩).1, hx'⟩).1
        else (he2 ⟨(he1.symm ⟨y, hy⟩).1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx'⟩⟩).1) = y
      split_ifs with hmem
      · simp
      · exact absurd (he1.symm ⟨y, hy⟩).2 hmem
  have hmul_img : ∀ p : Equiv.Perm (V w),
      A.image ((σ * p : Equiv.Perm (V w)) : V w → V w) = (A.image (p : V w → V w)).image σ := by
    intro p
    ext y
    simp only [Finset.mem_image, Equiv.Perm.mul_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨p a, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  refine Finset.card_bij (fun p _ => σ * p) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hmul_img, hp.2, hσ_img]
  · intro p1 _ p2 _ h
    exact mul_left_cancel h
  · intro q hq
    simp only [Finset.mem_filter] at hq
    refine ⟨σ⁻¹ * q, ?_, by simp⟩
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hq' : (A.image ((σ⁻¹ * q : Equiv.Perm (V w)) : V w → V w)).image σ = M2 := by
      rw [← hmul_img]
      simpa using hq.2
    have hinj : Function.Injective (fun S : Finset (V w) => S.image σ) := by
      intro S1 S2 hS
      dsimp only at hS
      ext x
      have hx : σ x ∈ S1.image σ ↔ σ x ∈ S2.image σ := by rw [hS]
      simpa [Finset.mem_image, σ.injective.eq_iff] using hx
    exact hinj (hq'.trans hσ_img.symm)

private lemma card_superset_prefix {w : ℕ} (H : Finset (U w)) :
    ((Finset.univ : Finset (Finset (U w))).filter (fun J => H ⊆ J)).card =
      2 ^ (2 ^ w - H.card) := by
  classical
  have hbij :
      ((Finset.univ : Finset (Finset (U w))).filter (fun J => H ⊆ J)).card =
        (Finset.univ \ H).powerset.card := by
    refine Finset.card_bij (fun J _ => J \ H) ?_ ?_ ?_
    · intro J _
      rw [Finset.mem_powerset]
      intro x hx
      rcases Finset.mem_sdiff.mp hx with ⟨_, hxH⟩
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxH⟩
    · intro J1 hJ1 J2 hJ2 h
      have h1 : H ⊆ J1 := (Finset.mem_filter.mp hJ1).2
      have h2 : H ⊆ J2 := (Finset.mem_filter.mp hJ2).2
      rw [← Finset.sdiff_union_of_subset h1, ← Finset.sdiff_union_of_subset h2, h]
    · intro K hK
      rw [Finset.mem_powerset] at hK
      refine ⟨K ∪ H, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_union_right⟩, ?_⟩
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxK | hxH, hxnotH⟩
        · exact hxK
        · exact absurd hxH hxnotH
      · intro hxK
        exact ⟨Or.inl hxK, (Finset.mem_sdiff.mp (hK hxK)).2⟩
  rw [hbij, Finset.card_powerset, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, card_U]

private lemma card_fiber_prefix {w : ℕ} (J : Finset (U w)) :
    ((Finset.univ : Finset (V w)).filter (fun v => prefixOf v ∈ J)).card = 2 * J.card := by
  have hbij :
      ((Finset.univ : Finset (V w)).filter (fun v => prefixOf v ∈ J)).card =
        (J ×ˢ (Finset.univ : Finset K)).card := by
    refine Finset.card_bij (fun v _ => (prefixOf v, lastBit v)) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      exact Finset.mem_product.mpr ⟨hv, Finset.mem_univ _⟩
    · intro v1 _ v2 _ h
      have h' := Prod.ext_iff.mp h
      exact (equivUV w).injective (Prod.ext h'.1 h'.2)
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp1, _⟩
      refine ⟨combine p.1 p.2, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, prefixOf_combine]
        exact hp1
      · exact Prod.ext (prefixOf_combine p.1 p.2) (lastBit_combine p.1 p.2)
  rw [hbij, Finset.card_product, Finset.card_univ, ZMod.card, mul_comm]

private lemma empty_eq_sum_subsets {w : ℕ} (m : ℕ) :
    ∑ j ∈ Finset.range (2 ^ w + 1), Nat.choose (2 ^ w) j * Nat.choose (2 * j) m =
      ∑ M ∈ (Finset.univ : Finset (V w)).powersetCard m,
        2 ^ (2 ^ w - (M.image prefixOf).card) := by
  classical
  let F := (Finset.univ : Finset (V w)).powersetCard m
  have h1 :
      ∑ M ∈ F, 2 ^ (2 ^ w - (M.image prefixOf).card) =
        ∑ M ∈ F, ∑ J : Finset (U w), (if M.image prefixOf ⊆ J then 1 else 0) := by
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [← card_superset_prefix (M.image prefixOf), Finset.card_filter]
  rw [h1, Finset.sum_comm]
  have h2 :
      ∑ J : Finset (U w), ∑ M ∈ F, (if M.image prefixOf ⊆ J then 1 else 0) =
        ∑ J : Finset (U w), Nat.choose (2 * J.card) m := by
    refine Finset.sum_congr rfl fun J _ => ?_
    let W := (Finset.univ : Finset (V w)).filter (fun v => prefixOf v ∈ J)
    have hfilter : F.filter (fun M => M.image prefixOf ⊆ J) = W.powersetCard m := by
      ext M
      simp only [F, W, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_iff,
        Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨⟨_, hm⟩, hsub⟩
        exact ⟨fun x hx => hsub ⟨x, hx, rfl⟩, hm⟩
      · rintro ⟨hsub, hm⟩
        refine ⟨⟨fun _ _ => trivial, hm⟩, ?_⟩
        rintro u ⟨x, hx, rfl⟩
        exact hsub hx
    rw [← Finset.card_filter, hfilter, Finset.card_powersetCard, card_fiber_prefix]
  rw [h2]
  have hmaps : ∀ J ∈ (Finset.univ : Finset (Finset (U w))), J.card ∈ Finset.range (2 ^ w + 1) := by
    intro J _
    rw [Finset.mem_range, Nat.lt_succ_iff, ← card_U w]
    exact Finset.card_le_univ J
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun J : Finset (U w) => Nat.choose (2 * J.card) m)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfib :
      ((Finset.univ : Finset (Finset (U w))).filter (fun J => J.card = j)).card =
        Nat.choose (2 ^ w) j := by
    have heq :
        (Finset.univ : Finset (Finset (U w))).filter (fun J => J.card = j) =
          (Finset.univ : Finset (U w)).powersetCard j := by
      ext J
      simp [Finset.mem_powersetCard]
    rw [heq, Finset.card_powersetCard, Finset.card_univ, card_U]
  symm
  calc
    ∑ J ∈ (Finset.univ : Finset (Finset (U w))).filter (fun J => J.card = j),
        Nat.choose (2 * J.card) m
      = ∑ _J ∈ (Finset.univ : Finset (Finset (U w))).filter (fun J => J.card = j),
          Nat.choose (2 * j) m := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [(Finset.mem_filter.mp hJ).2]
    _ = ((Finset.univ : Finset (Finset (U w))).filter (fun J => J.card = j)).card *
          Nat.choose (2 * j) m := Finset.sum_const _
    _ = Nat.choose (2 ^ w) j * Nat.choose (2 * j) m := by rw [hfib]

private lemma main_proof (w : ℕ) (A : Finset (V w)) (c : V w → Finset (I w) → K) :
    let m := A.card
    let s := 2 ^ w
    let pred := fun (p : Equiv.Perm (V w)) (a : V w) =>
      ∑ S ∈ (Finset.univ : Finset (Finset (I w))).filter (fun S => S.card ≤ w),
        c a S * ∏ j ∈ S, p j.1 j.2
    let bad := (Finset.univ : Finset (Equiv.Perm (V w))).filter (fun p =>
      ∃ a ∈ A, pred p a ≠ ∏ i : Fin (w + 1), p a i)
    let total := 2 ^ s * Nat.choose (2 * s) m
    let empty := ∑ j ∈ Finset.range (s + 1), Nat.choose s j * Nat.choose (2 * j) m
    Nat.factorial (2 * s) * (total - empty) ≤ s * total * bad.card := by
  classical
  intro m s pred bad total empty
  let F := (Finset.univ : Finset (V w)).powersetCard m
  have hF_card : F.card = Nat.choose (2 * s) m := by
    rw [Finset.card_powersetCard, Finset.card_univ, card_V]
  have hper_p : ∀ p : Equiv.Perm (V w),
      2 ^ s - 2 ^ (s - ((A.image (p : V w → V w)).image prefixOf).card) ≤
        ∑ f : U w → K, ∑ d : U w, (if tau d f * p ∈ bad then 1 else 0) := by
    intro p
    let H := (A.image (p : V w → V w)).image prefixOf
    have hH_le : H.card ≤ s := by
      dsimp only [s]
      rw [← card_U w]
      exact Finset.card_le_univ H
    have hex_pres : ∀ u ∈ H, ∃ a ∈ A, prefixOf (p a) = u := by
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨v, hv, rfl⟩
      rcases Finset.mem_image.mp hv with ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩
    let targetSum : V w → K := fun a => ∑ d : U w, pred (tau d 0 * p) a
    let prescribed : U w → K := fun u =>
      if hu : u ∈ H then
        let a := Classical.choose (hex_pres u hu)
        targetSum a + lastBit (p a)
      else 0
    let goodF := (Finset.univ : Finset (U w → K)).filter (fun f => ∀ d : U w, tau d f * p ∉ bad)
    have hsub : goodF ⊆ (Finset.univ : Finset (U w → K)).filter (fun f => ∀ u ∈ H, f u = prescribed u) := by
      intro f hf
      have hgood : ∀ d : U w, tau d f * p ∉ bad := (Finset.mem_filter.mp hf).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro u hu
      dsimp only [prescribed]
      simp only [hu, ↓reduceDIte]
      let a := Classical.choose (hex_pres u hu)
      have ha_mem : a ∈ A := (Classical.choose_spec (hex_pres u hu)).1
      have ha_pref : prefixOf (p a) = u := (Classical.choose_spec (hex_pres u hu)).2
      have hagree : ∀ d : U w, pred (tau d f * p) a = ∏ i : Fin (w + 1), (tau d f * p) a i := by
        intro d
        by_contra hne
        apply hgood d
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, ha_mem, hne⟩⟩
      have hsum_eq : ∑ d : U w, pred (tau d f * p) a = ∑ d : U w, ∏ i : Fin (w + 1), (tau d f * p) a i :=
        Finset.sum_congr rfl fun d _ => hagree d
      rw [sum_pred_tau_eq c p a f, sum_target_tau p a f, ha_pref] at hsum_eq
      change targetSum a = lastBit (p a) + f u at hsum_eq
      have hres := congrArg (fun x => x + lastBit (p a)) hsum_eq
      rw [add_right_comm, zmod2_add_self, zero_add] at hres
      exact hres.symm
    have hgood_card : goodF.card ≤ 2 ^ (s - H.card) := by
      calc
        goodF.card ≤ ((Finset.univ : Finset (U w → K)).filter (fun f => ∀ u ∈ H, f u = prescribed u)).card :=
          Finset.card_le_card hsub
        _ = 2 ^ (s - H.card) := card_filter_agree H prescribed
    let badF := (Finset.univ : Finset (U w → K)).filter (fun f => ∃ d : U w, tau d f * p ∈ bad)
    have hbadF_card : 2 ^ s - 2 ^ (s - H.card) ≤ badF.card := by
      have hdisj : Disjoint goodF badF := by
        rw [Finset.disjoint_left]
        intro f hf1 hf2
        have h1 := (Finset.mem_filter.mp hf1).2
        rcases (Finset.mem_filter.mp hf2).2 with ⟨d, hd⟩
        exact h1 d hd
      have hunion : goodF ∪ badF = Finset.univ := by
        ext f
        simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        by_cases h : ∀ d : U w, tau d f * p ∉ bad
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        · push Not at h
          exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have htot : goodF.card + badF.card = 2 ^ s := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fun,
          ZMod.card, card_U]
      omega
    have hbadF_sum : badF.card ≤ ∑ f : U w → K, ∑ d : U w, (if tau d f * p ∈ bad then 1 else 0) := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      refine Finset.sum_le_sum fun f _ => ?_
      by_cases hf : ∃ d : U w, tau d f * p ∈ bad
      · rcases hf with ⟨d, hd⟩
        have hex : ∃ d, tau d f * p ∈ bad := ⟨d, hd⟩
        simp only [hex, ↓reduceIte]
        have hle : (if tau d f * p ∈ bad then 1 else 0) ≤
            ∑ d' : U w, (if tau d' f * p ∈ bad then 1 else 0) :=
          Finset.single_le_sum (f := fun d' : U w => if tau d' f * p ∈ bad then 1 else 0)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
        simpa [hd] using hle
      · simp only [hf, ↓reduceIte]
        exact Nat.zero_le _
    exact le_trans hbadF_card hbadF_sum
  have hsum_p :
      ∑ p : Equiv.Perm (V w), (2 ^ s - 2 ^ (s - ((A.image (p : V w → V w)).image prefixOf).card)) ≤
        2 ^ s * s * bad.card := by
    calc
      ∑ p : Equiv.Perm (V w), (2 ^ s - 2 ^ (s - ((A.image (p : V w → V w)).image prefixOf).card))
        ≤ ∑ p : Equiv.Perm (V w), ∑ f : U w → K, ∑ d : U w, (if tau d f * p ∈ bad then 1 else 0) :=
          Finset.sum_le_sum fun p _ => hper_p p
      _ = ∑ f : U w → K, ∑ d : U w, ∑ p : Equiv.Perm (V w), (if tau d f * p ∈ bad then 1 else 0) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ f : U w → K, ∑ d : U w, bad.card := by
          refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun d _ => ?_
          have hbij :
              ∑ p : Equiv.Perm (V w), (if tau d f * p ∈ bad then 1 else 0) =
                ∑ q : Equiv.Perm (V w), (if q ∈ bad then 1 else 0) :=
            Fintype.sum_equiv (Equiv.mulLeft (tau d f)) _ _ (fun _ => rfl)
          rw [hbij, ← Finset.card_filter]
          simp
      _ = 2 ^ s * s * bad.card := by
          simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fun, ZMod.card,
            Fintype.card_fin]
          dsimp only [s]
          rw [mul_assoc]
  let c0 := ((Finset.univ : Finset (Equiv.Perm (V w))).filter
    (fun p : Equiv.Perm (V w) => A.image (p : V w → V w) = A)).card
  have hfib_const : ∀ M ∈ F,
      ((Finset.univ : Finset (Equiv.Perm (V w))).filter
        (fun p : Equiv.Perm (V w) => A.image (p : V w → V w) = M)).card = c0 := by
    intro M hM
    have hMcard : A.card = M.card := (Finset.mem_powersetCard.mp hM).2.symm
    exact (card_perm_image_eq A A M hMcard).symm
  have hmaps : ∀ p ∈ (Finset.univ : Finset (Equiv.Perm (V w))), A.image (p : V w → V w) ∈ F := by
    intro p _
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_image_of_injective A p.injective⟩
  have hfact_eq : F.card * c0 = Nat.factorial (2 * s) := by
    have hsum_card :
        (Finset.univ : Finset (Equiv.Perm (V w))).card =
          ∑ M ∈ F, ((Finset.univ : Finset (Equiv.Perm (V w))).filter
            (fun p : Equiv.Perm (V w) => A.image (p : V w → V w) = M)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_univ, Fintype.card_perm, card_V] at hsum_card
    have hconst : ∑ M ∈ F, ((Finset.univ : Finset (Equiv.Perm (V w))).filter
        (fun p : Equiv.Perm (V w) => A.image (p : V w → V w) = M)).card =
        F.card * c0 := by
      calc
        ∑ M ∈ F, ((Finset.univ : Finset (Equiv.Perm (V w))).filter
            (fun p : Equiv.Perm (V w) => A.image (p : V w → V w) = M)).card
          = ∑ _M ∈ F, c0 := Finset.sum_congr rfl hfib_const
        _ = F.card * c0 := Finset.sum_const _
    rw [hconst] at hsum_card
    exact hsum_card.symm
  have hlhs_eq :
      ∑ p : Equiv.Perm (V w), (2 ^ s - 2 ^ (s - ((A.image (p : V w → V w)).image prefixOf).card)) =
        c0 * ∑ M ∈ F, (2 ^ s - 2 ^ (s - (M.image prefixOf).card)) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun p : Equiv.Perm (V w) => 2 ^ s - 2 ^ (s - ((A.image (p : V w → V w)).image prefixOf).card))]
    have h1 :
        ∑ M ∈ F, ∑ p ∈ (Finset.univ : Finset (Equiv.Perm (V w))).filter
              (fun p : Equiv.Perm (V w) => A.image (p : V w → V w) = M),
            (2 ^ s - 2 ^ (s - ((A.image (p : V w → V w)).image prefixOf).card)) =
          ∑ M ∈ F, c0 * (2 ^ s - 2 ^ (s - (M.image prefixOf).card)) := by
      refine Finset.sum_congr rfl fun M hM => ?_
      have h2 :
          ∑ p ∈ (Finset.univ : Finset (Equiv.Perm (V w))).filter
                (fun p : Equiv.Perm (V w) => A.image (p : V w → V w) = M),
              (2 ^ s - 2 ^ (s - ((A.image (p : V w → V w)).image prefixOf).card)) =
            ∑ _p ∈ (Finset.univ : Finset (Equiv.Perm (V w))).filter
                (fun p : Equiv.Perm (V w) => A.image (p : V w → V w) = M),
              (2 ^ s - 2 ^ (s - (M.image prefixOf).card)) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [(Finset.mem_filter.mp hp).2]
      rw [h2, Finset.sum_const, smul_eq_mul, hfib_const M hM]
    rw [h1, Finset.mul_sum]
  have htotal_empty :
      ∑ M ∈ F, (2 ^ s - 2 ^ (s - (M.image prefixOf).card)) = total - empty := by
    have hadd :
        (∑ M ∈ F, (2 ^ s - 2 ^ (s - (M.image prefixOf).card))) +
          (∑ M ∈ F, 2 ^ (s - (M.image prefixOf).card)) = total := by
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ M ∈ F,
          (2 ^ s - 2 ^ (s - (M.image prefixOf).card)) + 2 ^ (s - (M.image prefixOf).card) = 2 ^ s := by
        intro M _
        refine Nat.sub_add_cancel ?_
        exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hF_card, mul_comm]
    have hempty : empty = ∑ M ∈ F, 2 ^ (s - (M.image prefixOf).card) :=
      empty_eq_sum_subsets m
    omega
  have hmul := Nat.mul_le_mul_left F.card hsum_p
  rw [hlhs_eq, htotal_empty, ← mul_assoc, hfact_eq] at hmul
  calc
    Nat.factorial (2 * s) * (total - empty) ≤ F.card * (2 ^ s * s * bad.card) := hmul
    _ = s * total * bad.card := by
      rw [hF_card]
      dsimp only [total]
      ring

end PEqualNP.Outside.L_lib_662

theorem PEqualNP.Outside.L_lib_662 : ∀ w : ℕ,
  let K := ZMod 2
  let V := Fin (w+1) → K
  let I := V × Fin (w+1)
  let s := 2^w
  ∀ (A : Finset V) (c : V → Finset I → K),
    let m := A.card
    let pred := fun (p : Equiv.Perm V) (a : V) =>
      ∑ S ∈ (Finset.univ : Finset (Finset I)).filter (fun S => S.card ≤ w),
        c a S * ∏ j ∈ S, p j.1 j.2
    let bad := (Finset.univ : Finset (Equiv.Perm V)).filter (fun p =>
      ∃ a ∈ A, pred p a ≠ ∏ i : Fin (w+1), p a i)
    let total := 2^s * Nat.choose (2*s) m
    let empty := ∑ j ∈ Finset.range (s+1), Nat.choose s j * Nat.choose (2*j) m
    Nat.factorial (2*s) * (total - empty) ≤ s * total * bad.card :=
  fun w A c => PEqualNP.Outside.L_lib_662.main_proof w A c
