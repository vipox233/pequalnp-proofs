import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_433_aux

open Finset

abbrev Z2 := ZMod 2

abbrev XU (m h l : ℕ) := (Fin m → Z2) × ((Fin h → Z2) × (Fin m → Fin h → Fin l → Z2))

def cellF {m h l : ℕ} (u : (Fin h → Z2) × (Fin m → Fin h → Fin l → Z2)) (i : Fin m) :
    Fin h → Fin (l+1) → Z2 :=
  fun j => Fin.cases (motive := fun _ => Z2) (u.1 j + ∑ p : Fin l, u.2 i j p) (u.2 i j)

def isLocal {m h l : ℕ} (L : ℕ) (f : XU m h l →ₗ[Z2] Z2) : Prop :=
  ∃ S : Finset ((Fin m × Fin h) × Fin (l+1)), S.card ≤ L ∧
    ∀ u : (Fin h → Z2) × (Fin m → Fin h → Fin l → Z2),
      f (0,u) = ∑ s ∈ S, cellF u s.1.1 s.1.2 s.2

theorem z2_add_self (a : Z2) : a + a = 0 := by
  revert a; decide

theorem z2_lemma : ∀ a a' b b' c : Z2, a + a' ≠ c → a + b + (a' + b') ≠ c → b + b' = 0 := by
  decide

theorem z2_lemma2 : ∀ S f c : Z2, S + f = 0 → S + c = 1 → f ≠ c := by
  decide

section cells
variable {m h l : ℕ}

@[simp] theorem cellF_zero (u : (Fin h → Z2) × (Fin m → Fin h → Fin l → Z2)) (i : Fin m)
    (j : Fin h) : cellF u i j 0 = u.1 j + ∑ p, u.2 i j p := rfl

@[simp] theorem cellF_succ (u : (Fin h → Z2) × (Fin m → Fin h → Fin l → Z2)) (i : Fin m)
    (j : Fin h) (p : Fin l) : cellF u i j p.succ = u.2 i j p := rfl

theorem cellF_add (u v : (Fin h → Z2) × (Fin m → Fin h → Fin l → Z2)) (i : Fin m) :
    cellF (u + v) i = cellF u i + cellF v i := by
  funext j k
  induction k using Fin.cases with
  | zero =>
    simp only [cellF_zero, Prod.fst_add, Prod.snd_add, Pi.add_apply, Finset.sum_add_distrib]
    ring
  | succ p =>
    simp only [cellF_succ, Prod.snd_add, Pi.add_apply]

theorem cellF_sub (u v : (Fin h → Z2) × (Fin m → Fin h → Fin l → Z2)) (i : Fin m) :
    cellF (u - v) i = cellF u i - cellF v i := by
  have := cellF_add (u - v) v i
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem cellF_sum (u : (Fin h → Z2) × (Fin m → Fin h → Fin l → Z2)) (i : Fin m) (j : Fin h) :
    ∑ k, cellF u i j k = u.1 j := by
  rw [Fin.sum_univ_succ]
  simp only [cellF_zero, cellF_succ]
  rw [add_assoc, z2_add_self, add_zero]

end cells

section lower
variable {n h l d : ℕ}

def sig (y : Fin h → Fin (l+1) → Z2) : (Fin h → Z2) × (Fin (n+1) → Fin h → Fin l → Z2) :=
  (fun j => ∑ k, y j k, fun i j p => if i = 0 then y j p.succ else 0)

theorem cellF_sig (y : Fin h → Fin (l+1) → Z2) : cellF (sig (n := n) y) 0 = y := by
  funext j k
  induction k using Fin.cases with
  | zero =>
    simp only [cellF_zero, sig, if_true]
    rw [Fin.sum_univ_succ (f := fun k => y j k), add_assoc, z2_add_self, add_zero]
  | succ p => simp [sig]

def tau (κ : Fin (n+1) → Fin h → Fin (l+1)) (s : Fin h → Z2) :
    (Fin h → Z2) × (Fin (n+1) → Fin h → Fin l → Z2) :=
  (s, fun i j p => if κ i j = p.succ then s j else 0)

theorem cellF_tau (κ : Fin (n+1) → Fin h → Fin (l+1)) (s : Fin h → Z2) (i : Fin (n+1))
    (j : Fin h) (k : Fin (l+1)) :
    cellF (tau κ s) i j k = if k = κ i j then s j else 0 := by
  induction k using Fin.cases with
  | zero =>
    simp only [cellF_zero, tau]
    rcases Fin.eq_zero_or_eq_succ (κ i j) with h0 | ⟨q, hq⟩
    · rw [h0]; simp [fun p : Fin l => (Fin.succ_ne_zero p).symm]
    · rw [hq]; simp [z2_add_self, (Fin.succ_ne_zero q).symm]
  | succ p =>
    simp only [cellF_succ, tau]
    by_cases hp : κ i j = p.succ
    · rw [if_pos hp, if_pos hp.symm]
    · rw [if_neg hp, if_neg (Ne.symm hp)]

def Oq (ask : Fin d → XU (n+1) h l →ₗ[Z2] Z2)
    (next : (Fin d → Z2) → Fin (h*l) → XU (n+1) h l →ₗ[Z2] Z2)
    (out : (Fin d → Z2) → (Fin (h*l) → Z2) → Fin (n+1) × (Fin h → Fin (l+1) → Z2))
    (q : XU (n+1) h l) : Fin (n+1) × (Fin h → Fin (l+1) → Z2) :=
  out (fun j => ask j q) (fun r => next (fun j => ask j q) r q)

def Good (ask : Fin d → XU (n+1) h l →ₗ[Z2] Z2)
    (next : (Fin d → Z2) → Fin (h*l) → XU (n+1) h l →ₗ[Z2] Z2)
    (out : (Fin d → Z2) → (Fin (h*l) → Z2) → Fin (n+1) × (Fin h → Fin (l+1) → Z2))
    (charge : Fin (n+1) → Z2) : Prop :=
  ∀ q : XU (n+1) h l, q.1 (Oq ask next out q).1 + q.1 ((Oq ask next out q).1 + 1) ≠
      charge (Oq ask next out q).1 ∧ (Oq ask next out q).2 = cellF q.2 (Oq ask next out q).1

theorem Oq_add (ask : Fin d → XU (n+1) h l →ₗ[Z2] Z2)
    (next : (Fin d → Z2) → Fin (h*l) → XU (n+1) h l →ₗ[Z2] Z2)
    (out : (Fin d → Z2) → (Fin (h*l) → Z2) → Fin (n+1) × (Fin h → Fin (l+1) → Z2))
    (q w : XU (n+1) h l) (hA : ∀ j, ask j w = 0)
    (hN : ∀ r, next (fun j => ask j q) r w = 0) :
    Oq ask next out (q + w) = Oq ask next out q := by
  have hz : (fun j => ask j (q + w)) = fun j => ask j q := by
    funext j; rw [map_add, hA j, add_zero]
  unfold Oq
  rw [hz]
  congr 1
  funext r
  rw [map_add, hN r, add_zero]

theorem key (ask : Fin d → XU (n+1) h l →ₗ[Z2] Z2)
    (next : (Fin d → Z2) → Fin (h*l) → XU (n+1) h l →ₗ[Z2] Z2)
    (out : (Fin d → Z2) → (Fin (h*l) → Z2) → Fin (n+1) × (Fin h → Fin (l+1) → Z2))
    (charge : Fin (n+1) → Z2) (hs : Good ask next out charge)
    (q w : XU (n+1) h l) (hA : ∀ j, ask j w = 0) (hN : ∀ r, next (fun j => ask j q) r w = 0) :
    cellF w.2 (Oq ask next out q).1 = 0 ∧
      w.1 (Oq ask next out q).1 + w.1 ((Oq ask next out q).1 + 1) = 0 := by
  have e := Oq_add ask next out q w hA hN
  have s1 := hs (q + w)
  rw [e] at s1
  have s0 := hs q
  constructor
  · have h1 := s1.2
    rw [s0.2, Prod.snd_add, cellF_add] at h1
    exact add_left_cancel (h1.symm.trans (add_zero _).symm)
  · have h2 := s1.1
    simp only [Prod.fst_add, Pi.add_apply] at h2
    exact z2_lemma _ _ _ _ _ s0.1 h2

theorem twoEdge (ask : Fin d → XU (n+1) h l →ₗ[Z2] Z2)
    (next : (Fin d → Z2) → Fin (h*l) → XU (n+1) h l →ₗ[Z2] Z2)
    (out : (Fin d → Z2) → (Fin (h*l) → Z2) → Fin (n+1) × (Fin h → Fin (l+1) → Z2))
    (charge : Fin (n+1) → Z2) (hs : Good ask next out charge) (hd : d < h*l + h)
    (q w : XU (n+1) h l) (hA : ∀ j, ask j w = 0) :
    (Oq ask next out (q + w)).1 = (Oq ask next out q).1 := by
  classical
  by_contra hne
  have hz : (fun j => ask j (q + w)) = fun j => ask j q := by
    funext j; rw [map_add, hA j, add_zero]
  have both : ∀ w' : XU (n+1) h l, (∀ j, ask j w' = 0) →
      (∀ r, next (fun j => ask j q) r w' = 0) →
      cellF w'.2 (Oq ask next out q).1 = 0 ∧ cellF w'.2 (Oq ask next out (q + w)).1 = 0 := by
    intro w' hA' hN'
    refine ⟨(key ask next out charge hs q w' hA' hN').1, ?_⟩
    have hN'' : ∀ r, next (fun j => ask j (q + w)) r w' = 0 := by rw [hz]; exact hN'
    exact (key ask next out charge hs (q + w) w' hA' hN'').1
  generalize (Oq ask next out q).1 = i1 at both hne
  generalize (Oq ask next out (q + w)).1 = i2 at both hne
  let φ : (Fin h → Z2) × (Fin h → Fin l → Z2) × (Fin h → Fin l → Z2) → XU (n+1) h l :=
    fun p => (0, (p.1, fun i => if i = i1 then p.2.1 else if i = i2 then p.2.2 else 0))
  let g : (Fin h → Z2) × (Fin h → Fin l → Z2) × (Fin h → Fin l → Z2) →
      (Fin d → Z2) × (Fin (h*l) → Z2) :=
    fun p => ((fun j => ask j (φ p)), (fun r => next (fun j => ask j q) r (φ p)))
  have ginj : Function.Injective g := by
    intro p p' hpp
    simp only [g, Prod.mk.injEq] at hpp
    obtain ⟨hp1, hp2⟩ := hpp
    have hA' : ∀ j, ask j (φ p - φ p') = 0 := fun j => by
      rw [map_sub, sub_eq_zero]; exact congrFun hp1 j
    have hN' : ∀ r, next (fun j => ask j q) r (φ p - φ p') = 0 := fun r => by
      rw [map_sub, sub_eq_zero]; exact congrFun hp2 r
    obtain ⟨c1, c2⟩ := both _ hA' hN'
    have ha : p.2.1 = p'.2.1 := by
      funext j t
      have h5 := congrFun (congrFun c1 j) t.succ
      have e5 : cellF (φ p - φ p').2 i1 j t.succ = p.2.1 j t - p'.2.1 j t := by
        rw [cellF_succ]
        show (if i1 = i1 then p.2.1 else if i1 = i2 then p.2.2 else 0) j t -
          (if i1 = i1 then p'.2.1 else if i1 = i2 then p'.2.2 else 0) j t = _
        rw [if_pos rfl, if_pos rfl]
      rw [e5] at h5
      exact sub_eq_zero.mp h5
    have hb : p.2.2 = p'.2.2 := by
      funext j t
      have h5 := congrFun (congrFun c2 j) t.succ
      have e5 : cellF (φ p - φ p').2 i2 j t.succ = p.2.2 j t - p'.2.2 j t := by
        rw [cellF_succ]
        show (if i2 = i1 then p.2.1 else if i2 = i2 then p.2.2 else 0) j t -
          (if i2 = i1 then p'.2.1 else if i2 = i2 then p'.2.2 else 0) j t = _
        rw [if_neg hne, if_neg hne, if_pos rfl, if_pos rfl]
      rw [e5] at h5
      exact sub_eq_zero.mp h5
    have hs1 : p.1 = p'.1 := by
      funext j
      have h5 := cellF_sum (φ p - φ p').2 i1 j
      rw [c1] at h5
      have e5 : (φ p - φ p').2.1 j = p.1 j - p'.1 j := rfl
      rw [e5] at h5
      simp only [Pi.zero_apply, Finset.sum_const_zero] at h5
      exact sub_eq_zero.mp h5.symm
    exact Prod.ext hs1 (Prod.ext ha hb)
  have c1 : Fintype.card ((Fin h → Z2) × (Fin h → Fin l → Z2) × (Fin h → Fin l → Z2)) =
      2 ^ (h + l*h + l*h) := by
    simp [Fintype.card_prod, Fintype.card_fun]; ring
  have c2 : Fintype.card ((Fin d → Z2) × (Fin (h*l) → Z2)) = 2 ^ (d + h*l) := by
    simp [Fintype.card_prod, Fintype.card_fun]; ring
  have hc : 2 ^ (h + l*h + l*h) ≤ 2 ^ (d + h*l) := by
    rw [← c1, ← c2]; exact Fintype.card_le_of_injective g ginj
  have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hc
  nlinarith

theorem lastEdge (c : Fin (n+1) → Z2) (r : Fin (n+1)) (hr : r ≠ Fin.last n) :
    (∑ t, if t.val < r.val then c t else 0) + (∑ t, if t.val < (r+1).val then c t else 0) =
      c r := by
  have hv : (r+1).val = r.val + 1 := by rw [Fin.val_add_one, if_neg hr]
  rw [hv]
  have key : ∀ t : Fin (n+1), (if t.val < r.val + 1 then c t else 0) =
      (if t.val < r.val then c t else 0) + (if t = r then c t else 0) := by
    intro t
    by_cases h1 : t.val < r.val
    · have h2 : t ≠ r := by intro e; rw [e] at h1; exact lt_irrefl _ h1
      rw [if_pos (by omega), if_pos h1, if_neg h2, add_zero]
    · by_cases h3 : t = r
      · rw [if_pos (by rw [h3]; omega), if_neg h1, if_pos h3, zero_add]
      · have h4 : ¬ t.val < r.val + 1 := by
          intro h5; apply h3; ext; omega
        rw [if_neg h4, if_neg h1, if_neg h3, add_zero]
  rw [Finset.sum_congr rfl (fun t _ => key t), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  rw [← add_assoc, z2_add_self, zero_add]

theorem onlyEdge (charge : Fin (n+1) → Z2) (i : Fin (n+1)) :
    ∃ x : Fin (n+1) → Z2, ∀ k, k ≠ i → x k + x (k+1) = charge k := by
  let c : Fin (n+1) → Z2 := fun t => charge (t + (i+1))
  let x' : Fin (n+1) → Z2 := fun k => ∑ t, if t.val < k.val then c t else 0
  refine ⟨fun k => x' (k - (i+1)), fun k hk => ?_⟩
  have hr : k - (i+1) ≠ Fin.last n := by
    intro hr
    apply hk
    have h1 : k - (i+1) + 1 = 0 := by rw [hr, Fin.last_add_one]
    have h2 : k - (i+1) + 1 = k - i := by abel
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  have step : x' (k - (i+1)) + x' (k - (i+1) + 1) = c (k - (i+1)) :=
    lastEdge c (k - (i+1)) hr
  have e1 : k + 1 - (i + 1) = k - (i+1) + 1 := by abel
  show x' (k - (i+1)) + x' (k + 1 - (i+1)) = charge k
  rw [e1, step]
  show charge (k - (i+1) + (i+1)) = charge k
  rw [sub_add_cancel]

theorem xzero (v : Fin (n+1) → Z2) (hv : ∀ k, v k + v (k+1) = 0) (h0 : v 0 = 0) : v = 0 := by
  have : ∀ t (ht : t < n+1), v ⟨t, ht⟩ = 0 := by
    intro t
    induction t with
    | zero =>
      intro ht
      have e : (⟨0, ht⟩ : Fin (n+1)) = 0 := Fin.ext (by simp)
      rw [e]; exact h0
    | succ t ih =>
      intro ht
      have h1 := hv ⟨t, by omega⟩
      have h2 : (⟨t, by omega⟩ : Fin (n+1)) + 1 = ⟨t+1, ht⟩ := by
        ext
        rw [Fin.val_add_one, if_neg]
        intro e
        have := congrArg Fin.val e
        simp at this
        omega
      rw [h2, ih (by omega), zero_add] at h1
      exact h1
  funext k
  exact this k.val k.isLt

theorem lower (n h l d L : ℕ) (hh : 1 ≤ h) (hL : 1 ≤ L) (hl : L * ((n+1)*h + (n+1)) ≤ l)
    (charge : Fin (n+1) → Z2)
    (ask : Fin d → XU (n+1) h l →ₗ[Z2] Z2)
    (next : (Fin d → Z2) → Fin (h*l) → XU (n+1) h l →ₗ[Z2] Z2)
    (out : (Fin d → Z2) → (Fin (h*l) → Z2) → Fin (n+1) × (Fin h → Fin (l+1) → Z2))
    (hs : Good ask next out charge) :
    n + h ≤ d ∧ ((∀ j, isLocal L (ask j)) → n + (n+1)*h ≤ d) := by
  classical
  have e1 : (n+1)*h + (n+1) ≤ l := le_trans (Nat.le_mul_of_pos_left _ hL) hl
  have e2 : l ≤ h * l := Nat.le_mul_of_pos_left _ hh
  by_cases hbig : h * l + h ≤ d
  · refine ⟨by nlinarith, fun _ => by nlinarith⟩
  push_neg at hbig
  choose X hX using fun i => onlyEdge charge i
  let P : Fin (n+1) → XU (n+1) h l := fun i => (X i, 0)
  have hP : ∀ i, (Oq ask next out (P i)).1 = i := by
    intro i; by_contra hne; exact (hs (P i)).1 (hX i _ hne)
  have factA : ∀ i (w : XU (n+1) h l), (∀ j, ask j w = 0) →
      (∀ r, next (fun j => ask j (P i)) r w = 0) → cellF w.2 i = 0 := by
    intro i w hA hN
    have := (key ask next out charge hs (P i) w hA hN).1
    rwa [hP i] at this
  have factC : ∀ (w : XU (n+1) h l), (∀ j, ask j w = 0) → w.1 0 = 0 → w.1 = 0 := by
    intro w hA h0
    refine xzero _ (fun i => ?_) h0
    have h2 := twoEdge ask next out charge hs hbig (P i) w hA
    rw [hP i] at h2
    have s1 := (hs (P i + w)).1
    rw [h2] at s1
    have s0 := (hs (P i)).1
    rw [hP i] at s0
    simp only [Prod.fst_add, Pi.add_apply] at s1
    exact z2_lemma _ _ _ _ _ s0 s1
  refine ⟨?_, ?_⟩
  · -- unrestricted bound
    let φ : (Fin (n+1) → Z2) × (Fin h → Fin (l+1) → Z2) → XU (n+1) h l :=
      fun a => (a.1, sig a.2)
    let g : (Fin (n+1) → Z2) × (Fin h → Fin (l+1) → Z2) →
        (Fin d → Z2) × Z2 × (Fin (h*l) → Z2) :=
      fun a => ((fun j => ask j (φ a)), a.1 0, (fun r => next (fun j => ask j (P 0)) r (φ a)))
    have ginj : Function.Injective g := by
      rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
      simp only [g, Prod.mk.injEq] at hxy
      obtain ⟨h1, h2, h3⟩ := hxy
      have hA : ∀ j, ask j (φ (x,y) - φ (x',y')) = 0 := fun j => by
        rw [map_sub, sub_eq_zero]; exact congrFun h1 j
      have hN : ∀ r, next (fun j => ask j (P 0)) r (φ (x,y) - φ (x',y')) = 0 := fun r => by
        rw [map_sub, sub_eq_zero]; exact congrFun h3 r
      have h0 : (φ (x,y) - φ (x',y')).1 0 = 0 := by
        show x 0 - x' 0 = 0
        rw [h2, sub_self]
      have hx : x - x' = 0 := factC _ hA h0
      have hy := factA 0 _ hA hN
      have e5 : (φ (x,y) - φ (x',y')).2 = sig y - sig y' := rfl
      rw [e5, cellF_sub, cellF_sig, cellF_sig] at hy
      rw [sub_eq_zero] at hx hy
      rw [hx, hy]
    have c1 : Fintype.card ((Fin (n+1) → Z2) × (Fin h → Fin (l+1) → Z2)) =
        2 ^ ((n+1) + (l+1)*h) := by
      simp [Fintype.card_prod, Fintype.card_fun]; ring
    have c2 : Fintype.card ((Fin d → Z2) × Z2 × (Fin (h*l) → Z2)) = 2 ^ (d + 1 + h*l) := by
      simp [Fintype.card_prod, Fintype.card_fun]; ring
    have hc : 2 ^ ((n+1) + (l+1)*h) ≤ 2 ^ (d + 1 + h*l) := by
      rw [← c1, ← c2]; exact Fintype.card_le_of_injective g ginj
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hc
    nlinarith
  · -- sparse bound
    intro hloc
    by_contra hlt
    push_neg at hlt
    simp only [isLocal] at hloc
    choose S hScard hS using hloc
    let T : Finset ((Fin (n+1) × Fin h) × Fin (l+1)) := Finset.univ.biUnion S
    have hT : T.card ≤ d * L := by
      calc T.card ≤ ∑ j, (S j).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin d, L := Finset.sum_le_sum (fun j _ => hScard j)
        _ = d * L := by simp
    have hTl : T.card < l + 1 := by
      have := Nat.mul_le_mul_right L (show d + 1 ≤ n + (n+1)*h by omega)
      nlinarith
    have miss : ∀ i j, ∃ k, ((i,j),k) ∉ T := by
      intro i j
      by_contra hall
      push_neg at hall
      have hsub : (Finset.univ.image (fun k : Fin (l+1) => ((i,j),k))) ⊆ T := by
        intro t ht
        rw [Finset.mem_image] at ht
        obtain ⟨k, _, rfl⟩ := ht
        exact hall k
      have := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ (fun k k' e => by simpa using e)] at this
      simp at this
      omega
    choose κ hκ using miss
    have tauA : ∀ (s : Fin h → Z2) j, ask j ((0 : Fin (n+1) → Z2), tau κ s) = 0 := by
      intro s j
      rw [hS j]
      apply Finset.sum_eq_zero
      intro t ht
      rw [cellF_tau, if_neg]
      intro e
      apply hκ t.1.1 t.1.2
      have ht' : t ∈ T := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ht⟩
      rw [← e]
      exact ht'
    let g : XU (n+1) h l × (Fin (n+1) → Fin h → Z2) →
        (Fin d → Z2) × Z2 × (Fin h → Z2) × (Fin (n+1) → Fin (h*l) → Z2) :=
      fun a => ((fun j => ask j a.1), a.1.1 0, a.1.2.1,
        fun i r => next (fun j => ask j (P i)) r (a.1 + ((0 : Fin (n+1) → Z2), tau κ (a.2 i))))
    have ginj : Function.Injective g := by
      rintro ⟨v, s⟩ ⟨v', s'⟩ hvv
      simp only [g, Prod.mk.injEq] at hvv
      obtain ⟨hv1, hv2, hv3, hv4⟩ := hvv
      have hA : ∀ j, ask j (v - v') = 0 := fun j => by
        rw [map_sub, sub_eq_zero]; exact congrFun hv1 j
      have h0 : (v - v').1 0 = 0 := by
        show v.1 0 - v'.1 0 = 0
        rw [hv2, sub_self]
      have hx : (v - v').1 = 0 := factC _ hA h0
      have hss : ∀ i, s i = s' i ∧ cellF (v - v').2 i = 0 := by
        intro i
        have hAi : ∀ j, ask j ((v + ((0 : Fin (n+1) → Z2), tau κ (s i))) -
            (v' + ((0 : Fin (n+1) → Z2), tau κ (s' i)))) = 0 := fun j => by
          rw [map_sub, map_add, map_add, tauA, tauA, add_zero, add_zero, sub_eq_zero]
          exact congrFun hv1 j
        have hNi : ∀ r, next (fun j => ask j (P i)) r ((v + ((0 : Fin (n+1) → Z2), tau κ (s i))) -
            (v' + ((0 : Fin (n+1) → Z2), tau κ (s' i)))) = 0 := fun r => by
          rw [map_sub, sub_eq_zero]; exact congrFun (congrFun hv4 i) r
        have hc := factA i _ hAi hNi
        have hsi : s i = s' i := by
          funext j
          have h5 := cellF_sum ((v + ((0 : Fin (n+1) → Z2), tau κ (s i))) -
            (v' + ((0 : Fin (n+1) → Z2), tau κ (s' i)))).2 i j
          have e : ((v + ((0 : Fin (n+1) → Z2), tau κ (s i))) -
              (v' + ((0 : Fin (n+1) → Z2), tau κ (s' i)))).2.1 j = s i j - s' i j := by
            show (v.2.1 j + s i j) - (v'.2.1 j + s' i j) = s i j - s' i j
            rw [hv3]; ring
          rw [hc, e] at h5
          simp only [Pi.zero_apply, Finset.sum_const_zero] at h5
          exact sub_eq_zero.mp h5.symm
        refine ⟨hsi, ?_⟩
        rw [hsi] at hc
        have e : (v + ((0 : Fin (n+1) → Z2), tau κ (s' i))) -
            (v' + ((0 : Fin (n+1) → Z2), tau κ (s' i))) = v - v' := add_sub_add_right_eq_sub _ _ _
        rw [e] at hc
        exact hc
      have hs' : s = s' := funext fun i => (hss i).1
      have hu2 : (v - v').2.2 = 0 := by
        funext i j p
        have := congrFun (congrFun (hss i).2 j) p.succ
        rw [cellF_succ] at this
        exact this
      have hu1 : (v - v').2.1 = 0 := by
        show v.2.1 - v'.2.1 = 0
        rw [hv3, sub_self]
      have hvv : v - v' = 0 := Prod.ext hx (Prod.ext hu1 hu2)
      rw [sub_eq_zero] at hvv
      rw [hvv, hs']
    have c1 : Fintype.card (XU (n+1) h l × (Fin (n+1) → Fin h → Z2)) =
        2 ^ ((n+1) + h + l*h*(n+1) + h*(n+1)) := by
      simp [XU, Fintype.card_prod, Fintype.card_fun]; ring
    have c2 : Fintype.card ((Fin d → Z2) × Z2 × (Fin h → Z2) × (Fin (n+1) → Fin (h*l) → Z2)) =
        2 ^ (d + 1 + h + h*l*(n+1)) := by
      simp [Fintype.card_prod, Fintype.card_fun]; ring
    have hc : 2 ^ ((n+1) + h + l*h*(n+1) + h*(n+1)) ≤ 2 ^ (d + 1 + h + h*l*(n+1)) := by
      rw [← c1, ← c2]; exact Fintype.card_le_of_injective g ginj
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hc
    nlinarith

end lower

noncomputable section
variable {n h l d N : ℕ}

theorem sum_edges (x : Fin (n+1) → Z2) : ∑ e, (x e + x (e+1)) = 0 := by
  rw [Finset.sum_add_distrib]
  have : ∑ e, x (e+1) = ∑ e, x e := Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  rw [this, z2_add_self]

def synL (e : Fin (n+1)) : XU (n+1) h l →ₗ[Z2] Z2 where
  toFun q := q.1 e + q.1 (e+1)
  map_add' q q' := by simp only [Prod.fst_add, Pi.add_apply]; ring
  map_smul' c q := by
    simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def readL (i : Fin (n+1)) (j : Fin h) (p : Fin l) : XU (n+1) h l →ₗ[Z2] Z2 where
  toFun q := q.2.2 i j p
  map_add' q q' := by simp only [Prod.snd_add, Pi.add_apply]
  map_smul' c q := by simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

def chkL (j : Fin h) : XU (n+1) h l →ₗ[Z2] Z2 where
  toFun q := q.2.1 j
  map_add' q q' := by simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply]
  map_smul' c q := by
    simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

def cell0L (i : Fin (n+1)) (j : Fin h) : XU (n+1) h l →ₗ[Z2] Z2 where
  toFun q := q.2.1 j + ∑ p, q.2.2 i j p
  map_add' q q' := by
    simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Finset.sum_add_distrib]; ring
  map_smul' c q := by
    simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← Finset.mul_sum]
    ring

def FU (dat : Fin N → XU (n+1) h l →ₗ[Z2] Z2) : Fin (n + N) → XU (n+1) h l →ₗ[Z2] Z2 :=
  Fin.addCases (motive := fun _ => XU (n+1) h l →ₗ[Z2] Z2)
    (fun k : Fin n => synL ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩) dat

def askU (dat : Fin N → XU (n+1) h l →ₗ[Z2] Z2) : Fin d → XU (n+1) h l →ₗ[Z2] Z2 :=
  fun j => if hj : j.val < n + N then FU dat ⟨j.val, hj⟩ else 0

def zzU (hdN : n + N ≤ d) (z : Fin d → Z2) : Fin (n+N) → Z2 :=
  fun k => z ⟨k.val, lt_of_lt_of_le k.isLt hdN⟩

def edgeU (hdN : n + N ≤ d) (charge : Fin (n+1) → Z2) (z : Fin d → Z2) : Fin (n+1) :=
  if hex : ∃ k : Fin n, zzU hdN z (Fin.castAdd N k) ≠ charge ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
  then ⟨hex.choose.val, Nat.lt_succ_of_lt hex.choose.isLt⟩ else Fin.last n

def nextU (hdN : n + N ≤ d) (charge : Fin (n+1) → Z2) (z : Fin d → Z2) (r : Fin (h*l)) :
    XU (n+1) h l →ₗ[Z2] Z2 :=
  readL (edgeU hdN charge z) (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2

def outU (hdN : n + N ≤ d) (charge : Fin (n+1) → Z2)
    (dec : (Fin N → Z2) → Fin (n+1) → (Fin h → Fin l → Z2) → (Fin h → Fin (l+1) → Z2))
    (z : Fin d → Z2) (w : Fin (h*l) → Z2) : Fin (n+1) × (Fin h → Fin (l+1) → Z2) :=
  (edgeU hdN charge z, dec (fun k => zzU hdN z (Fin.natAdd n k)) (edgeU hdN charge z)
    (fun j p => w (finProdFinEquiv (j,p))))

theorem FU_left (dat : Fin N → XU (n+1) h l →ₗ[Z2] Z2) (k : Fin n) :
    FU dat (Fin.castAdd N k) = synL ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ := by
  simp [FU]

theorem FU_right (dat : Fin N → XU (n+1) h l →ₗ[Z2] Z2) (k : Fin N) :
    FU dat (Fin.natAdd n k) = dat k := by
  simp [FU]

theorem zzU_askU (hdN : n + N ≤ d) (dat : Fin N → XU (n+1) h l →ₗ[Z2] Z2)
    (q : XU (n+1) h l) (k : Fin (n+N)) :
    zzU hdN (fun j => askU dat j q) k = FU dat k q := by
  simp [zzU, askU]

theorem upper (L : ℕ) (hL : 1 ≤ L) (charge : Fin (n+1) → Z2) (hch : ∑ i, charge i = 1)
    (dat : Fin N → XU (n+1) h l →ₗ[Z2] Z2)
    (dec : (Fin N → Z2) → Fin (n+1) → (Fin h → Fin l → Z2) → (Fin h → Fin (l+1) → Z2))
    (hdec : ∀ (x : Fin (n+1) → Z2) (u : (Fin h → Z2) × (Fin (n+1) → Fin h → Fin l → Z2))
      (i : Fin (n+1)), dec (fun k => dat k (x,u)) i (u.2 i) = cellF u i)
    (hdN : n + N ≤ d) :
    ∃ (ask : Fin d → XU (n+1) h l →ₗ[Z2] Z2)
      (next : (Fin d → Z2) → Fin (h*l) → XU (n+1) h l →ₗ[Z2] Z2)
      (out : (Fin d → Z2) → (Fin (h*l) → Z2) → Fin (n+1) × (Fin h → Fin (l+1) → Z2)),
      ((∀ k, isLocal L (dat k)) → ∀ j, isLocal L (ask j)) ∧
      (∀ z j, isLocal L (next z j)) ∧
      ∀ (x : Fin (n+1) → Z2) (u : (Fin h → Z2) × (Fin (n+1) → Fin h → Fin l → Z2)),
        let z := fun j => ask j (x,u)
        let y := out z (fun j => next z j (x,u))
        x y.1 + x (y.1+1) ≠ charge y.1 ∧ y.2 = cellF u y.1 := by
  classical
  refine ⟨askU dat, nextU hdN charge, outU hdN charge dec, ?_, ?_, ?_⟩
  · intro hdat j
    unfold askU
    split_ifs with hj
    · generalize (⟨j.val, hj⟩ : Fin (n+N)) = k
      induction k using Fin.addCases with
      | left k =>
        rw [FU_left]
        exact ⟨∅, by simp, fun u => by simp [synL]⟩
      | right k => rw [FU_right]; exact hdat k
    · exact ⟨∅, by simp, fun u => by simp⟩
  · intro z r
    refine ⟨{((edgeU hdN charge z, (finProdFinEquiv.symm r).1), (finProdFinEquiv.symm r).2.succ)},
      by simpa using hL, fun u => ?_⟩
    simp [nextU, readL]
  · intro x u
    dsimp only
    have hzz : ∀ k, zzU hdN (fun j => askU dat j (x,u)) k = FU dat k (x,u) :=
      fun k => zzU_askU hdN dat (x,u) k
    have hw : (fun j p => nextU hdN charge (fun j => askU dat j (x,u)) (finProdFinEquiv (j,p))
        (x,u)) = u.2 (edgeU hdN charge (fun j => askU dat j (x,u))) := by
      funext j p; simp [nextU, readL]
    have hd' : (fun k => zzU hdN (fun j => askU dat j (x,u)) (Fin.natAdd n k)) =
        fun k => dat k (x,u) := by
      funext k; rw [hzz, FU_right]
    refine ⟨?_, ?_⟩
    · show x (edgeU hdN charge (fun j => askU dat j (x,u))) +
        x (edgeU hdN charge (fun j => askU dat j (x,u)) + 1) ≠
        charge (edgeU hdN charge (fun j => askU dat j (x,u)))
      unfold edgeU
      split_ifs with hex
      · have := hex.choose_spec
        rw [hzz, FU_left] at this
        exact this
      · push_neg at hex
        have hsyn : ∀ k : Fin n, x (Fin.castSucc k) + x (Fin.castSucc k + 1) =
            charge (Fin.castSucc k) := by
          intro k; have := hex k; rw [hzz, FU_left] at this; exact this
        have h0 := sum_edges x
        rw [Fin.sum_univ_castSucc] at h0
        simp only [hsyn] at h0
        have h1 := hch
        rw [Fin.sum_univ_castSucc] at h1
        exact z2_lemma2 _ _ _ h0 h1
    · have := hdec x u (edgeU hdN charge (fun j => askU dat j (x,u)))
      rw [← hd', ← hw] at this
      exact this

def genDec (zd : Fin h → Z2) (_ : Fin (n+1)) (v : Fin h → Fin l → Z2) :
    Fin h → Fin (l+1) → Z2 :=
  fun j => Fin.cases (motive := fun _ => Z2) (zd j + ∑ p, v j p) (v j)

theorem genDec_ok (x : Fin (n+1) → Z2) (u : (Fin h → Z2) × (Fin (n+1) → Fin h → Fin l → Z2))
    (i : Fin (n+1)) : genDec (fun k => chkL (n := n) (l := l) k (x,u)) i (u.2 i) = cellF u i :=
  rfl

def spDat (k : Fin ((n+1)*h)) : XU (n+1) h l →ₗ[Z2] Z2 :=
  cell0L (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

def spDec (zd : Fin ((n+1)*h) → Z2) (i : Fin (n+1)) (v : Fin h → Fin l → Z2) :
    Fin h → Fin (l+1) → Z2 :=
  fun j => Fin.cases (motive := fun _ => Z2) (zd (finProdFinEquiv (i,j))) (v j)

theorem spDec_ok (x : Fin (n+1) → Z2) (u : (Fin h → Z2) × (Fin (n+1) → Fin h → Fin l → Z2))
    (i : Fin (n+1)) : spDec (fun k => spDat (l := l) k (x,u)) i (u.2 i) = cellF u i := by
  funext j
  simp [spDec, spDat, cell0L, cellF]

theorem spLocal (L : ℕ) (hL : 1 ≤ L) (k : Fin ((n+1)*h)) : isLocal L (spDat (l := l) k) :=
  ⟨{(finProdFinEquiv.symm k, 0)}, by simpa using hL, fun u => by simp [spDat, cell0L]⟩

end

theorem main_aux (a b c l : ℕ) (hl : (c+1) * ((a+2+1)*(b+1) + (a+2+1)) ≤ l)
    (charge : Fin (a+2+1) → Z2) (hch : ∑ i, charge i = 1) (fl ll : Bool) (d : ℕ) :
    (∃ (ask : Fin d → XU (a+2+1) (b+1) l →ₗ[Z2] Z2)
        (next : (Fin d → Z2) → Fin ((b+1)*l) → XU (a+2+1) (b+1) l →ₗ[Z2] Z2)
        (out : (Fin d → Z2) → (Fin ((b+1)*l) → Z2) → Fin (a+2+1) × (Fin (b+1) → Fin (l+1) → Z2)),
        (fl = true → ∀ j, isLocal (c+1) (ask j)) ∧
        (ll = true → ∀ z j, isLocal (c+1) (next z j)) ∧
        ∀ (x : Fin (a+2+1) → Z2) (u : (Fin (b+1) → Z2) × (Fin (a+2+1) → Fin (b+1) → Fin l → Z2)),
          let z := fun j => ask j (x,u)
          let y := out z (fun j => next z j (x,u))
          x y.1 + x (y.1+1) ≠ charge y.1 ∧ y.2 = cellF u y.1) ↔
      (a+2+1)-1 + (if fl then (a+2+1)*(b+1) else (b+1)) ≤ d := by
  constructor
  · rintro ⟨ask, next, out, hfl, _, hspec⟩
    have hs : Good ask next out charge := fun q => hspec q.1 q.2
    obtain ⟨hgen, hloc⟩ :=
      lower (a+2) (b+1) l d (c+1) (by omega) (by omega) hl charge ask next out hs
    rw [Nat.add_sub_cancel]
    cases fl
    · rw [if_neg (by decide)]; exact hgen
    · rw [if_pos rfl]; exact hloc (hfl rfl)
  · intro hd
    rw [Nat.add_sub_cancel] at hd
    cases fl
    · rw [if_neg (by decide)] at hd
      obtain ⟨ask, next, out, -, h2, h3⟩ := upper (c+1) (by omega) charge hch
        chkL genDec genDec_ok hd
      exact ⟨ask, next, out, fun h => absurd h (by decide), fun _ => h2, h3⟩
    · rw [if_pos rfl] at hd
      obtain ⟨ask, next, out, h1, h2, h3⟩ := upper (c+1) (by omega) charge hch
        spDat spDec spDec_ok hd
      exact ⟨ask, next, out, fun _ => h1 (spLocal (c+1) (by omega)), fun _ => h2, h3⟩

end PEqualNP.Outside.L_pcx_433_aux

theorem PEqualNP.Outside.L_pcx_433 : ∀ a b c l : ℕ,
  let m := a+3
  let h := b+1
  let L := c+1
  L*(m*h+m) ≤ l →
  let K := ZMod 2
  let I := Fin m
  let J := Fin h
  let X := I → K
  let U := (J → K) × (I → J → Fin l → K)
  let Y := J → Fin (l+1) → K
  let cell : U → I → Y := fun u i j =>
    Fin.cases (motive := fun _ => K) (u.1 j + ∑ p : Fin l, u.2 i j p) (u.2 i j)
  let localProbe := fun (f : (X × U) →ₗ[K] K) =>
    ∃ S : Finset ((I × J) × Fin (l+1)), S.card ≤ L ∧
      ∀ u : U, f (0,u) = ∑ s ∈ S, cell u s.1.1 s.1.2 s.2
  ∀ (charge : I → K), (∑ i, charge i) = 1 →
    ∀ (firstLocal lastLocal : Bool) (d : ℕ),
      (∃ (ask : Fin d → (X × U) →ₗ[K] K)
          (next : (Fin d → K) → Fin (h*l) → (X × U) →ₗ[K] K)
          (out : (Fin d → K) → (Fin (h*l) → K) → I × Y),
        (firstLocal = true → ∀ j, localProbe (ask j)) ∧
        (lastLocal = true → ∀ z j, localProbe (next z j)) ∧
        ∀ x : X, ∀ u : U,
          let z := fun j => ask j (x,u)
          let y := out z (fun j => next z j (x,u))
          x y.1 + x (y.1+1) ≠ charge y.1 ∧ y.2 = cell u y.1) ↔
        m-1 + (if firstLocal then m*h else h) ≤ d := by
  intro a b c l m h L hl K I J X U Y cell localProbe charge hch fl ll d
  exact PEqualNP.Outside.L_pcx_433_aux.main_aux a b c l hl charge hch fl ll d
