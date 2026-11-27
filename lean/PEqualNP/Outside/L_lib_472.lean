import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_472_aux

open PEqualNP.ProofComplexity Finset

abbrev PS (q : ℕ) := {S : Finset (Fin q) // S ≠ ∅ ∧ S ≠ univ}

abbrev Par (h q : ℕ) := Σ j : Fin h, Fin (h - j) × (Fin j → PS q)

def cut (h : ℕ) {q : ℕ} (S : ℕ → Finset (Fin q)) : Clause (Fin h × (Fin q × Fin q)) :=
  (univ.filter (fun e : Fin h × (Fin q × Fin q) => e.2.1 ∈ S e.1.val ∧ e.2.2 ∉ S (e.1.val + 1))).image
    (fun e => (e, true))

theorem mem_cut {h q : ℕ} {S : ℕ → Finset (Fin q)} {l : Literal (Fin h × (Fin q × Fin q))} :
    l ∈ cut h S ↔ l.2 = true ∧ l.1.2.1 ∈ S l.1.1.val ∧ l.1.2.2 ∉ S (l.1.1.val + 1) := by
  obtain ⟨e, b⟩ := l
  simp only [cut, mem_image, mem_filter, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨e', ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨rfl, h1, h2⟩
  · rintro ⟨rfl, h1, h2⟩; exact ⟨e, ⟨h1, h2⟩, rfl, rfl⟩

def seqOf {h q : ℕ} (start finish : Fin q) (p : Par h q) : ℕ → Finset (Fin q) := fun t =>
  if t = 0 then {start} else if h ≤ t then univ.erase finish else
  if t ≤ p.2.1.val then univ else
  if ht : t - p.2.1.val - 1 < p.1.val then (p.2.2 ⟨t - p.2.1.val - 1, ht⟩).val else ∅

section seq
variable {h q : ℕ} (start finish : Fin q) (p : Par h q)

theorem par_lt : p.2.1.val + p.1.val < h := by
  have := p.2.1.isLt; have := p.1.isLt; omega

theorem seq_zero : seqOf start finish p 0 = {start} := by simp [seqOf]

theorem seq_top {t : ℕ} (ht : h ≤ t) : seqOf start finish p t = univ.erase finish := by
  have := p.1.isLt
  simp [seqOf, ht, show t ≠ 0 by omega]

theorem seq_full {t : ℕ} (h1 : 1 ≤ t) (h2 : t ≤ p.2.1.val) : seqOf start finish p t = univ := by
  have := par_lt p
  simp [seqOf, h2, show t ≠ 0 by omega, show ¬ h ≤ t by omega]

theorem seq_mid {t : ℕ} (h1 : p.2.1.val < t) (h2 : t ≤ p.2.1.val + p.1.val) :
    seqOf start finish p t = (p.2.2 ⟨t - p.2.1.val - 1, by omega⟩).val := by
  have := par_lt p
  simp [seqOf, show t ≠ 0 by omega, show ¬ h ≤ t by omega, show ¬ t ≤ p.2.1.val by omega,
    show t - p.2.1.val - 1 < p.1.val by omega]

theorem seq_empty {t : ℕ} (h1 : p.2.1.val + p.1.val < t) (h2 : t < h) : seqOf start finish p t = ∅ := by
  simp [seqOf, show t ≠ 0 by omega, show ¬ h ≤ t by omega, show ¬ t ≤ p.2.1.val by omega,
    show ¬ t - p.2.1.val - 1 < p.1.val by omega]

theorem univ_ne_empty (hq : 0 < q) : (univ : Finset (Fin q)) ≠ ∅ := by
  intro h0; have : (⟨0, hq⟩ : Fin q) ∈ (univ : Finset (Fin q)) := mem_univ _
  rw [h0] at this; simp at this

theorem seq_eq_univ_iff (hq : 0 < q) {t : ℕ} (h1 : 1 ≤ t) (h2 : t < h) :
    seqOf start finish p t = univ ↔ t ≤ p.2.1.val := by
  constructor
  · intro hu; by_contra hk; rw [not_le] at hk
    by_cases hm : t ≤ p.2.1.val + p.1.val
    · rw [seq_mid start finish p hk hm] at hu; exact (p.2.2 _).2.2 hu
    · rw [not_le] at hm; rw [seq_empty start finish p hm h2] at hu; exact univ_ne_empty hq hu.symm
  · intro hk; exact seq_full start finish p h1 hk

theorem seq_eq_empty_iff (hq : 0 < q) {t : ℕ} (h1 : 1 ≤ t) (h2 : t < h) :
    seqOf start finish p t = ∅ ↔ p.2.1.val + p.1.val < t := by
  constructor
  · intro he; by_contra hk; rw [not_lt] at hk
    by_cases hm : t ≤ p.2.1.val
    · rw [seq_full start finish p h1 hm] at he; exact univ_ne_empty hq he
    · rw [not_le] at hm; rw [seq_mid start finish p hm hk] at he; exact (p.2.2 _).2.1 he
  · intro hk; exact seq_empty start finish p hk h2

end seq

def pathN (h : ℕ) {q : ℕ} (start finish : Fin q) (tab : Fin h × (Fin q × Fin q) → Bool) : Prop :=
  ∃ x : ℕ → Fin q, x 0 = start ∧ x h = finish ∧ ∀ i : Fin h, tab (i, x i.val, x (i.val + 1)) = true

theorem path_iff {h q : ℕ} (start finish : Fin q) (tab : Fin h × (Fin q × Fin q) → Bool) :
    (∃ x : Fin (h + 1) → Fin q, x 0 = start ∧ x (Fin.last h) = finish ∧
      ∀ i : Fin h, tab (i, x i.castSucc, x i.succ) = true) ↔ pathN h start finish tab := by
  constructor
  · rintro ⟨x, h0, hh, hx⟩
    refine ⟨fun t => if ht : t < h + 1 then x ⟨t, ht⟩ else start, ?_, ?_, ?_⟩
    · simpa using h0
    · simpa [Fin.last] using hh
    · intro i
      have h1 : i.val < h + 1 := by omega
      have h2 : i.val + 1 < h + 1 := by omega
      simp only [h1, h2, dite_true]
      simpa [Fin.castSucc, Fin.succ, Fin.castAdd, Fin.castLE] using hx i
  · rintro ⟨x, h0, hh, hx⟩
    refine ⟨fun t => x t.val, by simpa using h0, by simpa using hh, ?_⟩
    intro i; simpa using hx i

section paths
variable {h q : ℕ} (start finish : Fin q)

theorem sat_of_path {S : ℕ → Finset (Fin q)} (h0 : start ∈ S 0) (hh : finish ∉ S h)
    {tab : Fin h × (Fin q × Fin q) → Bool} (hp : pathN h start finish tab) :
    ClauseSat tab (cut h S) := by
  obtain ⟨x, hx0, hxh, hx⟩ := hp
  have : ∃ i, i < h ∧ x i ∈ S i ∧ x (i + 1) ∉ S (i + 1) := by
    by_contra hne
    have hne' : ∀ i, i < h → x i ∈ S i → x (i + 1) ∈ S (i + 1) := by
      intro i hi h1; by_contra h2; exact hne ⟨i, hi, h1, h2⟩
    have : ∀ t, t ≤ h → x t ∈ S t := by
      intro t; induction t with
      | zero => intro _; rw [hx0]; exact h0
      | succ n ih => intro hn; exact hne' n (by omega) (ih (by omega))
    exact hh (hxh ▸ this h le_rfl)
  obtain ⟨i, hi, h1, h2⟩ := this
  refine ⟨((⟨i, hi⟩, x i, x (i + 1)), true), ?_, ?_⟩
  · rw [mem_cut]; exact ⟨rfl, h1, h2⟩
  · exact hx ⟨i, hi⟩

def reach (h : ℕ) {q : ℕ} (start : Fin q) (tab : Fin h × (Fin q × Fin q) → Bool) : ℕ → Finset (Fin q)
  | 0 => {start}
  | t + 1 => if ht : t < h then
      univ.filter (fun b => ∃ a ∈ reach h start tab t, tab (⟨t, ht⟩, a, b) = true) else ∅

theorem mem_reach_succ {tab : Fin h × (Fin q × Fin q) → Bool} {t : ℕ} (ht : t < h) {b : Fin q} :
    b ∈ reach h start tab (t + 1) ↔ ∃ a ∈ reach h start tab t, tab (⟨t, ht⟩, a, b) = true := by
  simp [reach, ht]

theorem reach_path (tab : Fin h × (Fin q × Fin q) → Bool) : ∀ t, t ≤ h → ∀ b ∈ reach h start tab t,
    ∃ x : ℕ → Fin q, x 0 = start ∧ x t = b ∧
      ∀ i (hi : i < h), i < t → tab (⟨i, hi⟩, x i, x (i + 1)) = true := by
  intro t; induction t with
  | zero =>
    intro _ b hb
    simp only [reach, mem_singleton] at hb
    exact ⟨fun _ => start, rfl, hb.symm, fun i _ hi => absurd hi (by omega)⟩
  | succ n ih =>
    intro hn b hb
    rw [mem_reach_succ start (by omega : n < h)] at hb
    obtain ⟨a, ha, hab⟩ := hb
    obtain ⟨x, hx0, hxn, hx⟩ := ih (by omega) a ha
    refine ⟨fun i => if i ≤ n then x i else b, by simp [hx0], by simp, ?_⟩
    intro i hi hin
    by_cases hlt : i < n
    · simp only [show i ≤ n by omega, show i + 1 ≤ n by omega, ite_true]; exact hx i hi hlt
    · have : i = n := by omega
      subst this
      simp only [le_refl, ite_true, show ¬ i + 1 ≤ i by omega, ite_false, hxn]; exact hab

theorem reach_cut_false (tab : Fin h × (Fin q × Fin q) → Bool) (hnp : ¬ pathN h start finish tab) :
    ¬ ClauseSat tab (cut h (fun t => if h ≤ t then univ.erase finish else reach h start tab t)) := by
  have hfin : finish ∉ reach h start tab h := by
    intro hf
    obtain ⟨x, hx0, hxh, hx⟩ := reach_path start tab h le_rfl finish hf
    exact hnp ⟨x, hx0, hxh, fun i => hx i.val i.isLt i.isLt⟩
  rintro ⟨l, hl, hsat⟩
  rw [mem_cut] at hl
  obtain ⟨hl2, ha, hb⟩ := hl
  obtain ⟨⟨i, a, b⟩, s⟩ := l
  simp only at hl2 ha hb hsat
  subst hl2
  have hi := i.isLt
  simp only [show ¬ h ≤ i.val by omega, ite_false] at ha
  have hmem : b ∈ reach h start tab (i.val + 1) := by
    rw [mem_reach_succ start hi]; exact ⟨a, ha, hsat⟩
  by_cases hlast : h ≤ i.val + 1
  · simp only [hlast, ite_true, mem_erase, mem_univ, and_true, not_not] at hb
    have : i.val + 1 = h := by omega
    rw [this, hb] at hmem; exact hfin hmem
  · simp only [hlast, ite_false] at hb; exact hb hmem

end paths

section norm
variable {h q : ℕ} (start finish : Fin q)

theorem normalize (T : ℕ → Finset (Fin q)) (h0 : T 0 = {start}) (hh : T h = univ.erase finish)
    (hpos : 0 < h) : ∃ p : Par h q, cut h (seqOf start finish p) ⊆ cut h T := by
  classical
  set k := Nat.findGreatest (fun t => 1 ≤ t ∧ T t = univ) (h - 1) with hkdef
  have hk_le : k ≤ h - 1 := Nat.findGreatest_le _
  have hk_spec : k ≠ 0 → T k = univ := fun hk0 => (Nat.findGreatest_of_ne_zero hkdef.symm hk0).2
  have hk_max : ∀ t, k < t → t ≤ h - 1 → T t ≠ univ := fun t h1 h2 hu =>
    Nat.findGreatest_is_greatest h1 h2 ⟨by omega, hu⟩
  have hex : ∃ t, k < t ∧ (T t = ∅ ∨ h ≤ t) := ⟨h, by omega, Or.inr le_rfl⟩
  set e := Nat.find hex with hedef
  have he : k < e ∧ (T e = ∅ ∨ h ≤ e) := Nat.find_spec hex
  have he_min : ∀ t, t < e → ¬ (k < t ∧ (T t = ∅ ∨ h ≤ t)) := fun t ht => Nat.find_min hex ht
  have he_le : e ≤ h := Nat.find_min' hex ⟨by omega, Or.inr le_rfl⟩
  have hprop : ∀ i : Fin (e - k - 1), T (k + 1 + i.val) ≠ ∅ ∧ T (k + 1 + i.val) ≠ univ := by
    intro i
    have hi := i.isLt
    have hm := he_min (k + 1 + i.val) (by omega)
    refine ⟨fun h' => hm ⟨by omega, Or.inl h'⟩, hk_max _ (by omega) ?_⟩
    by_contra hc; exact hm ⟨by omega, Or.inr (by omega)⟩
  let p : Par h q := ⟨⟨e - k - 1, by omega⟩, ⟨k, by simp only; omega⟩,
    fun i => ⟨T (k + 1 + i.val), hprop i⟩⟩
  have pk : p.2.1.val = k := rfl
  have pj : p.1.val = e - k - 1 := rfl
  have hmid : ∀ t, k < t → t < e → seqOf start finish p t = T t := by
    intro t h1 h2
    rw [seq_mid start finish p (by rw [pk]; exact h1) (by rw [pk, pj]; omega)]
    simp only [p]; congr 1; omega

  have hbpart : ∀ i, k ≤ i → i < e → ∀ b, b ∉ seqOf start finish p (i + 1) → b ∉ T (i + 1) := by
    intro i h1 h2 b hb
    by_cases hlt : i + 1 < e
    · rwa [hmid (i + 1) (by omega) hlt] at hb
    · have hie : i + 1 = e := by omega
      by_cases heh : e < h
      · have : T e = ∅ := by rcases he.2 with h' | h'; exact h'; omega
        rw [hie, this]; simp
      · have : e = h := by omega
        rw [hie, this, hh]; rwa [hie, this, seq_top start finish p le_rfl] at hb
  refine ⟨p, fun l hl => ?_⟩
  rw [mem_cut] at hl ⊢
  obtain ⟨hl2, ha, hb⟩ := hl
  refine ⟨hl2, ?_, ?_⟩
  ·
    have hi := l.1.1.isLt
    by_cases h1 : l.1.1.val < k
    · exfalso; rw [seq_full start finish p (by omega) (by rw [pk]; omega)] at hb; exact hb (mem_univ _)
    by_cases h2 : l.1.1.val = k
    · rw [h2] at ha ⊢
      by_cases hk0 : k = 0
      · rw [hk0, seq_zero] at ha; rw [hk0, h0]; exact ha
      · rw [hk_spec hk0]; exact mem_univ _
    by_cases h3 : l.1.1.val < e
    · rwa [hmid _ (by omega) h3] at ha
    · exfalso
      rw [seq_empty start finish p (by rw [pk, pj]; omega) hi] at ha; simp at ha
  · have hi := l.1.1.isLt
    by_cases h1 : l.1.1.val < k
    · exfalso; rw [seq_full start finish p (by omega) (by rw [pk]; omega)] at hb; exact hb (mem_univ _)
    by_cases h3 : l.1.1.val < e
    · exact hbpart _ (by omega) h3 _ hb
    · exfalso
      rw [seq_empty start finish p (by rw [pk, pj]; omega) hi] at ha; simp at ha

end norm

section inj
variable {h q : ℕ} (start finish : Fin q)

theorem seq_ext_of_cut (hq : 0 < q) (p p' : Par h q)
    (hc : cut h (seqOf start finish p) = cut h (seqOf start finish p')) :
    ∀ t, seqOf start finish p t = seqOf start finish p' t := by
  have key : ∀ t, t < h → seqOf start finish p t = seqOf start finish p' t := by
    intro t; induction t with
    | zero => intro _; rw [seq_zero, seq_zero]
    | succ n ih =>
      intro hn
      have IH := ih (by omega)
      by_cases hne : (seqOf start finish p n).Nonempty
      · obtain ⟨a, ha⟩ := hne
        have ha' : a ∈ seqOf start finish p' n := IH ▸ ha
        ext b
        have e1 : ((⟨n, by omega⟩, a, b), true) ∈ cut h (seqOf start finish p) ↔
            b ∉ seqOf start finish p (n + 1) := by rw [mem_cut]; simp [ha]
        have e2 : ((⟨n, by omega⟩, a, b), true) ∈ cut h (seqOf start finish p') ↔
            b ∉ seqOf start finish p' (n + 1) := by rw [mem_cut]; simp [ha']
        rw [hc] at e1
        constructor
        · intro hb; by_contra hb'; exact (e1.1 (e2.2 hb')) hb
        · intro hb; by_contra hb'; exact (e2.1 (e1.2 hb')) hb
      · rw [not_nonempty_iff_eq_empty] at hne
        have hn1 : 1 ≤ n := by
          by_contra h0
          have : n = 0 := by omega
          rw [this, seq_zero] at hne; simp at hne
        have hp1 := (seq_eq_empty_iff start finish p hq hn1 (by omega)).1 hne
        have hp2 := (seq_eq_empty_iff start finish p' hq hn1 (by omega)).1 (IH ▸ hne)
        rw [seq_empty start finish p (by omega) hn, seq_empty start finish p' (by omega) hn]
  intro t
  by_cases ht : t < h
  · exact key t ht
  · rw [seq_top start finish p (by omega), seq_top start finish p' (by omega)]

theorem par_ext (hq : 0 < q) (p p' : Par h q)
    (hs : ∀ t, seqOf start finish p t = seqOf start finish p' t) : p = p' := by
  have A : ∀ t, 1 ≤ t → t < h → (t ≤ p.2.1.val ↔ t ≤ p'.2.1.val) := fun t h1 h2 => by
    rw [← seq_eq_univ_iff start finish p hq h1 h2, ← seq_eq_univ_iff start finish p' hq h1 h2, hs t]
  have B : ∀ t, 1 ≤ t → t < h → (p.2.1.val + p.1.val < t ↔ p'.2.1.val + p'.1.val < t) :=
    fun t h1 h2 => by
      rw [← seq_eq_empty_iff start finish p hq h1 h2, ← seq_eq_empty_iff start finish p' hq h1 h2, hs t]
  have l1 := par_lt p
  have l2 := par_lt p'
  have hk : p.2.1.val = p'.2.1.val := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := (A p'.2.1.val (by omega) (by omega)).2 le_rfl; omega
    · have := (A p.2.1.val (by omega) (by omega)).1 le_rfl; omega
  have hj : p.1.val = p'.1.val := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := (B (p'.2.1.val + p'.1.val) (by omega) (by omega)).1 (by omega); omega
    · have := (B (p.2.1.val + p.1.val) (by omega) (by omega)).2 (by omega); omega
  obtain ⟨j, k, f⟩ := p
  obtain ⟨j', k', f'⟩ := p'
  simp only at hk hj
  have hj' : j = j' := Fin.ext hj
  subst hj'
  have hk' : k = k' := Fin.ext hk
  subst hk'
  have hf : f = f' := by
    funext i
    apply Subtype.ext
    have hi := i.isLt
    have e1 := seq_mid start finish ⟨j, k, f⟩ (t := k.val + 1 + i.val) (by simp only; omega)
      (by simp only; omega)
    have e2 := seq_mid start finish ⟨j, k, f'⟩ (t := k.val + 1 + i.val) (by simp only; omega)
      (by simp only; omega)
    rw [hs] at e1
    rw [e1] at e2
    simp only at e2
    have : (⟨k.val + 1 + i.val - k.val - 1, by omega⟩ : Fin j) = i := Fin.ext (by simp only; omega)
    rw [this] at e2
    exact e2
  subst hf; rfl

theorem cut_inj (hq : 0 < q) : Function.Injective (fun p : Par h q => cut h (seqOf start finish p)) :=
  fun p p' hc => par_ext start finish hq p p' (seq_ext_of_cut start finish hq p p' hc)

theorem card_PS (hq : 0 < q) : Fintype.card (PS q) = 2 ^ q - 2 := by
  rw [Fintype.card_subtype]
  have : (univ.filter (fun S : Finset (Fin q) => S ≠ ∅ ∧ S ≠ univ)) = univ \ {∅, univ} := by
    ext S; simp [not_or]
  rw [this, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_finset, Fintype.card_fin,
    card_pair (univ_ne_empty hq).symm]

theorem card_Par (hq : 0 < q) :
    Fintype.card (Par h q) = ∑ j ∈ Finset.range h, (h - j) * (2 ^ q - 2) ^ j := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, card_PS hq]
  exact Fin.sum_univ_eq_sum_range (fun j => (h - j) * (2 ^ q - 2) ^ j) h

end inj

section minimal
variable {h q : ℕ} (start finish : Fin q)

theorem path_through (hq : 0 < q) (p : Par h q) (e : Fin h × (Fin q × Fin q))
    (he : (e, true) ∈ cut h (seqOf start finish p)) :
    pathN h start finish (fun e' => decide (e' = e ∨ (e', true) ∉ cut h (seqOf start finish p))) := by
  classical
  set S := seqOf start finish p with hS
  obtain ⟨i, a, b⟩ := e
  rw [mem_cut] at he
  obtain ⟨-, ha, hb⟩ := he
  simp only at ha hb
  have hi := i.isLt
  have l1 := par_lt p
  have hN : ∀ t, t ≤ i.val → (S t).Nonempty := by
    intro t ht
    by_cases t0 : t = 0
    · rw [t0, hS, seq_zero]; exact singleton_nonempty _
    · rw [nonempty_iff_ne_empty]; intro hE
      have h1 := (seq_eq_empty_iff start finish p hq (by omega) (by omega)).1 hE
      have : S i.val = ∅ := seq_empty start finish p (by omega) hi
      rw [this] at ha; simp at ha
  have hU : ∀ t, i.val + 1 ≤ t → t < h → S t ≠ univ := by
    intro t h1 h2 hu
    have := (seq_eq_univ_iff start finish p hq (by omega) h2).1 hu
    have : S (i.val + 1) = univ := seq_full start finish p (by omega) (by omega)
    rw [this] at hb; exact hb (mem_univ _)
  let x : ℕ → Fin q := fun t =>
    if t ≤ i.val then (if t = i.val then a else if ht : (S t).Nonempty then ht.choose else start)
    else (if t = i.val + 1 then b else if h ≤ t then finish else
      if ht : (univ \ S t).Nonempty then ht.choose else start)
  have xin : ∀ t, t ≤ i.val → x t ∈ S t := by
    intro t ht
    by_cases h' : t = i.val
    · subst h'; simp only [x, le_refl, ite_true]; exact ha
    · simp only [x, ht, ite_true, h', ite_false, hN t ht, dite_true]; exact (hN t ht).choose_spec
  have xout : ∀ t, i.val < t → t < h → x t ∉ S t := by
    intro t h1 h2
    by_cases h' : t = i.val + 1
    · subst h'; simp only [x, show ¬ i.val + 1 ≤ i.val by omega, ite_false, ite_true]; exact hb
    · have hne : (univ \ S t).Nonempty := by
        rw [sdiff_nonempty]; intro hsub; exact hU t (by omega) h2 (univ_subset_iff.mp hsub)
      simp only [x, show ¬ t ≤ i.val by omega, ite_false, h', show ¬ h ≤ t by omega, hne, dite_true]
      have := hne.choose_spec; rw [mem_sdiff] at this; exact this.2
  refine ⟨x, ?_, ?_, ?_⟩
  · have := xin 0 (Nat.zero_le _); rw [hS, seq_zero, mem_singleton] at this; exact this
  · by_cases hh : i.val + 1 = h
    · have hb' := hb
      rw [hh, hS, seq_top start finish p le_rfl] at hb'
      simp only [mem_erase, mem_univ, and_true, not_not] at hb'
      have hx1 : x (i.val + 1) = b := by
        simp only [x, show ¬ i.val + 1 ≤ i.val by omega, ite_false, ite_true]
      rw [← hh, hx1]; exact hb'
    · simp only [x, show ¬ h ≤ i.val by omega, ite_false, show h ≠ i.val + 1 by omega, le_refl, ite_true]
  · intro t
    have ht := t.isLt
    simp only [decide_eq_true_eq]
    by_cases h1 : t.val = i.val
    · left
      have e1 : x t.val = a := by simp [x, h1]
      have e2 : x (t.val + 1) = b := by simp [x, h1]
      rw [e1, e2]; exact Prod.ext (Fin.ext h1) rfl
    · right
      rw [mem_cut]; simp only [not_and, true_implies]
      intro hxt
      by_cases h2 : t.val < i.val
      · exact not_not.mpr (xin (t.val + 1) (by omega))
      · exact absurd hxt (xout t.val (by omega) ht)

theorem forced (hq : 0 < q) (p : Par h q) (G : Finset (Clause (Fin h × (Fin q × Fin q))))
    (hG : ∀ tab, pathN h start finish tab ↔ Satisfies tab (↑G : Set _)) :
    ∃ B ∈ G, B.filter (fun l => l.2 = true) = cut h (seqOf start finish p) := by
  classical
  set C := cut h (seqOf start finish p) with hC
  let tab0 : Fin h × (Fin q × Fin q) → Bool := fun e => decide ((e, true) ∉ C)
  have hnp : ¬ pathN h start finish tab0 := by
    intro hp
    obtain ⟨l, hl, hsat⟩ := sat_of_path start finish (S := seqOf start finish p)
      (by rw [seq_zero]; simp) (by rw [seq_top start finish p le_rfl]; simp) hp
    have hl2 := (mem_cut.1 hl).1
    obtain ⟨e, s⟩ := l; simp only at hl2; subst hl2
    simp only [tab0, decide_eq_true_eq] at hsat
    exact hsat hl
  have hns : ¬ Satisfies tab0 (↑G : Set _) := fun hs => hnp ((hG tab0).2 hs)
  simp only [Satisfies, not_forall] at hns
  obtain ⟨B, hBG, hB⟩ := hns
  refine ⟨B, hBG, ?_⟩
  have hB' : ∀ l ∈ B, tab0 l.1 ≠ l.2 := fun l hl heq => hB ⟨l, hl, heq⟩
  ext l
  simp only [mem_filter]
  constructor
  · rintro ⟨hlB, hl2⟩
    obtain ⟨e, s⟩ := l; simp only at hl2; subst hl2
    have := hB' _ hlB
    simp only [tab0, ne_eq, decide_eq_true_eq, not_not] at this
    exact this
  · intro hlC
    have hl2 := (mem_cut.1 hlC).1
    obtain ⟨e, s⟩ := l; simp only at hl2; subst hl2
    refine ⟨?_, rfl⟩
    by_contra hnot
    have hp := path_through start finish hq p e hlC
    have hs := (hG _).1 hp
    obtain ⟨l', hl'B, hsat'⟩ := hs B hBG
    have h0 := hB' l' hl'B
    obtain ⟨e', s'⟩ := l'
    cases s'
    · simp only [tab0, ne_eq, decide_eq_false_iff_not, not_not] at h0
      simp only [decide_eq_false_iff_not, not_or, not_not] at hsat'
      exact h0 hsat'.2
    · simp only [tab0, ne_eq, decide_eq_true_eq, not_not] at h0
      simp only [decide_eq_true_eq] at hsat'
      rcases hsat' with h1 | h1
      · subst h1; exact hnot hl'B
      · exact h1 h0

end minimal

theorem sum_identity (h : ℕ) : ∑ j ∈ Finset.range h, (h - j) * 2 ^ j + h + 2 = 2 ^ (h + 1) := by
  have geo : ∀ n : ℕ, ∑ j ∈ Finset.range n, 2 ^ j + 1 = 2 ^ n := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega
  induction h with
  | zero => simp
  | succ n ih =>
    have e1 : ∑ j ∈ Finset.range n, (n + 1 - j) * 2 ^ j =
        ∑ j ∈ Finset.range n, (n - j) * 2 ^ j + ∑ j ∈ Finset.range n, 2 ^ j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show n + 1 - j = (n - j) + 1 by omega, add_mul, one_mul]
    rw [Finset.sum_range_succ, e1, show n + 1 - n = 1 by omega, one_mul]
    have g := geo n
    set P := 2 ^ n
    rw [show 2 ^ (n + 1 + 1) = 4 * P by rw [pow_succ, pow_succ]; ring]
    rw [show 2 ^ (n + 1) = 2 * P by rw [pow_succ]; ring] at ih
    omega

theorem card_cut_eq {h q : ℕ} (S : ℕ → Finset (Fin q)) :
    (cut h S).card = ∑ i ∈ Finset.range h, (S i).card * (univ \ S (i + 1)).card := by
  classical
  rw [cut, card_image_of_injective _ (fun e e' heq => (Prod.mk.inj heq).1), card_filter,
    Fintype.sum_prod_type]
  have : ∀ i : Fin h, (∑ ab : Fin q × Fin q, if ab.1 ∈ S i.val ∧ ab.2 ∉ S (i.val + 1) then 1 else 0)
      = (S i.val).card * (univ \ S (i.val + 1)).card := by
    intro i
    rw [← card_product, ← card_filter]
    congr 1; ext ab; simp [mem_product]
  simp only [this]
  exact Fin.sum_univ_eq_sum_range (fun i => (S i).card * (univ \ S (i + 1)).card) h

theorem card_cut_q2 {h : ℕ} (start finish : Fin 2) (p : Par h 2) :
    (cut h (seqOf start finish p)).card ≤ max 4 h := by
  classical
  rw [card_cut_eq]
  set S := seqOf start finish p with hS
  have hq : 0 < 2 := by norm_num
  have l1 := par_lt p
  have hle : ∀ T : Finset (Fin 2), T.card ≤ 2 := fun T => by
    simpa using card_le_univ T
  have hcomp : ∀ T : Finset (Fin 2), (univ \ T).card = 2 - T.card := fun T => by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  have h2 : ∀ T : Finset (Fin 2), T.card = 2 → T = univ := fun T hT =>
    (card_eq_iff_eq_univ T).1 (by simpa using hT)
  have h0 : ∀ T : Finset (Fin 2), T.card = 0 → T = ∅ := fun T hT => card_eq_zero.1 hT
  have w0 : (S 0).card = 1 := by rw [hS, seq_zero]; simp
  have wh : ∀ t, h ≤ t → (S t).card = 1 := fun t ht => by
    rw [hS, seq_top start finish p ht, card_erase_of_mem (mem_univ _)]; simp
  by_cases hj : p.1.val = 0
  · have hsum : ∑ i ∈ Finset.range h, (S i).card * (univ \ S (i + 1)).card =
        (S p.2.1.val).card * (univ \ S (p.2.1.val + 1)).card := by
      apply Finset.sum_eq_single
      · intro i hi hik
        rw [Finset.mem_range] at hi
        rcases Nat.lt_or_gt_of_ne hik with hlt | hlt
        · rw [hS, seq_full start finish p (t := i + 1) (by omega) (by omega)]; simp
        · rw [hS, seq_empty start finish p (t := i) (by omega) hi]; simp
      · intro hk; exact absurd (Finset.mem_range.2 (by omega)) hk
    rw [hsum]
    have := Nat.mul_le_mul (hle (S p.2.1.val)) (hle (univ \ S (p.2.1.val + 1)))
    omega
  · have step : ∀ i ∈ Finset.range h,
        (S i).card * (univ \ S (i + 1)).card + (S (i + 1)).card ≤ 1 + (S i).card := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [hcomp]
      have a1 := hle (S i)
      have a2 := hle (S (i + 1))
      have ex1 : ¬ ((S i).card = 0 ∧ (S (i + 1)).card = 2) := by
        rintro ⟨e1, e2⟩
        have E1 := h0 _ e1
        have E2 := h2 _ e2
        have hi1 : 1 ≤ i := by
          by_contra hc; have : i = 0 := by omega
          rw [this, w0] at e1; omega
        have := (seq_eq_empty_iff start finish p hq hi1 hi).1 E1
        by_cases hlast : i + 1 < h
        · have := (seq_eq_univ_iff start finish p hq (by omega) hlast).1 E2; omega
        · rw [wh (i + 1) (by omega)] at e2; omega
      have ex2 : ¬ ((S i).card = 2 ∧ (S (i + 1)).card = 0) := by
        rintro ⟨e1, e2⟩
        have E1 := h2 _ e1
        have E2 := h0 _ e2
        have hi1 : 1 ≤ i := by
          by_contra hc; have : i = 0 := by omega
          rw [this, w0] at e1; omega
        have := (seq_eq_univ_iff start finish p hq hi1 hi).1 E1
        by_cases hlast : i + 1 < h
        · have := (seq_eq_empty_iff start finish p hq (by omega) hlast).1 E2; omega
        · rw [wh (i + 1) (by omega)] at e2; omega
      generalize (S i).card = w at a1 ex1 ex2 ⊢
      generalize (S (i + 1)).card = w' at a2 ex1 ex2 ⊢
      interval_cases w <;> interval_cases w' <;> simp_all
    have hsum := Finset.sum_le_sum step
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, mul_one] at hsum
    have tele : ∑ i ∈ Finset.range h, (S (i + 1)).card + (S 0).card =
        ∑ i ∈ Finset.range h, (S i).card + (S h).card := by
      exact (Finset.sum_range_succ' (fun i => (S i).card) h).symm.trans
        (Finset.sum_range_succ (fun i => (S i).card) h)
    rw [w0, wh h le_rfl] at tele
    omega

end PEqualNP.Outside.L_lib_472_aux

theorem PEqualNP.Outside.L_lib_472 : (∀ (h q : ℕ), 0 < h → 0 < q → ∀ start finish : Fin q,
  let Edge := Fin h × (Fin q × Fin q)
  let path := fun tab : Edge → Bool =>
    ∃ x : Fin (h + 1) → Fin q, x 0 = start ∧ x (Fin.last h) = finish ∧
      ∀ i : Fin h, tab (i, x i.castSucc, x i.succ) = true
  let enc := fun F : Finset (PEqualNP.ProofComplexity.Clause Edge) =>
    ∀ tab : Edge → Bool, path tab ↔
      PEqualNP.ProofComplexity.Satisfies tab (↑F : Set _)
  let count := ∑ j ∈ Finset.range h, (h - j) * (2 ^ q - 2) ^ j
  ∃ F : Finset (PEqualNP.ProofComplexity.Clause Edge), enc F ∧ F.card = count ∧
    (∀ C ∈ F, ∀ l ∈ C, l.2 = true) ∧
    (q = 2 → F.card + h + 2 = 2 ^ (h + 1) ∧ ∀ C ∈ F, C.card ≤ max 4 h) ∧
    ∀ G : Finset (PEqualNP.ProofComplexity.Clause Edge), enc G →
      F.card ≤ G.card ∧ ∀ C ∈ F, ∃ B ∈ G, B.filter (fun l => l.2 = true) = C) := by
  intro h q hh hq start finish
  dsimp only
  have hcard := Finset.card_image_of_injective (Finset.univ : Finset (L_lib_472_aux.Par h q))
    (L_lib_472_aux.cut_inj start finish hq)
  refine ⟨Finset.univ.image (fun p : L_lib_472_aux.Par h q =>
    L_lib_472_aux.cut h (L_lib_472_aux.seqOf start finish p)), ?_, ?_, ?_, ?_, ?_⟩
  · intro tab
    rw [L_lib_472_aux.path_iff]
    constructor
    · intro hp C hC
      rw [Finset.mem_coe, Finset.mem_image] at hC
      obtain ⟨p, -, rfl⟩ := hC
      exact L_lib_472_aux.sat_of_path start finish
        (by rw [L_lib_472_aux.seq_zero]; exact Finset.mem_singleton_self _)
        (by rw [L_lib_472_aux.seq_top start finish p le_rfl]; simp) hp
    · intro hs
      by_contra hnp
      obtain ⟨p, hsub⟩ := L_lib_472_aux.normalize start finish
        (fun t => if h ≤ t then Finset.univ.erase finish else L_lib_472_aux.reach h start tab t)
        (by simp [L_lib_472_aux.reach, show ¬ h ≤ 0 by omega]) (by simp) hh
      apply L_lib_472_aux.reach_cut_false start finish tab hnp
      obtain ⟨l, hl, hsat⟩ := hs _ (by
        rw [Finset.mem_coe]; exact Finset.mem_image_of_mem _ (Finset.mem_univ p))
      exact ⟨l, hsub hl, hsat⟩
  · rw [hcard, Finset.card_univ, L_lib_472_aux.card_Par hq]
  · intro C hC l hl
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hC
    exact (L_lib_472_aux.mem_cut.1 hl).1
  · intro hq2
    subst hq2
    refine ⟨?_, ?_⟩
    · rw [hcard, Finset.card_univ, L_lib_472_aux.card_Par hq]
      simpa using L_lib_472_aux.sum_identity h
    · intro C hC
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hC
      exact L_lib_472_aux.card_cut_q2 start finish p
  · intro G hG
    have hG' : ∀ tab, L_lib_472_aux.pathN h start finish tab ↔
        PEqualNP.ProofComplexity.Satisfies tab (↑G : Set _) := fun tab =>
      (L_lib_472_aux.path_iff start finish tab).symm.trans (hG tab)
    refine ⟨?_, ?_⟩
    · have hsub : Finset.univ.image (fun p : L_lib_472_aux.Par h q =>
          L_lib_472_aux.cut h (L_lib_472_aux.seqOf start finish p)) ⊆
          G.image (fun B => B.filter (fun l => l.2 = true)) := by
        intro C hC
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hC
        obtain ⟨B, hB, hBe⟩ := L_lib_472_aux.forced start finish hq p G hG'
        exact Finset.mem_image.2 ⟨B, hB, hBe⟩
      exact (Finset.card_le_card hsub).trans Finset.card_image_le
    · intro C hC
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hC
      exact L_lib_472_aux.forced start finish hq p G hG'
