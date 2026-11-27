import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_581_aux

private def segFlip {m : ℕ} (f : Fin m → Bool) (l r : ℕ) : Bool :=
  decide (Odd ((Finset.univ.filter (fun i : Fin m => l ≤ i.val ∧ i.val < r ∧ f i = true)).card))

private lemma odd_add_decide (a b : ℕ) :
    decide (Odd (a + b)) = (decide (Odd a) ^^ decide (Odd b)) := by
  by_cases ha : Odd a <;> by_cases hb : Odd b
  · have hab : ¬ Odd (a + b) := by
      rcases ha with ⟨k, rfl⟩; rcases hb with ⟨j, rfl⟩
      rw [Nat.not_odd_iff_even]; exact ⟨k + j + 1, by omega⟩
    simp [ha, hb, hab]
  · have hab : Odd (a + b) := by
      rcases ha with ⟨k, rfl⟩
      rw [Nat.not_odd_iff_even] at hb; rcases hb with ⟨j, rfl⟩
      exact ⟨k + j, by omega⟩
    simp [ha, hb, hab]
  · have hab : Odd (a + b) := by
      rw [Nat.not_odd_iff_even] at ha; rcases ha with ⟨k, rfl⟩
      rcases hb with ⟨j, rfl⟩
      exact ⟨k + j, by omega⟩
    simp [ha, hb, hab]
  · have hab : ¬ Odd (a + b) := by
      rw [Nat.not_odd_iff_even] at ha hb
      rcases ha with ⟨k, rfl⟩; rcases hb with ⟨j, rfl⟩
      rw [Nat.not_odd_iff_even]; exact ⟨k + j, by omega⟩
    simp [ha, hb, hab]

private lemma segFlip_full {m : ℕ} (f : Fin m → Bool) :
    segFlip f 0 m = decide (Odd ((Finset.univ.filter (fun i : Fin m => f i = true)).card)) := by
  unfold segFlip
  have hset :
      (Finset.univ.filter (fun i : Fin m => 0 ≤ i.val ∧ i.val < m ∧ f i = true)) =
        (Finset.univ.filter (fun i : Fin m => f i = true)) := by
    ext i
    simp [i.isLt]
  rw [hset]

private lemma segFlip_single {m : ℕ} (f : Fin m → Bool) (l : ℕ) (hl : l < m) :
    segFlip f l (l + 1) = f ⟨l, hl⟩ := by
  unfold segFlip
  cases hfl : f ⟨l, hl⟩
  · have hempty :
        (Finset.univ.filter (fun i : Fin m => l ≤ i.val ∧ i.val < l + 1 ∧ f i = true)) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2, h3⟩
      have hi : i = ⟨l, hl⟩ := Fin.ext (by dsimp; omega)
      rw [hi, hfl] at h3
      cases h3
    rw [hempty, Finset.card_empty]
    decide
  · have hsing :
        (Finset.univ.filter (fun i : Fin m => l ≤ i.val ∧ i.val < l + 1 ∧ f i = true)) =
          {⟨l, hl⟩} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact Fin.ext (by dsimp; omega)
      · rintro rfl
        exact ⟨le_rfl, Nat.lt_succ_self l, hfl⟩
    rw [hsing, Finset.card_singleton]
    decide

private lemma segFlip_split {m : ℕ} (f : Fin m → Bool) (l k r : ℕ)
    (hlk : l ≤ k) (hkr : k ≤ r) :
    segFlip f l r = (segFlip f l k ^^ segFlip f k r) := by
  unfold segFlip
  have hunion :
      (Finset.univ.filter (fun i : Fin m => l ≤ i.val ∧ i.val < r ∧ f i = true)) =
        (Finset.univ.filter (fun i : Fin m => l ≤ i.val ∧ i.val < k ∧ f i = true)) ∪
        (Finset.univ.filter (fun i : Fin m => k ≤ i.val ∧ i.val < r ∧ f i = true)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hk : i.val < k
      · left; exact ⟨h1, hk, h3⟩
      · right; exact ⟨by omega, h2, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, by omega, h3⟩
      · exact ⟨by omega, h2, h3⟩
  have hdisj : Disjoint
      (Finset.univ.filter (fun i : Fin m => l ≤ i.val ∧ i.val < k ∧ f i = true))
      (Finset.univ.filter (fun i : Fin m => k ≤ i.val ∧ i.val < r ∧ f i = true)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisj, odd_add_decide]

private def cellMatches {m : ℕ} (x : Fin (m + 1) → Bool)
    (C : Finset (Fin (m + 1) × Bool)) : Prop :=
  C.filter (fun p => x p.1 ≠ p.2) = ∅

private lemma cellMatches_iff {m : ℕ} (x : Fin (m + 1) → Bool)
    (C : Finset (Fin (m + 1) × Bool)) :
    cellMatches x C ↔ ∀ p ∈ C, x p.1 = p.2 := by
  unfold cellMatches
  constructor
  · intro h p hp
    by_contra hne
    have hmem : p ∈ C.filter (fun q => x q.1 ≠ q.2) :=
      Finset.mem_filter.mpr ⟨hp, hne⟩
    rw [h] at hmem
    exact Finset.notMem_empty p hmem
  · intro h
    ext p
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_not]
    exact fun hp => h p hp

private lemma load_eq_sum {m : ℕ} (L : Finset (Finset (Fin (m + 1) × Bool)))
    (x : Fin (m + 1) → Bool) :
    (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card =
      (L.filter (fun C => ∀ p ∈ C, x p.1 = p.2)).card := by
  congr 1
  ext C
  simp only [Finset.mem_filter, ← cellMatches_iff]
  rfl

private lemma bool_xor_assoc_not (a p1 p2 : Bool) :
    (!(a ^^ (p1 ^^ p2))) = !((a ^^ p1) ^^ p2) := by
  cases a <;> cases p1 <;> cases p2 <;> decide

private lemma load_combine_aux :
    ∀ xl xm xr a bm be : Bool,
      (if xr = be then (if xl = a ∧ xm = !bm then 1 else 0) else 0) +
      (if xl = a then (if xm = bm ∧ xr = be then 1 else 0) else 0) =
      if xl = a ∧ xr = be then 1 else 0 := by
  decide

private lemma build_base {m : ℕ} (f : Fin m → Bool)
    (d l r : ℕ) (hlr : l < r) (hrm : r ≤ m) (hlen : r - l = 1)
    (hd : d = 0 ∨ d = 1) (a : Bool) :
    let pl : Fin (m + 1) := ⟨l, by omega⟩
    let pr : Fin (m + 1) := ⟨r, by omega⟩
    let b_end : Bool := !(a ^^ segFlip f l r)
    ∃ L : Finset (Finset (Fin (m + 1) × Bool)),
      L.card = r - l ∧
      (∀ C ∈ L,
        (∀ p ∈ C, l ≤ p.1.val ∧ p.1.val ≤ r) ∧
        (∀ i : Fin (m + 1), ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
        (pl, a) ∈ C ∧ (pr, b_end) ∈ C ∧
        (∃ (i : Fin m) (b : Bool), (i.castSucc, b) ∈ C ∧ (i.succ, !(b ^^ f i)) ∈ C) ∧
        (C.card = d + 1 ∨ C.card = d + 2)) ∧
      (L.filter (fun C => C.card = d + 1)).card = 2 ^ d - (r - l) ∧
      (L.filter (fun C => C.card = d + 2)).card = 2 * (r - l) - 2 ^ d ∧
      ∀ x : Fin (m + 1) → Bool,
        (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card =
          if x pl = a ∧ x pr = b_end then 1 else 0 := by
  have hr_eq : r = l + 1 := by omega
  subst hr_eq
  intro pl pr b_end
  let C0 : Finset (Fin (m + 1) × Bool) := {(pl, a), (pr, b_end)}
  have hne_pt : (pl, a) ≠ (pr, b_end) := by
    intro h
    have hv := congrArg (fun p : Fin (m + 1) × Bool => p.1.val) h
    change l = l + 1 at hv
    omega
  have hC0_card : C0.card = 2 := Finset.card_pair hne_pt
  have hC0_mem1 : (pl, a) ∈ C0 := Finset.mem_insert_self _ _
  have hC0_mem2 : (pr, b_end) ∈ C0 := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hC0_iff : ∀ p : Fin (m + 1) × Bool, p ∈ C0 ↔ p = (pl, a) ∨ p = (pr, b_end) := by
    intro p
    exact Finset.mem_insert.trans (or_congr_right Finset.mem_singleton)
  refine ⟨{C0}, by simp [hlen], ?_, ?_, ?_, ?_⟩
  · intro C hC
    rw [Finset.mem_singleton] at hC
    subst hC
    refine ⟨?_, ?_, hC0_mem1, hC0_mem2, ?_, ?_⟩
    · intro p hp
      rcases (hC0_iff p).mp hp with rfl | rfl
      · exact ⟨by dsimp [pl]; omega, by dsimp [pl]; omega⟩
      · exact ⟨by dsimp [pr]; omega, by dsimp [pr]; omega⟩
    · intro i ⟨hf, ht⟩
      rcases (hC0_iff (i, false)).mp hf with h1 | h1 <;>
      rcases (hC0_iff (i, true)).mp ht with h2 | h2
      · rw [Prod.mk.injEq] at h1 h2; exact Bool.noConfusion (h1.2.trans h2.2.symm)
      · rw [Prod.mk.injEq] at h1 h2
        have hv := congrArg Fin.val (h1.1.symm.trans h2.1); change l = l + 1 at hv; omega
      · rw [Prod.mk.injEq] at h1 h2
        have hv := congrArg Fin.val (h1.1.symm.trans h2.1); change l + 1 = l at hv; omega
      · rw [Prod.mk.injEq] at h1 h2; exact Bool.noConfusion (h1.2.trans h2.2.symm)
    · refine ⟨⟨l, by omega⟩, a, ?_, ?_⟩
      · have h1 : (⟨l, by omega⟩ : Fin m).castSucc = pl := Fin.ext rfl
        rw [h1]; exact hC0_mem1
      · have h2 : (⟨l, by omega⟩ : Fin m).succ = pr := Fin.ext rfl
        have hf : segFlip f l (l + 1) = f ⟨l, by omega⟩ := segFlip_single f l (by omega)
        rw [h2, ← hf]; exact hC0_mem2
    · rcases hd with rfl | rfl
      · right; exact hC0_card
      · left; exact hC0_card
  · rcases hd with rfl | rfl
    · have hflt : ({C0} : Finset (Finset (Fin (m + 1) × Bool))).filter (fun C => C.card = 1) = ∅ := by
        ext C
        simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        rintro rfl; omega
      rw [show (0 + 1 : ℕ) = 1 from rfl, hflt, Finset.card_empty, hlen]
      decide
    · have hflt : ({C0} : Finset (Finset (Fin (m + 1) × Bool))).filter (fun C => C.card = 2) = {C0} := by
        ext C
        simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
        rintro rfl; exact hC0_card
      rw [show (1 + 1 : ℕ) = 2 from rfl, hflt, Finset.card_singleton, hlen]
      decide
  · rcases hd with rfl | rfl
    · have hflt : ({C0} : Finset (Finset (Fin (m + 1) × Bool))).filter (fun C => C.card = 2) = {C0} := by
        ext C
        simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
        rintro rfl; exact hC0_card
      rw [show (0 + 2 : ℕ) = 2 from rfl, hflt, Finset.card_singleton, hlen]
      decide
    · have hflt : ({C0} : Finset (Finset (Fin (m + 1) × Bool))).filter (fun C => C.card = 3) = ∅ := by
        ext C
        simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        rintro rfl; omega
      rw [show (1 + 2 : ℕ) = 3 from rfl, hflt, Finset.card_empty, hlen]
      decide
  · intro x
    rw [load_eq_sum]
    by_cases hx : x pl = a ∧ x pr = b_end
    · have hflt :
          ({C0} : Finset (Finset (Fin (m + 1) × Bool))).filter (fun C => ∀ p ∈ C, x p.1 = p.2) =
            {C0} := by
        ext C
        simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
        rintro rfl p hp
        rcases (hC0_iff p).mp hp with rfl | rfl
        · exact hx.1
        · exact hx.2
      rw [hflt, Finset.card_singleton, if_pos hx]
    · have hflt :
          ({C0} : Finset (Finset (Fin (m + 1) × Bool))).filter (fun C => ∀ p ∈ C, x p.1 = p.2) =
            ∅ := by
        ext C
        simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        rintro rfl hall
        exact hx ⟨hall (pl, a) hC0_mem1, hall (pr, b_end) hC0_mem2⟩
      rw [hflt, Finset.card_empty, if_neg hx]

private lemma build_sub {m : ℕ} (f : Fin m → Bool) :
    ∀ (d : ℕ) (l r : ℕ) (hlr : l < r) (hrm : r ≤ m)
      (hupper : r - l ≤ 2 ^ d) (hlower : 2 ^ d ≤ 2 * (r - l)) (a : Bool),
    let pl : Fin (m + 1) := ⟨l, by omega⟩
    let pr : Fin (m + 1) := ⟨r, by omega⟩
    let b_end : Bool := !(a ^^ segFlip f l r)
    ∃ L : Finset (Finset (Fin (m + 1) × Bool)),
      L.card = r - l ∧
      (∀ C ∈ L,
        (∀ p ∈ C, l ≤ p.1.val ∧ p.1.val ≤ r) ∧
        (∀ i : Fin (m + 1), ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
        (pl, a) ∈ C ∧ (pr, b_end) ∈ C ∧
        (∃ (i : Fin m) (b : Bool), (i.castSucc, b) ∈ C ∧ (i.succ, !(b ^^ f i)) ∈ C) ∧
        (C.card = d + 1 ∨ C.card = d + 2)) ∧
      (L.filter (fun C => C.card = d + 1)).card = 2 ^ d - (r - l) ∧
      (L.filter (fun C => C.card = d + 2)).card = 2 * (r - l) - 2 ^ d ∧
      ∀ x : Fin (m + 1) → Bool,
        (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card =
          if x pl = a ∧ x pr = b_end then 1 else 0 := by
  intro d
  induction d with
  | zero =>
    intro l r hlr hrm hupper hlower a
    have hlen : r - l = 1 := by simp at hupper; omega
    exact build_base f 0 l r hlr hrm hlen (Or.inl rfl) a
  | succ d ih =>
    intro l r hlr hrm hupper hlower a
    by_cases hlen1 : r - l = 1
    · have hd0 : d = 0 := by
        have hpow : 2 ^ (d + 1) ≤ 2 := by omega
        by_contra hne
        have h1 : 1 ≤ d := Nat.pos_of_ne_zero hne
        have h2 : 4 ≤ 2 ^ (d + 1) := by
          calc
            4 = 2 ^ 2 := by decide
            _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      subst hd0
      exact build_base f 1 l r hlr hrm hlen1 (Or.inr rfl) a
    · intro pl pr b_end
      have hlen2 : 2 ≤ r - l := by omega
      let mid : ℕ := l + (r - l) / 2
      have hlm : l < mid := by omega
      have hmr : mid < r := by omega
      have hpow_succ : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
      have hupper1 : mid - l ≤ 2 ^ d := by omega
      have hupper2 : r - mid ≤ 2 ^ d := by omega
      have hlower1 : 2 ^ d ≤ 2 * (mid - l) := by
        cases d with
        | zero => simp; omega
        | succ d' =>
          have hpow2 : 2 ^ (d' + 1) = 2 * 2 ^ d' := by ring
          omega
      have hlower2 : 2 ^ d ≤ 2 * (r - mid) := by omega
      let pmid : Fin (m + 1) := ⟨mid, by omega⟩
      let b_mid : Bool := a ^^ segFlip f l mid
      have hflip_split : segFlip f l r = (segFlip f l mid ^^ segFlip f mid r) :=
        segFlip_split f l mid r (by omega) (by omega)
      have hb_end_eq : b_end = !(b_mid ^^ segFlip f mid r) := by
        dsimp only [b_end, b_mid]
        rw [hflip_split, bool_xor_assoc_not]
      obtain ⟨L1, hL1_card, hL1_prop, hL1_lo, hL1_hi, hL1_load⟩ :=
        ih l mid hlm (by omega) hupper1 hlower1 a
      obtain ⟨L2, hL2_card, hL2_prop, hL2_lo, hL2_hi, hL2_load⟩ :=
        ih mid r hmr hrm hupper2 hlower2 b_mid
      let insR : Finset (Fin (m + 1) × Bool) → Finset (Fin (m + 1) × Bool) :=
        fun C => insert (pr, b_end) C
      let insL : Finset (Fin (m + 1) × Bool) → Finset (Fin (m + 1) × Bool) :=
        fun C => insert (pl, a) C
      let L1' : Finset (Finset (Fin (m + 1) × Bool)) := L1.image insR
      let L2' : Finset (Finset (Fin (m + 1) × Bool)) := L2.image insL
      have hnotmemR : ∀ C ∈ L1, (pr, b_end) ∉ C := by
        intro C hC hmem
        have hbnd := (hL1_prop C hC).1 (pr, b_end) hmem
        dsimp only [pr] at hbnd
        omega
      have hnotmemL : ∀ C ∈ L2, (pl, a) ∉ C := by
        intro C hC hmem
        have hbnd := (hL2_prop C hC).1 (pl, a) hmem
        dsimp only [pl] at hbnd
        omega
      have hinj1 : Set.InjOn insR (↑L1 : Set (Finset (Fin (m + 1) × Bool))) := by
        intro C1 hC1 C2 hC2 heq
        have h1 : (pr, b_end) ∉ C1 := hnotmemR C1 hC1
        have h2 : (pr, b_end) ∉ C2 := hnotmemR C2 hC2
        have herase := congrArg (fun S : Finset (Fin (m + 1) × Bool) => S.erase (pr, b_end)) heq
        simpa [insR, Finset.erase_insert h1, Finset.erase_insert h2] using herase
      have hinj2 : Set.InjOn insL (↑L2 : Set (Finset (Fin (m + 1) × Bool))) := by
        intro C1 hC1 C2 hC2 heq
        have h1 : (pl, a) ∉ C1 := hnotmemL C1 hC1
        have h2 : (pl, a) ∉ C2 := hnotmemL C2 hC2
        have herase := congrArg (fun S : Finset (Fin (m + 1) × Bool) => S.erase (pl, a)) heq
        simpa [insL, Finset.erase_insert h1, Finset.erase_insert h2] using herase
      have hcardR : ∀ C ∈ L1, (insR C).card = C.card + 1 :=
        fun C hC => Finset.card_insert_of_notMem (hnotmemR C hC)
      have hcardL : ∀ C ∈ L2, (insL C).card = C.card + 1 :=
        fun C hC => Finset.card_insert_of_notMem (hnotmemL C hC)
      have hdisj : Disjoint L1' L2' := by
        rw [Finset.disjoint_left]
        intro C hC1 hC2
        rcases Finset.mem_image.mp hC1 with ⟨C1, h1, rfl⟩
        rcases Finset.mem_image.mp hC2 with ⟨C2, h2, heq⟩
        have hmem2 : (pmid, b_mid) ∈ insR C1 := by
          rw [← heq]
          exact Finset.mem_insert_of_mem (hL2_prop C2 h2).2.2.1
        have hmem2' : (pmid, b_mid) ∈ C1 := by
          rcases Finset.mem_insert.mp hmem2 with hpr | hC1'
          · have hv := congrArg (fun p : Fin (m + 1) × Bool => p.1.val) hpr
            change mid = r at hv; omega
          · exact hC1'
        have hmem1' : (pmid, !b_mid) ∈ C1 := (hL1_prop C1 h1).2.2.2.1
        cases hb : b_mid
        · rw [hb] at hmem1' hmem2'
          exact (hL1_prop C1 h1).2.1 pmid ⟨hmem2', hmem1'⟩
        · rw [hb] at hmem1' hmem2'
          exact (hL1_prop C1 h1).2.1 pmid ⟨hmem1', hmem2'⟩
      refine ⟨L1' ∪ L2', ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj1,
          Finset.card_image_of_injOn hinj2, hL1_card, hL2_card]
        omega
      · intro C hC
        rcases Finset.mem_union.mp hC with hC1 | hC2
        · rcases Finset.mem_image.mp hC1 with ⟨C1, h1, rfl⟩
          obtain ⟨hbnd, hcons, hpl, hpmid, hedge, hcard⟩ := hL1_prop C1 h1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro p hp
            rcases Finset.mem_insert.mp hp with rfl | hp1
            · exact ⟨by dsimp [pr]; omega, by dsimp [pr]; omega⟩
            · have := hbnd p hp1; exact ⟨this.1, by omega⟩
          · intro i ⟨hf, ht⟩
            rcases Finset.mem_insert.mp hf with hf_eq | hf1 <;>
            rcases Finset.mem_insert.mp ht with ht_eq | ht1
            · rw [Prod.mk.injEq] at hf_eq ht_eq
              exact Bool.noConfusion (hf_eq.2.trans ht_eq.2.symm)
            · rw [Prod.mk.injEq] at hf_eq
              have := hbnd (i, true) ht1; rw [hf_eq.1] at this; dsimp [pr] at this; omega
            · rw [Prod.mk.injEq] at ht_eq
              have := hbnd (i, false) hf1; rw [ht_eq.1] at this; dsimp [pr] at this; omega
            · exact hcons i ⟨hf1, ht1⟩
          · exact Finset.mem_insert_of_mem hpl
          · exact Finset.mem_insert_self _ _
          · rcases hedge with ⟨i, b, hi1, hi2⟩
            exact ⟨i, b, Finset.mem_insert_of_mem hi1, Finset.mem_insert_of_mem hi2⟩
          · rw [hcardR C1 h1]; rcases hcard with h | h <;> [left; right] <;> omega
        · rcases Finset.mem_image.mp hC2 with ⟨C2, h2, rfl⟩
          obtain ⟨hbnd, hcons, hpmid, hpr, hedge, hcard⟩ := hL2_prop C2 h2
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro p hp
            rcases Finset.mem_insert.mp hp with rfl | hp2
            · exact ⟨by dsimp [pl]; omega, by dsimp [pl]; omega⟩
            · have := hbnd p hp2; exact ⟨by omega, this.2⟩
          · intro i ⟨hf, ht⟩
            rcases Finset.mem_insert.mp hf with hf_eq | hf2 <;>
            rcases Finset.mem_insert.mp ht with ht_eq | ht2
            · rw [Prod.mk.injEq] at hf_eq ht_eq
              exact Bool.noConfusion (hf_eq.2.trans ht_eq.2.symm)
            · rw [Prod.mk.injEq] at hf_eq
              have := hbnd (i, true) ht2; rw [hf_eq.1] at this; dsimp [pl] at this; omega
            · rw [Prod.mk.injEq] at ht_eq
              have := hbnd (i, false) hf2; rw [ht_eq.1] at this; dsimp [pl] at this; omega
            · exact hcons i ⟨hf2, ht2⟩
          · exact Finset.mem_insert_self _ _
          · rw [hb_end_eq]; exact Finset.mem_insert_of_mem hpr
          · rcases hedge with ⟨i, b, hi1, hi2⟩
            exact ⟨i, b, Finset.mem_insert_of_mem hi1, Finset.mem_insert_of_mem hi2⟩
          · rw [hcardL C2 h2]; rcases hcard with h | h <;> [left; right] <;> omega
      · rw [Finset.filter_union, Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter hdisj)]
        have hf1 : (L1'.filter (fun C => C.card = d + 1 + 1)) =
            (L1.filter (fun C => C.card = d + 1)).image insR := by
          ext C
          simp only [L1', Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨⟨C1, h1, rfl⟩, hc⟩
            have := hcardR C1 h1
            exact ⟨C1, ⟨h1, by omega⟩, rfl⟩
          · rintro ⟨C1, ⟨h1, hc⟩, rfl⟩
            exact ⟨⟨C1, h1, rfl⟩, by rw [hcardR C1 h1, hc]⟩
        have hf2 : (L2'.filter (fun C => C.card = d + 1 + 1)) =
            (L2.filter (fun C => C.card = d + 1)).image insL := by
          ext C
          simp only [L2', Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨⟨C2, h2, rfl⟩, hc⟩
            have := hcardL C2 h2
            exact ⟨C2, ⟨h2, by omega⟩, rfl⟩
          · rintro ⟨C2, ⟨h2, hc⟩, rfl⟩
            exact ⟨⟨C2, h2, rfl⟩, by rw [hcardL C2 h2, hc]⟩
        rw [hf1, hf2,
          Finset.card_image_of_injOn (hinj1.mono (by intro C hC; exact (Finset.mem_filter.mp hC).1)),
          Finset.card_image_of_injOn (hinj2.mono (by intro C hC; exact (Finset.mem_filter.mp hC).1)),
          hL1_lo, hL2_lo]
        omega
      · rw [Finset.filter_union, Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter hdisj)]
        have hf1 : (L1'.filter (fun C => C.card = d + 1 + 2)) =
            (L1.filter (fun C => C.card = d + 2)).image insR := by
          ext C
          simp only [L1', Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨⟨C1, h1, rfl⟩, hc⟩
            have := hcardR C1 h1
            exact ⟨C1, ⟨h1, by omega⟩, rfl⟩
          · rintro ⟨C1, ⟨h1, hc⟩, rfl⟩
            exact ⟨⟨C1, h1, rfl⟩, by rw [hcardR C1 h1, hc]⟩
        have hf2 : (L2'.filter (fun C => C.card = d + 1 + 2)) =
            (L2.filter (fun C => C.card = d + 2)).image insL := by
          ext C
          simp only [L2', Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨⟨C2, h2, rfl⟩, hc⟩
            have := hcardL C2 h2
            exact ⟨C2, ⟨h2, by omega⟩, rfl⟩
          · rintro ⟨C2, ⟨h2, hc⟩, rfl⟩
            exact ⟨⟨C2, h2, rfl⟩, by rw [hcardL C2 h2, hc]⟩
        rw [hf1, hf2,
          Finset.card_image_of_injOn (hinj1.mono (by intro C hC; exact (Finset.mem_filter.mp hC).1)),
          Finset.card_image_of_injOn (hinj2.mono (by intro C hC; exact (Finset.mem_filter.mp hC).1)),
          hL1_hi, hL2_hi]
        omega
      · intro x
        rw [Finset.filter_union, Finset.card_union_of_disjoint
          (Finset.disjoint_filter_filter hdisj)]
        have hpart1 : (L1'.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card =
            if x pr = b_end then
              (L1.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card
            else 0 := by
          rw [load_eq_sum, load_eq_sum]
          by_cases hxr : x pr = b_end
          · rw [if_pos hxr]
            have hfeq : L1'.filter (fun C => ∀ p ∈ C, x p.1 = p.2) =
                (L1.filter (fun C => ∀ p ∈ C, x p.1 = p.2)).image insR := by
              ext C
              simp only [L1', Finset.mem_filter, Finset.mem_image]
              constructor
              · rintro ⟨⟨C1, h1, rfl⟩, hall⟩
                exact ⟨C1, ⟨h1, fun p hp => hall p (Finset.mem_insert_of_mem hp)⟩, rfl⟩
              · rintro ⟨C1, ⟨h1, hall⟩, rfl⟩
                refine ⟨⟨C1, h1, rfl⟩, fun p hp => ?_⟩
                rcases Finset.mem_insert.mp hp with rfl | hp1
                · exact hxr
                · exact hall p hp1
            rw [hfeq, Finset.card_image_of_injOn
              (hinj1.mono (by intro C hC; exact (Finset.mem_filter.mp hC).1))]
          · rw [if_neg hxr]
            have hempty : L1'.filter (fun C => ∀ p ∈ C, x p.1 = p.2) = ∅ := by
              ext C
              simp only [L1', Finset.mem_filter, Finset.mem_image, Finset.notMem_empty,
                iff_false, not_and]
              rintro ⟨C1, _, rfl⟩ hall
              exact hxr (hall (pr, b_end) (Finset.mem_insert_self _ _))
            rw [hempty, Finset.card_empty]
        have hpart2 : (L2'.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card =
            if x pl = a then
              (L2.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card
            else 0 := by
          rw [load_eq_sum, load_eq_sum]
          by_cases hxl : x pl = a
          · rw [if_pos hxl]
            have hfeq : L2'.filter (fun C => ∀ p ∈ C, x p.1 = p.2) =
                (L2.filter (fun C => ∀ p ∈ C, x p.1 = p.2)).image insL := by
              ext C
              simp only [L2', Finset.mem_filter, Finset.mem_image]
              constructor
              · rintro ⟨⟨C2, h2, rfl⟩, hall⟩
                exact ⟨C2, ⟨h2, fun p hp => hall p (Finset.mem_insert_of_mem hp)⟩, rfl⟩
              · rintro ⟨C2, ⟨h2, hall⟩, rfl⟩
                refine ⟨⟨C2, h2, rfl⟩, fun p hp => ?_⟩
                rcases Finset.mem_insert.mp hp with rfl | hp2
                · exact hxl
                · exact hall p hp2
            rw [hfeq, Finset.card_image_of_injOn
              (hinj2.mono (by intro C hC; exact (Finset.mem_filter.mp hC).1))]
          · rw [if_neg hxl]
            have hempty : L2'.filter (fun C => ∀ p ∈ C, x p.1 = p.2) = ∅ := by
              ext C
              simp only [L2', Finset.mem_filter, Finset.mem_image, Finset.notMem_empty,
                iff_false, not_and]
              rintro ⟨C2, _, rfl⟩ hall
              exact hxl (hall (pl, a) (Finset.mem_insert_self _ _))
            rw [hempty, Finset.card_empty]
        rw [hpart1, hpart2, hL1_load x, hL2_load x, ← hb_end_eq]
        exact load_combine_aux (x pl) (x pmid) (x pr) a b_mid b_end

end PEqualNP.Outside.L_lib_581_aux

theorem PEqualNP.Outside.L_lib_581 : (∀ (m : ℕ), 0 < m → ∀ f : Fin m → Bool,
  let Cell := Finset (Fin (m+1) × Bool)
  let flip := decide (Odd ((Finset.univ.filter (fun i => f i = true)).card))
  let last := Fin.last m
  let load := fun (L : Finset Cell) (x : Fin (m+1) → Bool) =>
    (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card
  let h := Nat.clog 2 m
  ∃ L : Finset Cell, L.card = 2*m ∧
    (∀ C ∈ L,
      (∀ i : Fin (m+1), ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
      (∃ a : Bool, (0, a) ∈ C ∧ (last, !(a ^^ flip)) ∈ C) ∧
      (∃ (i : Fin m) (b : Bool), (i.castSucc, b) ∈ C ∧ (i.succ, !(b ^^ f i)) ∈ C) ∧
      (C.card = h+1 ∨ C.card = h+2)) ∧
    (L.filter (fun C => C.card = h+1)).card = 2*(2^h-m) ∧
    (L.filter (fun C => C.card = h+2)).card = 2*(2*m-2^h) ∧
    ∀ x, load L x = if x last = (x 0 ^^ flip) then 0 else 1) := by
  intro m hm f Cell flip last load h
  have hupper : m - 0 ≤ 2 ^ h := by
    rw [Nat.sub_zero]
    exact Nat.le_pow_clog (by decide : 1 < 2) m
  have hlower : 2 ^ h ≤ 2 * (m - 0) := by
    rw [Nat.sub_zero]
    by_cases hm1 : m = 1
    · subst hm1
      have : h = 0 := by dsimp [h]; decide
      rw [this]; omega
    · have hh_pos : 0 < h := by
        dsimp [h]
        exact Nat.clog_pos (by decide : 1 < 2) (by omega)
      have hlt : 2 ^ (h - 1) < m := by
        have h1 : h - 1 < Nat.clog 2 m := by omega
        exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp h1
      have hpow : 2 ^ h = 2 * 2 ^ (h - 1) := by
        conv_lhs => rw [show h = (h - 1) + 1 by omega]
        ring
      omega
  obtain ⟨Lf, hLf_card, hLf_prop, hLf_lo, hLf_hi, hLf_load⟩ :=
    PEqualNP.Outside.L_lib_581_aux.build_sub f h 0 m hm le_rfl hupper hlower false
  obtain ⟨Lt, hLt_card, hLt_prop, hLt_lo, hLt_hi, hLt_load⟩ :=
    PEqualNP.Outside.L_lib_581_aux.build_sub f h 0 m hm le_rfl hupper hlower true
  have hflip_eq : PEqualNP.Outside.L_lib_581_aux.segFlip f 0 m = flip :=
    PEqualNP.Outside.L_lib_581_aux.segFlip_full f
  have h0_eq : (⟨0, by omega⟩ : Fin (m + 1)) = 0 := rfl
  have hlast_eq : (⟨m, by omega⟩ : Fin (m + 1)) = last := rfl
  have hdisj : Disjoint Lf Lt := by
    rw [Finset.disjoint_left]
    intro C hCf hCt
    have hf_mem : ((⟨0, by omega⟩ : Fin (m + 1)), false) ∈ C := (hLf_prop C hCf).2.2.1
    have ht_mem : ((⟨0, by omega⟩ : Fin (m + 1)), true) ∈ C := (hLt_prop C hCt).2.2.1
    exact (hLf_prop C hCf).2.1 ⟨0, by omega⟩ ⟨hf_mem, ht_mem⟩
  refine ⟨Lf ∪ Lt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdisj, hLf_card, hLt_card]
    omega
  · intro C hC
    rcases Finset.mem_union.mp hC with hCf | hCt
    · obtain ⟨_, hcons, h0, hlast, hedge, hcard⟩ := hLf_prop C hCf
      refine ⟨hcons, ⟨false, ?_, ?_⟩, hedge, hcard⟩
      · rwa [← h0_eq]
      · rwa [← hlast_eq, ← hflip_eq]
    · obtain ⟨_, hcons, h0, hlast, hedge, hcard⟩ := hLt_prop C hCt
      refine ⟨hcons, ⟨true, ?_, ?_⟩, hedge, hcard⟩
      · rwa [← h0_eq]
      · rwa [← hlast_eq, ← hflip_eq]
  · rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
      hLf_lo, hLt_lo]
    omega
  · rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
      hLf_hi, hLt_hi]
    omega
  · intro x
    dsimp only [load]
    rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
      hLf_load x, hLt_load x, h0_eq, hlast_eq, hflip_eq]
    cases hx0 : x 0 <;> cases hxl : x last <;> cases hfl : flip <;> decide
