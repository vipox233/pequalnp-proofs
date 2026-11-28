import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_924

def NC (n : ℕ) : Finset (Finset ℕ) := (Finset.range n).powerset.filter (fun I => ∀ i ∈ I, i + 1 ∉ I)

theorem NC_succ_succ (n : ℕ) : (NC (n + 2)).card = (NC (n + 1)).card + (NC n).card := by
  rw [← Finset.card_filter_add_card_filter_not (fun I => n + 1 ∈ I), add_comm (NC (n + 1)).card]
  congr 1
  ·
    symm
    refine Finset.card_bij' (fun J _ => insert (n + 1) J) (fun I _ => I.erase (n + 1)) ?_ ?_ ?_ ?_
    · intro J hJ
      simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hJ ⊢
      obtain ⟨hs, hc⟩ := hJ
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hs hi); omega)
      · intro i hi h2
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rcases Finset.mem_insert.mp h2 with h | h
          · omega
          · have := Finset.mem_range.mp (hs h); omega
        · rcases Finset.mem_insert.mp h2 with h | h
          · have hlt : i < n := Finset.mem_range.mp (hs hi)
            have hieq : i = n := by omega
            exact absurd hlt (by omega)
          · exact hc i hi h
    · intro I hI
      simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hI ⊢
      obtain ⟨⟨hs, hc⟩, hn⟩ := hI
      refine ⟨fun i hi => ?_, fun i hi h2 => hc i (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase h2)⟩
      have hne := Finset.ne_of_mem_erase hi
      have hi' := Finset.mem_of_mem_erase hi
      have hr := Finset.mem_range.mp (hs hi')
      have : i ≠ n := fun h => hc i hi' (h ▸ hn)
      exact Finset.mem_range.mpr (by omega)
    · intro J hJ
      simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hJ
      apply Finset.erase_insert
      intro h; have := Finset.mem_range.mp (hJ.1 h); omega
    · intro I hI
      simp only [Finset.mem_filter] at hI
      exact Finset.insert_erase hI.2
  ·
    congr 1
    ext I
    simp only [NC, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨⟨hs, hc⟩, hn⟩
      refine ⟨fun i hi => ?_, hc⟩
      have hlt : i < n + 2 := Finset.mem_range.mp (hs hi)
      have hne : i ≠ n + 1 := fun h => hn (h ▸ hi)
      exact Finset.mem_range.mpr (by omega)
    · rintro ⟨hs, hc⟩
      refine ⟨⟨fun i hi => Finset.mem_range.mpr (by have := Finset.mem_range.mp (hs hi); omega), hc⟩, fun h => ?_⟩
      have := Finset.mem_range.mp (hs h); omega

theorem NC_card (n : ℕ) : (NC n).card = Nat.fib (n + 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | k + 2 =>
      rw [NC_succ_succ, ih (k + 1) (by omega), ih k (by omega)]
      have h := Nat.fib_add_two (n := k + 2)
      rw [show k + 2 + 2 = k + 2 + 2 from rfl, h, show k + 1 + 2 = k + 2 + 1 from rfl]
      ring

theorem NC_avoid0_card (n : ℕ) : ((NC n).filter (fun I => 0 ∉ I)).card = Nat.fib (n + 1) := by
  match n with
  | 0 => decide
  | k + 1 =>
    rw [show k + 1 + 1 = k + 2 from rfl, ← NC_card k]
    symm
    refine Finset.card_bij' (fun J _ => J.image (· + 1)) (fun I _ => I.image (· - 1)) ?_ ?_ ?_ ?_
    · intro J hJ
      simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hJ
      obtain ⟨hs, hc⟩ := hJ
      simp only [NC, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hs hj); omega)
      · intro i hi h2
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨j', hj', h⟩ := Finset.mem_image.mp h2
        exact hc j hj (by rw [show j + 1 = j' by omega]; exact hj')
      · intro h; obtain ⟨j, _, h⟩ := Finset.mem_image.mp h; omega
    · intro I hI
      simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hI
      obtain ⟨⟨hs, hc⟩, h0⟩ := hI
      simp only [NC, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro i hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        have hj0 : j ≠ 0 := fun h => h0 (h ▸ hj)
        exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hs hj); omega)
      · intro i hi h2
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨j', hj', h⟩ := Finset.mem_image.mp h2
        have hj0 : j ≠ 0 := fun h => h0 (h ▸ hj)
        have hj0' : j' ≠ 0 := fun h => h0 (h ▸ hj')
        exact hc j hj (by rw [show j + 1 = j' by omega]; exact hj')
    · intro J hJ
      ext i
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨j, ⟨j', hj', rfl⟩, rfl⟩; simpa using hj'
      · intro hi; exact ⟨i + 1, ⟨i, hi, rfl⟩, by omega⟩
    · intro I hI
      simp only [NC, Finset.mem_filter] at hI
      ext i
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨j, ⟨j', hj', rfl⟩, rfl⟩
        have hj0 : j' ≠ 0 := fun h => hI.2 (h ▸ hj')
        rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
      · intro hi
        have : i ≠ 0 := fun h => hI.2 (h ▸ hi)
        exact ⟨i - 1, ⟨i, hi, rfl⟩, by omega⟩

theorem cassini_even (k : ℕ) : Nat.fib (2 * k + 1) ^ 2 = Nat.fib (2 * k) * Nat.fib (2 * k + 2) + 1 := by
  have h : ∀ n : ℕ, (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e1 : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by exact_mod_cast Nat.fib_add_two
      have e2 : (Nat.fib (n + 1 + 2) : ℤ) = Nat.fib (n + 1) + Nat.fib (n + 2) := by exact_mod_cast Nat.fib_add_two
      rw [show n + 1 + 1 = n + 2 by ring, e2, pow_succ (-1 : ℤ) n, ← ih, e1]; ring
  have := h (2 * k)
  rw [pow_mul, show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_pow] at this
  have : (Nat.fib (2 * k + 1) : ℤ) ^ 2 = Nat.fib (2 * k) * Nat.fib (2 * k + 2) + 1 := by linarith
  exact_mod_cast this

abbrev good (C : Finset ℕ) (I : Finset (ℕ × ℕ)) : Prop :=
  (∀ z ∈ I, (z.1, z.2 + 1) ∉ I) ∧ (∀ x ∈ C, (x, 0) ∉ I)


def Gset (v L : ℕ) (C : Finset ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((Finset.range v ×ˢ Finset.range L).powerset).filter (good C)

def blk (L : ℕ) (C : Finset ℕ) (x : ℕ) : Finset (Finset ℕ) :=
  if x ∈ C then (NC L).filter (fun I => 0 ∉ I) else NC L

theorem blk_card (L : ℕ) (C : Finset ℕ) (x : ℕ) :
    (blk L C x).card = if x ∈ C then Nat.fib (L + 1) else Nat.fib (L + 2) := by
  unfold blk; split_ifs
  · exact NC_avoid0_card L
  · exact NC_card L

theorem Gset_succ (v L : ℕ) (C : Finset ℕ) :
    (Gset (v + 1) L C).card = (Gset v L C).card * (blk L C v).card := by
  rw [← Finset.card_product]
  refine Finset.card_bij' (fun I _ => (I.filter (fun z => z.1 < v), (I.filter (fun z => z.1 = v)).image Prod.snd))
    (fun p _ => p.1 ∪ p.2.image (fun i => (v, i))) ?_ ?_ ?_ ?_
  · intro I hI
    simp only [Gset, good, Finset.mem_filter, Finset.mem_powerset] at hI
    obtain ⟨hs, hc, h0⟩ := hI
    simp only [Finset.mem_product, Gset, good, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro z hz
      obtain ⟨hz, hlt⟩ := Finset.mem_filter.mp hz
      have := Finset.mem_product.mp (hs hz)
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hlt, this.2⟩
    · intro z hz h2
      exact hc z hz.1 h2.1
    · intro x hx h2
      exact h0 x hx h2.1
    · unfold blk
      have hsub : (I.filter (fun z => z.1 = v)).image Prod.snd ⊆ Finset.range L := by
        intro i hi
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
        exact (Finset.mem_product.mp (hs (Finset.mem_filter.mp hz).1)).2
      have hnc : (I.filter (fun z => z.1 = v)).image Prod.snd ∈ NC L := by
        simp only [NC, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨hsub, fun i hi h2 => ?_⟩
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨z', hz', h'⟩ := Finset.mem_image.mp h2
        obtain ⟨hzI, hz1⟩ := Finset.mem_filter.mp hz
        obtain ⟨hzI', hz1'⟩ := Finset.mem_filter.mp hz'
        apply hc z hzI
        have : z' = (z.1, z.2 + 1) := Prod.ext (by omega) h'
        rw [← this]; exact hzI'
      split_ifs with hv
      · refine Finset.mem_filter.mpr ⟨hnc, fun h => ?_⟩
        obtain ⟨z, hz, h'⟩ := Finset.mem_image.mp h
        obtain ⟨hzI, hz1⟩ := Finset.mem_filter.mp hz
        apply h0 v hv
        have : z = (v, 0) := Prod.ext hz1 h'
        rw [← this]; exact hzI
      · exact hnc
  · intro p hp
    obtain ⟨hJ, hK⟩ := Finset.mem_product.mp hp
    simp only [Gset, good, Finset.mem_filter, Finset.mem_powerset] at hJ
    obtain ⟨hs, hc, h0⟩ := hJ
    have hK' : p.2 ∈ NC L ∧ (v ∈ C → 0 ∉ p.2) := by
      unfold blk at hK; split_ifs at hK with hv
      · exact ⟨(Finset.mem_filter.mp hK).1, fun _ => (Finset.mem_filter.mp hK).2⟩
      · exact ⟨hK, fun h => absurd h hv⟩
    obtain ⟨hKnc, hK0⟩ := hK'
    simp only [NC, Finset.mem_filter, Finset.mem_powerset] at hKnc
    simp only [Gset, good, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.mp hz with h | h
      · have := Finset.mem_product.mp (hs h)
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_range.mp this.1; omega), this.2⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), hKnc.1 hi⟩
    · intro z hz h2
      rcases Finset.mem_union.mp hz with h | h
      · rcases Finset.mem_union.mp h2 with h' | h'
        · exact hc z h h'
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h'
          have h1 : z.1 = v := (congrArg Prod.fst hi).symm
          have := Finset.mem_range.mp (Finset.mem_product.mp (hs h)).1
          omega
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        rcases Finset.mem_union.mp h2 with h' | h'
        · have := Finset.mem_range.mp (Finset.mem_product.mp (hs h')).1
          simp at this
        · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h'
          have : j = i + 1 := congrArg Prod.snd hji
          exact hKnc.2 i hi (this ▸ hj)
    · intro x hx h2
      rcases Finset.mem_union.mp h2 with h | h
      · exact h0 x hx h
      · obtain ⟨i, hi, hxi⟩ := Finset.mem_image.mp h
        have e1 : v = x := congrArg Prod.fst hxi
        have e2 : i = 0 := congrArg Prod.snd hxi
        exact hK0 (e1 ▸ hx) (e2 ▸ hi)
  · intro I hI
    simp only [Gset, Finset.mem_filter, Finset.mem_powerset] at hI
    ext z
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro (⟨hz, _⟩ | ⟨i, ⟨w, ⟨hw, hw1⟩, rfl⟩, rfl⟩)
      · exact hz
      · rw [← hw1]; exact hw
    · intro hz
      have := Finset.mem_range.mp (Finset.mem_product.mp (hI.1 hz)).1
      rcases Nat.lt_or_ge z.1 v with h | h
      · exact Or.inl ⟨hz, h⟩
      · exact Or.inr ⟨z.2, ⟨z, ⟨hz, by omega⟩, rfl⟩, Prod.ext (by omega) rfl⟩
  · intro p hp
    obtain ⟨hJ, hK⟩ := Finset.mem_product.mp hp
    simp only [Gset, Finset.mem_filter, Finset.mem_powerset] at hJ
    refine Prod.ext ?_ ?_
    · ext z
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨h | ⟨i, _, rfl⟩, hlt⟩
        · exact h
        · simp at hlt
      · intro hz
        exact ⟨Or.inl hz, Finset.mem_range.mp (Finset.mem_product.mp (hJ.1 hz)).1⟩
    · ext i
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨z, ⟨h | ⟨j, hj, rfl⟩, hz1⟩, rfl⟩
        · have := Finset.mem_range.mp (Finset.mem_product.mp (hJ.1 h)).1; omega
        · exact hj
      · intro hi; exact ⟨(v, i), ⟨Or.inr ⟨i, hi, rfl⟩, rfl⟩, rfl⟩

theorem Gset_card (v L : ℕ) (C : Finset ℕ) :
    (Gset v L C).card = ∏ x ∈ Finset.range v, (if x ∈ C then Nat.fib (L + 1) else Nat.fib (L + 2)) := by
  induction v with
  | zero =>
    have : Finset.filter (good C) {∅} = {∅} := Finset.filter_true_of_mem (fun I hI => by
      rw [Finset.mem_singleton.mp hI]; exact ⟨fun z hz => absurd hz (Finset.notMem_empty z), fun x _ h => absurd h (Finset.notMem_empty _)⟩)
    simp [Gset, this]
  | succ v ih => rw [Gset_succ, ih, Finset.prod_range_succ, blk_card]

theorem Gset_card' (v L : ℕ) (C : Finset ℕ) (hC : C ⊆ Finset.range v) :
    (Gset v L C).card = Nat.fib (L + 1) ^ C.card * Nat.fib (L + 2) ^ (v - C.card) := by
  rw [Gset_card, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.range v).filter (fun x => x ∈ C) = C := by
    ext x; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hC h, h⟩⟩
  have h2 : ((Finset.range v).filter (fun x => x ∉ C)).card = v - C.card := by
    rw [Finset.filter_not, Finset.card_sdiff, h1, Finset.inter_eq_left.mpr hC, Finset.card_range]
  rw [h1, h2]

def verts (e : ℕ × ℕ) : Finset ℕ := {e.1, e.2}
abbrev IsMatch (S : Finset (ℕ × ℕ)) : Prop := ∀ e ∈ S, ∀ g ∈ S, e ≠ g → Disjoint (verts e) (verts g)
def lift (L : ℕ) (e : ℕ × ℕ) : ℕ × ℕ := (e.1 * (L + 1), e.2 * (L + 1))
def rail (L : ℕ) (z : ℕ × ℕ) : ℕ × ℕ := (z.1 * (L + 1) + z.2, z.1 * (L + 1) + z.2 + 1)
def cov (S : Finset (ℕ × ℕ)) : Finset ℕ := S.biUnion verts

theorem dm (L x i : ℕ) (hi : i < L + 1) : (x * (L + 1) + i) / (L + 1) = x ∧ (x * (L + 1) + i) % (L + 1) = i := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hi

theorem blk_eq {L x y i j : ℕ} (hi : i < L + 1) (hj : j < L + 1) (h : x * (L + 1) + i = y * (L + 1) + j) :
    x = y ∧ i = j := by
  obtain ⟨a1, a2⟩ := dm L x i hi
  obtain ⟨b1, b2⟩ := dm L y j hj
  rw [h] at a1 a2
  exact ⟨a1.symm.trans b1, a2.symm.trans b2⟩

theorem not_disj {a b c d : ℕ} (h : ¬ Disjoint ({a, b} : Finset ℕ) {c, d}) : a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra hn
  push Not at hn
  apply h
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
  rcases hx with rfl | rfl <;> rcases hx' with h' | h' <;> simp_all

theorem disj_of {a b c d : ℕ} (h1 : a ≠ c) (h2 : a ≠ d) (h3 : b ≠ c) (h4 : b ≠ d) :
    Disjoint ({a, b} : Finset ℕ) {c, d} := by
  by_contra h; rcases not_disj h with h | h | h | h <;> contradiction

theorem rail_rail {L : ℕ} {z w : ℕ × ℕ} (hz : z.2 < L) (hw : w.2 < L) (hne : z ≠ w)
    (h : ¬ Disjoint (verts (rail L z)) (verts (rail L w))) :
    (w = (z.1, z.2 + 1)) ∨ (z = (w.1, w.2 + 1)) := by
  simp only [verts, rail] at h
  rcases not_disj h with h | h | h | h
  · exact absurd (Prod.ext (blk_eq (by omega) (by omega) h).1 (blk_eq (by omega) (by omega) h).2) hne
  · have := blk_eq (L := L) (x := z.1) (y := w.1) (i := z.2) (j := w.2 + 1) (by omega) (by omega) (by omega)
    right; exact Prod.ext this.1 this.2
  · have := blk_eq (L := L) (x := z.1) (y := w.1) (i := z.2 + 1) (j := w.2) (by omega) (by omega) (by omega)
    left; exact Prod.ext this.1.symm this.2.symm
  · have := blk_eq (L := L) (x := z.1) (y := w.1) (i := z.2) (j := w.2) (by omega) (by omega) (by omega)
    exact absurd (Prod.ext this.1 this.2) hne

theorem lift_rail {L : ℕ} {e z : ℕ × ℕ} (hz : z.2 < L) (h : ¬ Disjoint (verts (lift L e)) (verts (rail L z))) :
    z.2 = 0 ∧ (z.1 = e.1 ∨ z.1 = e.2) := by
  simp only [verts, lift, rail] at h
  rcases not_disj h with h | h | h | h
  · have := blk_eq (L := L) (x := e.1) (y := z.1) (i := 0) (j := z.2) (by omega) (by omega) (by omega)
    exact ⟨this.2.symm, Or.inl this.1.symm⟩
  · have := blk_eq (L := L) (x := e.1) (y := z.1) (i := 0) (j := z.2 + 1) (by omega) (by omega) (by omega); omega
  · have := blk_eq (L := L) (x := e.2) (y := z.1) (i := 0) (j := z.2) (by omega) (by omega) (by omega)
    exact ⟨this.2.symm, Or.inr this.1.symm⟩
  · have := blk_eq (L := L) (x := e.2) (y := z.1) (i := 0) (j := z.2 + 1) (by omega) (by omega) (by omega); omega

theorem lift_ne_rail {L : ℕ} {e z : ℕ × ℕ} (hz : z.2 < L) : lift L e ≠ rail L z := by
  intro h
  simp only [lift, rail, Prod.mk.injEq] at h
  have b := blk_eq (L := L) (x := e.2) (y := z.1) (i := 0) (j := z.2 + 1) (by omega) (by omega) (by omega)
  omega

theorem rail_inj {L : ℕ} {z w : ℕ × ℕ} (hz : z.2 < L) (hw : w.2 < L) (h : rail L z = rail L w) : z = w := by
  simp only [rail, Prod.mk.injEq] at h
  have := blk_eq (L := L) (by omega) (by omega) h.1
  exact Prod.ext this.1 this.2

theorem lift_inj {L : ℕ} {e g : ℕ × ℕ} (h : lift L e = lift L g) : e = g := by
  simp only [lift, Prod.mk.injEq] at h
  exact Prod.ext (Nat.eq_of_mul_eq_mul_right (by omega) h.1) (Nat.eq_of_mul_eq_mul_right (by omega) h.2)

theorem lift_disj {L : ℕ} {e g : ℕ × ℕ} (h : Disjoint (verts e) (verts g)) : Disjoint (verts (lift L e)) (verts (lift L g)) := by
  simp only [verts, lift]
  have hd : ∀ a b : ℕ, a * (L + 1) = b * (L + 1) → a = b := fun a b h => Nat.eq_of_mul_eq_mul_right (by omega) h
  have h' : ∀ x, x ∈ verts e → x ∉ verts g := fun x hx hg => Finset.disjoint_left.mp h hx hg
  simp only [verts, Finset.mem_insert, Finset.mem_singleton] at h'
  apply disj_of
  · intro hh; exact h' _ (Or.inl rfl) (Or.inl (hd _ _ hh))
  · intro hh; exact h' _ (Or.inl rfl) (Or.inr (hd _ _ hh))
  · intro hh; exact h' _ (Or.inr rfl) (Or.inl (hd _ _ hh))
  · intro hh; exact h' _ (Or.inr rfl) (Or.inr (hd _ _ hh))

theorem lift_disj_rev {L : ℕ} {e g : ℕ × ℕ} (h : Disjoint (verts (lift L e)) (verts (lift L g))) : Disjoint (verts e) (verts g) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hg
  simp only [verts, lift, Finset.mem_insert, Finset.mem_singleton] at hx hg h
  exact h (a := x * (L + 1)) (by rcases hx with rfl | rfl <;> simp) (by rcases hg with rfl | rfl <;> simp)

theorem rail_meet (L : ℕ) (z : ℕ × ℕ) : z.1 * (L + 1) + z.2 + 1 ∈ verts (rail L z) := by simp [verts, rail]

def railsF (v L : ℕ) : Finset (ℕ × ℕ) := (Finset.range v ×ˢ Finset.range L).image (rail L)
def bigF (v L : ℕ) (E : Finset (ℕ × ℕ)) : Finset (Finset (ℕ × ℕ)) :=
  ((E.image (lift L)) ∪ railsF v L).powerset.filter IsMatch

theorem fiber_card (v L : ℕ) (E S : Finset (ℕ × ℕ)) (hSE : S ⊆ E) (hS : IsMatch S) :
    ((bigF v L E).filter (fun T => E.filter (fun e => lift L e ∈ T) = S)).card = (Gset v L (cov S)).card := by
  refine Finset.card_bij' (fun T _ => (Finset.range v ×ˢ Finset.range L).filter (fun z => rail L z ∈ T))
    (fun I _ => S.image (lift L) ∪ I.image (rail L)) ?_ ?_ ?_ ?_
  ·
    intro T hT
    simp only [bigF, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨⟨hsub, hm⟩, hS'⟩ := hT
    simp only [Gset, good, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, ?_, ?_⟩
    · intro z hz hz'
      obtain ⟨hzr, hzT⟩ := hz
      obtain ⟨hzr', hzT'⟩ := hz'
      have hL : z.2 < L := (Finset.mem_product.mp hzr).2 |> Finset.mem_range.mp
      have hL' : z.2 + 1 < L := (Finset.mem_product.mp hzr').2 |> Finset.mem_range.mp
      have hne : rail L z ≠ rail L (z.1, z.2 + 1) := fun h => by
        have := rail_inj (w := (z.1, z.2 + 1)) hL hL' h
        have := congrArg Prod.snd this; simp at this
      have hd := hm _ hzT _ hzT' hne
      apply Finset.disjoint_left.mp hd (rail_meet L z)
      simp [verts, rail]; omega
    · intro x hx hx0
      obtain ⟨hxr, hxT⟩ := hx0
      have hL : 0 < L := (Finset.mem_product.mp hxr).2 |> Finset.mem_range.mp
      obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
      have heT : lift L e ∈ T := by
        rw [← hS'] at he; exact (Finset.mem_filter.mp he).2
      have hne : lift L e ≠ rail L (x, 0) := lift_ne_rail (by simpa using hL)
      have hd := hm _ heT _ hxT hne
      have h1 : x * (L + 1) ∈ verts (lift L e) := by
        simp only [verts, Finset.mem_insert, Finset.mem_singleton] at hxe
        simp only [verts, lift, Finset.mem_insert, Finset.mem_singleton]
        rcases hxe with rfl | rfl <;> simp
      have h2 : x * (L + 1) ∈ verts (rail L (x, 0)) := by simp [verts, rail]
      exact Finset.disjoint_left.mp hd h1 h2
  ·
    intro I hI
    simp only [Gset, good, Finset.mem_filter, Finset.mem_powerset] at hI
    obtain ⟨hIs, hc, h0⟩ := hI
    have hIL : ∀ z ∈ I, z.2 < L := fun z hz => Finset.mem_range.mp (Finset.mem_product.mp (hIs hz)).2
    simp only [bigF, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨⟨Finset.union_subset_union (Finset.image_subset_image hSE) (Finset.image_subset_image hIs), ?_⟩, ?_⟩
    · intro t1 ht1 t2 ht2 hne
      rcases Finset.mem_union.mp ht1 with h1 | h1 <;> rcases Finset.mem_union.mp ht2 with h2 | h2
      · obtain ⟨e1, he1, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨e2, he2, rfl⟩ := Finset.mem_image.mp h2
        exact lift_disj (hS e1 he1 e2 he2 (fun h => hne (h ▸ rfl)))
      · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h2
        by_contra h
        obtain ⟨hz0, hz1⟩ := lift_rail (hIL z hz) h
        apply h0 z.1 (Finset.mem_biUnion.mpr ⟨e, he, by rcases hz1 with h | h <;> simp [verts, h]⟩)
        have : z = (z.1, 0) := Prod.ext rfl hz0
        rw [← this]; exact hz
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp h2
        by_contra h
        obtain ⟨hz0, hz1⟩ := lift_rail (hIL z hz) (fun hd => h hd.symm)
        apply h0 z.1 (Finset.mem_biUnion.mpr ⟨e, he, by rcases hz1 with h | h <;> simp [verts, h]⟩)
        have : z = (z.1, 0) := Prod.ext rfl hz0
        rw [← this]; exact hz
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h2
        by_contra h
        rcases rail_rail (hIL z hz) (hIL w hw) (fun e => hne (e ▸ rfl)) h with e | e
        · exact hc z hz (e ▸ hw)
        · exact hc w hw (e ▸ hz)
    · ext e
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨heE, ⟨e', he', hee⟩ | ⟨z, hz, hze⟩⟩
        · rw [← lift_inj hee]; exact he'
        · exact absurd hze.symm (lift_ne_rail (hIL z hz))
      · intro he; exact ⟨hSE he, Or.inl ⟨e, he, rfl⟩⟩
  ·
    intro T hT
    simp only [bigF, Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨⟨hsub, hm⟩, hS'⟩ := hT
    ext t
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro (⟨e, he, rfl⟩ | ⟨z, ⟨_, hzT⟩, rfl⟩)
      · rw [← hS'] at he; exact (Finset.mem_filter.mp he).2
      · exact hzT
    · intro ht
      rcases Finset.mem_union.mp (hsub ht) with h | h
      · obtain ⟨e, heE, rfl⟩ := Finset.mem_image.mp h
        left; refine ⟨e, ?_, rfl⟩
        rw [← hS']; exact Finset.mem_filter.mpr ⟨heE, ht⟩
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
        right; exact ⟨z, ⟨hz, ht⟩, rfl⟩
  ·
    intro I hI
    simp only [Gset, Finset.mem_filter, Finset.mem_powerset] at hI
    have hIL : ∀ z ∈ I, z.2 < L := fun z hz => Finset.mem_range.mp (Finset.mem_product.mp (hI.1 hz)).2
    ext z
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hzr, ⟨e, _, he⟩ | ⟨w, hw, hwz⟩⟩
      · exact absurd he (lift_ne_rail (Finset.mem_range.mp (Finset.mem_product.mp hzr).2))
      · rw [← rail_inj (hIL w hw) (Finset.mem_range.mp (Finset.mem_product.mp hzr).2) hwz]; exact hw
    · intro hz; exact ⟨hI.1 hz, Or.inr ⟨z, hz, rfl⟩⟩

theorem cov_card (S : Finset (ℕ × ℕ)) (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) : (cov S).card = 2 * S.card := by
  unfold cov
  rw [Finset.card_biUnion (fun e he g hg hne => hS e he g hg hne)]
  rw [Finset.sum_congr rfl (g := fun _ => 2) (fun e he => by unfold verts; exact Finset.card_pair (Nat.ne_of_lt (hlt e he)))]
  simp [mul_comm]

theorem cov_sub (v : ℕ) (S : Finset (ℕ × ℕ)) (hv : ∀ e ∈ S, e.1 < e.2 ∧ e.2 < v) : cov S ⊆ Finset.range v := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
  simp only [verts, Finset.mem_insert, Finset.mem_singleton] at hxe
  have := hv e he
  exact Finset.mem_range.mpr (by rcases hxe with rfl | rfl <;> omega)

theorem part1 (v L : ℕ) (E S : Finset (ℕ × ℕ)) (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < v) (hSE : S ⊆ E) (hS : IsMatch S) :
    ((bigF v L E).filter (fun T => E.filter (fun e => lift L e ∈ T) = S)).card =
      Nat.fib (L + 1) ^ (2 * S.card) * Nat.fib (L + 2) ^ (v - 2 * S.card) := by
  rw [fiber_card v L E S hSE hS, Gset_card' v L (cov S) (cov_sub v S (fun e he => hE e (hSE he))),
    cov_card S hS (fun e he => (hE e (hSE he)).1)]

theorem restrict_mem (v L : ℕ) (E : Finset (ℕ × ℕ)) (T : Finset (ℕ × ℕ)) (hT : T ∈ bigF v L E) :
    E.filter (fun e => lift L e ∈ T) ∈ E.powerset.filter IsMatch := by
  simp only [bigF, Finset.mem_filter, Finset.mem_powerset] at hT
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
  intro e he g hg hne
  obtain ⟨_, heT⟩ := Finset.mem_filter.mp he
  obtain ⟨_, hgT⟩ := Finset.mem_filter.mp hg
  exact lift_disj_rev (hT.2 _ heT _ hgT (fun h => hne (lift_inj h)))

theorem card_le_half (v : ℕ) (S : Finset (ℕ × ℕ)) (hS : IsMatch S) (hv : ∀ e ∈ S, e.1 < e.2 ∧ e.2 < v) :
    S.card ≤ v / 2 := by
  have h1 := cov_card S hS (fun e he => (hv e he).1)
  have h2 := Finset.card_le_card (cov_sub v S hv)
  rw [Finset.card_range] at h2
  omega

theorem part2 (v L : ℕ) (E : Finset (ℕ × ℕ)) (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < v) :
    (bigF v L E).card = (Finset.range (v / 2 + 1)).sum (fun r =>
      ((E.powerset.filter IsMatch).filter (fun S => S.card = r)).card *
        Nat.fib (L + 1) ^ (2 * r) * Nat.fib (L + 2) ^ (v - 2 * r)) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun T => E.filter (fun e => lift L e ∈ T))
    (t := E.powerset.filter IsMatch) (fun T hT => restrict_mem v L E T hT)]
  have hfib : ∀ S ∈ E.powerset.filter IsMatch,
      ((bigF v L E).filter (fun T => E.filter (fun e => lift L e ∈ T) = S)).card =
        Nat.fib (L + 1) ^ (2 * S.card) * Nat.fib (L + 2) ^ (v - 2 * S.card) := by
    intro S hS
    obtain ⟨hSE, hSm⟩ := Finset.mem_filter.mp hS
    exact part1 v L E S hE (Finset.mem_powerset.mp hSE) hSm
  rw [Finset.sum_congr rfl hfib]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.range (v / 2 + 1))]
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_congr rfl (g := fun _ => Nat.fib (L + 1) ^ (2 * r) * Nat.fib (L + 2) ^ (v - 2 * r))
      (fun S hS => by rw [(Finset.mem_filter.mp hS).2])]
    rw [Finset.sum_const, smul_eq_mul, mul_assoc]
  · intro S hS
    obtain ⟨hSE, hSm⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (card_le_half v S hSm (fun e he => hE e (Finset.mem_powerset.mp hSE he))))

def Pset (S : Finset (ℕ × ℕ)) (x : ℕ) : Finset ℕ :=
  (S.filter (fun e => e.1 = x)).image Prod.snd ∪ (S.filter (fun e => e.2 = x)).image Prod.fst

def partner (S : Finset (ℕ × ℕ)) (x : ℕ) : ℕ := if Pset S x = ∅ then x else (Pset S x).sum id

theorem share {S : Finset (ℕ × ℕ)} (hS : IsMatch S) {e e' : ℕ × ℕ} (he : e ∈ S) (he' : e' ∈ S) {x : ℕ}
    (hx : x ∈ verts e) (hx' : x ∈ verts e') : e = e' := by
  by_contra hne
  exact Finset.disjoint_left.mp (hS e he e' he' hne) hx hx'

theorem Pset_fst {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) {e : ℕ × ℕ} (he : e ∈ S) :
    Pset S e.1 = {e.2} := by
  ext y
  simp only [Pset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (⟨e', ⟨he', h1⟩, rfl⟩ | ⟨e', ⟨he', h2⟩, rfl⟩)
    · have := share hS he he' (x := e.1) (by simp [verts]) (by simp [verts, h1])
      rw [← this]
    · have := share hS he he' (x := e.1) (by simp [verts]) (by simp [verts, h2])
      subst this; have := hlt e he; omega
  · rintro rfl; exact Or.inl ⟨e, ⟨he, rfl⟩, rfl⟩

theorem Pset_snd {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) {e : ℕ × ℕ} (he : e ∈ S) :
    Pset S e.2 = {e.1} := by
  ext y
  simp only [Pset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro (⟨e', ⟨he', h1⟩, rfl⟩ | ⟨e', ⟨he', h2⟩, rfl⟩)
    · have := share hS he he' (x := e.2) (by simp [verts]) (by simp [verts, h1])
      subst this; have := hlt e he; omega
    · have := share hS he he' (x := e.2) (by simp [verts]) (by simp [verts, h2])
      rw [← this]
  · rintro rfl; exact Or.inr ⟨e, ⟨he, rfl⟩, rfl⟩

theorem Pset_empty {S : Finset (ℕ × ℕ)} {x : ℕ} (hx : ∀ e ∈ S, x ∉ verts e) : Pset S x = ∅ := by
  ext y
  simp only [Pset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro (⟨e, ⟨he, h1⟩, rfl⟩ | ⟨e, ⟨he, h2⟩, rfl⟩)
  · exact hx e he (by simp [verts, h1])
  · exact hx e he (by simp [verts, h2])

theorem partner_fst {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) {e : ℕ × ℕ} (he : e ∈ S) :
    partner S e.1 = e.2 := by
  unfold partner; rw [Pset_fst hS hlt he]; simp

theorem partner_snd {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) {e : ℕ × ℕ} (he : e ∈ S) :
    partner S e.2 = e.1 := by
  unfold partner; rw [Pset_snd hS hlt he]; simp

theorem partner_free {S : Finset (ℕ × ℕ)} {x : ℕ} (hx : ∀ e ∈ S, x ∉ verts e) : partner S x = x := by
  unfold partner; rw [Pset_empty hx]; simp

theorem partner_invol {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hlt : ∀ e ∈ S, e.1 < e.2) (x : ℕ) :
    partner S (partner S x) = x := by
  by_cases h : ∃ e ∈ S, x ∈ verts e
  · obtain ⟨e, he, hx⟩ := h
    simp only [verts, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · rw [partner_fst hS hlt he, partner_snd hS hlt he]
    · rw [partner_snd hS hlt he, partner_fst hS hlt he]
  · push Not at h
    rw [partner_free h, partner_free h]

theorem partner_lt {v : ℕ} {S : Finset (ℕ × ℕ)} (hS : IsMatch S) (hv : ∀ e ∈ S, e.1 < e.2 ∧ e.2 < v) {x : ℕ}
    (hx : x < v) : partner S x < v := by
  by_cases h : ∃ e ∈ S, x ∈ verts e
  · obtain ⟨e, he, hx'⟩ := h
    simp only [verts, Finset.mem_insert, Finset.mem_singleton] at hx'
    have := hv e he
    rcases hx' with rfl | rfl
    · rw [partner_fst hS (fun e he => (hv e he).1) he]; exact this.2
    · rw [partner_snd hS (fun e he => (hv e he).1) he]; omega
  · push Not at h
    rw [partner_free h]; exact hx

theorem matchings_le_factorial (v : ℕ) (E : Finset (ℕ × ℕ)) (hE : ∀ e ∈ E, e.1 < e.2 ∧ e.2 < v) :
    (E.powerset.filter IsMatch).card ≤ v.factorial := by
  classical
  have key : ∀ S ∈ E.powerset.filter IsMatch, IsMatch S ∧ ∀ e ∈ S, e.1 < e.2 ∧ e.2 < v := by
    intro S hS
    obtain ⟨hSE, hSm⟩ := Finset.mem_filter.mp hS
    exact ⟨hSm, fun e he => hE e (Finset.mem_powerset.mp hSE he)⟩
  let f : (ℕ × ℕ) → ℕ → ℕ := fun _ x => x
  let σ : Finset (ℕ × ℕ) → (Fin v → Fin v) := fun S i =>
    if h : IsMatch S ∧ ∀ e ∈ S, e.1 < e.2 ∧ e.2 < v then ⟨partner S i, partner_lt h.1 h.2 i.2⟩ else i
  have hσ : ∀ S ∈ E.powerset.filter IsMatch, Function.Involutive (σ S) := by
    intro S hS i
    have h := key S hS
    simp only [σ, dif_pos h]
    exact Fin.ext (partner_invol h.1 (fun e he => (h.2 e he).1) i)
  let F : Finset (ℕ × ℕ) → Equiv.Perm (Fin v) := fun S =>
    if h : S ∈ E.powerset.filter IsMatch then Function.Involutive.toPerm (σ S) (hσ S h) else 1
  have ev : ∀ S ∈ E.powerset.filter IsMatch, ∀ i : Fin v, ((F S i : Fin v) : ℕ) = partner S i := by
    intro S hS i
    have h := key S hS
    simp only [F, dif_pos hS, Function.Involutive.coe_toPerm, σ, dif_pos h]
  calc (E.powerset.filter IsMatch).card
      ≤ (Finset.univ : Finset (Equiv.Perm (Fin v))).card := by
        refine Finset.card_le_card_of_injOn F (fun _ _ => Finset.mem_univ _) ?_
        intro S hS S' hS' heq
        have h := key S hS
        have h' := key S' hS'
        have hp : ∀ x, x < v → partner S x = partner S' x := by
          intro x hx
          have := congrArg (fun p : Equiv.Perm (Fin v) => ((p ⟨x, hx⟩ : Fin v) : ℕ)) heq
          rwa [ev S hS, ev S' hS'] at this
        have sub : ∀ (A B : Finset (ℕ × ℕ)), IsMatch A → (∀ e ∈ A, e.1 < e.2 ∧ e.2 < v) → IsMatch B →
            (∀ e ∈ B, e.1 < e.2 ∧ e.2 < v) → (∀ x, x < v → partner A x = partner B x) → A ⊆ B := by
          intro A B hA hAv hB hBv hAB e he
          have h1 := partner_fst hA (fun e he => (hAv e he).1) he
          rw [hAB e.1 (by have := hAv e he; omega)] at h1
          by_cases hc : ∃ g ∈ B, e.1 ∈ verts g
          · obtain ⟨g, hg, hxg⟩ := hc
            simp only [verts, Finset.mem_insert, Finset.mem_singleton] at hxg
            have hgv := hBv g hg
            rcases hxg with h0 | h0
            · rw [h0, partner_fst hB (fun e he => (hBv e he).1) hg] at h1
              have : g = e := Prod.ext h0.symm h1
              rw [← this]; exact hg
            · rw [h0, partner_snd hB (fun e he => (hBv e he).1) hg] at h1
              have := hAv e he; omega
          · push Not at hc
            rw [partner_free hc] at h1
            have := hAv e he; omega
        exact Finset.Subset.antisymm (sub S S' h.1 h.2 h'.1 h'.2 hp)
          (sub S' S h'.1 h'.2 h.1 h.2 (fun x hx => (hp x hx).symm))
    _ = v.factorial := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

def Q (m : ℕ → ℕ) (a b n : ℕ) : ℕ := (Finset.range (n + 1)).sum (fun r => m r * a ^ (2 * r) * b ^ (2 * (n - r)))

theorem Q_succ (m : ℕ → ℕ) (a b n : ℕ) : Q m a b (n + 1) = Q m a b n * b ^ 2 + m (n + 1) * a ^ (2 * (n + 1)) := by
  unfold Q
  rw [Finset.sum_range_succ, Nat.sub_self, Nat.mul_zero, pow_zero, Nat.mul_one, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  rw [show 2 * (n + 1 - r) = 2 * (n - r) + 2 by omega, pow_add]; ring

theorem pow_mod_one {a b : ℕ} (ha : a ^ 2 % b = 1) (hb : 1 < b) (n : ℕ) : a ^ (2 * n) % b = 1 := by
  rw [pow_mul, Nat.pow_mod, ha, one_pow, Nat.one_mod_eq_one.mpr (by omega)]

theorem Q_mod (m : ℕ → ℕ) {a b : ℕ} (ha : a ^ 2 % b = 1) (hb : 1 < b) (n : ℕ) (hm : m n < b) :
    Q m a b n % b = m n := by
  cases n with
  | zero => simp [Q, Nat.mod_eq_of_lt hm]
  | succ n =>
    rw [Q_succ, Nat.add_mod, show Q m a b n * b ^ 2 = (Q m a b n * b) * b by ring, Nat.mul_mod_left, Nat.zero_add,
      Nat.mod_mod, Nat.mul_mod, pow_mod_one ha hb, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hm]

theorem rounds (m : ℕ → ℕ) {a b d : ℕ} (ha : a ^ 2 % b = 1) (hb : 1 < b) (hm : ∀ r ≤ d, m r < b) (z0 : ℕ)
    (hz0 : z0 = Q m a b d) :
    ∀ k, k ≤ d → (Nat.rec (motive := fun _ => ℕ) z0
      (fun roundIndex z => (z - (z % b) * a ^ (2 * (d - roundIndex))) / b ^ 2) k : ℕ) = Q m a b (d - k) := by
  intro k
  induction k with
  | zero => intro _; simpa using hz0
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    simp only at ih' ⊢
    rw [ih']
    obtain ⟨n, hn⟩ : ∃ n, d - k = n + 1 := ⟨d - k - 1, by omega⟩
    rw [hn, Q_mod m ha hb (n + 1) (hm _ (by omega)), Q_succ, Nat.add_sub_cancel,
      Nat.mul_div_cancel _ (by positivity), show d - (k + 1) = n by omega]

theorem big_eq (m : ℕ → ℕ) (a b v : ℕ) :
    (Finset.range (v / 2 + 1)).sum (fun r => m r * a ^ (2 * r) * b ^ (v - 2 * r)) = b ^ (v % 2) * Q m a b (v / 2) := by
  unfold Q
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  rw [show v - 2 * r = v % 2 + 2 * (v / 2 - r) by omega, pow_add]; ring

end PEqualNP.Outside.L_lib_924

theorem PEqualNP.Outside.L_lib_924 : ∀ (v L : Nat) (E : Finset (Nat × Nat)), (∀ e ∈ E, e.1 < e.2 ∧ e.2 < v) →
  let verts := fun e : Nat × Nat => ({e.1,e.2} : Finset Nat)
  let matching := fun S : Finset (Nat × Nat) =>
    ∀ e ∈ S, ∀ g ∈ S, e ≠ g → Disjoint (verts e) (verts g)
  let old := E.powerset.filter matching
  let liftEdge := fun e : Nat × Nat => (e.1*(L+1),e.2*(L+1))
  let rails := ((Finset.range v).product (Finset.range L)).image (fun z =>
    let x := z.1*(L+1)+z.2
    (x,x+1))
  let big := ((E.image liftEdge) ∪ rails).powerset.filter matching
  let freeTail := Nat.fib (L+1)
  let wholePath := Nat.fib (L+2)
  let d := v/2
  let m := fun r : Nat => (old.filter (fun S => S.card = r)).card
  (∀ S ∈ old, (big.filter (fun T => E.filter (fun e => liftEdge e ∈ T) = S)).card =
    freeTail^(2*S.card) * wholePath^(v-2*S.card)) ∧
  big.card = (Finset.range (d+1)).sum (fun r => m r * freeTail^(2*r) * wholePath^(v-2*r)) ∧
  (2 ∣ L → v.factorial < wholePath →
    let q := Nat.rec (motive := fun _ => Nat) (big.card / wholePath^(v % 2))
      (fun roundIndex z => (z - (z % wholePath)*freeTail^(2*(d-roundIndex))) / wholePath^2)
    freeTail^2 % wholePath = 1 ∧ ∀ offset : Nat, offset ≤ d → q offset % wholePath = m (d-offset)) := by
  intro v L E hE verts matching old liftEdge rails big freeTail wholePath d m
  have hold : old = E.powerset.filter PEqualNP.Outside.L_lib_924.IsMatch := rfl
  have hbig : big = PEqualNP.Outside.L_lib_924.bigF v L E := rfl
  have hp2 := PEqualNP.Outside.L_lib_924.part2 v L E hE
  refine ⟨?_, ?_, ?_⟩
  · intro S hS
    rw [hold] at hS
    obtain ⟨hSE, hSm⟩ := Finset.mem_filter.mp hS
    exact PEqualNP.Outside.L_lib_924.part1 v L E S hE (Finset.mem_powerset.mp hSE) hSm
  · exact hp2
  · intro hL hfac
    have hb : 1 < wholePath := lt_of_le_of_lt (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero v)) hfac
    have ha : freeTail ^ 2 % wholePath = 1 := by
      obtain ⟨k, hk⟩ := hL
      show Nat.fib (L + 1) ^ 2 % Nat.fib (L + 2) = 1
      have hb' : 1 < Nat.fib (L + 2) := hb
      subst hk
      rw [PEqualNP.Outside.L_lib_924.cassini_even k, add_comm, Nat.add_mul_mod_self_right,
        Nat.one_mod_eq_one.mpr (by omega)]
    refine ⟨ha, ?_⟩
    intro offset hoff
    have hm : ∀ r ≤ d, m r < wholePath := fun r _ =>
      lt_of_le_of_lt ((Finset.card_filter_le _ _).trans
        (PEqualNP.Outside.L_lib_924.matchings_le_factorial v E hE)) hfac
    have hz0 : big.card / wholePath ^ (v % 2) = PEqualNP.Outside.L_lib_924.Q m freeTail wholePath d := by
      rw [hbig, hp2, PEqualNP.Outside.L_lib_924.big_eq]
      exact Nat.mul_div_cancel_left _ (by positivity)
    have hr := PEqualNP.Outside.L_lib_924.rounds m ha hb hm _ hz0 offset hoff
    show (Nat.rec (motive := fun _ => Nat) (big.card / wholePath ^ (v % 2))
      (fun roundIndex z => (z - (z % wholePath) * freeTail ^ (2 * (d - roundIndex))) / wholePath ^ 2) offset : ℕ) % wholePath = _
    rw [hr]
    exact PEqualNP.Outside.L_lib_924.Q_mod m ha hb _ (hm _ (Nat.sub_le _ _))
