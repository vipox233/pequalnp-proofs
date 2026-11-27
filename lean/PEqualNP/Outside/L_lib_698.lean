import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_698

open Finset

abbrev V8 := Fin 8 → ZMod 2

def u8 (i : Fin 8) : V8 := fun j => if j = i then 1 else 0

def outL (z : Fin 8 → V8) (i : Fin 8) : V8 := z i + u8 i

def inL (c : V8) (z : Fin 8 → V8) (j : Fin 8) : V8 := c + z j

lemma u8_inj {i j : Fin 8} (h : u8 i = u8 j) : i = j := by
  by_contra hne
  have := congrFun h i
  simp [u8, hne] at this

lemma hit_iff (c : V8) (z : Fin 8 → V8) (i j : Fin 8) :
    c + z i + z j = u8 i ↔ outL z i = inL c z j := by
  unfold outL inL
  rw [funext_iff, funext_iff]
  refine forall_congr' (fun k => ?_)
  simp only [Pi.add_apply]
  generalize c k = a, z i k = b, z j k = d, u8 i k = e
  revert a b d e
  decide

lemma loop_iff (c : V8) (z : Fin 8 → V8) (i : Fin 8) :
    outL z i = inL c z i ↔ c = u8 i := by
  unfold outL inL
  rw [funext_iff, funext_iff]
  refine forall_congr' (fun k => ?_)
  simp only [Pi.add_apply]
  generalize c k = a, z i k = b, u8 i k = e
  revert a b e
  decide

lemma loop_unique {c : V8} {z : Fin 8 → V8} {i j : Fin 8}
    (hi : outL z i = inL c z i) (hj : outL z j = inL c z j) : i = j :=
  u8_inj (((loop_iff c z i).1 hi).symm.trans ((loop_iff c z j).1 hj))

lemma asym {c : V8} {z : Fin 8 → V8} {x y : Fin 8}
    (h1 : c + z x + z y = u8 x) (h2 : c + z y + z x = u8 y) : x = y := by
  apply u8_inj
  rw [← h1, ← h2, add_right_comm]

lemma labels_card (c : V8) (z : Fin 8 → V8) (L : Finset V8)
    (ho : ∀ i, outL z i ∈ L) (hi : ∀ i, inL c z i ∈ L) : 8 ≤ L.card := by
  obtain ⟨l0, hl0⟩ : ∃ l, l = inL c z 0 := ⟨_, rfl⟩
  have hl0L : l0 ∈ L := hl0 ▸ hi 0
  obtain ⟨S, hS⟩ : ∃ S : Finset V8, S = (L.erase l0).image (fun v => v - l0) := ⟨_, rfl⟩
  have hW : ∀ v ∈ L, v - l0 ∈ Submodule.span (ZMod 2) (S : Set V8) := by
    intro v hv
    by_cases h : v = l0
    · rw [h, sub_self]; exact Submodule.zero_mem _
    · apply Submodule.subset_span
      rw [hS, coe_image]
      exact ⟨v, mem_erase.2 ⟨h, hv⟩, rfl⟩
  have hf : LinearIndependent (ZMod 2) (fun k : Fin 7 => u8 k.succ + u8 0) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k
    have h := congrFun hg k.succ
    simpa [u8, Finset.sum_apply, Fin.succ_ne_zero, Fin.succ_inj] using h
  have hrange : Submodule.span (ZMod 2) (Set.range (fun k : Fin 7 => u8 k.succ + u8 0)) ≤
      Submodule.span (ZMod 2) (S : Set V8) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have key : u8 k.succ + u8 0 = (outL z k.succ - l0) + (inL c z k.succ - l0) +
        ((outL z 0 - l0) + (inL c z 0 - l0)) := by
      funext m
      simp only [outL, inL, Pi.add_apply, Pi.sub_apply]
      generalize c m = a, z k.succ m = b, z 0 m = d, u8 k.succ m = e1, u8 0 m = e0, l0 m = w
      revert a b d e1 e0 w
      decide
    change u8 k.succ + u8 0 ∈ Submodule.span (ZMod 2) (S : Set V8)
    rw [key]
    exact Submodule.add_mem _ (Submodule.add_mem _ (hW _ (ho _)) (hW _ (hi _)))
      (Submodule.add_mem _ (hW _ (ho _)) (hW _ (hi _)))
  have h1 := finrank_span_eq_card hf
  have h2 := Submodule.finrank_mono hrange
  have h3 := finrank_span_finset_le_card (R := ZMod 2) S
  have h4 : S.card ≤ (L.erase l0).card := hS ▸ card_image_le
  have h5 : (L.erase l0).card = L.card - 1 := card_erase_of_mem hl0L
  rw [Fintype.card_fin] at h1
  have h6 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S : Set V8)) ≤ S.card := h3
  omega

def pc (z : Fin 8 → V8) (v : V8) : ℕ := (univ.filter (fun i => outL z i = v)).card

def qc (c : V8) (z : Fin 8 → V8) (v : V8) : ℕ := (univ.filter (fun i => inL c z i = v)).card

def hits (c : V8) (z : Fin 8 → V8) : Finset (Fin 8 × Fin 8) :=
  univ.filter (fun p => p.1 ≠ p.2 ∧ c + z p.1 + z p.2 = u8 p.1)

def Big (c : V8) (z : Fin 8 → V8) : Prop := ∃ v, 9 ≤ pc z v + qc c z v

lemma s_split (c : V8) (z : Fin 8 → V8) (v : V8) :
    pc z v + qc c z v = (univ.filter (fun i => outL z i = v ∨ inL c z i = v)).card +
      (univ.filter (fun i => outL z i = v ∧ inL c z i = v)).card := by
  rw [filter_or, filter_and, card_union_add_card_inter]
  rfl

lemma and_le_one (c : V8) (z : Fin 8 → V8) (v : V8) :
    (univ.filter (fun i => outL z i = v ∧ inL c z i = v)).card ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  simp only [mem_filter, mem_univ, true_and] at ha hb
  exact loop_unique (ha.1.trans ha.2.symm) (hb.1.trans hb.2.symm)

lemma s_le_nine (c : V8) (z : Fin 8 → V8) (v : V8) : pc z v + qc c z v ≤ 9 := by
  rw [s_split]
  have h1 := and_le_one c z v
  have h2 := card_le_univ (univ.filter (fun i => outL z i = v ∨ inL c z i = v))
  rw [Fintype.card_fin] at h2
  omega

lemma big_struct (c : V8) (z : Fin 8 → V8) (v : V8) (hv : 9 ≤ pc z v + qc c z v) :
    (∃ s, outL z s = v ∧ inL c z s = v) ∧ (∀ i, outL z i = v ∨ inL c z i = v) := by
  rw [s_split] at hv
  have h1 := and_le_one c z v
  have h2 := card_le_univ (univ.filter (fun i => outL z i = v ∨ inL c z i = v))
  rw [Fintype.card_fin] at h2
  constructor
  · have : 0 < (univ.filter (fun i => outL z i = v ∧ inL c z i = v)).card := by omega
    obtain ⟨s, hs⟩ := card_pos.1 this
    exact ⟨s, (mem_filter.1 hs).2⟩
  · have h3 : (univ.filter (fun i => outL z i = v ∨ inL c z i = v)) = univ := by
      apply eq_univ_of_card
      rw [Fintype.card_fin]
      omega
    intro i
    have : i ∈ univ.filter (fun i => outL z i = v ∨ inL c z i = v) := by
      rw [h3]; exact mem_univ i
    exact (mem_filter.1 this).2

lemma A_card (c : V8) (z : Fin 8 → V8) :
    (univ.filter (fun p : Fin 8 × Fin 8 => outL z p.1 = inL c z p.2)).card =
      ∑ v, pc z v * qc c z v := by
  rw [card_eq_sum_card_fiberwise (f := fun p : Fin 8 × Fin 8 => outL z p.1) (t := univ)
    (by intro x _; simp)]
  refine sum_congr rfl (fun v _ => ?_)
  rw [pc, qc, ← card_product]
  congr 1
  ext ⟨i, j⟩
  simp only [mem_filter, mem_univ, true_and, mem_product]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1.symm.trans h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans h2.symm, h1⟩

lemma num1 : ∀ p q : ℕ, p + q ≤ 9 →
    2 * (p * q) + 5 * (if 0 < p + q then 1 else 0) ≤ 5 * (p + q) := by
  intro p q h
  have hp : p ≤ 9 := by omega
  have hq : q ≤ 9 := by omega
  interval_cases p <;> interval_cases q <;> simp_all

lemma num2 : ∀ p q : ℕ, p + q ≤ 8 →
    7 * (p * q) + 16 * (if 0 < p + q then 1 else 0) ≤ 16 * (p + q) := by
  intro p q h
  have hp : p ≤ 8 := by omega
  have hq : q ≤ 8 := by omega
  interval_cases p <;> interval_cases q <;> simp_all

lemma hits_le (c : V8) (z : Fin 8 → V8) :
    (hits c z).card ≤ 19 ∧ (¬ Big c z → (hits c z).card ≤ 18) := by
  have hHA : hits c z ⊆ univ.filter (fun p : Fin 8 × Fin 8 => outL z p.1 = inL c z p.2) := by
    intro p hp
    simp only [hits, mem_filter, mem_univ, true_and] at hp ⊢
    exact (hit_iff c z p.1 p.2).1 hp.2
  have hA := A_card c z
  have hL : 8 ≤ (univ.filter (fun v : V8 => 0 < pc z v + qc c z v)).card := by
    apply labels_card c z
    · intro i
      simp only [mem_filter, mem_univ, true_and]
      have : 0 < pc z (outL z i) := card_pos.2 ⟨i, by simp⟩
      omega
    · intro i
      simp only [mem_filter, mem_univ, true_and]
      have : 0 < qc c z (inL c z i) := card_pos.2 ⟨i, by simp⟩
      omega
  rw [card_filter] at hL
  have hsp : ∑ v, pc z v = 8 := by
    have := card_eq_sum_card_fiberwise (f := outL z) (s := univ) (t := univ)
      (by intro x _; simp)
    rw [card_univ, Fintype.card_fin] at this
    exact this.symm
  have hsq : ∑ v, qc c z v = 8 := by
    have := card_eq_sum_card_fiberwise (f := inL c z) (s := univ) (t := univ)
      (by intro x _; simp)
    rw [card_univ, Fintype.card_fin] at this
    exact this.symm
  have e2 : ∑ v, 5 * (pc z v + qc c z v) = 5 * (∑ v, pc z v + ∑ v, qc c z v) := by
    rw [← mul_sum, sum_add_distrib]
  have e3 : ∑ v, 16 * (pc z v + qc c z v) = 16 * (∑ v, pc z v + ∑ v, qc c z v) := by
    rw [← mul_sum, sum_add_distrib]
  have e1 : ∑ v, (2 * (pc z v * qc c z v) + 5 * (if 0 < pc z v + qc c z v then 1 else 0)) =
      2 * ∑ v, pc z v * qc c z v + 5 * ∑ v, (if 0 < pc z v + qc c z v then 1 else 0) := by
    rw [sum_add_distrib, mul_sum, mul_sum]
  have e4 : ∑ v, (7 * (pc z v * qc c z v) + 16 * (if 0 < pc z v + qc c z v then 1 else 0)) =
      7 * ∑ v, pc z v * qc c z v + 16 * ∑ v, (if 0 < pc z v + qc c z v then 1 else 0) := by
    rw [sum_add_distrib, mul_sum, mul_sum]
  have hs1 := sum_le_sum (s := univ) (fun v _ => num1 (pc z v) (qc c z v) (s_le_nine c z v))
  rw [e1, e2] at hs1
  have hHle := card_le_card hHA
  have part2 : ¬ Big c z → (hits c z).card ≤ 18 := by
    intro hB
    have hle8 : ∀ v, pc z v + qc c z v ≤ 8 := by
      intro v
      by_contra hcon
      exact hB ⟨v, by omega⟩
    have hs2 := sum_le_sum (s := univ) (fun v _ => num2 (pc z v) (qc c z v) (hle8 v))
    rw [e4, e3] at hs2
    omega
  refine ⟨?_, part2⟩
  by_cases hB : Big c z
  · obtain ⟨v, hv⟩ := hB
    obtain ⟨⟨s, hs1', hs2'⟩, -⟩ := big_struct c z v hv
    have hss : hits c z ⊂ univ.filter (fun p : Fin 8 × Fin 8 => outL z p.1 = inL c z p.2) := by
      rw [ssubset_iff_of_subset hHA]
      refine ⟨(s, s), ?_, ?_⟩
      · simp only [mem_filter, mem_univ, true_and]
        exact hs1'.trans hs2'.symm
      · simp [hits]
    have := card_lt_card hss
    omega
  · have := part2 hB
    omega

def col (c : V8) (z : Fin 8 → V8) (v : V8) (x : Fin 8) : Fin 3 :=
  if outL z x = v ∧ inL c z x ≠ v then 0 else if inL c z x = v ∧ outL z x ≠ v then 1 else 2

lemma col_spec (c : V8) (z : Fin 8 → V8) (v : V8) (hall : ∀ i, outL z i = v ∨ inL c z i = v)
    (x : Fin 8) :
    (col c z v x = 0 ∧ outL z x = v ∧ inL c z x ≠ v) ∨
    (col c z v x = 1 ∧ inL c z x = v ∧ outL z x ≠ v) ∨
    (col c z v x = 2 ∧ outL z x = v ∧ inL c z x = v) := by
  unfold col
  split_ifs with h1 h2
  · exact Or.inl ⟨rfl, h1⟩
  · exact Or.inr (Or.inl ⟨rfl, h2⟩)
  · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    have h3 := hall x
    tauto

lemma col_two (c : V8) (z : Fin 8 → V8) (v : V8) (hall : ∀ i, outL z i = v ∨ inL c z i = v)
    (x : Fin 8) (h : col c z v x = 2) : outL z x = inL c z x := by
  rcases col_spec c z v hall x with ⟨hx, _, _⟩ | ⟨hx, _, _⟩ | ⟨_, h1, h2⟩
  · rw [hx] at h; exact absurd h (by decide)
  · rw [hx] at h; exact absurd h (by decide)
  · exact h1.trans h2.symm

lemma col_nohit (c : V8) (z : Fin 8 → V8) (v : V8) (hall : ∀ i, outL z i = v ∨ inL c z i = v)
    {x y : Fin 8} (hxy : x ≠ y) (hc : col c z v x = col c z v y) :
    c + z x + z y ≠ u8 x := by
  intro hh
  have h := (hit_iff c z x y).1 hh
  rcases col_spec c z v hall x with ⟨hx, hx1, hx2⟩ | ⟨hx, hx1, hx2⟩ | ⟨hx, hx1, hx2⟩ <;>
  rcases col_spec c z v hall y with ⟨hy, hy1, hy2⟩ | ⟨hy, hy1, hy2⟩ | ⟨hy, hy1, hy2⟩
  all_goals first
    | (rw [hx, hy] at hc; exact absurd hc (by decide))
    | exact hy2 (h.symm.trans hx1)
    | exact hx2 (h.trans hy1)
    | exact hxy (loop_unique (hx1.trans hx2.symm) (hy1.trans hy2.symm))

lemma fin3_ne_two : ∀ t : Fin 3, ¬ t = 2 → t ∈ ({0, 1} : Finset (Fin 3)) := by decide

theorem core8 (c : Fin 3 → V8) (z : Fin 3 → Fin 8 → V8) :
    ∃ i j : Fin 8, i ≠ j ∧ ∀ a, c a + z a i + z a j ≠ u8 i := by
  by_contra hcon
  simp only [not_exists, not_and, not_forall, not_not] at hcon
  have key : ∀ a1 a2 : Fin 3, a1 ≠ a2 → Big (c a1) (z a1) → Big (c a2) (z a2) → False := by
    intro a1 a2 h12 hB1 hB2
    obtain ⟨v1, hv1⟩ := hB1
    obtain ⟨v2, hv2⟩ := hB2
    have hall1 := (big_struct _ _ v1 hv1).2
    have hall2 := (big_struct _ _ v2 hv2).2
    have hT : 7 ≤ (univ.filter (fun x => ¬ col (c a2) (z a2) v2 x = 2)).card := by
      have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin 8)))
        (fun x => col (c a2) (z a2) v2 x = 2)
      have h2 : (univ.filter (fun x => col (c a2) (z a2) v2 x = 2)).card ≤ 1 := by
        rw [card_le_one]
        intro x hx y hy
        simp only [mem_filter, mem_univ, true_and] at hx hy
        exact loop_unique (col_two _ _ _ hall2 x hx) (col_two _ _ _ hall2 y hy)
      rw [card_univ, Fintype.card_fin] at h
      omega
    have hmap : Set.MapsTo (fun x => (col (c a1) (z a1) v1 x, col (c a2) (z a2) v2 x))
        ((univ.filter (fun x => ¬ col (c a2) (z a2) v2 x = 2) : Finset (Fin 8)) : Set (Fin 8))
        (((univ : Finset (Fin 3)) ×ˢ ({0, 1} : Finset (Fin 3)) : Finset (Fin 3 × Fin 3)) :
          Set (Fin 3 × Fin 3)) := by
      intro x hx
      simp only [mem_coe, mem_filter, mem_univ, true_and] at hx
      simp only [mem_coe, mem_product, mem_univ, true_and]
      exact fin3_ne_two _ hx
    have hcard : ((univ : Finset (Fin 3)) ×ˢ ({0, 1} : Finset (Fin 3))).card = 6 := by rfl
    obtain ⟨x, -, y, -, hxy, hf⟩ := exists_ne_map_eq_of_card_lt_of_maps_to (by omega) hmap
    simp only [Prod.mk.injEq] at hf
    obtain ⟨b, hb⟩ := hcon x y hxy
    obtain ⟨b', hb'⟩ := hcon y x (Ne.symm hxy)
    have nb1 : b ≠ a1 := by
      rintro rfl; exact col_nohit _ _ _ hall1 hxy hf.1 hb
    have nb2 : b ≠ a2 := by
      rintro rfl; exact col_nohit _ _ _ hall2 hxy hf.2 hb
    have nb1' : b' ≠ a1 := by
      rintro rfl; exact col_nohit _ _ _ hall1 (Ne.symm hxy) hf.1.symm hb'
    have nb2' : b' ≠ a2 := by
      rintro rfl; exact col_nohit _ _ _ hall2 (Ne.symm hxy) hf.2.symm hb'
    have hbb : b = b' := by
      rw [Ne, Fin.ext_iff] at nb1 nb2 nb1' nb2' h12
      apply Fin.ext
      have := b.isLt
      have := b'.isLt
      have := a1.isLt
      have := a2.isLt
      omega
    subst hbb
    exact hxy (asym hb hb')
  have hcover : univ.filter (fun p : Fin 8 × Fin 8 => p.1 ≠ p.2) ⊆
      univ.biUnion (fun a => hits (c a) (z a)) := by
    intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨a, ha⟩ := hcon p.1 p.2 hp
    simp only [mem_biUnion, mem_univ, true_and]
    refine ⟨a, ?_⟩
    simp only [hits, mem_filter, mem_univ, true_and]
    exact ⟨hp, ha⟩
  have h56 : (univ.filter (fun p : Fin 8 × Fin 8 => p.1 ≠ p.2)).card = 56 := by decide
  have hle := (card_le_card hcover).trans card_biUnion_le
  rw [Fin.sum_univ_three, h56] at hle
  obtain ⟨b0, n0⟩ := hits_le (c 0) (z 0)
  obtain ⟨b1, n1⟩ := hits_le (c 1) (z 1)
  obtain ⟨b2, n2⟩ := hits_le (c 2) (z 2)
  by_cases B0 : Big (c 0) (z 0) <;> by_cases B1 : Big (c 1) (z 1) <;>
    by_cases B2 : Big (c 2) (z 2)
  · exact key 0 1 (by decide) B0 B1
  · exact key 0 1 (by decide) B0 B1
  · exact key 0 2 (by decide) B0 B2
  · have := n1 B1; have := n2 B2; omega
  · exact key 1 2 (by decide) B1 B2
  · have := n0 B0; have := n2 B2; omega
  · have := n0 B0; have := n1 B1; omega
  · have := n0 B0; have := n1 B1; have := n2 B2; omega

lemma restrict (n : ℕ) (c : Fin 3 → Fin n → ZMod 2) (z : Fin 3 → Fin n → Fin n → ZMod 2)
    (e : Fin 8 → Fin n) (he : Function.Injective e) :
    ∃ i j : Fin 8, e i ≠ e j ∧
      ∀ a, c a + z a (e i) + z a (e j) ≠ fun k => if k = e i then (1 : ZMod 2) else 0 := by
  obtain ⟨i, j, hij, h⟩ := core8 (fun a k => c a (e k)) (fun a p k => z a (e p) (e k))
  refine ⟨i, j, he.ne hij, fun a ha => h a ?_⟩
  funext k
  have hk := congrFun ha (e k)
  simp only [Pi.add_apply] at hk ⊢
  rw [hk]
  simp only [u8, he.eq_iff]

lemma pair_count (n : ℕ) (a b : Fin n) (hab : a ≠ b) :
    ((powersetCard 8 (univ : Finset (Fin n))).filter (fun T => a ∈ T ∧ b ∈ T)).card ≤
      (n - 2).choose 6 := by
  have ht : (powersetCard 6 ((univ.erase a).erase b)).card = (n - 2).choose 6 := by
    rw [card_powersetCard, card_erase_of_mem (mem_erase.2 ⟨hab.symm, mem_univ b⟩),
      card_erase_of_mem (mem_univ a), card_univ, Fintype.card_fin]
    congr 1
  rw [← ht]
  apply card_le_card_of_injOn (fun T => (T.erase a).erase b)
  · intro T hT
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powersetCard] at hT
    simp only [mem_coe, mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [mem_erase] at hx ⊢
      exact ⟨hx.1, hx.2.1, mem_univ _⟩
    · rw [card_erase_of_mem (mem_erase.2 ⟨hab.symm, hT.2.2⟩), card_erase_of_mem hT.2.1, hT.1.2]
  · intro T hT T' hT' h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_powersetCard] at hT hT'
    have e1 : T = insert a (insert b ((T.erase a).erase b)) := by
      rw [insert_erase (mem_erase.2 ⟨hab.symm, hT.2.2⟩), insert_erase hT.2.1]
    have e2 : T' = insert a (insert b ((T'.erase a).erase b)) := by
      rw [insert_erase (mem_erase.2 ⟨hab.symm, hT'.2.2⟩), insert_erase hT'.2.1]
    simp only at h
    rw [e1, e2, h]

theorem main (n : ℕ) (hn : 8 ≤ n) (c : Fin 3 → Fin n → ZMod 2)
    (z : Fin 3 → Fin n → Fin n → ZMod 2) :
    n * (n - 1) ≤ 56 * ((univ : Finset (Fin n × Fin n)).filter (fun p =>
      p.1 ≠ p.2 ∧ ∀ a, c a + z a p.1 + z a p.2 ≠
        (fun (i j : Fin n) => if j = i then (1 : ZMod 2) else 0) p.1)).card := by
  obtain ⟨M, hM⟩ : ∃ M : Finset (Fin n × Fin n), M = (univ : Finset (Fin n × Fin n)).filter
      (fun p => p.1 ≠ p.2 ∧ ∀ a, c a + z a p.1 + z a p.2 ≠
        (fun (i j : Fin n) => if j = i then (1 : ZMod 2) else 0) p.1) := ⟨_, rfl⟩
  rw [← hM]
  have hdc : (powersetCard 8 (univ : Finset (Fin n))).card * 1 ≤ M.card * (n - 2).choose 6 := by
    apply card_mul_le_card_mul (fun (T : Finset (Fin n)) (p : Fin n × Fin n) => p.1 ∈ T ∧ p.2 ∈ T)
    · intro T hT
      rw [mem_powersetCard] at hT
      obtain ⟨i, j, hij, hmiss⟩ :=
        restrict n c z (T.orderEmbOfFin hT.2) (T.orderEmbOfFin hT.2).injective
      apply card_pos.2
      refine ⟨(T.orderEmbOfFin hT.2 i, T.orderEmbOfFin hT.2 j), ?_⟩
      simp only [bipartiteAbove, mem_filter]
      refine ⟨?_, orderEmbOfFin_mem _ _ _, orderEmbOfFin_mem _ _ _⟩
      rw [hM, mem_filter]
      exact ⟨mem_univ _, hij, hmiss⟩
    · intro p hp
      rw [hM, mem_filter] at hp
      exact pair_count n p.1 p.2 hp.2.1
  rw [card_powersetCard, card_univ, Fintype.card_fin, mul_one] at hdc
  have hid : n.choose 8 * 28 = n.choose 2 * (n - 2).choose 6 := by
    have := Nat.choose_mul (n := n) (k := 8) (s := 2) (by norm_num)
    rw [show Nat.choose 8 2 = 28 by rfl, show 8 - 2 = 6 by rfl] at this
    exact this
  have h2 : n.choose 2 * 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd
  have hpos : 0 < (n - 2).choose 6 := Nat.choose_pos (by omega)
  have h3 : n * (n - 1) * (n - 2).choose 6 ≤ 56 * M.card * (n - 2).choose 6 := by
    rw [← h2]
    nlinarith [hid, hdc]
  exact Nat.le_of_mul_le_mul_right h3 hpos

end PEqualNP.Outside.L_lib_698

open PEqualNP.Outside.L_lib_698

theorem PEqualNP.Outside.L_lib_698 : (∀ n : Nat, 8 ≤ n →
  let V := Fin n → ZMod 2
  let unit := fun (i j : Fin n) => if j = i then (1 : ZMod 2) else 0
  ∀ (c : Fin 3 → V) (z : Fin 3 → Fin n → V),
    let missed := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p =>
      p.1 ≠ p.2 ∧ ∀ a, c a + z a p.1 + z a p.2 ≠ unit p.1)
    n*(n-1) ≤ 56*missed.card) := by
  intro n hn V unit c z missed
  exact main n hn c z
