import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_714.Affine

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

end PEqualNP.Outside.L_lib_714.Affine


namespace PEqualNP.Outside.L_lib_714.Matching

variable {α β : Type*} [Fintype α]

noncomputable def cost (event : α → Prop) : Nat := by
  classical
  exact ∑ point, if event point then 1 else 0

lemma cost_card (event : α → Prop) [DecidablePred event] :
    cost event = (Finset.univ.filter event).card := by
  calc
    _ = ∑ point, if event point then 1 else 0 := by
      unfold cost
      apply Finset.sum_congr rfl
      intro point _
      by_cases yes : event point <;> simp [yes]
    _ = _ := by simpa only [Nat.cast_id] using Finset.sum_boole (R := Nat) event Finset.univ

lemma cost_transport (event : α → Prop) (perm : Equiv.Perm α) :
    cost (fun point => event (perm point)) = cost event := by
  classical
  exact Equiv.sum_comp perm (fun point => if event point then 1 else 0)

lemma cost_mono {left right : α → Prop} (imp : ∀ point, left point → right point) :
    cost left ≤ cost right := by
  classical
  unfold cost
  exact Finset.sum_le_sum fun point _ => by specialize imp point; split_ifs <;> simp_all

lemma cost_split {event left right : α → Prop}
    (imp : ∀ point, event point → left point ∨ right point) :
    cost event ≤ cost left + cost right := by
  classical
  unfold cost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun point _ => by specialize imp point; split_ifs <;> simp_all

def permute {ι : Type*} (relabel : Equiv.Perm ι) : Equiv.Perm (Equiv.Perm ι) where
  toFun perm := relabel.trans perm
  invFun perm := relabel.symm.trans perm
  left_inv perm := by ext; simp
  right_inv perm := by ext; simp

variable {b : Nat} {V : Type*} [AddCommGroup V]

abbrev Vertex (size : Nat) := Fin size × Bool
abbrev Match (size : Nat) := Equiv.Perm (Vertex size)

def score (table : Vertex b → Vertex b → V) (perm : Match b) :=
  ∑ slot, table (perm (slot,false)) (perm (slot,true))

lemma compare_scores (table : Vertex b → Vertex b → V) (target : V)
    (left right : Match b) (event : Match b → Prop)
    (witness : ∀ perm, event perm → score table (left.trans perm) ≠ score table (right.trans perm)) :
    cost event ≤ 2 * cost (fun perm => score table perm ≠ target) := by
  let bad := fun perm => score table perm ≠ target
  have bound := cost_split (left := fun perm => bad (permute left perm))
    (right := fun perm => bad (permute right perm)) (event := event) (by
      intro perm hit
      change score table (left.trans perm) ≠ target ∨ score table (right.trans perm) ≠ target
      by_contra! contra
      exact witness perm hit (contra.1.trans contra.2.symm))
  rw [cost_transport, cost_transport] at bound
  simpa [bad, two_mul] using bound

def edge (table : Vertex b → Vertex b → V) (first last : Vertex b) (perm : Match b) :=
  table (perm first) (perm last)

lemma reversal (table : Vertex b → Vertex b → V) (target : V) (slot : Fin b)
    {first last : Vertex b} (hne : first ≠ last) :
    cost (fun perm => edge table first last perm ≠ edge table last first perm) ≤
      2 * cost (fun perm => score table perm ≠ target) := by
  classical
  let src : Bool → Vertex b := fun side => (slot, side)
  let dst : Bool → Vertex b := fun side => if side then last else first
  obtain ⟨arrange, ha⟩ := Equiv.Perm.exists_extending_pair src dst
    (fun _ _ hh => congrArg Prod.snd hh) (by intro x y hh; cases x <;> cases y <;> simp_all [dst])
  let flip := Equiv.swap (slot,false) (slot,true)
  apply compare_scores table target arrange (flip.trans arrange)
  intro perm hit eqn
  let term := fun (map : Match b) (idx : Fin b) => table (map (idx,false)) (map (idx,true))
  change (∑ idx, term (arrange.trans perm) idx) = ∑ idx, term ((flip.trans arrange).trans perm) idx at eqn
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ slot),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ slot)] at eqn
  have rest : (∑ idx ∈ Finset.univ.erase slot, term (arrange.trans perm) idx) =
      ∑ idx ∈ Finset.univ.erase slot, term ((flip.trans arrange).trans perm) idx := by
    apply Finset.sum_congr rfl
    intro idx hi
    have hn := (Finset.mem_erase.mp hi).1
    simp [term, flip, Equiv.swap_apply_def, hn]
  rw [rest] at eqn
  have loc := add_right_cancel eqn
  have hl : arrange (slot,false) = first := ha false
  have hr : arrange (slot,true) = last := ha true
  exact hit (by simpa [term, flip, hl, hr, edge] using loc)

lemma rectangle (table : Vertex b → Vertex b → V) (target : V) {slot next : Fin b}
    (hs : slot ≠ next) {aa bb cc dd : Vertex b}
    (hab : aa ≠ bb) (hac : aa ≠ cc) (had : aa ≠ dd)
    (hbc : bb ≠ cc) (hbd : bb ≠ dd) (hcd : cc ≠ dd) :
    cost (fun perm => edge table aa bb perm + edge table cc dd perm ≠
      edge table aa dd perm + edge table cc bb perm) ≤
      2 * cost (fun perm => score table perm ≠ target) := by
  classical
  let src : Fin 4 → Vertex b := ![(slot,false), (slot,true), (next,false), (next,true)]
  let dst : Fin 4 → Vertex b := ![aa, bb, cc, dd]
  obtain ⟨arrange, ha⟩ := Equiv.Perm.exists_extending_pair src dst
    (by intro x y hh; fin_cases x <;> fin_cases y <;> simp_all [src])
    (by intro x y hh; fin_cases x <;> fin_cases y <;> simp_all [dst])
  let flip := Equiv.swap (slot,true) (next,true)
  apply compare_scores table target arrange (flip.trans arrange)
  intro perm hit eqn
  let term := fun (map : Match b) (idx : Fin b) => table (map (idx,false)) (map (idx,true))
  have extract (map : Match b) : (∑ idx, term map idx) =
      term map slot + term map next + ∑ idx ∈ (Finset.univ.erase slot).erase next, term map idx := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ slot),
      ← Finset.add_sum_erase _ _ (show next ∈ Finset.univ.erase slot by simp [Ne.symm hs]), add_assoc]
  change (∑ idx, term (arrange.trans perm) idx) = ∑ idx, term ((flip.trans arrange).trans perm) idx at eqn
  rw [extract, extract] at eqn
  have rest : (∑ idx ∈ (Finset.univ.erase slot).erase next, term (arrange.trans perm) idx) =
      ∑ idx ∈ (Finset.univ.erase slot).erase next, term ((flip.trans arrange).trans perm) idx := by
    apply Finset.sum_congr rfl
    intro idx hi
    obtain ⟨hn, hi⟩ := Finset.mem_erase.mp hi
    have hm := (Finset.mem_erase.mp hi).1
    simp [term, flip, Equiv.swap_apply_def, hm, hn]
  rw [rest] at eqn
  have loc := add_right_cancel eqn
  have h0 : arrange (slot,false) = aa := ha 0
  have h1 : arrange (slot,true) = bb := ha 1
  have h2 : arrange (next,false) = cc := ha 2
  have h3 : arrange (next,true) = dd := ha 3
  exact hit (by simpa [term, flip, Equiv.swap_apply_def, hs, hs.symm, h0, h1, h2, h3, edge] using loc)

def tri (table : Vertex b → Vertex b → V) (anchor row col : Vertex b) (perm : Match b) :=
  edge table row col perm - edge table anchor row perm - edge table anchor col perm

noncomputable def dist (left right : α → β) := cost (fun point => left point ≠ right point)

lemma dist_triangle (left middle right : α → β) :
    dist left right ≤ dist left middle + dist middle right := by
  apply cost_split
  intro point hit
  by_contra! same
  exact hit (same.1.trans same.2)

lemma tri_bound (table : Vertex b → Vertex b → V) (target : V) {slot next : Fin b}
    (hs : slot ≠ next) {anchor first last row col : Vertex b}
    (haf : anchor ≠ first) (hal : anchor ≠ last) (hfl : first ≠ last)
    (har : anchor ≠ row) (hac : anchor ≠ col) (hrc : row ≠ col) :
    dist (tri table anchor row col) (tri table anchor first last) ≤
      13 * cost (fun perm => score table perm ≠ target) := by
  let bad := cost (fun perm => score table perm ≠ target)
  let triangle := tri table anchor
  have rev (ii jj : Vertex b) (hne : ii ≠ jj) : dist (triangle ii jj) (triangle jj ii) ≤ 2 * bad := by
    apply le_trans _ (reversal table target slot hne)
    apply cost_mono
    intro perm hit same
    apply hit
    change edge table ii jj perm - _ - _ = edge table jj ii perm - _ - _
    rw [same]
    abel
  have column (ii jj kk : Vertex b) (hai : anchor ≠ ii) (haj : anchor ≠ jj) (hak : anchor ≠ kk)
      (hij : ii ≠ jj) (hik : ii ≠ kk) : dist (triangle ii jj) (triangle ii kk) ≤ 2 * bad := by
    by_cases hjk : jj = kk
    · subst kk; simp [dist, cost]
    apply le_trans _ (rectangle table target hs haj hai hak hij.symm hjk hik)
    apply cost_mono
    intro perm hit same
    apply hit
    change edge table ii jj perm - _ - _ = edge table ii kk perm - _ - _
    change edge table anchor jj perm + edge table ii kk perm =
      edge table anchor kk perm + edge table ii jj perm at same
    have swap : edge table ii jj perm = (edge table anchor jj perm + edge table ii kk perm) -
        edge table anchor kk perm := by rw [same]; abel
    rw [swap]
    abel
  have line (ii jj kk : Vertex b) (hai : anchor ≠ ii) (haj : anchor ≠ jj) (hak : anchor ≠ kk)
      (hij : ii ≠ jj) (hik : ii ≠ kk) : dist (triangle jj ii) (triangle kk ii) ≤ 6 * bad := by
    have h1 := rev jj ii hij.symm
    have h2 := column ii jj kk hai haj hak hij hik
    have h3 := rev ii kk hik
    have h4 := dist_triangle (triangle jj ii) (triangle ii jj) (triangle ii kk)
    have h5 := dist_triangle (triangle jj ii) (triangle ii kk) (triangle kk ii)
    omega
  change dist (triangle row col) (triangle first last) ≤ 13 * bad
  by_cases hrl : row = last
  · subst row
    by_cases hcf : col = first
    · subst col; have hh := rev last first hfl.symm; omega
    have h1 := line col last first hac hal haf hrc.symm hcf
    have h2 := column first col last haf hac hal (Ne.symm hcf) hfl
    have h3 := dist_triangle (triangle last col) (triangle first col) (triangle first last)
    omega
  have h1 := column row col last har hac hal hrc hrl
  have h2 := line last row first hal har haf (Ne.symm hrl) hfl.symm
  have h3 := dist_triangle (triangle row col) (triangle row last) (triangle first last)
  omega

lemma average {ι π : Type*} [Fintype ι] [Fintype π] [Nonempty π]
    (event : π → ι → Prop) (budget : ι → Nat)
    (bounds : ∀ idx, cost (fun perm => event perm idx) ≤ budget idx) :
    ∃ perm, cost (event perm) * Fintype.card π ≤ ∑ idx, budget idx := by
  classical
  obtain ⟨best, _, least⟩ := Finset.univ.exists_min_image (fun perm => cost (event perm))
    Finset.univ_nonempty
  refine ⟨best, ?_⟩
  calc
    _ = ∑ _ : π, cost (event best) := by simp [Nat.mul_comm]
    _ ≤ ∑ perm : π, cost (event perm) := Finset.sum_le_sum fun perm hp => least perm hp
    _ = ∑ idx, cost (fun perm => event perm idx) := by unfold cost; rw [Finset.sum_comm]
    _ ≤ _ := Finset.sum_le_sum fun idx _ => bounds idx

lemma obtain_table (table : Vertex b → Vertex b → V) (target : V) {slot next : Fin b}
    (hs : slot ≠ next) : ∃ (constant : V) (labels : Vertex b → V),
    cost (fun pair : Vertex b × Vertex b => pair.1 ≠ pair.2 ∧
      table pair.1 pair.2 ≠ constant + labels pair.1 + labels pair.2) * Nat.factorial (2*b) ≤
      13 * cost (fun perm => score table perm ≠ target) * (2*b) * (2*b-1) := by
  classical
  let anchor : Vertex b := (slot,false)
  let first : Vertex b := (slot,true)
  let last : Vertex b := (next,false)
  have haf : anchor ≠ first := by simp [anchor, first]
  have hal : anchor ≠ last := by simp [anchor, last, hs]
  have hfl : first ≠ last := by simp [first, last]
  let constant := tri table anchor first last
  let labels (perm : Match b) (idx : Vertex b) :=
    if idx = anchor then -constant perm else edge table anchor idx perm
  let event (perm : Match b) (pair : Vertex b × Vertex b) :=
    pair.1 ≠ pair.2 ∧ edge table pair.1 pair.2 perm ≠
      constant perm + labels perm pair.1 + labels perm pair.2
  let limit := 13 * cost (fun perm => score table perm ≠ target)
  let budget (pair : Vertex b × Vertex b) := if pair.1 ≠ pair.2 then limit else 0
  have bounds (pair : Vertex b × Vertex b) : cost (fun perm => event perm pair) ≤ budget pair := by
    obtain ⟨row,col⟩ := pair
    by_cases hrc : row = col
    · subst col; simp [event, cost, budget]
    change _ ≤ if row ≠ col then limit else 0
    rw [ite_eq_left hrc]
    by_cases har : anchor = row
    · subst row; simp [event, cost, labels, Ne.symm hrc]
    by_cases hac : anchor = col
    · subst col
      have hh := reversal table target slot hrc
      have ht : cost (fun perm => event perm (row,anchor)) ≤
          cost (fun perm => edge table row anchor perm ≠ edge table anchor row perm) := by
        apply cost_mono
        intro perm hit eqn
        exact hit.2 (by simp [labels, hrc, eqn, add_comm])
      exact ht.trans (hh.trans (Nat.mul_le_mul_right _ (by decide : 2 ≤ 13)))
    apply le_trans _ (tri_bound table target hs haf hal hfl har hac hrc)
    apply cost_mono
    intro perm hit eqn
    apply hit.2
    simp only [labels, ite_eq_right (Ne.symm har), ite_eq_right (Ne.symm hac)]
    change edge table row col perm - edge table anchor row perm - edge table anchor col perm = constant perm at eqn
    rw [← eqn]
    abel
  obtain ⟨best, bound⟩ := average event budget bounds
  refine ⟨constant best, fun idx => labels best (best.symm idx), ?_⟩
  let actual (pair : Vertex b × Vertex b) := pair.1 ≠ pair.2 ∧ table pair.1 pair.2 ≠
    constant best + labels best (best.symm pair.1) + labels best (best.symm pair.2)
  have shift := cost_transport actual (best.prodCongr best)
  have agree : (fun point => actual ((best.prodCongr best) point)) = event best := by
    funext point; simp [actual, event, edge]
  rw [agree] at shift
  have count : Fintype.card (Vertex b) = 2*b := by simp [Vertex, Nat.mul_comm]
  have perms : Fintype.card (Match b) = Nat.factorial (2*b) := by rw [Fintype.card_perm, count]
  have pairs : (Finset.univ.filter (fun pair : Vertex b × Vertex b => pair.1 ≠ pair.2)) =
      (Finset.univ : Finset (Vertex b)).offDiag := by ext; simp
  have total : (∑ idx, budget idx) = limit * (2*b) * (2*b-1) := by
    simp only [budget, ← Finset.sum_filter, Finset.sum_const, pairs, Finset.offDiag_card,
      Finset.card_univ, count, nsmul_eq_mul]
    rw [← Nat.mul_sub_one, Nat.cast_id, Nat.mul_comm _ limit, ← Nat.mul_assoc]
  rw [shift, perms, total] at bound
  exact bound

end PEqualNP.Outside.L_lib_714.Matching


namespace PEqualNP.Outside.L_lib_714

lemma add_self (x : ZMod 2) : x + x = 0 := by
  have h := ZMod.natCast_self 2
  linear_combination x * h

lemma sum_affine (a : ZMod 2) : ∑ x : ZMod 2, (a + x) = 1 := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu]
  simp [← add_assoc, add_self]

lemma monomial_sum {m : Nat} {J : Type*} [DecidableEq J]
    (T : Finset J) (coord : J → Option (Fin m))
    (hcard : T.card ≤ m) (a : J → ZMod 2) :
    (∑ u : Fin m → ZMod 2,
      ∏ j ∈ T, (a j + (coord j).elim 0 u)) =
    (if ∀ k : Fin m, ∃ j ∈ T, coord j = some k then 1 else 0) := by
  classical
  by_cases hc : ∀ k : Fin m, ∃ j ∈ T, coord j = some k
  · rw [ite_eq_left hc]
    choose g hg hcoord using hc
    let f : Fin m → T := fun k => ⟨g k, hg k⟩
    have hf : Function.Injective f := by
      intro k l h
      have e := congrArg (fun j : T => coord j.val) h
      simpa [f, hcoord] using e
    have hbij : Function.Bijective f := by
      apply (Fintype.bijective_iff_injective_and_card f).2
      refine ⟨hf, ?_⟩
      have hh := Fintype.card_le_of_injective f hf
      simpa only [Fintype.card_fin, Fintype.card_coe] using
        Nat.le_antisymm hh (by simpa using hcard)
    let e : Fin m ≃ T := Equiv.ofBijective f hbij
    have hp (u : Fin m → ZMod 2) :
        (∏ j ∈ T, (a j + (coord j).elim 0 u)) =
        ∏ k : Fin m, (a (g k) + u k) := by
      rw [← Finset.prod_coe_sort T]
      rw [← e.prod_comp]
      simp [e, f, hcoord]
    simp_rw [hp]
    rw [← Fintype.prod_sum]
    simp [sum_affine]
  · rw [ite_eq_right hc]
    push Not at hc
    obtain ⟨k, hk⟩ := hc
    let flip : (Fin m → ZMod 2) → (Fin m → ZMod 2) :=
      fun u => Function.update u k (u k + 1)
    have hcoord (j : J) (hj : j ∈ T) (u : Fin m → ZMod 2) :
        (coord j).elim 0 (flip u) = (coord j).elim 0 u := by
      cases he : coord j with
      | none => rfl
      | some l =>
        have hne : l ≠ k := by
          intro h; exact hk j hj (by simpa [h] using he)
        simp [flip, hne]
    apply Finset.sum_involution (fun u _ => flip u)
    · intro u hu
      have he :
          (∏ j ∈ T, (a j + (coord j).elim 0 (flip u))) =
          ∏ j ∈ T, (a j + (coord j).elim 0 u) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hcoord j hj u]
      rw [he, add_self]
    · intro u hu hn he
      have h := congrFun he k
      simp [flip] at h
    · intro u hu
      exact Finset.mem_univ _
    · intro u hu
      ext l
      by_cases h : l = k
      · subst l; simp [flip, add_assoc, add_self]
      · simp [flip, h]


open Matching

lemma cost_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (event : β → Prop) :
    cost (fun x => event (e x)) = cost event := by
  classical
  exact e.sum_comp (fun x => if event x then 1 else 0)

lemma cost_sum {α β : Type*} [Fintype α] [Fintype β]
    (event : α → β → Prop) :
    (∑ a, cost (event a)) = ∑ b, cost (fun a => event a b) := by
  classical
  unfold cost
  rw [Finset.sum_comm]

lemma cost_exists {α β : Type*} [Fintype α] [Fintype β]
    (event : β → α → Prop) :
    cost (fun x => ∃ b, event b x) ≤ ∑ b, cost (event b) := by
  classical
  unfold cost
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : ∃ b, event b x
  · obtain ⟨b, hb⟩ := h
    have hh := Finset.single_le_sum (f := fun b => if event b x then (1 : Nat) else 0)
      (fun b _ => Nat.zero_le _) (Finset.mem_univ b)
    rw [if_pos hb] at hh
    rw [if_pos ⟨b, hb⟩]
    exact hh
  · simp only [h, ite_false]
    exact Nat.zero_le _

lemma pair_uniform {α : Type*} [Fintype α] [DecidableEq α]
    (i j : α) (hij : i ≠ j) (event : α × α → Prop) :
    cost (fun p : α × α => p.1 ≠ p.2 ∧ event p) * Fintype.card (Equiv.Perm α) =
      cost (fun p : Equiv.Perm α => event (p i, p j)) *
        (Fintype.card α * (Fintype.card α - 1)) := by
  classical
  have same (a b : α) (hab : a ≠ b) :
      cost (fun p : Equiv.Perm α => event (p a, p b)) =
        cost (fun p : Equiv.Perm α => event (p i, p j)) := by
    obtain ⟨r, hr⟩ := Equiv.Perm.exists_extending_pair
      (fun t : Bool => if t then j else i) (fun t : Bool => if t then b else a)
      (by intro x y h; cases x <;> cases y <;> simp_all)
      (by intro x y h; cases x <;> cases y <;> simp_all)
    have hi : r i = a := by simpa using hr false
    have hj : r j = b := by simpa using hr true
    simpa [permute, Equiv.trans_apply, hi, hj] using
      (cost_transport (fun p : Equiv.Perm α => event (p i, p j)) (permute r))
  have key := cost_sum (fun (p : Equiv.Perm α) (v : α × α) =>
    v.1 ≠ v.2 ∧ event (p v.1, p v.2))
  have left (p : Equiv.Perm α) :
      cost (fun v : α × α => v.1 ≠ v.2 ∧ event (p v.1, p v.2)) =
        cost (fun v : α × α => v.1 ≠ v.2 ∧ event v) := by
    have h := cost_equiv (p.prodCongr p) (fun v : α × α => v.1 ≠ v.2 ∧ event v)
    change cost (fun v : α × α => p v.1 ≠ p v.2 ∧ event (p v.1, p v.2)) = _ at h
    simpa only [p.injective.ne_iff] using h
  have right (v : α × α) :
      cost (fun p : Equiv.Perm α => v.1 ≠ v.2 ∧ event (p v.1, p v.2)) =
        if v.1 ≠ v.2 then cost (fun p : Equiv.Perm α => event (p i, p j)) else 0 := by
    by_cases h : v.1 ≠ v.2
    · rw [if_pos h]
      have he : (fun p : Equiv.Perm α => v.1 ≠ v.2 ∧ event (p v.1, p v.2)) =
          (fun p => event (p v.1, p v.2)) := by funext p; exact propext (and_iff_right h)
      rw [he]
      exact same v.1 v.2 h
    · simp [h, cost]
  simp_rw [left, right] at key
  have cardPairs : cost (fun v : α × α => v.1 ≠ v.2) =
      Fintype.card α * (Fintype.card α - 1) := by
    rw [cost_card]
    have he : (Finset.univ.filter (fun v : α × α => v.1 ≠ v.2)) =
        (Finset.univ : Finset α).offDiag := by ext v; simp
    rw [he, Finset.offDiag_card, Finset.card_univ, ← Nat.mul_sub_one]
  have count : (∑ v : α × α, if v.1 ≠ v.2 then
      cost (fun p : Equiv.Perm α => event (p i, p j)) else 0) =
      cost (fun v : α × α => v.1 ≠ v.2) *
        cost (fun p : Equiv.Perm α => event (p i, p j)) := by
    unfold cost
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  rw [count, cardPairs] at key
  simpa [Nat.mul_comm] using key

lemma affine_bound {α : Type*} [Fintype α] [DecidableEq α]
    (hn : 8 ≤ Fintype.card α)
    (c : Fin 3 → α → ZMod 2) (z : Fin 3 → α → α → ZMod 2) :
    Fintype.card α * (Fintype.card α - 1) ≤
      56 * cost (fun p : α × α => p.1 ≠ p.2 ∧ ∀ a,
        c a + z a p.1 + z a p.2 ≠ fun k => if k = p.1 then 1 else 0) := by
  classical
  let e := Fintype.equivFin α
  have h := Affine.main (Fintype.card α) hn
    (fun a k => c a (e.symm k)) (fun a i k => z a (e.symm i) (e.symm k))
  rw [← cost_card] at h
  have eqn := cost_equiv (e.symm.prodCongr e.symm)
    (fun p : α × α => p.1 ≠ p.2 ∧ ∀ a,
      c a + z a p.1 + z a p.2 ≠ fun k => if k = p.1 then 1 else 0)
  have point (i j : Fin (Fintype.card α)) :
      (∀ a, c a + z a (e.symm i) + z a (e.symm j) ≠
        fun k => if k = e.symm i then 1 else 0) ↔
      (∀ a, (fun k => c a (e.symm k)) +
        (fun k => z a (e.symm i) (e.symm k)) +
        (fun k => z a (e.symm j) (e.symm k)) ≠
          fun k => if k = i then 1 else 0) := by
    apply forall_congr'
    intro a
    rw [not_iff_not]
    constructor
    · intro h; funext k
      simpa only [Pi.add_apply, e.symm.injective.eq_iff] using congrFun h (e.symm k)
    · intro h; funext k
      simpa only [Pi.add_apply, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq_symm_apply]
        using congrFun h (e k)
  change cost (fun p : Fin (Fintype.card α) × Fin (Fintype.card α) =>
    e.symm p.1 ≠ e.symm p.2 ∧ ∀ a,
      c a + z a (e.symm p.1) + z a (e.symm p.2) ≠
        fun k => if k = e.symm p.1 then 1 else 0) = _ at eqn
  simp only [e.symm.injective.ne_iff, point] at eqn
  rw [eqn] at h
  exact h

lemma matching_approx {α V : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup V] (b : Nat) [NeZero b] (hb : 2 ≤ b)
    (e : (Fin b × Bool) ≃ α) (table : α → α → V) (target : V) :
    ∃ (c : V) (z : α → V),
      cost (fun p : Equiv.Perm α =>
        table (p (e (0,false))) (p (e (0,true))) ≠
          c + z (p (e (0,false))) + z (p (e (0,true)))) ≤
      13 * cost (fun p : Equiv.Perm α =>
        (∑ u : Fin b, table (p (e (u,false))) (p (e (u,true)))) ≠ target) := by
  classical
  let f : Matching.Vertex b → Matching.Vertex b → V := fun i j => table (e i) (e j)
  obtain ⟨c, z, h⟩ := Matching.obtain_table f target
    (slot := ⟨0, by omega⟩) (next := ⟨1, by omega⟩) (by intro h; cases h)
  let event (v : Matching.Vertex b × Matching.Vertex b) :=
    f v.1 v.2 ≠ c + z v.1 + z v.2
  have uni := pair_uniform (α := Matching.Vertex b)
    (0,false) (0,true) (by simp) event
  have hc : Fintype.card (Matching.Vertex b) = 2*b := by
    simp [Matching.Vertex, Nat.mul_comm]
  rw [Fintype.card_perm, hc] at uni
  change cost (fun v : Matching.Vertex b × Matching.Vertex b => v.1 ≠ v.2 ∧ event v) *
    (2*b).factorial ≤ _ at h
  rw [uni] at h
  have reduced : cost (fun p : Equiv.Perm (Matching.Vertex b) =>
      event (p (0,false), p (0,true))) ≤
      13 * cost (fun p => Matching.score f p ≠ target) := by
    apply Nat.le_of_mul_le_mul_right _ (show 0 < 2*b*(2*b-1) from Nat.mul_pos (by omega) (by omega))
    simpa only [Nat.mul_assoc] using h
  refine ⟨c, fun i => z (e.symm i), ?_⟩
  have err := cost_equiv e.permCongr
    (fun p : Equiv.Perm α => table (p (e (0,false))) (p (e (0,true))) ≠
      c + z (e.symm (p (e (0,false)))) + z (e.symm (p (e (0,true)))))
  have scoreEq := cost_equiv e.permCongr
    (fun p : Equiv.Perm α =>
      (∑ u : Fin b, table (p (e (u,false))) (p (e (u,true)))) ≠ target)
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply] at err scoreEq
  rw [← err, ← scoreEq]
  exact reduced

abbrev K := ZMod 2
abbrev U (m : Nat) := Fin m → K
abbrev I (m : Nat) := U m × K
abbrev V (m : Nat) := I m → K
abbrev J (m : Nat) := I m × (Fin m ⊕ Unit)

def shift {m : Nat} (p : Equiv.Perm (I m)) (u : U m) : Equiv.Perm (I m) :=
  p.trans ((Equiv.addRight u).prodCongr (Equiv.refl K))

lemma shift_inv {m : Nat} (p : Equiv.Perm (I m)) (u : U m) (v : K) :
    (shift p u).symm (0,v) = p.symm (u,v) := by
  have hn : -u = u := by ext i; exact ZMod.neg_eq_self_mod_two _
  simp [shift, Equiv.prodCongr_symm, Equiv.addRight, hn]

def translatePerm {m : Nat} (u : U m) : Equiv.Perm (Equiv.Perm (I m)) where
  toFun p := shift p u
  invFun p := p.trans ((Equiv.addRight u).prodCongr (Equiv.refl K)).symm
  left_inv p := by
    apply Equiv.ext
    intro i
    exact ((Equiv.addRight u).prodCongr (Equiv.refl K)).symm_apply_apply (p i)
  right_inv p := by
    apply Equiv.ext
    intro i
    exact ((Equiv.addRight u).prodCongr (Equiv.refl K)).apply_symm_apply (p i)

lemma predictor_constant {m : Nat} (P : Equiv.Perm (I m) → V m)
    (hP : ∀ i, ∃ T : Finset (Finset (J m)), (∀ mon ∈ T, mon.card ≤ m) ∧
      ∀ p, P p i = ∑ mon ∈ T, ∏ j ∈ mon,
        Sum.elim (p j.1).1 (fun _ => (p j.1).2) j.2) :
    ∃ A : V m, ∀ p, (∑ u : U m, P (shift p u)) = A := by
  classical
  refine ⟨∑ u : U m, P (shift (Equiv.refl _) u), ?_⟩
  intro p
  funext i
  simp only [Finset.sum_apply]
  obtain ⟨T, hT, hrep⟩ := hP i
  simp_rw [hrep]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mon hmon
  let coord : J m → Option (Fin m) := fun j => Sum.elim some (fun _ => none) j.2
  have he (p : Equiv.Perm (I m)) (u : U m) (j : J m) :
      Sum.elim ((shift p u) j.1).1 (fun _ => ((shift p u) j.1).2) j.2 =
        Sum.elim (p j.1).1 (fun _ => (p j.1).2) j.2 + (coord j).elim 0 u := by
    rcases j with ⟨i, k | k⟩ <;> simp [shift, coord]
  simp_rw [he]
  rw [monomial_sum mon coord (hT mon hmon), monomial_sum mon coord (hT mon hmon)]

lemma orbit_failures {m : Nat} (P : Equiv.Perm (I m) → V m)
    (f : I m → I m → V m) (A : V m)
    (constant : ∀ p, (∑ u : U m, P (shift p u)) = A) :
    cost (fun p : Equiv.Perm (I m) =>
      (∑ u : U m, f (p.symm (u,0)) (p.symm (u,1))) ≠ A) ≤
      2^m * cost (fun p : Equiv.Perm (I m) => P p ≠ f (p.symm (0,0)) (p.symm (0,1))) := by
  classical
  let D (p : Equiv.Perm (I m)) := P p ≠ f (p.symm (0,0)) (p.symm (0,1))
  have cover : cost (fun p : Equiv.Perm (I m) =>
      (∑ u : U m, f (p.symm (u,0)) (p.symm (u,1))) ≠ A) ≤
      cost (fun p : Equiv.Perm (I m) => ∃ u, D (shift p u)) := by
    apply cost_mono
    intro p hp
    by_contra! h
    apply hp
    rw [← constant p]
    apply Finset.sum_congr rfl
    intro u _
    simpa [D, shift_inv] using (not_not.mp (h u)).symm
  refine cover.trans ((cost_exists (fun u p => D (shift p u))).trans ?_)
  have hc : Fintype.card (U m) = 2^m := by simp [U, K, ZMod.card]
  have he (u : U m) : cost (fun p => D (shift p u)) = cost D :=
    cost_equiv (translatePerm u) D
  simp_rw [he]
  simp [hc, D]

def inversePerm (α : Type*) : Equiv.Perm (Equiv.Perm α) where
  toFun p := p.symm
  invFun p := p.symm
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def boolBit : Bool ≃ K := Equiv.ofBijective (fun b => if b then 1 else 0) (by decide)

lemma predictor_approx (m : Nat) (hm : 2 ≤ m)
    (P : Equiv.Perm (I m) → V m)
    (hP : ∀ i, ∃ T : Finset (Finset (J m)), (∀ mon ∈ T, mon.card ≤ m) ∧
      ∀ p, P p i = ∑ mon ∈ T, ∏ j ∈ mon,
        Sum.elim (p j.1).1 (fun _ => (p j.1).2) j.2)
    (f : I m → I m → V m) :
    ∃ (c : V m) (z : I m → V m),
      cost (fun p : Equiv.Perm (I m) =>
        f (p.symm (0,0)) (p.symm (0,1)) ≠
          c + z (p.symm (0,0)) + z (p.symm (0,1))) ≤
        13 * 2^m * cost (fun p : Equiv.Perm (I m) =>
          P p ≠ f (p.symm (0,0)) (p.symm (0,1))) := by
  classical
  let b := 2^m
  have hb : 2 ≤ b := by
    dsimp [b]
    calc 2 = 2^1 := by norm_num
         _ ≤ 2^m := Nat.pow_le_pow_right (by decide) (by omega)
  have hc : Fintype.card (U m) = b := by simp [U, K, b, ZMod.card]
  letI : NeZero b := ⟨by omega⟩
  let raw : Fin b ≃ U m := (Fintype.equivFinOfCardEq hc).symm
  let coord : Fin b ≃ U m := (Equiv.swap 0 (raw.symm 0)).trans raw
  have czero : coord 0 = 0 := by simp [coord]
  let e : (Fin b × Bool) ≃ I m := coord.prodCongr boolBit
  have e0 : e (0,false) = (0,0) := by simp [e, boolBit, czero]
  have e1 : e (0,true) = (0,1) := by simp [e, boolBit, czero]
  obtain ⟨A, hA⟩ := predictor_constant P hP
  obtain ⟨c, z, h⟩ := matching_approx b hb e f A
  have scoreEq (p : Equiv.Perm (I m)) :
      (∑ u : Fin b, f (p (e (u,false))) (p (e (u,true)))) =
      ∑ u : U m, f (p (u,0)) (p (u,1)) := by
    simpa [e, boolBit] using coord.sum_comp (fun u => f (p (u,0)) (p (u,1)))
  simp only [e0, e1] at h
  simp_rw [scoreEq] at h
  have hi := cost_equiv (inversePerm (I m))
    (fun p : Equiv.Perm (I m) => f (p (0,0)) (p (0,1)) ≠
      c + z (p (0,0)) + z (p (0,1)))
  have hs := cost_equiv (inversePerm (I m))
    (fun p : Equiv.Perm (I m) => (∑ u : U m, f (p (u,0)) (p (u,1))) ≠ A)
  change cost (fun p : Equiv.Perm (I m) => f (p.symm (0,0)) (p.symm (0,1)) ≠
    c + z (p.symm (0,0)) + z (p.symm (0,1))) = _ at hi
  change cost (fun p : Equiv.Perm (I m) =>
    (∑ u : U m, f (p.symm (u,0)) (p.symm (u,1))) ≠ A) = _ at hs
  rw [← hi, ← hs] at h
  refine ⟨c, z, h.trans ?_⟩
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 13 (orbit_failures P f A hA)

lemma three_bound (m : Nat) (hm : 2 ≤ m)
    (P : Fin 3 → Equiv.Perm (I m) → V m)
    (f : Fin 3 → I m → I m → V m)
    (hP : ∀ a i, ∃ T : Finset (Finset (J m)), (∀ mon ∈ T, mon.card ≤ m) ∧
      ∀ p, P a p i = ∑ mon ∈ T, ∏ j ∈ mon,
        Sum.elim (p j.1).1 (fun _ => (p j.1).2) j.2) :
    Fintype.card (Equiv.Perm (I m)) ≤
      56 * (cost (fun p : Equiv.Perm (I m) => ∀ a,
        P a p ≠ fun k => if k = p.symm (0,0) then (1 : K) else 0) +
        (1+13*2^m) * ∑ a : Fin 3, cost (fun p : Equiv.Perm (I m) =>
          P a p ≠ f a (p.symm (0,0)) (p.symm (0,1)))) := by
  classical
  choose c z ha using fun a => predictor_approx m hm (P a) (hP a) (f a)
  let unit (i k : I m) : K := if k = i then 1 else 0
  let aff (a : Fin 3) (i j : I m) := c a + z a i + z a j
  let D (a : Fin 3) (p : Equiv.Perm (I m)) :=
    P a p ≠ f a (p.symm (0,0)) (p.symm (0,1))
  let E (a : Fin 3) (p : Equiv.Perm (I m)) :=
    P a p ≠ aff a (p.symm (0,0)) (p.symm (0,1))
  let M (p : Equiv.Perm (I m)) := ∀ a, P a p ≠ unit (p.symm (0,0))
  let B (p : Equiv.Perm (I m)) :=
    ∀ a, aff a (p.symm (0,0)) (p.symm (0,1)) ≠ unit (p.symm (0,0))
  have errs (a : Fin 3) : cost (E a) ≤ (1+13*2^m) * cost (D a) := by
    have h := cost_split (event := E a) (left := D a)
      (right := fun p => f a (p.symm (0,0)) (p.symm (0,1)) ≠
        aff a (p.symm (0,0)) (p.symm (0,1))) (by
        intro p hp
        by_cases h : D a p
        · exact Or.inl h
        · exact Or.inr (fun he => hp ((not_not.mp h).trans he)))
    have hh := ha a
    dsimp only [aff] at h
    nlinarith
  have miss : cost B ≤ cost M + ∑ a : Fin 3, cost (E a) := by
    have h := cost_split (event := B) (left := M)
      (right := fun p => ∃ a, E a p) (by
        intro p hp
        by_cases h : M p
        · exact Or.inl h
        · right
          change ¬ ∀ a, P a p ≠ unit (p.symm (0,0)) at h
          push_neg at h
          obtain ⟨a, h⟩ := h
          exact ⟨a, fun he => hp a (he.symm.trans h)⟩)
    exact h.trans (Nat.add_le_add_left (cost_exists E) _)
  have hn : 8 ≤ Fintype.card (I m) := by
    have hp : 2^2 ≤ 2^m := Nat.pow_le_pow_right (by decide) hm
    simp only [I, U, K, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    omega
  let event (v : I m × I m) := ∀ a, aff a v.1 v.2 ≠ unit v.1
  have lower := affine_bound hn c z
  change Fintype.card (I m) * (Fintype.card (I m)-1) ≤
    56 * cost (fun v : I m × I m => v.1 ≠ v.2 ∧ event v) at lower
  have uniform := pair_uniform (α := I m) (0,0) (0,1) (by simp) event
  have inv := cost_equiv (inversePerm (I m))
    (fun p : Equiv.Perm (I m) => event (p (0,0), p (0,1)))
  change cost B = _ at inv
  rw [← inv] at uniform
  have scaled := Nat.mul_le_mul_right (Fintype.card (Equiv.Perm (I m))) lower
  rw [Nat.mul_assoc 56, uniform] at scaled
  have lowerPerm : Fintype.card (Equiv.Perm (I m)) ≤ 56 * cost B := by
    apply Nat.le_of_mul_le_mul_right _
      (show 0 < Fintype.card (I m) * (Fintype.card (I m)-1) from
        Nat.mul_pos (by omega) (by omega))
    nlinarith [scaled]
  refine lowerPerm.trans (Nat.mul_le_mul_left 56 ?_)
  apply miss.trans
  apply Nat.add_le_add_left
  calc (∑ a : Fin 3, cost (E a)) ≤ ∑ a : Fin 3, (1+13*2^m) * cost (D a) :=
      Finset.sum_le_sum fun a _ => errs a
    _ = _ := (Finset.mul_sum _ _ _).symm


end PEqualNP.Outside.L_lib_714

theorem PEqualNP.Outside.L_lib_714 : (∀ m : Nat, 2 ≤ m →
  let K := ZMod 2
  let U := Fin m → K
  let I := U × K
  let V := I → K
  let J := I × (Fin m ⊕ Unit)
  let bit := fun (p : Equiv.Perm I) (j : J) =>
    Sum.elim (p j.1).1 (fun _ => (p j.1).2) j.2
  let unit := fun (i j : I) => if j = i then (1 : K) else 0
  let first := fun (p : Equiv.Perm I) => p.symm (0,0)
  let second := fun (p : Equiv.Perm I) => p.symm (0,1)
  ∀ (P : Fin 3 → Equiv.Perm I → V) (f : Fin 3 → I → I → V),
    (∀ a i, ∃ T : Finset (Finset J), (∀ mon ∈ T, mon.card ≤ m) ∧
      ∀ p, P a p i = ∑ mon ∈ T, ∏ j ∈ mon, bit p j) →
    let disagreements := fun (a : Fin 3) =>
      ((Finset.univ : Finset (Equiv.Perm I)).filter
        (fun p => P a p ≠ f a (first p) (second p))).card
    let missed := (Finset.univ : Finset (Equiv.Perm I)).filter (fun p =>
      ∀ a, P a p ≠ unit (first p))
    Nat.factorial (2^(m+1)) ≤
      56 * (missed.card + (1 + 13*2^m) * ∑ a : Fin 3, disagreements a)) := by
  classical
  intro m hm K U I V J bit unit first second P f hP disagreements missed
  have h := PEqualNP.Outside.L_lib_714.three_bound m hm P f hP
  have hc : Fintype.card (Equiv.Perm I) = Nat.factorial (2^(m+1)) := by
    rw [Fintype.card_perm]
    simp [I, U, K, ZMod.card, pow_succ]
  rw [hc] at h
  simpa only [PEqualNP.Outside.L_lib_714.Matching.cost_card,
    disagreements, missed, unit, first, second] using h
