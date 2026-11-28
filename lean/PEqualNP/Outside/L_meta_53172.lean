import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53172

namespace CycleResidue

open Finset
open scoped BigOperators

def offset (weight : Nat → Nat) (i : Nat) : Nat := ∑ j ∈ range i, weight j

theorem prefix_succ (weight : Nat → Nat) (i : Nat) :
    offset weight (i + 1) = offset weight i + weight i :=
  Finset.sum_range_succ weight i

def interval (weight : Nat → Nat) (i : Nat) : Finset Nat :=
  Ico (offset weight i) (offset weight (i + 1))

theorem interval_card (weight : Nat → Nat) (i : Nat) :
    (interval weight i).card = weight i := by
  unfold interval
  rw [Nat.card_Ico, prefix_succ]
  omega

theorem sum_interval (weight value : Nat → Nat) (N : Nat) :
    (∑ i ∈ range N, ∑ j ∈ interval weight i, value j) =
      ∑ j ∈ range (offset weight N), value j := by
  induction N with
  | zero => simp [offset]
  | succ N ih =>
    have hd : Disjoint (range (offset weight N)) (interval weight N) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      have h₁ := Finset.mem_range.mp ha
      have h₂ := (Finset.mem_Ico.mp hb).1
      omega
    have hu : range (offset weight N) ∪ interval weight N =
        range (offset weight (N + 1)) := by
      ext a
      simp only [Finset.mem_union, Finset.mem_range, interval, Finset.mem_Ico, prefix_succ]
      omega
    rw [Finset.sum_range_succ, ih, ← Finset.sum_union hd, hu]

theorem same_remainder {x y T : Nat} (hxy : x ≤ y) (hgap : y < x + T)
    (hmod : x % T = y % T) : x = y := by
  by_contra hne
  have hpos : 0 < y - x := by omega
  have hdiv : T ∣ y - x := (Nat.modEq_iff_dvd' hxy).mp hmod
  have hle := Nat.le_of_dvd hpos hdiv
  omega

theorem interval_injective {weight : Nat → Nat} {i T : Nat} (h : weight i ≤ T) :
    ∀ ⦃a⦄, a ∈ interval weight i → ∀ ⦃b⦄, b ∈ interval weight i →
      a % T = b % T → a = b := by
  intro a ha b hb hm
  simp only [interval, Finset.mem_Ico, prefix_succ] at ha hb
  by_cases hle : a ≤ b
  · exact same_remainder hle (by omega) hm
  · exact (same_remainder (by omega) (by omega) hm.symm).symm

theorem count_remainder {T m r : Nat} (hT : 0 < T) (hr : r < T) :
    ((range (T * m)).filter fun j => j % T = r).card = m := by
  let label := fun i : Nat => r + T * i
  have hinj : Function.Injective label := by
    intro a b h
    have he : T * a = T * b := Nat.add_left_cancel h
    exact (Nat.mul_left_cancel hT he)
  have he : (range m).image label = (range (T * m)).filter (fun j => j % T = r) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨a, ha, rfl⟩
      change r + T * a < T * m ∧ (r + T * a) % T = r
      refine ⟨?_, by simp [Nat.add_mod, Nat.mod_eq_of_lt hr]⟩
      calc
        r + T * a < T * (a + 1) := by rw [Nat.mul_succ]; omega
        _ ≤ T * m := Nat.mul_le_mul_left T (by omega)
    · rintro ⟨hl, hh⟩
      refine ⟨j / T, ?_, ?_⟩
      · exact (Nat.div_lt_iff_lt_mul hT).2 (by simpa [Nat.mul_comm] using hl)
      · change r + T * (j / T) = j
        rw [← hh]
        exact Nat.mod_add_div j T
  rw [← he, Finset.card_image_of_injective _ hinj, Finset.card_range]

def colorSet (weight : Nat → Nat) (T i : Nat) : Finset Nat :=
  (interval weight i).image (fun j => j % T)

def residueMatching (weight : Nat → Nat) (T N r : Nat) : Finset Nat :=
  (range N).filter (fun i => r ∈ colorSet weight T i)

theorem card_residueMatching {weight : Nat → Nat} {T N m r : Nat}
    (hT : 0 < T) (hr : r < T) (hsum : offset weight N = T * m)
    (hli : ∀ i < N, weight i ≤ T) :
    (residueMatching weight T N r).card = m := by
  have indicator : ∀ i < N,
      (if r ∈ colorSet weight T i then 1 else 0 : Nat) =
        ((interval weight i).filter (fun j => j % T = r)).card := by
    intro i hi
    have hrange : ((interval weight i).filter (fun j => j % T = r)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have h₁ := Finset.mem_filter.mp ha
      have h₂ := Finset.mem_filter.mp hb
      exact interval_injective (hli i hi) h₁.1 h₂.1 (h₁.2.trans h₂.2.symm)
    by_cases h : r ∈ colorSet weight T i
    · have hn : ((interval weight i).filter (fun j => j % T = r)).Nonempty := by
        obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
        exact ⟨k, Finset.mem_filter.mpr ⟨hk, he⟩⟩
      have hpos := Finset.card_pos.mpr hn
      simp only [h, ite_true]
      omega
    · have he : (interval weight i).filter (fun j => j % T = r) = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hn
        obtain ⟨j, hj⟩ := hn
        have hp := Finset.mem_filter.mp hj
        exact h (Finset.mem_image.mpr ⟨j, hp.1, hp.2⟩)
      simp [h, he]
  calc
    (residueMatching weight T N r).card =
        ∑ i ∈ range N, if r ∈ colorSet weight T i then 1 else 0 := by
      unfold residueMatching
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ i ∈ range N, ((interval weight i).filter (fun j => j % T = r)).card := by
      apply Finset.sum_congr rfl
      intro i hi
      exact indicator i (Finset.mem_range.mp hi)
    _ = ((range (offset weight N)).filter (fun j => j % T = r)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact sum_interval weight (fun j => if j % T = r then 1 else 0) N
    _ = m := hsum ▸ count_remainder hT hr

theorem residue_independent {weight : Nat → Nat} {T N m r : Nat}
    (hsum : offset weight N = T * m)
    (hpair : ∀ i < N, weight i + weight ((i + 1) % N) ≤ T) :
    ∀ i ∈ residueMatching weight T N r, (i + 1) % N ∉ residueMatching weight T N r := by
  intro i hi hnext
  have hi' : i < N := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
  obtain ⟨a, ha, hra⟩ : ∃ j ∈ interval weight i, j % T = r :=
    Finset.mem_image.mp (Finset.mem_filter.mp hi).2
  obtain ⟨b, hb, hrb⟩ : ∃ j ∈ interval weight ((i + 1) % N), j % T = r :=
    Finset.mem_image.mp (Finset.mem_filter.mp hnext).2
  have hbound := hpair i hi'
  by_cases hlt : i + 1 < N
  · have hn : (i + 1) % N = i + 1 := Nat.mod_eq_of_lt hlt
    rw [hn] at hb hbound
    simp only [interval, Finset.mem_Ico, prefix_succ] at ha hb
    have heq := same_remainder (x := a) (y := b) (by omega) (by omega) (hra.trans hrb.symm)
    omega
  · have hn : i + 1 = N := by omega
    have hz : (i + 1) % N = 0 := by rw [hn, Nat.mod_self]
    have hp : offset weight i + weight i = T * m := by rw [← prefix_succ, hn, hsum]
    rw [hz] at hb hbound
    simp only [interval, Finset.mem_Ico, prefix_succ] at ha hb
    have hp0 : offset weight 0 = 0 := by simp [offset]
    rw [hp0] at hb
    have hc : (b + T * m) % T = a % T := by
      calc
        (b + T * m) % T = b % T := by simp
        _ = a % T := hrb.trans hra.symm
    have heq := same_remainder (x := a) (y := b + T * m)
      (by omega) (by omega) hc.symm
    omega

def cycleMatching (N m : Nat) (M : Finset Nat) : Prop :=
  M ⊆ range N ∧ M.card = m ∧ ∀ i ∈ M, (i + 1) % N ∉ M

theorem weighted_lower {N m T q : Nat} {weight cost : Nat → Nat}
    (hT : 0 < T) (hsum : offset weight N = T * m)
    (hpair : ∀ i < N, weight i + weight ((i + 1) % N) ≤ T)
    (hmin : ∀ M, cycleMatching N m M → q ≤ M.sum cost) :
    T * q ≤ ∑ i ∈ range N, weight i * cost i := by
  have hli : ∀ i < N, weight i ≤ T := by
    intro i hi
    have hp := hpair i hi
    omega
  have hcolor (i : Nat) : colorSet weight T i ⊆ range T := by
    intro r hr
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_range.mpr (Nat.mod_lt _ hT)
  calc
    T * q = ∑ r ∈ range T, q := by simp
    _ ≤ ∑ r ∈ range T, (residueMatching weight T N r).sum cost := by
      apply Finset.sum_le_sum
      intro r hr
      have hr := Finset.mem_range.mp hr
      apply hmin
      refine ⟨Finset.filter_subset _ _, card_residueMatching hT hr hsum hli, ?_⟩
      exact residue_independent hsum hpair
    _ = ∑ i ∈ range N, weight i * cost i := by
      simp only [residueMatching, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      have he : (range T).filter (fun r => r ∈ colorSet weight T i) =
          colorSet weight T i := by
        ext r
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hcolor i h, h⟩⟩
      have hc : (colorSet weight T i).card = weight i := by
        unfold colorSet
        rw [Finset.card_image_iff.mpr ?_, interval_card]
        exact interval_injective (hli i (Finset.mem_range.mp hi))
      rw [← Finset.sum_filter, he, Finset.sum_const, hc, Nat.nsmul_eq_mul]

end CycleResidue

namespace CycleTight

open Finset

def selectNext (tight : Nat → Bool) : Nat → Bool
  | 0 => false
  | i + 1 => tight i && !(selectNext tight i)

theorem select_implies_tight {tight : Nat → Bool} {i : Nat}
    (hs : selectNext tight (i + 1) = true) : tight i = true := by
  simp only [selectNext, Bool.and_eq_true] at hs
  exact hs.1

theorem select_next_false {tight : Nat → Bool} {i : Nat}
    (hs : selectNext tight i = true) : selectNext tight (i + 1) = false := by
  simp [selectNext, hs]

theorem select_covers {tight : Nat → Bool} {i : Nat} (ht : tight i = true) :
    selectNext tight i = true ∨ selectNext tight (i + 1) = true := by
  cases h : selectNext tight i <;> simp [selectNext, ht, h]

def rotate (N start i : Nat) : Nat := (start + i) % N

def next (N i : Nat) : Nat := (i + 1) % N

theorem rotate_step (N start i : Nat) :
    rotate N start (i + 1) = next N (rotate N start i) := by
  simp [rotate, next, ← Nat.add_assoc]

theorem rotate_injOn (N start : Nat) : Set.InjOn (rotate N start) (↑(range N)) := by
  intro i hi j hj e
  have hi := Finset.mem_range.mp hi
  have hj := Finset.mem_range.mp hj
  unfold rotate at e
  by_cases h : i ≤ j
  · have hq := CycleResidue.same_remainder (by omega) (by omega) e
    omega
  · have hq := CycleResidue.same_remainder (by omega) (by omega) e.symm
    omega

theorem next_injOn (N : Nat) : Set.InjOn (next N) (↑(range N)) := by
  intro i hi j hj h
  apply rotate_injOn N 1 hi hj
  change (1+i) % N = (1+j) % N
  simpa only [next, Nat.add_comm 1 i, Nat.add_comm 1 j] using h

theorem rotate_range {N : Nat} (hN : 0 < N) (start : Nat) :
    (range N).image (rotate N start) = range N := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (Nat.mod_lt _ hN)
  · rw [Finset.card_image_iff.mpr (rotate_injOn N start)]

theorem independent_cover {N cut : Nat} {tight : Nat → Bool}
    (hc : cut < N) (hslack : tight cut = false) :
    ∃ P : Finset Nat, P ⊆ range N ∧ (∀ i ∈ P, tight i = true) ∧
      (∀ i ∈ P, next N i ∉ P) ∧
      ∀ i < N, tight i = true → i ∈ P.image (next N) ∨ next N i ∈ P.image (next N) := by
  let f := rotate N (cut + 1)
  let tight' := fun j => tight (f j)
  let g := selectNext tight'
  let R := (range N).filter (fun j => g (j + 1) = true)
  let P := R.image f
  have hN : 0 < N := by omega
  have hfmem : ∀ j, f j ∈ range N := fun j => Finset.mem_range.mpr (Nat.mod_lt _ hN)
  have hinj := rotate_injOn N (cut+1)
  have hprev : ∀ j ∈ R, j + 1 < N := by
    intro j hj
    have h := Finset.mem_filter.mp hj
    have hjn := Finset.mem_range.mp h.1
    by_contra hnot
    have fcut : f j = cut := by
      change (cut + 1 + j) % N = cut
      rw [show cut + 1 + j = cut + N by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hc]
    have hg := select_implies_tight h.2
    change tight (f j) = true at hg
    rw [fcut, hslack] at hg
    cases hg
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact hfmem j
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact select_implies_tight (tight := tight') (i := j) (Finset.mem_filter.mp hj).2
  · intro i hi hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hn
    have he : f k = f (j + 1) := hke.trans (rotate_step N (cut + 1) j).symm
    have hk' : k = j + 1 := hinj (Finset.mem_filter.mp hk).1
      (Finset.mem_range.mpr (hprev j hj)) he
    have hfalse : g (j + 2) = false := select_next_false (Finset.mem_filter.mp hj).2
    have htrue : g (k + 1) = true := (Finset.mem_filter.mp hk).2
    rw [hk'] at htrue
    rw [hfalse] at htrue
    cases htrue
  · intro i hi ht
    have hh : i ∈ (range N).image f := by
      rw [show (range N).image f = range N from rotate_range hN _]
      exact Finset.mem_range.mpr hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    rcases select_covers (tight := tight') (i := j) ht with hg | hg
    · have hjpos : 0 < j := by
        by_contra hn
        have hz : j = 0 := by omega
        rw [hz] at hg
        cases hg
      have hn : (j - 1) + 1 = j := by omega
      have hp : j - 1 ∈ R := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
          have hv := Finset.mem_range.mp hj
          omega), ?_⟩
        simpa only [hn] using hg
      have hk : f (j - 1) ∈ P := Finset.mem_image.mpr ⟨j - 1, hp, rfl⟩
      left
      apply Finset.mem_image.mpr
      refine ⟨_, hk, ?_⟩
      rw [← rotate_step N (cut+1) (j-1)]
      exact congrArg f hn
    · right
      apply Finset.mem_image.mpr
      refine ⟨f j, ?_, rfl⟩
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hg⟩, rfl⟩

theorem successors_card {N : Nat} {P : Finset Nat} (hP : P ⊆ range N) :
    (P.image (next N)).card = P.card := by
  apply Finset.card_image_iff.mpr
  intro i hi j hj e
  exact next_injOn N (hP hi) (hP hj) e

theorem successors_independent {N : Nat} {P : Finset Nat} (hN : 0 < N)
    (hP : P ⊆ range N) (hi : ∀ i ∈ P, next N i ∉ P) :
    ∀ i ∈ P.image (next N), next N i ∉ P.image (next N) := by
  intro i h₁ h₂
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h₁
  obtain ⟨b, hb, he⟩ := Finset.mem_image.mp h₂
  have hj : next N a ∈ range N := Finset.mem_range.mpr (Nat.mod_lt _ hN)
  have hb' := next_injOn N (hP hb) hj he
  exact hi a ha (hb' ▸ hb)

end CycleTight

namespace CycleMultiplicity

open Finset
open scoped BigOperators

def indicator (M : Finset Nat) (i : Nat) : Nat := if i ∈ M then 1 else 0

def appearances {d : Nat} (C : Fin d → Finset Nat) (i : Nat) : Nat :=
  ∑ r : Fin d, indicator (C r) i

theorem sum_indicator {N : Nat} {M : Finset Nat} (hm : M ⊆ range N) (cost : Nat → Nat) :
    (∑ i ∈ range N, indicator M i * cost i) = M.sum cost := by
  have hf : (range N).filter (fun i => i ∈ M) = M := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hm h, h⟩⟩
  simp only [indicator, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, hf]

theorem sum_cost_appearances {d N q : Nat} {C : Fin d → Finset Nat} {cost : Nat → Nat}
    (hM : ∀ r, C r ⊆ range N) (hcost : ∀ r, (C r).sum cost = q) :
    (∑ i ∈ range N, appearances C i * cost i) = d * q := by
  simp only [appearances, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    (∑ r : Fin d, ∑ i ∈ range N, indicator (C r) i * cost i) =
        ∑ _ : Fin d, q := by
      apply Finset.sum_congr rfl
      intro r _
      rw [sum_indicator (hM r), hcost r]
    _ = d * q := by simp

theorem sum_appearances {d N m : Nat} {C : Fin d → Finset Nat}
    (hM : ∀ r, C r ⊆ range N) (hcard : ∀ r, (C r).card = m) :
    CycleResidue.offset (appearances C) N = d * m := by
  have H := sum_cost_appearances (C := C) (cost := fun _ => 1) (q := m)
    hM (fun r => by simpa using hcard r)
  simpa [CycleResidue.offset] using H

theorem appearance_pos {d i : Nat} {C : Fin d → Finset Nat} (r : Fin d) (hi : i ∈ C r) :
    1 ≤ appearances C i := by
  calc
    1 = indicator (C r) i := by simp [indicator, hi]
    _ ≤ appearances C i :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (indicator (C j) i)) (Finset.mem_univ r)

theorem pair_indicator_le_one {M : Finset Nat} {i j : Nat} (h : i ∈ M → j ∉ M) :
    indicator M i + indicator M j ≤ 1 := by
  by_cases hi : i ∈ M
  · simp [indicator, hi, h hi]
  · by_cases hj : j ∈ M <;> simp [indicator, hi, hj]

theorem appearances_pair_le {d i j : Nat} {C : Fin d → Finset Nat}
    (h : ∀ r, i ∈ C r → j ∉ C r) : appearances C i + appearances C j ≤ d := by
  unfold appearances
  rw [← Finset.sum_add_distrib]
  calc
    (∑ r : Fin d, (indicator (C r) i + indicator (C r) j)) ≤ ∑ _ : Fin d, 1 :=
      Finset.sum_le_sum (fun r _ => pair_indicator_le_one (h r))
    _ = d := by simp

theorem tight_pair_hits {d i j : Nat} {C : Fin d → Finset Nat}
    (h : ∀ r, i ∈ C r → j ∉ C r) (heq : appearances C i + appearances C j = d) :
    ∀ r, i ∈ C r ∨ j ∈ C r := by
  intro r
  by_contra hn
  have hn₁ : i ∉ C r := fun hi => hn (Or.inl hi)
  have hn₂ : j ∉ C r := fun hj => hn (Or.inr hj)
  let f := fun t : Fin d => indicator (C t) i + indicator (C t) j
  have hsum : (∑ t : Fin d, f t) = d := by
    exact (Finset.sum_add_distrib.trans heq)
  have hz : f r = 0 := by simp [f, indicator, hn₁, hn₂]
  have hErase := Finset.sum_erase_add Finset.univ f (Finset.mem_univ r)
  have hlt : (∑ t ∈ (Finset.univ : Finset (Fin d)).erase r, f t) ≤ d - 1 := by
    calc
      (∑ t ∈ (Finset.univ : Finset (Fin d)).erase r, f t) ≤
          ∑ _ ∈ (Finset.univ : Finset (Fin d)).erase r, 1 :=
        Finset.sum_le_sum (fun t _ => pair_indicator_le_one (h t))
      _ = d - 1 := by simp
  have hd := r.isLt
  rw [hz, Nat.add_zero, hsum] at hErase
  omega

theorem choose_endpoint {N : Nat} {P M : Finset Nat}
    (hP : P ⊆ range N) (hIndep : ∀ i ∈ P, CycleTight.next N i ∉ P)
    (hHit : ∀ i ∈ P, i ∈ M ∨ CycleTight.next N i ∈ M) :
    ∃ U : Finset Nat, U ⊆ M ∧ U ⊆ P ∪ P.image (CycleTight.next N) ∧ U.card = P.card := by
  let f := fun i => if i ∈ M then i else CycleTight.next N i
  refine ⟨P.image f, ?_, ?_, Finset.card_image_iff.mpr ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    by_cases h : j ∈ M
    · simp [f, h]
    · simpa [f, h] using (hHit j hj).resolve_left h
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    by_cases h : j ∈ M
    · exact Finset.mem_union.mpr (Or.inl (by simpa [f, h] using hj))
    · exact Finset.mem_union.mpr (Or.inr (by
        simpa [f, h] using Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  · intro a ha b hb hab
    by_cases aM : a ∈ M <;> by_cases bM : b ∈ M
    · simpa [f, aM, bM] using hab
    · have he : a = CycleTight.next N b := by simpa [f, aM, bM] using hab
      exact False.elim (hIndep b hb (he ▸ ha))
    · have he : CycleTight.next N a = b := by simpa [f, aM, bM] using hab
      exact False.elim (hIndep a ha (he.symm ▸ hb))
    · apply CycleTight.next_injOn N (hP ha) (hP hb)
      simpa [f, aM, bM] using hab

theorem tight_few_starts {N m : Nat} {P : Finset Nat}
    (hsize : 2*m < N) (hP : P ⊆ range N)
    (hIndep : ∀ i ∈ P, CycleTight.next N i ∉ P)
    (hcover : ∀ i < N, ∃ M : Finset Nat, i ∈ M ∧ M.card = m ∧
      ∀ j ∈ P, j ∈ M ∨ CycleTight.next N j ∈ M) :
    P.card < m := by
  have hN : 0 < N := by omega
  obtain ⟨M₀, _, hcard₀, hhit₀⟩ := hcover 0 hN
  obtain ⟨U, hU, _, hUc⟩ := choose_endpoint hP hIndep hhit₀
  have hle : P.card ≤ m := hUc ▸ hcard₀ ▸ Finset.card_le_card hU
  by_contra hnot
  have hPcard : P.card = m := by omega
  let S := P ∪ P.image (CycleTight.next N)
  have hsmall : S.card < (range N).card := by
    have hbound := Finset.card_union_le P (P.image (CycleTight.next N))
    rw [CycleTight.successors_card hP, hPcard] at hbound
    rw [Finset.card_range]
    exact lt_of_le_of_lt hbound (by omega)
  have hfresh : ∃ i ∈ range N, i ∉ S := by
    by_contra h
    have hs : range N ⊆ S := by
      intro i hi
      by_contra his
      exact h ⟨i, hi, his⟩
    exact (not_le_of_gt hsmall) (Finset.card_le_card hs)
  obtain ⟨i, hi, hiS⟩ := hfresh
  obtain ⟨M, hiM, hcard, hhit⟩ := hcover i (Finset.mem_range.mp hi)
  obtain ⟨U, hUM, hUS, hUc⟩ := choose_endpoint hP hIndep hhit
  have hu : U = M := Finset.eq_of_subset_of_card_le hUM (by rw [hcard, hUc, hPcard])
  exact hiS (hUS (hu.symm ▸ hiM))

end CycleMultiplicity

namespace CycleBalance

open Finset
open scoped BigOperators

theorem parts_mul (t d x : Nat) (hd : 1 ≤ d) :
    t * (d - 1) * x + t * x = t * (d * x) := by
  have h : (d - 1).succ = d := by omega
  rw [← Nat.add_mul, ← Nat.mul_succ, h, Nat.mul_assoc]

theorem estimate {N m K d q : Nat} {A w : Nat → Nat} {Y : Finset Nat}
    (hN : N = K + 2 * m) (hm : 0 < m) (hd : 2 ≤ d)
    (hMass : CycleResidue.offset A N = d * m)
    (hCost : (∑ i ∈ range N, A i * w i) = d * q)
    (hPositive : ∀ i < N, 1 ≤ A i)
    (hPair : ∀ i < N, A i + A (CycleTight.next N i) ≤ d)
    (hY : Y ⊆ range N) (hSmall : Y.card < m)
    (hYind : ∀ i ∈ Y, CycleTight.next N i ∉ Y)
    (hTight : K ≠ 0 → ∀ i < N, A i + A (CycleTight.next N i) = d →
      i ∈ Y ∨ CycleTight.next N i ∈ Y)
    (hMin : ∀ M, CycleResidue.cycleMatching N m M → q ≤ M.sum w) :
    (range N).sum w ≤ (K + 2) * q := by
  let a := m - Y.card
  let t := K + 2*a
  let Z := fun i => a + K * CycleMultiplicity.indicator Y i
  let U := fun i => t * A i - Z i
  have ha : 0 < a := by omega
  have ht : 0 < t := by omega
  have hn : 0 < N := by omega
  have hnext : ∀ i, CycleTight.next N i < N := fun _ => Nat.mod_lt _ hn
  have hZpoint : ∀ i, a ≤ Z i ∧ Z i ≤ t := by
    intro i
    by_cases hi : i ∈ Y <;> simp [Z, t, CycleMultiplicity.indicator, hi] <;> omega
  have hZpair : ∀ i ∈ range N, Z i + Z (CycleTight.next N i) ≤ t := by
    intro i _
    by_cases hi : i ∈ Y
    · simp [Z, t, CycleMultiplicity.indicator, hi, hYind i hi]
      omega
    · by_cases h : CycleTight.next N i ∈ Y
      · simp [Z, t, CycleMultiplicity.indicator, hi, h]
        omega
      · simp [Z, t, CycleMultiplicity.indicator, hi, h]
        omega
  have hZtight : ∀ i < N, A i + A (CycleTight.next N i) = d →
      Z i + Z (CycleTight.next N i) = t := by
    intro i hi htight
    by_cases hK : K = 0
    · simp [Z, t, hK]
      omega
    · rcases hTight hK i hi htight with h₁ | h₂
      · simp [Z, t, CycleMultiplicity.indicator, h₁, hYind i h₁]
        omega
      · have h₁ : i ∉ Y := fun hi' => hYind i hi' h₂
        simp [Z, t, CycleMultiplicity.indicator, h₁, h₂]
        omega
  have hZle : ∀ i < N, Z i ≤ t * A i := by
    intro i hi
    exact (hZpoint i).2.trans (by simpa using Nat.mul_le_mul_left t (hPositive i hi))
  have hAdd : ∀ i < N, Z i + U i = t * A i := by
    intro i hi
    exact Nat.add_sub_of_le (hZle i hi)
  have hZMass : CycleResidue.offset Z N = t * m := by
    have hIndicators : (∑ i ∈ range N, CycleMultiplicity.indicator Y i) = Y.card := by
      simpa using CycleMultiplicity.sum_indicator hY (fun _ => 1)
    have hAcard : a + Y.card = m := by omega
    have hKmul := congrArg (fun n => K * n) hAcard
    simp only [Nat.mul_add] at hKmul
    dsimp [CycleResidue.offset, Z, t]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul,
        ← Finset.mul_sum, hIndicators, hN]
    nlinarith
  have hUMass : CycleResidue.offset U N = t * (d-1) * m := by
    have he : CycleResidue.offset Z N + CycleResidue.offset U N = t * (d * m) := by
      unfold CycleResidue.offset
      rw [← Finset.sum_add_distrib]
      calc
        (∑ i ∈ range N, (Z i + U i)) = ∑ i ∈ range N, t * A i := by
          exact Finset.sum_congr rfl (fun i hi => hAdd i (Finset.mem_range.mp hi))
        _ = t * (d * m) := by
          rw [← Finset.mul_sum]
          change t * CycleResidue.offset A N = t * (d * m)
          rw [hMass]
    have hd₁ : 1 ≤ d := by omega
    have hp := parts_mul t d m hd₁
    omega
  have hUPair : ∀ i < N, U i + U (CycleTight.next N i) ≤ t*(d-1) := by
    intro i hi
    let j := CycleTight.next N i
    have hj := hnext i
    have hpair : A i + A j ≤ d := hPair i hi
    have hZsum : U i + U j = t * (A i + A j) - (Z i + Z j) := by
      dsimp only [U]
      rw [Nat.mul_add]
      have hx := hZle i hi
      have hy := hZle j hj
      omega
    rw [hZsum]
    by_cases hEq : A i + A j = d
    · rw [hEq, hZtight i hi hEq, Nat.mul_sub, Nat.mul_one]
    · have hle : A i + A j ≤ d - 1 := by omega
      exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_left t hle)
  have htU : 0 < t*(d-1) := Nat.mul_pos ht (by omega)
  have hzLower := CycleResidue.weighted_lower ht hZMass
    (fun i hi => hZpair i (Finset.mem_range.mpr hi)) hMin
  have huLower := CycleResidue.weighted_lower htU hUMass hUPair hMin
  have hBalance : (∑ i ∈ range N, Z i * w i) + (∑ i ∈ range N, U i * w i) =
      t * (d * q) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ i ∈ range N, (Z i * w i + U i * w i)) = ∑ i ∈ range N, t * (A i * w i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Nat.add_mul, hAdd i (Finset.mem_range.mp hi), Nat.mul_assoc]
      _ = t * (d * q) := by rw [← Finset.mul_sum, hCost]
  have hZCost : (∑ i ∈ range N, Z i * w i) = t*q := by
    have hp := parts_mul t d q (by omega)
    omega
  have hSumLe : a * (range N).sum w ≤ t*q := by
    rw [Finset.mul_sum, ← hZCost]
    exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right _ (hZpoint i).1)
  have hTle : t ≤ a*(K+2) := by
    have ha1 : 1 ≤ a := by omega
    have hKa := Nat.mul_le_mul_right K ha1
    simp only [Nat.one_mul] at hKa
    change K + 2*a ≤ a*(K+2)
    rw [Nat.mul_add, Nat.mul_comm a 2]
    omega
  apply (Nat.mul_le_mul_left_iff ha).mp
  exact hSumLe.trans (by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right q hTle)

end CycleBalance


namespace CycleSlack

open Finset
open scoped BigOperators

theorem sum_next {N : Nat} (hn : 0 < N) (A : Nat → Nat) :
    (∑ i ∈ range N, A (CycleTight.next N i)) = ∑ i ∈ range N, A i := by
  have he : (range N).image (CycleTight.next N) = range N := by
    have h : CycleTight.next N = CycleTight.rotate N 1 := by
      funext i
      simp only [CycleTight.next, CycleTight.rotate, Nat.add_comm 1 i]
    rw [h, CycleTight.rotate_range hn 1]
  calc
    (∑ i ∈ range N, A (CycleTight.next N i)) =
        ∑ i ∈ (range N).image (CycleTight.next N), A i :=
      (Finset.sum_image (CycleTight.next_injOn N)).symm
    _ = ∑ i ∈ range N, A i := by rw [he]

theorem exists_slack {N m d : Nat} {A : Nat → Nat} (hWide : 2*m < N) (hd : 0 < d)
    (hMass : CycleResidue.offset A N = d*m)
    (hBound : ∀ i < N, A i + A (CycleTight.next N i) ≤ d) :
    ∃ i < N, A i + A (CycleTight.next N i) < d := by
  by_contra h
  have hn : 0 < N := by omega
  have he : ∀ i ∈ range N, A i + A (CycleTight.next N i) = d := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hb := hBound i hi'
    have hn' : ¬ (A i + A (CycleTight.next N i) < d) := fun hlt => h ⟨i, hi', hlt⟩
    omega
  have hfull : (∑ i ∈ range N, (A i + A (CycleTight.next N i))) = N*d := by
    simpa using Finset.sum_const_nat he
  have hsum : (∑ i ∈ range N, (A i + A (CycleTight.next N i))) = 2*(d*m) := by
    rw [Finset.sum_add_distrib, sum_next hn]
    change CycleResidue.offset A N + CycleResidue.offset A N = 2*(d*m)
    rw [hMass]
    omega
  have hl : 2*(d*m) < N*d := by
    calc
      2*(d*m) = (2*m)*d := by ac_rfl
      _ < N*d := Nat.mul_lt_mul_of_pos_right hWide hd
  exact (ne_of_lt hl) (hsum.symm.trans hfull)

end CycleSlack



namespace CycleCover

open Finset
open scoped BigOperators

theorem bound_from_collection {N m K d q : Nat} {w : Nat → Nat}
    (hshape : N = K + 2*m) (hm : 0 < m) (hd : 2 ≤ d)
    (C : Fin d → Finset Nat)
    (hC : ∀ r, CycleResidue.cycleMatching N m (C r) ∧ (C r).sum w = q)
    (hCover : ∀ i < N, ∃ r, i ∈ C r)
    (hMin : ∀ M, CycleResidue.cycleMatching N m M → q ≤ M.sum w) :
    (range N).sum w ≤ (K + 2)*q := by
  let A := CycleMultiplicity.appearances C
  have hN : 0 < N := by omega
  have hMass : CycleResidue.offset A N = d*m :=
    CycleMultiplicity.sum_appearances (fun r => (hC r).1.1) (fun r => (hC r).1.2.1)
  have hCost : (∑ i ∈ range N, A i * w i) = d*q :=
    CycleMultiplicity.sum_cost_appearances (fun r => (hC r).1.1) (fun r => (hC r).2)
  have hpositive : ∀ i < N, 1 ≤ A i := by
    intro i hi
    obtain ⟨r, hr⟩ := hCover i hi
    exact CycleMultiplicity.appearance_pos r hr
  have hdPair : ∀ i r, i ∈ C r → CycleTight.next N i ∉ C r := by
    intro i r hi
    exact (hC r).1.2.2 i hi
  have hPair : ∀ i < N, A i + A (CycleTight.next N i) ≤ d :=
    fun i _ => CycleMultiplicity.appearances_pair_le (hdPair i)
  by_cases hzero : K = 0
  · apply CycleBalance.estimate (Y := ∅) hshape hm hd hMass hCost hpositive hPair
    · simp
    · simpa using hm
    · simp
    · intro hne
      exact False.elim (hne hzero)
    · exact hMin
  have hwide : 2*m < N := by omega
  obtain ⟨cut, hcut, hgap⟩ := CycleSlack.exists_slack hwide (by omega) hMass hPair
  let tight := fun i => decide (A i + A (CycleTight.next N i) = d)
  have hgap' : tight cut = false := by simp [tight, ne_of_lt hgap]
  obtain ⟨P, hP, hPTight, hPInd, hHit⟩ := CycleTight.independent_cover hcut hgap'
  have hPsmall : P.card < m := by
    apply CycleMultiplicity.tight_few_starts hwide hP hPInd
    intro i hi
    obtain ⟨r, hr⟩ := hCover i hi
    refine ⟨C r, hr, (hC r).1.2.1, ?_⟩
    intro j hj
    have eq : A j + A (CycleTight.next N j) = d := of_decide_eq_true (hPTight j hj)
    exact CycleMultiplicity.tight_pair_hits (hdPair j) eq r
  let Y := P.image (CycleTight.next N)
  have hY : Y ⊆ range N := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (Nat.mod_lt _ hN)
  have hYsmall : Y.card < m := by
    change (P.image (CycleTight.next N)).card < m
    rw [CycleTight.successors_card hP]
    exact hPsmall
  have hYInd := CycleTight.successors_independent hN hP hPInd
  refine CycleBalance.estimate hshape hm hd hMass hCost hpositive hPair
    hY hYsmall hYInd ?_ hMin
  intro _ i hi eq
  exact hHit i hi (by simp [tight, eq])

end CycleCover

end PEqualNP.Outside.L_meta_53172

open PEqualNP.Outside.L_meta_53172 in
theorem PEqualNP.Outside.L_meta_53172 : ∀ (K m q : Nat), 0 < m → ∀ w : Nat → Nat,
  let N := K+2*m
  let matching := fun M : Finset Nat => M ⊆ Finset.range N ∧ M.card=m ∧
    ∀ i ∈ M, (i+1) % N ∉ M
  (∀ M, matching M → q ≤ M.sum w) →
  (∀ i < N, ∃ M, matching M ∧ i ∈ M ∧ M.sum w=q) →
  (Finset.range N).sum w ≤ (K+2)*q := by
  intro K m q hm w
  let N := K + 2*m
  change (∀ M, CycleResidue.cycleMatching N m M → q ≤ M.sum w) →
    (∀ i < N, ∃ M, CycleResidue.cycleMatching N m M ∧ i ∈ M ∧ M.sum w = q) →
    (Finset.range N).sum w ≤ (K+2)*q
  intro hMin hCover
  have hFinite : ∀ i : Fin N, ∃ M, CycleResidue.cycleMatching N m M ∧
      i.val ∈ M ∧ M.sum w = q := fun i => hCover i.val i.isLt
  choose C hC using hFinite
  have hN : 2 ≤ N := by omega
  refine CycleCover.bound_from_collection (d := N) rfl hm hN C ?_ ?_ hMin
  · intro i
    exact ⟨(hC i).1, (hC i).2.2⟩
  · intro i hi
    exact ⟨⟨i, hi⟩, (hC ⟨i, hi⟩).2.1⟩
