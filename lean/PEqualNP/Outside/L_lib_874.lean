import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Logic.Relation
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.Finite
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_874_aux

open Classical
noncomputable section

section Cycle

variable {n : ℕ} (hn : 0 < n)

def ix (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt _ hn⟩

def next (i : Fin n) : Fin n := ix hn (i.val + 1)

def prev (i : Fin n) : Fin n := ix hn (i.val + (n - 1))

lemma ix_val (i : Fin n) : ix hn i.val = i := by
  ext
  exact Nat.mod_eq_of_lt i.isLt

lemma ix_add_left (a b : ℕ) : ix hn ((ix hn a).val + b) = ix hn (a + b) := by
  ext
  simp [ix, Nat.mod_add_mod]

lemma next_ix (a : ℕ) : next hn (ix hn a) = ix hn (a + 1) :=
  ix_add_left hn a 1

lemma next_prev (i : Fin n) : next hn (prev hn i) = i := by
  rw [prev, next_ix]
  ext
  have h1 : i.val + (n - 1) + 1 = i.val + n := by omega
  simp [ix, h1, Nat.mod_eq_of_lt i.isLt]

lemma prev_next (i : Fin n) : prev hn (next hn i) = i := by
  rw [next, prev, ix_add_left]
  ext
  have h1 : i.val + 1 + (n - 1) = i.val + n := by omega
  simp [ix, h1, Nat.mod_eq_of_lt i.isLt]

lemma next_inj : Function.Injective (next hn) := by
  intro a b hab
  have := congrArg (prev hn) hab
  rwa [prev_next, prev_next] at this

lemma prev_inj : Function.Injective (prev hn) := by
  intro a b hab
  have := congrArg (next hn) hab
  rwa [next_prev, next_prev] at this

lemma next_surj : Function.Surjective (next hn) := fun i => ⟨prev hn i, next_prev hn i⟩

def pos (a u : Fin n) : ℕ := (u.val + n - a.val) % n

lemma pos_lt (a u : Fin n) : pos a u < n := Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)

lemma ix_add_pos (a u : Fin n) : ix hn (a.val + pos a u) = u := by
  ext
  change (a.val + (u.val + n - a.val) % n) % n = u.val
  rw [Nat.add_mod_mod]
  have h1 : a.val + (u.val + n - a.val) = u.val + n := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt u.isLt]

lemma pos_inj (a : Fin n) : Function.Injective (pos a) := by
  have hn' : 0 < n := Nat.zero_lt_of_lt a.isLt
  intro u v huv
  have := congrArg (fun k => ix hn' (a.val + k)) huv
  simpa only [ix_add_pos] using this

lemma pos_self (a : Fin n) : pos a a = 0 := by
  unfold pos
  have h1 : a.val + n - a.val = n := by omega
  rw [h1, Nat.mod_self]

lemma pos_eq_zero_iff (a u : Fin n) : pos a u = 0 ↔ u = a := by
  constructor
  · intro h
    exact pos_inj a (h.trans (pos_self a).symm)
  · rintro rfl
    exact pos_self u

lemma pos_next (a u : Fin n) (hne : next hn u ≠ a) : pos a (next hn u) = pos a u + 1 := by
  have hlt : pos a u < n := pos_lt a u
  have hne_last : pos a u ≠ n - 1 := by
    intro heq
    apply hne
    have hu : u = ix hn (a.val + (n - 1)) := by
      rw [← heq, ix_add_pos]
    rw [hu, next_ix]
    ext
    have h1 : a.val + (n - 1) + 1 = a.val + n := by omega
    simp [ix, h1, Nat.mod_eq_of_lt a.isLt]
  have hlt2 : pos a u + 1 < n := by omega
  have hix : ix hn (a.val + (pos a u + 1)) = next hn u := by
    rw [← Nat.add_assoc, ← next_ix, ix_add_pos]
  have hmod : pos a (ix hn (a.val + (pos a u + 1))) = pos a u + 1 := by
    change ((a.val + (pos a u + 1)) % n + n - a.val) % n = pos a u + 1
    have h1 : (a.val + (pos a u + 1)) % n + n - a.val =
        ((a.val + (pos a u + 1)) % n) + (n - a.val) := by omega
    rw [h1, Nat.mod_add_mod]
    have h2 : a.val + (pos a u + 1) + (n - a.val) = (pos a u + 1) + n := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
  rwa [hix] at hmod

def step (S : Finset (Fin n)) (i j : Fin n) : Prop :=
  i ∈ S ∧ j ∈ S ∧ (next hn i = j ∨ next hn j = i)

def comp (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n) :=
  S.filter (fun u => Relation.ReflTransGen (step hn S) v u)

def parts (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  S.image (comp hn S)

lemma step_symm {S : Finset (Fin n)} {i j : Fin n} (h : step hn S i j) : step hn S j i :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

lemma rtg_symm {S : Finset (Fin n)} {u v : Fin n}
    (h : Relation.ReflTransGen (step hn S) u v) : Relation.ReflTransGen (step hn S) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (step_symm hn hstep) ih

lemma mem_comp_self {S : Finset (Fin n)} {v : Fin n} (hv : v ∈ S) : v ∈ comp hn S v :=
  Finset.mem_filter.mpr ⟨hv, Relation.ReflTransGen.refl⟩

lemma comp_eq_of_mem {S : Finset (Fin n)} {u v : Fin n} (hu : u ∈ comp hn S v) :
    comp hn S u = comp hn S v := by
  have huv := (Finset.mem_filter.mp hu).2
  ext w
  simp only [comp, Finset.mem_filter]
  exact ⟨fun ⟨hw, huw⟩ => ⟨hw, huv.trans huw⟩, fun ⟨hw, hvw⟩ => ⟨hw, (rtg_symm hn huv).trans hvw⟩⟩

lemma comp_subset (S : Finset (Fin n)) (v : Fin n) : comp hn S v ⊆ S :=
  Finset.filter_subset _ _

lemma parts_mem_nonempty {S : Finset (Fin n)} {C : Finset (Fin n)} (hC : C ∈ parts hn S) :
    C.Nonempty := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨v, mem_comp_self hn hv⟩

lemma parts_mem_subset {S : Finset (Fin n)} {C : Finset (Fin n)} (hC : C ∈ parts hn S) :
    C ⊆ S := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hC
  exact comp_subset hn S v

lemma parts_mem_eq_comp {S : Finset (Fin n)} {C : Finset (Fin n)} {u : Fin n}
    (hC : C ∈ parts hn S) (hu : u ∈ C) : C = comp hn S u := by
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hC
  exact (comp_eq_of_mem hn hu).symm

lemma parts_pairwise_disjoint (S : Finset (Fin n)) :
    (parts hn S : Set (Finset (Fin n))).PairwiseDisjoint id := by
  intro C₁ hC₁ C₂ hC₂ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro u hu₁ hu₂
  exact hne ((parts_mem_eq_comp hn hC₁ hu₁).trans (parts_mem_eq_comp hn hC₂ hu₂).symm)

lemma parts_biUnion_eq (S : Finset (Fin n)) : (parts hn S).biUnion id = S := by
  ext u
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨C, hC, hu⟩
    exact parts_mem_subset hn hC hu
  · intro hu
    exact ⟨comp hn S u, Finset.mem_image_of_mem _ hu, mem_comp_self hn hu⟩

lemma comp_singleton {S : Finset (Fin n)} {v : Fin n}
    (hv : v ∈ S) (hp : prev hn v ∉ S) (hnx : next hn v ∉ S) : comp hn S v = {v} := by
  ext u
  simp only [comp, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hrtg⟩
    rcases Relation.ReflTransGen.cases_head hrtg with rfl | ⟨w, hstep, _⟩
    · rfl
    · rcases hstep.2.2 with hw | hw
      · exact (hnx (hw ▸ hstep.2.1)).elim
      · have : w = prev hn v := by rw [← hw, prev_next]
        exact (hp (this ▸ hstep.2.1)).elim
  · rintro rfl
    exact ⟨hv, Relation.ReflTransGen.refl⟩

def bOut (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ∈ S ∧ next hn i ∉ S)

def bIn (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i ∉ S ∧ next hn i ∈ S)

def bTrans (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i ∈ S) ≠ (next hn i ∈ S))

def bMono (S : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i ∈ S) ↔ (next hn i ∈ S))

lemma card_bOut_eq_card_bIn (S : Finset (Fin n)) : (bOut hn S).card = (bIn hn S).card := by
  let both := Finset.univ.filter (fun i : Fin n => i ∈ S ∧ next hn i ∈ S)
  have h1 : S = both ∪ bOut hn S := by
    ext i
    simp only [both, bOut, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hni : next hn i ∈ S <;> simp [hni]
  have hd1 : Disjoint both (bOut hn S) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact (Finset.mem_filter.mp hi2).2.2 (Finset.mem_filter.mp hi1).2.2
  have h2 : S.image (prev hn) = both ∪ bIn hn S := by
    ext i
    simp only [both, bIn, Finset.mem_image, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [next_prev]
      by_cases hp : prev hn j ∈ S <;> simp [hp, hj]
    · intro h
      refine ⟨next hn i, ?_, prev_next hn i⟩
      rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
  have hd2 : Disjoint both (bIn hn S) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact (Finset.mem_filter.mp hi2).2.1 (Finset.mem_filter.mp hi1).2.1
  have hc1 : S.card = both.card + (bOut hn S).card := by
    conv_lhs => rw [h1]
    exact Finset.card_union_of_disjoint hd1
  have hc2 : S.card = both.card + (bIn hn S).card := by
    rw [← Finset.card_image_of_injective S (prev_inj hn), h2]
    exact Finset.card_union_of_disjoint hd2
  omega

lemma card_bTrans_eq_two_mul_bOut (S : Finset (Fin n)) :
    (bTrans hn S).card = 2 * (bOut hn S).card := by
  have hu : bTrans hn S = bOut hn S ∪ bIn hn S := by
    ext i
    simp only [bTrans, bOut, bIn, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ S <;> by_cases hni : next hn i ∈ S <;> simp [hi, hni]
  have hd : Disjoint (bOut hn S) (bIn hn S) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact (Finset.mem_filter.mp hi2).2.1 (Finset.mem_filter.mp hi1).2.1
  rw [hu, Finset.card_union_of_disjoint hd, card_bOut_eq_card_bIn]
  omega

lemma card_bMono_add_bTrans (S : Finset (Fin n)) :
    (bMono hn S).card + (bTrans hn S).card = n := by
  have hu : bMono hn S ∪ bTrans hn S = Finset.univ := by
    ext i
    simp only [bMono, bTrans, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    by_cases hi : i ∈ S <;> by_cases hni : next hn i ∈ S <;> simp [hi, hni]
  have hd : Disjoint (bMono hn S) (bTrans hn S) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 := (Finset.mem_filter.mp hi1).2
    have h2 := (Finset.mem_filter.mp hi2).2
    exact h2 (propext h1)
  have hcard := Finset.card_union_of_disjoint hd
  rw [hu, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard.symm

lemma pos_step {S : Finset (Fin n)} {a u v : Fin n} (ha : a ∉ S) (h : step hn S u v) :
    pos a v = pos a u + 1 ∨ pos a u = pos a v + 1 := by
  rcases h.2.2 with rfl | rfl
  · left
    exact pos_next hn a u (fun heq => ha (heq ▸ h.2.1))
  · right
    exact pos_next hn a v (fun heq => ha (heq ▸ h.1))

lemma rtg_ivt {S : Finset (Fin n)} {a u v : Fin n} (ha : a ∉ S) (hu : u ∈ S)
    (h : Relation.ReflTransGen (step hn S) u v) :
    ∀ k : ℕ, pos a u ≤ k → k ≤ pos a v → ∃ w ∈ S, pos a w = k := by
  induction h with
  | refl =>
    intro k hk1 hk2
    exact ⟨u, hu, by omega⟩
  | @tail b c _ hstep ih =>
    intro k hk1 hk2
    rcases pos_step hn ha hstep with hbc | hbc
    · by_cases hk : k ≤ pos a b
      · exact ih k hk1 hk
      · have hkc : k = pos a c := by omega
        exact ⟨c, hstep.2.1, hkc.symm⟩
    · exact ih k hk1 (by omega)

lemma card_parts_eq_card_bOut {S : Finset (Fin n)} (hS : S ≠ Finset.univ) :
    (parts hn S).card = (bOut hn S).card := by
  have hex : ∃ a : Fin n, a ∉ S := by
    by_contra hall
    push Not at hall
    exact hS (Finset.eq_univ_iff_forall.mpr hall)
  obtain ⟨a, ha⟩ := hex
  have hmap : (bOut hn S).image (comp hn S) = parts hn S := by
    ext C
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hi).2.1
    · intro hC
      obtain ⟨v, hv⟩ := parts_mem_nonempty hn hC
      have hvS : v ∈ S := parts_mem_subset hn hC hv
      have hexk : ∃ k : ℕ, ix hn (v.val + k) ∉ S := by
        refine ⟨pos v a, ?_⟩
        rw [ix_add_pos]
        exact ha
      let k₀ := Nat.find hexk
      have hk₀_out : ix hn (v.val + k₀) ∉ S := Nat.find_spec hexk
      have hk₀_pos : 0 < k₀ := by
        by_contra h0
        have heq : k₀ = 0 := by omega
        have : ix hn (v.val + 0) ∈ S := by simpa [ix_val] using hvS
        exact hk₀_out (heq ▸ this)
      have hreach : ∀ t : ℕ, t < k₀ → ix hn (v.val + t) ∈ comp hn S v := by
        intro t
        induction t with
        | zero =>
          intro _
          simpa [ix_val] using mem_comp_self hn hvS
        | succ t iht =>
          intro ht
          have hprev_in : ix hn (v.val + t) ∈ comp hn S v := iht (by omega)
          have hcur_in : ix hn (v.val + (t + 1)) ∈ S := by
            by_contra hnot
            exact Nat.find_min hexk ht hnot
          have hst : step hn S (ix hn (v.val + t)) (ix hn (v.val + (t + 1))) :=
            ⟨(Finset.mem_filter.mp hprev_in).1, hcur_in, Or.inl (by
              rw [next_ix, Nat.add_assoc])⟩
          exact Finset.mem_filter.mpr ⟨hcur_in, (Finset.mem_filter.mp hprev_in).2.tail hst⟩
      let i := ix hn (v.val + (k₀ - 1))
      have hi_comp : i ∈ comp hn S v := hreach (k₀ - 1) (by omega)
      have hi_out : i ∈ bOut hn S := by
        rw [bOut, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi_comp).1, ?_⟩
        have hnx : next hn i = ix hn (v.val + k₀) := by
          simp only [i, next_ix]
          congr 1
          omega
        rwa [hnx]
      refine ⟨i, hi_out, ?_⟩
      rw [comp_eq_of_mem hn hi_comp, ← parts_mem_eq_comp hn hC hv]
  have hinj : Set.InjOn (comp hn S) (bOut hn S : Set (Fin n)) := by
    intro i hi j hj heq
    have hi' := Finset.mem_filter.mp hi
    have hj' := Finset.mem_filter.mp hj
    have hij : Relation.ReflTransGen (step hn S) i j := by
      have : j ∈ comp hn S i := by rw [heq]; exact mem_comp_self hn hj'.2.1
      exact (Finset.mem_filter.mp this).2
    rcases lt_trichotomy (pos a i) (pos a j) with hlt | heqp | hgt
    · obtain ⟨w, hwS, hwp⟩ := rtg_ivt hn ha hi'.2.1 hij (pos a i + 1) (by omega) (by omega)
      have hne : next hn i ≠ a := by
        intro heqa
        have hpi : pos a i = n - 1 := by
          have : i = prev hn a := by rw [← heqa, prev_next]
          rw [this, prev]
          unfold pos ix
          simp only
          have h1 : (a.val + (n - 1)) % n + n - a.val = (a.val + (n - 1)) % n + (n - a.val) := by
            omega
          rw [h1, Nat.mod_add_mod]
          have h2 : a.val + (n - 1) + (n - a.val) = (n - 1) + n := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have := pos_lt a j
        omega
      have hw_eq : w = next hn i := pos_inj a (hwp.trans (pos_next hn a i hne).symm)
      exact (hi'.2.2 (hw_eq ▸ hwS)).elim
    · exact pos_inj a heqp
    · obtain ⟨w, hwS, hwp⟩ := rtg_ivt hn ha hj'.2.1 (rtg_symm hn hij) (pos a j + 1)
        (by omega) (by omega)
      have hne : next hn j ≠ a := by
        intro heqa
        have hpj : pos a j = n - 1 := by
          have : j = prev hn a := by rw [← heqa, prev_next]
          rw [this, prev]
          unfold pos ix
          simp only
          have h1 : (a.val + (n - 1)) % n + n - a.val = (a.val + (n - 1)) % n + (n - a.val) := by
            omega
          rw [h1, Nat.mod_add_mod]
          have h2 : a.val + (n - 1) + (n - a.val) = (n - 1) + n := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have := pos_lt a i
        omega
      have hw_eq : w = next hn j := pos_inj a (hwp.trans (pos_next hn a j hne).symm)
      exact (hj'.2.2 (hw_eq ▸ hwS)).elim
  rw [← hmap, Finset.card_image_of_injOn hinj]

lemma card_bTrans_eq_two_mul_parts {S : Finset (Fin n)} (hS : S ≠ Finset.univ) :
    (bTrans hn S).card = 2 * (parts hn S).card := by
  rw [card_bTrans_eq_two_mul_bOut, card_parts_eq_card_bOut hn hS]

lemma two_mul_card_parts_le {S : Finset (Fin n)} (hS : S ≠ Finset.univ) :
    2 * (parts hn S).card ≤ n := by
  have h1 := card_bMono_add_bTrans hn S
  rw [card_bTrans_eq_two_mul_parts hn hS] at h1
  omega

def fromPair (b : Bool) (E : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n =>
    (b != decide ((E.filter (fun k : Fin n => k.val < i.val)).card % 2 = 1)) = true)

lemma mem_fromPair_zero (b : Bool) (E : Finset (Fin n)) :
    (⟨0, hn⟩ : Fin n) ∈ fromPair b E ↔ b = true := by
  unfold fromPair
  rw [Finset.mem_filter]
  cases b <;> simp

lemma bTrans_fromPair (b : Bool) (E : Finset (Fin n)) (heven : E.card % 2 = 0) :
    bTrans hn (fromPair b E) = E := by
  ext i
  simp only [bTrans, fromPair, Finset.mem_filter, Finset.mem_univ, true_and]
  let p := (E.filter (fun k : Fin n => k.val < i.val)).card
  by_cases hlast : i.val + 1 < n
  · have hnx : (next hn i).val = i.val + 1 := Nat.mod_eq_of_lt hlast
    have hfilt : E.filter (fun k : Fin n => k.val < (next hn i).val) =
        if i ∈ E then insert i (E.filter (fun k : Fin n => k.val < i.val))
        else E.filter (fun k : Fin n => k.val < i.val) := by
      ext k
      rw [hnx]
      by_cases hiE : i ∈ E
      · simp only [hiE, ↓reduceIte, Finset.mem_filter, Finset.mem_insert]
        constructor
        · intro ⟨hkE, hlt⟩
          by_cases hki : k = i
          · exact Or.inl hki
          · right
            refine ⟨hkE, ?_⟩
            have : k.val ≠ i.val := fun h => hki (Fin.ext h)
            omega
        · rintro (rfl | ⟨hkE, hlt⟩)
          · exact ⟨hiE, by omega⟩
          · exact ⟨hkE, by omega⟩
      · simp only [hiE, ↓reduceIte, Finset.mem_filter]
        constructor
        · intro ⟨hkE, hlt⟩
          have : k.val ≠ i.val := fun h => hiE (Fin.ext h ▸ hkE)
          exact ⟨hkE, by omega⟩
        · intro ⟨hkE, hlt⟩
          exact ⟨hkE, by omega⟩
    have hnotin : i ∉ E.filter (fun k : Fin n => k.val < i.val) := by simp
    have hcard : (E.filter (fun k : Fin n => k.val < (next hn i).val)).card =
        p + if i ∈ E then 1 else 0 := by
      rw [hfilt]
      by_cases hiE : i ∈ E
      · simp only [hiE, ↓reduceIte, Finset.card_insert_of_notMem hnotin, p]
      · simp only [hiE, ↓reduceIte, Nat.add_zero, p]
    rw [hcard]
    change (((b != decide (p % 2 = 1)) = true) ≠
      ((b != decide ((p + if i ∈ E then 1 else 0) % 2 = 1)) = true)) ↔ i ∈ E
    by_cases hiE : i ∈ E <;> cases b <;>
      rcases Nat.mod_two_eq_zero_or_one p with hp | hp <;> simp [hiE, hp, Nat.add_mod]
  · have hval : i.val = n - 1 := by omega
    have hnx : (next hn i).val = 0 := by
      change (i.val + 1) % n = 0
      have : i.val + 1 = n := by omega
      rw [this, Nat.mod_self]
    have hfilt0 : E.filter (fun k : Fin n => k.val < (next hn i).val) = ∅ := by
      rw [hnx]
      ext k
      simp
    have hEeq : E = if i ∈ E then insert i (E.filter (fun k : Fin n => k.val < i.val))
        else E.filter (fun k : Fin n => k.val < i.val) := by
      ext k
      by_cases hiE : i ∈ E
      · simp only [hiE, ↓reduceIte, Finset.mem_insert, Finset.mem_filter]
        constructor
        · intro hkE
          by_cases hki : k = i
          · exact Or.inl hki
          · right
            have : k.val ≠ i.val := fun h => hki (Fin.ext h)
            exact ⟨hkE, by omega⟩
        · rintro (rfl | ⟨hkE, _⟩)
          · exact hiE
          · exact hkE
      · simp only [hiE, ↓reduceIte, Finset.mem_filter]
        constructor
        · intro hkE
          have : k.val ≠ i.val := fun h => hiE (Fin.ext h ▸ hkE)
          exact ⟨hkE, by omega⟩
        · exact And.left
    have hnotin : i ∉ E.filter (fun k : Fin n => k.val < i.val) := by simp
    have hcardE : E.card = p + if i ∈ E then 1 else 0 := by
      conv_lhs => rw [hEeq]
      by_cases hiE : i ∈ E
      · simp only [hiE, ↓reduceIte, Finset.card_insert_of_notMem hnotin, p]
      · simp only [hiE, ↓reduceIte, Nat.add_zero, p]
    rw [hfilt0]
    change (((b != decide (p % 2 = 1)) = true) ≠ ((b != decide (0 % 2 = 1)) = true)) ↔ i ∈ E
    by_cases hiE : i ∈ E
    · have hp1 : p % 2 = 1 := by simp only [hiE, ↓reduceIte] at hcardE; omega
      cases b <;> simp [hiE, hp1]
    · have hp0 : p % 2 = 0 := by simp only [hiE, ↓reduceIte, Nat.add_zero] at hcardE; omega
      cases b <;> simp [hiE, hp0]

lemma fromPair_bTrans (S : Finset (Fin n)) :
    fromPair (decide ((⟨0, hn⟩ : Fin n) ∈ S)) (bTrans hn S) = S := by
  have heven : (bTrans hn S).card % 2 = 0 := by
    rw [card_bTrans_eq_two_mul_bOut]
    omega
  let S' := fromPair (decide ((⟨0, hn⟩ : Fin n) ∈ S)) (bTrans hn S)
  have htr : bTrans hn S' = bTrans hn S := bTrans_fromPair hn _ _ heven
  have h0 : (⟨0, hn⟩ : Fin n) ∈ S' ↔ (⟨0, hn⟩ : Fin n) ∈ S := by
    rw [mem_fromPair_zero hn]
    simp
  have hall : ∀ k : ℕ, (hk : k < n) → ((⟨k, hk⟩ : Fin n) ∈ S' ↔ (⟨k, hk⟩ : Fin n) ∈ S) := by
    intro k
    induction k with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      let j : Fin n := ⟨k, hk'⟩
      have hnx : next hn j = ⟨k + 1, hk⟩ := by
        ext
        exact Nat.mod_eq_of_lt hk
      have hj := ih hk'
      have hflip : ((j ∈ S') ≠ (next hn j ∈ S')) ↔ ((j ∈ S) ≠ (next hn j ∈ S)) := by
        have hmem := Finset.ext_iff.mp htr j
        simpa only [bTrans, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
      rw [hnx] at hflip
      by_cases hjS : j ∈ S
      · have hjS' : j ∈ S' := hj.mpr hjS
        by_cases h1 : (⟨k + 1, hk⟩ : Fin n) ∈ S' <;> by_cases h2 : (⟨k + 1, hk⟩ : Fin n) ∈ S <;>
          simp_all
      · have hjS' : j ∉ S' := fun h => hjS (hj.mp h)
        by_cases h1 : (⟨k + 1, hk⟩ : Fin n) ∈ S' <;> by_cases h2 : (⟨k + 1, hk⟩ : Fin n) ∈ S <;>
          simp_all
  ext i
  exact hall i.val i.isLt

lemma card_supports_with_parts (c : ℕ) (hc : 1 ≤ c) :
    ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S ≠ Finset.univ ∧ (parts hn S).card = c)).card =
      2 * Nat.choose n (2 * c) := by
  let lhs := (Finset.univ : Finset (Finset (Fin n))).filter
    (fun S => S ≠ Finset.univ ∧ (parts hn S).card = c)
  let rhs := (Finset.univ : Finset Bool) ×ˢ (Finset.univ : Finset (Fin n)).powersetCard (2 * c)
  have hbij : lhs.card = rhs.card := by
    refine Finset.card_bij (fun S _ => (decide ((⟨0, hn⟩ : Fin n) ∈ S), bTrans hn S))
      ?_ ?_ ?_
    · intro S hS
      obtain ⟨_, hne, hpc⟩ := Finset.mem_filter.mp hS
      rw [Finset.mem_product]
      refine ⟨Finset.mem_univ _, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩⟩
      rw [card_bTrans_eq_two_mul_parts hn hne, hpc]
    · intro S₁ _ S₂ _ heq
      have hb : decide ((⟨0, hn⟩ : Fin n) ∈ S₁) = decide ((⟨0, hn⟩ : Fin n) ∈ S₂) :=
        congrArg Prod.fst heq
      have hE : bTrans hn S₁ = bTrans hn S₂ := congrArg Prod.snd heq
      rw [← fromPair_bTrans hn S₁, ← fromPair_bTrans hn S₂, hb, hE]
    · intro p hp
      obtain ⟨b, E⟩ := p
      rw [Finset.mem_product] at hp
      have hEc : E.card = 2 * c := (Finset.mem_powersetCard.mp hp.2).2
      have heven : E.card % 2 = 0 := by omega
      let S := fromPair b E
      have htr : bTrans hn S = E := bTrans_fromPair hn b E heven
      have hne : S ≠ Finset.univ := by
        intro huniv
        have hpos : 0 < E.card := by omega
        obtain ⟨i, hiE⟩ := Finset.card_pos.mp hpos
        rw [← htr, bTrans, Finset.mem_filter] at hiE
        exact hiE.2 (by simp [huniv])
      have hpc : (parts hn S).card = c := by
        have h2 := card_bTrans_eq_two_mul_parts hn hne
        rw [htr, hEc] at h2
        omega
      refine ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hpc⟩, ?_⟩
      ext1
      · simp [S, mem_fromPair_zero]
      · exact htr
  rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_bool,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma parts_sdiff_union {S : Finset (Fin n)} {J : Finset (Finset (Fin n))} (_hJ : J ⊆ parts hn S) :
    parts hn ((parts hn S \ J).biUnion id) = parts hn S \ J := by
  let S' := (parts hn S \ J).biUnion id
  have hS'sub : S' ⊆ S := by
    intro u hu
    obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hu
    exact parts_mem_subset hn (Finset.mem_sdiff.mp hC).1 huC
  have hcomp_eq : ∀ C ∈ parts hn S \ J, ∀ v ∈ C, comp hn S' v = C := by
    intro C hC v hv
    have hCp : C ∈ parts hn S := (Finset.mem_sdiff.mp hC).1
    have hCsub : C ⊆ S' := fun u hu => Finset.mem_biUnion.mpr ⟨C, hC, hu⟩
    have hCE : C = comp hn S v := parts_mem_eq_comp hn hCp hv
    ext u
    constructor
    · intro hu
      have ⟨huS', hrtg⟩ := Finset.mem_filter.mp hu
      have hrtgS : ∀ x : Fin n, Relation.ReflTransGen (step hn S') v x →
          Relation.ReflTransGen (step hn S) v x := by
        intro x hx
        induction hx with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hst ih => exact ih.tail ⟨hS'sub hst.1, hS'sub hst.2.1, hst.2.2⟩
      rw [hCE]
      exact Finset.mem_filter.mpr ⟨hS'sub huS', hrtgS u hrtg⟩
    · intro hu
      rw [hCE] at hu
      have ⟨_, hrtg⟩ := Finset.mem_filter.mp hu
      have hrtgS' : ∀ x : Fin n, Relation.ReflTransGen (step hn S) v x →
          Relation.ReflTransGen (step hn S') v x := by
        intro x hx
        induction hx with
        | refl => exact Relation.ReflTransGen.refl
        | @tail a b hab hst ih =>
          have haC : a ∈ C := by rw [hCE]; exact Finset.mem_filter.mpr ⟨hst.1, hab⟩
          have hbC : b ∈ C := by rw [hCE]; exact Finset.mem_filter.mpr ⟨hst.2.1, hab.tail hst⟩
          exact ih.tail ⟨hCsub haC, hCsub hbC, hst.2.2⟩
      exact Finset.mem_filter.mpr ⟨hCsub (hCE ▸ hu), hrtgS' u hrtg⟩
  ext C
  constructor
  · intro hC
    obtain ⟨v, hvS', rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨C₀, hC₀, hvC₀⟩ := Finset.mem_biUnion.mp hvS'
    rwa [hcomp_eq C₀ hC₀ v hvC₀]
  · intro hC
    obtain ⟨v, hv⟩ := parts_mem_nonempty hn (Finset.mem_sdiff.mp hC).1
    have hvS' : v ∈ S' := Finset.mem_biUnion.mpr ⟨C, hC, hv⟩
    rw [← hcomp_eq C hC v hv]
    exact Finset.mem_image_of_mem _ hvS'

end Cycle

section Part1

lemma localSpan_imp_cutoff {n m d : ℕ} (hn : 0 < n) (h : Fin n → (Fin m → ZMod 2)) :
    let F := ZMod 2
    let A := Fin m → F
    let D := Submodule.span F (Set.range h)
    let r := Module.finrank F D
    let rankOn := fun S : Finset (Fin n) =>
      Module.finrank F (Submodule.span F
        (↑((parts hn S).image (fun C => ∑ i ∈ C, h i)) : Set A))
    (∃ b : ℕ, 0 < b ∧ (2 * b + 1) * (n - 2 * d) < n ∧
      ∀ i : Fin n, Submodule.span F (Set.range
        (fun j : Fin b => h (ix hn (i.val + 2 * j.val)))) = D) →
    (∀ S : Finset (Fin n), S ≠ Finset.univ →
      rankOn S < r → (parts hn S).card - rankOn S < d) := by
  intro F A D r rankOn ⟨b, hb, hbound, hspan⟩ S hS hlt
  by_contra hge
  have hcd : d ≤ (parts hn S).card := by omega
  have hmono_le : (bMono hn S).card ≤ n - 2 * d := by
    have h1 := card_bMono_add_bTrans hn S
    rw [card_bTrans_eq_two_mul_parts hn hS] at h1
    omega
  let bad : Finset (Fin n) := Finset.univ.filter (fun v : Fin n =>
    ∃ k ∈ Finset.range (2 * b + 1), ix hn (v.val + k) ∈ bMono hn S)
  have hbad_sub : bad ⊆ (Finset.range (2 * b + 1) ×ˢ bMono hn S).image
      (fun p => ix hn (p.2.val + (n - p.1 % n))) := by
    intro v hv
    obtain ⟨_, k, hk, hmem⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_image.mpr ⟨(k, ix hn (v.val + k)), Finset.mem_product.mpr ⟨hk, hmem⟩, ?_⟩
    simp only
    rw [ix_add_left]
    ext
    change (v.val + k + (n - k % n)) % n = v.val
    have hkm : k % n < n := Nat.mod_lt k hn
    have h1 : k = n * (k / n) + k % n := (Nat.div_add_mod k n).symm
    have h2 : v.val + k + (n - k % n) = v.val + n * (k / n) + n := by omega
    rw [h2, Nat.add_mod_right, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.isLt]
  have hbad_card : bad.card < n := by
    calc bad.card
        ≤ ((Finset.range (2 * b + 1) ×ˢ bMono hn S).image
            (fun p => ix hn (p.2.val + (n - p.1 % n)))).card := Finset.card_le_card hbad_sub
      _ ≤ (Finset.range (2 * b + 1) ×ˢ bMono hn S).card := Finset.card_image_le
      _ = (2 * b + 1) * (bMono hn S).card := by rw [Finset.card_product, Finset.card_range]
      _ ≤ (2 * b + 1) * (n - 2 * d) := Nat.mul_le_mul_left _ hmono_le
      _ < n := hbound
  have hex_good : ∃ v₀ : Fin n, v₀ ∉ bad := by
    by_contra hall
    push Not at hall
    have : bad = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hbad_card
    omega
  obtain ⟨v₀, hv₀⟩ := hex_good
  have hno_mono : ∀ k : ℕ, k < 2 * b + 1 → ix hn (v₀.val + k) ∉ bMono hn S := by
    intro k hk hmem
    exact hv₀ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, k, Finset.mem_range.mpr hk, hmem⟩)
  have halt : ∀ k : ℕ, k ≤ 2 * b + 1 →
      (ix hn (v₀.val + k) ∈ S ↔ if k % 2 = 0 then v₀ ∈ S else v₀ ∉ S) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [ix_val]
    | succ k ih =>
      intro hk
      have hstep_b : ¬ ((ix hn (v₀.val + k) ∈ S) ↔ (next hn (ix hn (v₀.val + k)) ∈ S)) := by
        intro heq
        exact hno_mono k (by omega) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
      rw [next_ix, Nat.add_assoc] at hstep_b
      have hih := ih (by omega)
      rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
      · have hk1' : (k + 1) % 2 = 1 := by omega
        simp only [hk0, ↓reduceIte] at hih
        simp only [hk1', one_ne_zero, ↓reduceIte]
        by_cases h0 : v₀ ∈ S
        · have hcur : ix hn (v₀.val + k) ∈ S := hih.mpr h0
          exact ⟨fun hnext => (hstep_b ⟨fun _ => hnext, fun _ => hcur⟩).elim,
            fun hnot => (hnot h0).elim⟩
        · have hcur : ix hn (v₀.val + k) ∉ S := fun h => h0 (hih.mp h)
          constructor
          · intro _; exact h0
          · intro _
            by_contra hnext
            exact hstep_b ⟨fun h => (hcur h).elim, fun h => (hnext h).elim⟩
      · have hk0' : (k + 1) % 2 = 0 := by omega
        simp only [hk1, one_ne_zero, ↓reduceIte] at hih
        simp only [hk0', ↓reduceIte]
        by_cases h0 : v₀ ∈ S
        · have hcur : ix hn (v₀.val + k) ∉ S := fun h => hih.mp h h0
          constructor
          · intro _; exact h0
          · intro _
            by_contra hnext
            exact hstep_b ⟨fun h => (hcur h).elim, fun h => (hnext h).elim⟩
        · have hcur : ix hn (v₀.val + k) ∈ S := hih.mpr h0
          exact ⟨fun hnext => (hstep_b ⟨fun _ => hnext, fun _ => hcur⟩).elim,
            fun h => (h0 h).elim⟩
  let i₀ : Fin n := if v₀ ∈ S then ix hn (v₀.val + 2) else ix hn (v₀.val + 1)
  have hsing : ∀ j : Fin b, {ix hn (i₀.val + 2 * j.val)} ∈ parts hn S := by
    intro j
    by_cases hv : v₀ ∈ S
    · have hi₀ : i₀ = ix hn (v₀.val + 2) := by simp [i₀, hv]
      rw [hi₀, ix_add_left, Nat.add_assoc]
      have hw : ix hn (v₀.val + (2 + 2 * j.val)) ∈ S := by
        have h1 := halt (2 + 2 * j.val) (by omega)
        have hmod : (2 + 2 * j.val) % 2 = 0 := by omega
        simp only [hmod, ↓reduceIte] at h1
        exact h1.mpr hv
      have hnx : next hn (ix hn (v₀.val + (2 + 2 * j.val))) ∉ S := by
        rw [next_ix, Nat.add_assoc]
        have h1 := halt (2 + 2 * j.val + 1) (by omega)
        have hmod : (2 + 2 * j.val + 1) % 2 = 1 := by omega
        simp only [hmod, one_ne_zero, ↓reduceIte] at h1
        exact fun h => h1.mp h hv
      have hpv : prev hn (ix hn (v₀.val + (2 + 2 * j.val))) ∉ S := by
        have heq : prev hn (ix hn (v₀.val + (2 + 2 * j.val))) = ix hn (v₀.val + (1 + 2 * j.val)) := by
          apply next_inj hn
          rw [next_prev, next_ix]
          congr 1
          omega
        rw [heq]
        have h1 := halt (1 + 2 * j.val) (by omega)
        have hmod : (1 + 2 * j.val) % 2 = 1 := by omega
        simp only [hmod, one_ne_zero, ↓reduceIte] at h1
        exact fun h => h1.mp h hv
      rw [← comp_singleton hn hw hpv hnx]
      exact Finset.mem_image_of_mem _ hw
    · have hi₀ : i₀ = ix hn (v₀.val + 1) := by simp [i₀, hv]
      rw [hi₀, ix_add_left, Nat.add_assoc]
      have hw : ix hn (v₀.val + (1 + 2 * j.val)) ∈ S := by
        have h1 := halt (1 + 2 * j.val) (by omega)
        have hmod : (1 + 2 * j.val) % 2 = 1 := by omega
        simp only [hmod, one_ne_zero, ↓reduceIte] at h1
        exact h1.mpr hv
      have hnx : next hn (ix hn (v₀.val + (1 + 2 * j.val))) ∉ S := by
        rw [next_ix, Nat.add_assoc]
        have h1 := halt (1 + 2 * j.val + 1) (by omega)
        have hmod : (1 + 2 * j.val + 1) % 2 = 0 := by omega
        simp only [hmod, ↓reduceIte] at h1
        exact fun h => hv (h1.mp h)
      have hpv : prev hn (ix hn (v₀.val + (1 + 2 * j.val))) ∉ S := by
        have heq : prev hn (ix hn (v₀.val + (1 + 2 * j.val))) = ix hn (v₀.val + (2 * j.val)) := by
          apply next_inj hn
          rw [next_prev, next_ix]
          congr 1
          omega
        rw [heq]
        have h1 := halt (2 * j.val) (by omega)
        have hmod : (2 * j.val) % 2 = 0 := by omega
        simp only [hmod, ↓reduceIte] at h1
        exact fun h => hv (h1.mp h)
      rw [← comp_singleton hn hw hpv hnx]
      exact Finset.mem_image_of_mem _ hw
  let M : Submodule F A := Submodule.span F (↑((parts hn S).image (fun C => ∑ i ∈ C, h i)) : Set A)
  have hDM : D ≤ M := by
    rw [← hspan i₀, Submodule.span_le]
    rintro v ⟨j, rfl⟩
    apply Submodule.subset_span
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨{ix hn (i₀.val + 2 * j.val)}, hsing j, by simp⟩)
  have hMD : M ≤ D := by
    rw [Submodule.span_le]
    intro v hv
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    exact Submodule.sum_mem D (fun i _ => Submodule.subset_span ⟨i, rfl⟩)
  have heq : M = D := le_antisymm hMD hDM
  have hreq : rankOn S = r := by
    change Module.finrank F M = Module.finrank F D
    rw [heq]
  omega

end Part1

section Part2

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

lemma zmod2_mul_eq_one_left {a b : ZMod 2} (h : a * b = 1) : a = 1 := by
  fin_cases a
  · exfalso
    have h0 : (0 : ZMod 2) = 1 := by
      have h' : (0 : ZMod 2) * b = 1 := h
      rwa [zero_mul] at h'
    exact zero_ne_one h0
  · rfl

def supp {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ x ∈ U, x i ≠ 0)

def isConstOn {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (x : Fin n → ZMod 2) : Prop :=
  ∀ C ∈ parts hn S, ∀ i ∈ C, ∀ j ∈ C, x i = x j

def inParity {n m : ℕ} (h : Fin n → (Fin m → ZMod 2)) (x : Fin n → ZMod 2) : Prop :=
  ∀ b : Fin m, (∑ i : Fin n, h i b * x i) = 0

lemma good_const_iff {n : ℕ} (hn : 0 < n) (U : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next hn i) = x (next hn i) * y i) ↔
      (∀ x ∈ U, isConstOn hn (supp U) x) := by
  constructor
  · intro hsym x hx C hC i hi j hj
    have hstep_eq : ∀ a b : Fin n, step hn (supp U) a b → x a = x b := by
      have hadj : ∀ a : Fin n, a ∈ supp U → next hn a ∈ supp U → x a = x (next hn a) := by
        intro a ha hna
        obtain ⟨u, huU, hua⟩ := (Finset.mem_filter.mp ha).2
        obtain ⟨v, hvU, hvna⟩ := (Finset.mem_filter.mp hna).2
        have hua1 : u a = 1 := zmod2_eq_one_of_ne_zero hua
        have hvna1 : v (next hn a) = 1 := zmod2_eq_one_of_ne_zero hvna
        have h1 := hsym u huU v hvU a
        rw [hua1, hvna1, one_mul] at h1
        have huna1 : u (next hn a) = 1 := zmod2_mul_eq_one_left h1.symm
        have h2 := hsym x hx u huU a
        simpa [hua1, huna1] using h2
      intro a b hab
      rcases hab.2.2 with rfl | rfl
      · exact hadj a hab.1 hab.2.1
      · exact (hadj b hab.2.1 hab.1).symm
    have hrtg_eq : ∀ a b : Fin n, Relation.ReflTransGen (step hn (supp U)) a b → x a = x b := by
      intro a b hrtg
      induction hrtg with
      | refl => rfl
      | tail _ hst ih => exact ih.trans (hstep_eq _ _ hst)
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hC
    exact (hrtg_eq v i (Finset.mem_filter.mp hi).2).symm.trans
      (hrtg_eq v j (Finset.mem_filter.mp hj).2)
  · intro hconst x hx y hy i
    by_cases hi : i ∈ supp U
    · by_cases hni : next hn i ∈ supp U
      · have hC : comp hn (supp U) i ∈ parts hn (supp U) := Finset.mem_image_of_mem _ hi
        have hiC : i ∈ comp hn (supp U) i := mem_comp_self hn hi
        have hniC : next hn i ∈ comp hn (supp U) i :=
          Finset.mem_filter.mpr ⟨hni, Relation.ReflTransGen.single ⟨hi, hni, Or.inl rfl⟩⟩
        rw [hconst x hx _ hC i hiC (next hn i) hniC,
          hconst y hy _ hC i hiC (next hn i) hniC]
      · have hx0 : x (next hn i) = 0 := by
          by_contra hne
          exact hni (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hne⟩)
        have hy0 : y (next hn i) = 0 := by
          by_contra hne
          exact hni (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy, hne⟩)
        simp [hx0, hy0]
    · have hx0 : x i = 0 := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hne⟩)
      have hy0 : y i = 0 := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy, hne⟩)
      simp [hx0, hy0]

lemma good_supp_props {n d : ℕ} (hn : 0 < n) (hd : 2 ≤ d)
    (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hdim : Module.finrank (ZMod 2) U = d)
    (hconst : ∀ x ∈ U, isConstOn hn (supp U) x) :
    supp U ≠ Finset.univ ∧ 1 ≤ (parts hn (supp U)).card ∧ (parts hn (supp U)).card ≤ n / 2 := by
  have hne_univ : supp U ≠ Finset.univ := by
    intro huniv
    have hreach : ∀ k : ℕ, (hk : k < n) →
        Relation.ReflTransGen (step hn Finset.univ) ⟨0, hn⟩ ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero => intro _; exact Relation.ReflTransGen.refl
      | succ k ih =>
        intro hk
        have hnx : next hn ⟨k, by omega⟩ = ⟨k + 1, hk⟩ := by ext; exact Nat.mod_eq_of_lt hk
        exact (ih (by omega)).tail ⟨Finset.mem_univ _, Finset.mem_univ _, Or.inl hnx⟩
    have hle : U ≤ Submodule.span (ZMod 2) ({(fun _ : Fin n => (1 : ZMod 2))} : Set (Fin n → ZMod 2)) := by
      intro x hx
      have hxall : ∀ i : Fin n, x i = x ⟨0, hn⟩ := by
        intro i
        have hC : comp hn (supp U) ⟨0, hn⟩ ∈ parts hn (supp U) :=
          Finset.mem_image_of_mem _ (huniv.symm ▸ Finset.mem_univ _)
        have h0C : ⟨0, hn⟩ ∈ comp hn (supp U) ⟨0, hn⟩ :=
          mem_comp_self hn (huniv.symm ▸ Finset.mem_univ _)
        have hiC : i ∈ comp hn (supp U) ⟨0, hn⟩ := by
          rw [huniv]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreach i.val i.isLt⟩
        exact (hconst x hx _ hC ⟨0, hn⟩ h0C i hiC).symm
      have heq : x = x ⟨0, hn⟩ • (fun _ : Fin n => (1 : ZMod 2)) := by
        ext i
        simp [hxall i]
      rw [heq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    have hfr1 : Module.finrank (ZMod 2) U ≤ 1 := by
      calc Module.finrank (ZMod 2) U
          ≤ Module.finrank (ZMod 2)
              (Submodule.span (ZMod 2) ({(fun _ : Fin n => (1 : ZMod 2))} : Set (Fin n → ZMod 2))) :=
            Submodule.finrank_mono hle
        _ ≤ 1 := by
          have hcard : ({(fun _ : Fin n => (1 : ZMod 2))} : Set (Fin n → ZMod 2)).toFinset.card = 1 := by
            simp
          simpa [hcard] using
            (finrank_span_le_card (R := ZMod 2) ({(fun _ : Fin n => (1 : ZMod 2))} : Set (Fin n → ZMod 2)))
    omega
  have hne_empty : (supp U).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hbot : U = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      ext i
      by_contra hne
      have : i ∈ supp U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hne⟩
      rw [hemp] at this
      exact Finset.notMem_empty _ this
    rw [hbot, finrank_bot] at hdim
    omega
  have hge1 : 1 ≤ (parts hn (supp U)).card := by
    obtain ⟨v, hv⟩ := hne_empty
    exact Finset.card_pos.mpr ⟨comp hn (supp U) v, Finset.mem_image_of_mem _ hv⟩
  have hle_half : (parts hn (supp U)).card ≤ n / 2 := by
    have h2 := two_mul_card_parts_le hn hne_univ
    omega
  exact ⟨hne_univ, hge1, hle_half⟩

def emb {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    (↥(parts hn S) → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
  toFun α i := ∑ C : ↥(parts hn S), if i ∈ C.1 then α C else 0
  map_add' α β := by
    ext i
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    congr 1
    ext C
    split_ifs <;> simp
  map_smul' r α := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    congr 1
    ext C
    split_ifs <;> simp

lemma emb_apply_mem {n : ℕ} (hn : 0 < n) (S : Finset (Fin n))
    (α : ↥(parts hn S) → ZMod 2) (C : ↥(parts hn S)) {i : Fin n} (hi : i ∈ C.1) :
    emb hn S α i = α C := by
  change (∑ C' : ↥(parts hn S), if i ∈ C'.1 then α C' else 0) = α C
  rw [Finset.sum_eq_single C]
  · simp [hi]
  · intro C' _ hne
    have hnot : i ∉ C'.1 := by
      intro hi'
      apply hne
      apply Subtype.ext
      exact (parts_mem_eq_comp hn C'.2 hi').trans (parts_mem_eq_comp hn C.2 hi).symm
    simp [hnot]
  · intro h
    exact (h (Finset.mem_univ C)).elim

lemma emb_apply_notMem {n : ℕ} (hn : 0 < n) (S : Finset (Fin n))
    (α : ↥(parts hn S) → ZMod 2) {i : Fin n} (hi : i ∉ S) :
    emb hn S α i = 0 := by
  change (∑ C' : ↥(parts hn S), if i ∈ C'.1 then α C' else 0) = 0
  apply Finset.sum_eq_zero
  intro C' _
  have hnot : i ∉ C'.1 := fun h => hi (parts_mem_subset hn C'.2 h)
  simp [hnot]

lemma emb_injective {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) :
    Function.Injective (emb hn S) := by
  intro α β hab
  ext C
  obtain ⟨i, hi⟩ := parts_mem_nonempty hn C.2
  have := congrFun hab i
  rwa [emb_apply_mem hn S α C hi, emb_apply_mem hn S β C hi] at this

def chkMap {n m : ℕ} (hn : 0 < n) (h : Fin n → (Fin m → ZMod 2)) (S : Finset (Fin n)) :
    (↥(parts hn S) → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) where
  toFun α := ∑ C : ↥(parts hn S), α C • (∑ i ∈ C.1, h i)
  map_add' α β := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r α := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

lemma chkMap_apply_eq_parity {n m : ℕ} (hn : 0 < n) (h : Fin n → (Fin m → ZMod 2))
    (S : Finset (Fin n)) (α : ↥(parts hn S) → ZMod 2) (b : Fin m) :
    chkMap hn h S α b = ∑ i : Fin n, h i b * emb hn S α i := by
  have h1 : (∑ i : Fin n, h i b * emb hn S α i) = ∑ i ∈ S, h i b * emb hn S α i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hiS
    rw [emb_apply_notMem hn S α hiS, mul_zero]
  have h2 : (∑ i ∈ S, h i b * emb hn S α i) =
      ∑ i ∈ (parts hn S).biUnion id, h i b * emb hn S α i :=
    Finset.sum_congr (parts_biUnion_eq hn S).symm fun _ _ => rfl
  rw [h1, h2, Finset.sum_biUnion (parts_pairwise_disjoint hn S)]
  change (∑ C : ↥(parts hn S), α C • (∑ i ∈ C.1, h i)) b = _
  rw [Finset.sum_apply, ← Finset.sum_attach (parts hn S)]
  congr 1
  ext C
  simp only [id_eq, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [emb_apply_mem hn S α C hi, mul_comm]

lemma inParity_emb_iff {n m : ℕ} (hn : 0 < n) (h : Fin n → (Fin m → ZMod 2))
    (S : Finset (Fin n)) (α : ↥(parts hn S) → ZMod 2) :
    inParity h (emb hn S α) ↔ α ∈ LinearMap.ker (chkMap hn h S) := by
  simp only [inParity, LinearMap.mem_ker, funext_iff, Pi.zero_apply, chkMap_apply_eq_parity]

lemma range_chkMap {n m : ℕ} (hn : 0 < n) (h : Fin n → (Fin m → ZMod 2))
    (S : Finset (Fin n)) :
    LinearMap.range (chkMap hn h S) =
      Submodule.span (ZMod 2) (↑((parts hn S).image (fun C => ∑ i ∈ C, h i)) : Set (Fin m → ZMod 2)) := by
  apply le_antisymm
  · rintro _ ⟨α, rfl⟩
    apply Submodule.sum_mem
    intro C _
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ C.2)))
  · rw [Submodule.span_le]
    intro v hv
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    refine ⟨(Pi.single (⟨C, hC⟩ : ↥(parts hn S)) (1 : ZMod 2) : ↥(parts hn S) → ZMod 2), ?_⟩
    change (∑ C' : ↥(parts hn S),
      (Pi.single (⟨C, hC⟩ : ↥(parts hn S)) (1 : ZMod 2) : ↥(parts hn S) → ZMod 2) C' •
      (∑ i ∈ C'.1, h i)) = ∑ i ∈ C, h i
    rw [Finset.sum_eq_single (⟨C, hC⟩ : ↥(parts hn S))]
    · simp
    · intro C' _ hne
      simp [Pi.single_eq_of_ne hne]
    · intro hmem
      exact (hmem (Finset.mem_univ _)).elim

lemma finrank_ker_chkMap {n m : ℕ} (hn : 0 < n) (h : Fin n → (Fin m → ZMod 2))
    (S : Finset (Fin n)) :
    Module.finrank (ZMod 2) (LinearMap.ker (chkMap hn h S)) =
      (parts hn S).card -
        Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2)
            (↑((parts hn S).image (fun C => ∑ i ∈ C, h i)) : Set (Fin m → ZMod 2))) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (chkMap hn h S)
  rw [range_chkMap, Module.finrank_pi, Fintype.card_coe] at hrn
  omega

lemma rankOn_le_finrank_D {n m : ℕ} (hn : 0 < n) (h : Fin n → (Fin m → ZMod 2))
    (S : Finset (Fin n)) :
    Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2)
        (↑((parts hn S).image (fun C => ∑ i ∈ C, h i)) : Set (Fin m → ZMod 2))) ≤
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range h)) := by
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  intro v hv
  obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
  exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span ⟨i, rfl⟩)

lemma natCard_submodules_eq_grass {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (d : ℕ) :
    Nat.card {U : Submodule (ZMod 2) V // Module.finrank (ZMod 2) U = d} =
      Nat.card {U : Submodule (ZMod 2) (Fin (Module.finrank (ZMod 2) V) → ZMod 2) //
        Module.finrank (ZMod 2) U = d} := by
  let e : V ≃ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) V) → ZMod 2) :=
    (Module.finBasis (ZMod 2) V).equivFun
  refine Nat.card_congr
    { toFun := fun U => ⟨U.1.map e.toLinearMap, by
        rw [LinearEquiv.finrank_map_eq, U.2]⟩
      invFun := fun W => ⟨W.1.map e.symm.toLinearMap, by
        rw [LinearEquiv.finrank_map_eq, W.2]⟩
      left_inv := fun U => Subtype.ext (by
        dsimp only
        rw [← Submodule.map_comp]
        have hcomp : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
          ext x; simp
        rw [hcomp, Submodule.map_id])
      right_inv := fun W => Subtype.ext (by
        dsimp only
        rw [← Submodule.map_comp]
        have hcomp : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
          ext x; simp
        rw [hcomp, Submodule.map_id]) }

lemma grass_eq_zero_of_lt {d q : ℕ} (hq : q < d) :
    Nat.card {U : Submodule (ZMod 2) (Fin q → ZMod 2) // Module.finrank (ZMod 2) U = d} = 0 := by
  have : IsEmpty {U : Submodule (ZMod 2) (Fin q → ZMod 2) // Module.finrank (ZMod 2) U = d} :=
    ⟨fun ⟨U, hU⟩ => by
      have hle : Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) (Fin q → ZMod 2) :=
        Submodule.finrank_le U
      rw [Module.finrank_pi, Fintype.card_fin] at hle
      omega⟩
  exact Nat.card_eq_fintype_card.trans Fintype.card_eq_zero

lemma finrank_map_of_inj {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (f : V →ₗ[ZMod 2] W) (hf : Function.Injective f) (U : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (U.map f) = Module.finrank (ZMod 2) U :=
  (Submodule.equivMapOfInjective f hf U).finrank_eq.symm

lemma card_submodules_le_eq_grass {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (K : Submodule (ZMod 2) V) (d : ℕ) :
    Nat.card {U : Submodule (ZMod 2) V // U ≤ K ∧ Module.finrank (ZMod 2) U = d} =
      Nat.card {U : Submodule (ZMod 2) (Fin (Module.finrank (ZMod 2) K) → ZMod 2) //
        Module.finrank (ZMod 2) U = d} := by
  rw [← natCard_submodules_eq_grass (V := K) d]
  refine Nat.card_congr
    { toFun := fun U => ⟨U.1.comap K.subtype, by
        have hmap : (U.1.comap K.subtype).map K.subtype = U.1 :=
          Submodule.map_comap_eq_self (by simpa [Submodule.range_subtype] using U.2.1)
        have hfr := finrank_map_of_inj K.subtype Subtype.val_injective (U.1.comap K.subtype)
        rw [hmap, U.2.2] at hfr
        exact hfr.symm⟩
      invFun := fun W => ⟨W.1.map K.subtype,
        by
          rintro _ ⟨x, _, rfl⟩
          exact x.2,
        by
          rw [finrank_map_of_inj K.subtype Subtype.val_injective W.1, W.2]⟩
      left_inv := fun U => Subtype.ext (Submodule.map_comap_eq_self
        (by simpa [Submodule.range_subtype] using U.2.1))
      right_inv := fun W => Subtype.ext (Submodule.comap_map_eq_of_injective Subtype.val_injective W.1) }

lemma card_good_fixed_supp {n m d : ℕ} (hn : 0 < n) (h : Fin n → (Fin m → ZMod 2))
    (S : Finset (Fin n)) (hS : S ≠ Finset.univ)
    (hcutoff : ∀ T : Finset (Fin n), T ≠ Finset.univ →
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (↑((parts hn T).image (fun C => ∑ i ∈ C, h i)) : Set (Fin m → ZMod 2))) <
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range h)) →
      (parts hn T).card -
        Module.finrank (ZMod 2)
          (Submodule.span (ZMod 2)
            (↑((parts hn T).image (fun C => ∑ i ∈ C, h i)) : Set (Fin m → ZMod 2))) < d) :
    let F := ZMod 2
    let W := Fin n → F
    let r := Module.finrank F (Submodule.span F (Set.range h))
    let c := (parts hn S).card
    let grass := fun q : ℕ =>
      Nat.card {U : Submodule F (Fin q → F) // Module.finrank F U = d}
    (Nat.card {U : Submodule F W //
      Module.finrank F U = d ∧ (∀ x ∈ U, inParity h x) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next hn i) = x (next hn i) * y i) ∧
      supp U = S} : ℤ) =
      ∑ j ∈ Finset.range (c + 1), (-1 : ℤ) ^ j * Nat.choose c j * grass (c - j - r) := by
  intro F W r c grass
  let P := ↥(parts hn S)
  let _ : Fintype (Submodule F (P → F)) := Fintype.ofFinite _

  let GoodAmp := {U₀ : Submodule F (P → F) //
    U₀ ≤ LinearMap.ker (chkMap hn h S) ∧ Module.finrank F U₀ = d ∧
    ∀ C : P, ∃ α ∈ U₀, α C ≠ 0}
  have hcard_bij :
      Nat.card {U : Submodule F W //
        Module.finrank F U = d ∧ (∀ x ∈ U, inParity h x) ∧
        (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next hn i) = x (next hn i) * y i) ∧
        supp U = S} = Nat.card GoodAmp := by
    refine Nat.card_congr
      { toFun := fun U => ⟨U.1.comap (emb hn S), ?_, ?_, ?_⟩
        invFun := fun U₀ => ⟨U₀.1.map (emb hn S), ?_, ?_, ?_, ?_⟩
        left_inv := fun U => Subtype.ext ?_
        right_inv := fun U₀ => Subtype.ext
          (Submodule.comap_map_eq_of_injective (emb_injective hn S) U₀.1) }
    · intro α hα
      exact (inParity_emb_iff hn h S α).mp (U.2.2.1 _ hα)
    · have hle_range : U.1 ≤ LinearMap.range (emb hn S) := by
        intro x hx
        have hconst := (good_const_iff hn U.1).mp U.2.2.2.1 x hx
        rw [U.2.2.2.2] at hconst
        let α : P → F := fun C => x (parts_mem_nonempty hn C.2).choose
        refine ⟨α, ?_⟩
        ext i
        by_cases hi : i ∈ S
        · let C : P := ⟨comp hn S i, Finset.mem_image_of_mem _ hi⟩
          rw [emb_apply_mem hn S α C (mem_comp_self hn hi)]
          exact hconst C.1 C.2 _ (parts_mem_nonempty hn C.2).choose_spec i (mem_comp_self hn hi)
        · rw [emb_apply_notMem hn S α hi]
          symm
          by_contra hne
          have : i ∈ supp U.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hne⟩
          rw [U.2.2.2.2] at this
          exact hi this
      have hmap : (U.1.comap (emb hn S)).map (emb hn S) = U.1 :=
        Submodule.map_comap_eq_self hle_range
      have hfr := finrank_map_of_inj (emb hn S) (emb_injective hn S) (U.1.comap (emb hn S))
      rw [hmap, U.2.1] at hfr
      exact hfr.symm
    · intro C
      obtain ⟨i, hiC⟩ := parts_mem_nonempty hn C.2
      have hiS : i ∈ supp U.1 := U.2.2.2.2.symm ▸ parts_mem_subset hn C.2 hiC
      obtain ⟨x, hxU, hxi⟩ := (Finset.mem_filter.mp hiS).2
      have hconst := (good_const_iff hn U.1).mp U.2.2.2.1 x hxU
      rw [U.2.2.2.2] at hconst
      let α : P → F := fun C' => x (parts_mem_nonempty hn C'.2).choose
      have hemb : emb hn S α = x := by
        ext j
        by_cases hj : j ∈ S
        · let C' : P := ⟨comp hn S j, Finset.mem_image_of_mem _ hj⟩
          rw [emb_apply_mem hn S α C' (mem_comp_self hn hj)]
          exact hconst C'.1 C'.2 _ (parts_mem_nonempty hn C'.2).choose_spec j (mem_comp_self hn hj)
        · rw [emb_apply_notMem hn S α hj]
          symm
          by_contra hne
          have : j ∈ supp U.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxU, hne⟩
          rw [U.2.2.2.2] at this
          exact hj this
      refine ⟨α, ?_, ?_⟩
      · change emb hn S α ∈ U.1
        rw [hemb]
        exact hxU
      · have := congrFun hemb i
        rw [emb_apply_mem hn S α C hiC] at this
        rwa [this]
    · rw [finrank_map_of_inj (emb hn S) (emb_injective hn S) U₀.1, U₀.2.2.1]
    · rintro _ ⟨α, hα, rfl⟩
      exact (inParity_emb_iff hn h S α).mpr (U₀.2.1 hα)
    · have hsupp : supp (U₀.1.map (emb hn S)) = S := by
        ext i
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨_, ⟨α, _, rfl⟩, hne⟩
          by_contra hi
          exact hne (emb_apply_notMem hn S α hi)
        · intro hi
          let C : P := ⟨comp hn S i, Finset.mem_image_of_mem _ hi⟩
          obtain ⟨α, hα, hαC⟩ := U₀.2.2.2 C
          refine ⟨emb hn S α, ⟨α, hα, rfl⟩, ?_⟩
          rwa [emb_apply_mem hn S α C (mem_comp_self hn hi)]
      rw [good_const_iff hn, hsupp]
      rintro _ ⟨α, _, rfl⟩ C hC i hi j hj
      rw [emb_apply_mem hn S α ⟨C, hC⟩ hi, emb_apply_mem hn S α ⟨C, hC⟩ hj]
    · ext i
      simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, ⟨α, _, rfl⟩, hne⟩
        by_contra hi
        exact hne (emb_apply_notMem hn S α hi)
      · intro hi
        let C : P := ⟨comp hn S i, Finset.mem_image_of_mem _ hi⟩
        obtain ⟨α, hα, hαC⟩ := U₀.2.2.2 C
        refine ⟨emb hn S α, ⟨α, hα, rfl⟩, ?_⟩
        rwa [emb_apply_mem hn S α C (mem_comp_self hn hi)]
    · apply Submodule.map_comap_eq_self
      intro x hx
      have hconst := (good_const_iff hn U.1).mp U.2.2.2.1 x hx
      rw [U.2.2.2.2] at hconst
      let α : P → F := fun C => x (parts_mem_nonempty hn C.2).choose
      refine ⟨α, ?_⟩
      ext i
      by_cases hi : i ∈ S
      · let C : P := ⟨comp hn S i, Finset.mem_image_of_mem _ hi⟩
        rw [emb_apply_mem hn S α C (mem_comp_self hn hi)]
        exact hconst C.1 C.2 _ (parts_mem_nonempty hn C.2).choose_spec i (mem_comp_self hn hi)
      · rw [emb_apply_notMem hn S α hi]
        symm
        by_contra hne
        have : i ∈ supp U.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hx, hne⟩
        rw [U.2.2.2.2] at this
        exact hi this

  let AllKer : Finset (Submodule F (P → F)) :=
    Finset.univ.filter (fun U₀ => U₀ ≤ LinearMap.ker (chkMap hn h S) ∧ Module.finrank F U₀ = d)
  let zeroOn : Submodule F (P → F) → Finset P :=
    fun U₀ => Finset.univ.filter (fun C : P => ∀ α ∈ U₀, α C = 0)
  have hgood_card : (Nat.card GoodAmp : ℤ) =
      ((AllKer.filter (fun U₀ => zeroOn U₀ = ∅)).card : ℤ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    congr 1
    ext U₀
    simp only [AllKer, zeroOn, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.eq_empty_iff_forall_notMem]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2⟩, fun C hC => ?_⟩
      obtain ⟨α, hα, hne⟩ := h3 C
      exact hne (hC α hα)
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, fun C => ?_⟩
      by_contra hnot
      push Not at hnot
      exact h3 C hnot
  rw [hcard_bij, hgood_card]
  have hie : ((AllKer.filter (fun U₀ => zeroOn U₀ = ∅)).card : ℤ) =
      ∑ J ∈ (Finset.univ : Finset P).powerset,
        (-1 : ℤ) ^ J.card *
          ((AllKer.filter (fun U₀ => ∀ C ∈ J, ∀ α ∈ U₀, α C = 0)).card : ℤ) := by
    have h1 : ((AllKer.filter (fun U₀ => zeroOn U₀ = ∅)).card : ℤ) =
        ∑ U₀ ∈ AllKer, ∑ J ∈ (zeroOn U₀).powerset, (-1 : ℤ) ^ J.card := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun U₀ _ => ?_
      rw [Finset.sum_powerset_neg_one_pow_card]
      split_ifs <;> simp
    rw [h1]
    have h2 : ∀ U₀ ∈ AllKer,
        (∑ J ∈ (zeroOn U₀).powerset, (-1 : ℤ) ^ J.card) =
          ∑ J ∈ (Finset.univ : Finset P).powerset,
            if ∀ C ∈ J, ∀ α ∈ U₀, α C = 0 then (-1 : ℤ) ^ J.card else 0 := by
      intro U₀ _
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext J
      simp only [Finset.mem_powerset, Finset.mem_filter, zeroOn]
      constructor
      · intro hJ
        exact ⟨Finset.subset_univ _, fun C hCJ => (Finset.mem_filter.mp (hJ hCJ)).2⟩
      · rintro ⟨_, hJ⟩ C hCJ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ C hCJ⟩
    rw [Finset.sum_congr rfl h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hie]

  have hterm : ∀ J ∈ (Finset.univ : Finset P).powerset,
      ((AllKer.filter (fun U₀ => ∀ C ∈ J, ∀ α ∈ U₀, α C = 0)).card : ℤ) =
        (grass (c - J.card - r) : ℤ) := by
    intro J _
    congr 1
    let ZJ : Submodule F (P → F) :=
      { carrier := {α | ∀ C ∈ J, α C = 0}
        zero_mem' := fun _ _ => rfl, add_mem' := fun {α β} hα hβ C hC => by simp [hα C hC, hβ C hC]
        smul_mem' := fun r {α} hα C hC => by simp [hα C hC] }
    let KJ : Submodule F (P → F) := LinearMap.ker (chkMap hn h S) ⊓ ZJ
    have hcard_KJ : (AllKer.filter (fun U₀ => ∀ C ∈ J, ∀ α ∈ U₀, α C = 0)).card =
        Nat.card {U₀ : Submodule F (P → F) // U₀ ≤ KJ ∧ Module.finrank F U₀ = d} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext U₀
      simp only [AllKer, KJ, ZJ, Finset.mem_filter, Finset.mem_univ, true_and, le_inf_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, fun α hα C hC => h3 C hC α hα⟩, h2⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩
        exact ⟨⟨h1, h2⟩, fun C hC α hα => h3 hα C hC⟩
    rw [hcard_KJ, card_submodules_le_eq_grass KJ d]
    let J' : Finset (Finset (Fin n)) := J.image Subtype.val
    have hJ'sub : J' ⊆ parts hn S := by
      intro C hC
      obtain ⟨C', _, rfl⟩ := Finset.mem_image.mp hC
      exact C'.2
    have hJ'card : J'.card = J.card := Finset.card_image_of_injective J Subtype.val_injective
    let S' : Finset (Fin n) := (parts hn S \ J').biUnion id
    have hpartsS' : parts hn S' = parts hn S \ J' := parts_sdiff_union hn hJ'sub
    have hS'sub : S' ⊆ S := by
      intro u hu
      obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hu
      exact parts_mem_subset hn (Finset.mem_sdiff.mp hC).1 huC
    have hS'ne : S' ≠ Finset.univ := fun huniv =>
      hS (Finset.eq_univ_iff_forall.mpr fun x => hS'sub (huniv.symm ▸ Finset.mem_univ x))
    have hmem_S'_to_S : ∀ C' : ↥(parts hn S'), C'.1 ∈ parts hn S := fun C' =>
      (Finset.mem_sdiff.mp (by rw [← hpartsS']; exact C'.2)).1

    have hKJ_equiv : KJ ≃ₗ[F] LinearMap.ker (chkMap hn h S') := by
      refine
        { toFun := fun α => ⟨fun C' => α.1 ⟨C'.1, hmem_S'_to_S C'⟩, ?_⟩
          invFun := fun β => ⟨fun C =>
            if hC : C.1 ∈ parts hn S' then β.1 ⟨C.1, hC⟩ else 0, ?_, ?_⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun α => ?_
          right_inv := fun β => ?_ }
      · rw [LinearMap.mem_ker]
        have hker : chkMap hn h S α.1 = 0 := α.2.1
        rw [← hker]
        change (∑ C' : ↥(parts hn S'),
          α.1 ⟨C'.1, hmem_S'_to_S C'⟩ • (∑ i ∈ C'.1, h i)) =
          ∑ C : P, α.1 C • (∑ i ∈ C.1, h i)
        symm
        have hsum1 : (∑ C : P, α.1 C • (∑ i ∈ C.1, h i)) =
            ∑ C ∈ (Finset.univ : Finset P).filter (fun C : P => C ∉ J),
              α.1 C • (∑ i ∈ C.1, h i) := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro C _ hC
          have hCJ : C ∈ J := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hC
            exact hC
          have hzero : α.1 C = 0 := α.2.2 C hCJ
          simp [hzero]
        rw [hsum1]
        refine Finset.sum_bij (fun C hC => ⟨C.1, by
            rw [hpartsS', Finset.mem_sdiff]
            refine ⟨C.2, fun hCJ' => ?_⟩
            obtain ⟨C₁, hC₁J, heq⟩ := Finset.mem_image.mp hCJ'
            have : C₁ = C := Subtype.ext heq
            exact (Finset.mem_filter.mp hC).2 (this ▸ hC₁J)⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun C₁ _ C₂ _ heq => Subtype.ext (congrArg (fun x : ↥(parts hn S') => x.1) heq))
          (fun C' _ => ⟨⟨C'.1, hmem_S'_to_S C'⟩, by
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, fun hCJ => ?_⟩
            have hmem : C'.1 ∈ parts hn S \ J' := by rw [← hpartsS']; exact C'.2
            exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_image.mpr ⟨_, hCJ, rfl⟩), rfl⟩)
          (fun _ _ => rfl)
      · change chkMap hn h S _ = 0
        have hker : chkMap hn h S' β.1 = 0 := β.2
        rw [← hker]
        change (∑ C : P, (if hC : C.1 ∈ parts hn S' then β.1 ⟨C.1, hC⟩ else 0) •
          (∑ i ∈ C.1, h i)) = ∑ C' : ↥(parts hn S'), β.1 C' • (∑ i ∈ C'.1, h i)
        have hsum1 : (∑ C : P, (if hC : C.1 ∈ parts hn S' then β.1 ⟨C.1, hC⟩ else 0) •
            (∑ i ∈ C.1, h i)) =
            ∑ C ∈ (Finset.univ : Finset P).filter (fun C : P => C.1 ∈ parts hn S'),
              (if hC : C.1 ∈ parts hn S' then β.1 ⟨C.1, hC⟩ else 0) • (∑ i ∈ C.1, h i) := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro C _ hC
          have hnot : C.1 ∉ parts hn S' := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
            exact hC
          simp [hnot]
        rw [hsum1]
        refine Finset.sum_bij (fun C hC => ⟨C.1, (Finset.mem_filter.mp hC).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun C₁ _ C₂ _ heq => Subtype.ext (congrArg (fun x : ↥(parts hn S') => x.1) heq))
          (fun C' _ => ⟨⟨C'.1, hmem_S'_to_S C'⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, C'.2⟩, rfl⟩)
          (fun C hC => by
            have hmem : C.1 ∈ parts hn S' := (Finset.mem_filter.mp hC).2
            simp [hmem])
      · intro C hCJ
        have hnot : C.1 ∉ parts hn S' := by
          rw [hpartsS', Finset.mem_sdiff]
          intro hmem
          exact hmem.2 (Finset.mem_image.mpr ⟨C, hCJ, rfl⟩)
        simp [hnot]
      · ext C
        change (if hC : C.1 ∈ parts hn S' then α.1 ⟨C.1, _⟩ else 0) = α.1 C
        by_cases hC : C.1 ∈ parts hn S'
        · simp [hC]
        · simp only [hC, ↓reduceDIte]
          have hCJ : C ∈ J := by
            rw [hpartsS', Finset.mem_sdiff] at hC
            by_contra hnot
            apply hC
            refine ⟨C.2, fun hmem => ?_⟩
            obtain ⟨C₁, hC₁, heq⟩ := Finset.mem_image.mp hmem
            exact hnot (Subtype.ext heq ▸ hC₁)
          exact (α.2.2 C hCJ).symm
      · ext C'
        simp [C'.2]
    have hfr_KJ : Module.finrank F KJ =
        (c - J.card) -
          Module.finrank F
            (Submodule.span F (↑((parts hn S').image (fun C => ∑ i ∈ C, h i)) : Set (Fin m → F))) := by
      rw [LinearEquiv.finrank_eq hKJ_equiv, finrank_ker_chkMap, hpartsS',
        Finset.card_sdiff_of_subset hJ'sub, hJ'card]
    let r' := Module.finrank F
      (Submodule.span F (↑((parts hn S').image (fun C => ∑ i ∈ C, h i)) : Set (Fin m → F)))
    have hr'_le : r' ≤ r := rankOn_le_finrank_D hn h S'
    by_cases heq : r' = r
    · have : Module.finrank F KJ = c - J.card - r := by rw [hfr_KJ]; exact congrArg ((c - J.card) - ·) heq
      rw [this]
    · have hlt' : r' < r := lt_of_le_of_ne hr'_le heq
      have hcut' := hcutoff S' hS'ne hlt'
      have hcardS' : (parts hn S').card = c - J.card := by
        rw [hpartsS', Finset.card_sdiff_of_subset hJ'sub, hJ'card]
      have h1 : Module.finrank F KJ < d := by
        rw [hfr_KJ, ← hcardS']
        exact hcut'
      have h2 : c - J.card - r < d := by omega
      dsimp only [grass]
      rw [grass_eq_zero_of_lt h1, grass_eq_zero_of_lt h2]
  rw [Finset.sum_congr rfl (fun J hJ => by rw [hterm J hJ])]

  have hgroup : (∑ J ∈ (Finset.univ : Finset P).powerset,
      (-1 : ℤ) ^ J.card * (grass (c - J.card - r) : ℤ)) =
      ∑ j ∈ Finset.range (c + 1),
        ∑ J ∈ (Finset.univ : Finset P).powersetCard j,
          (-1 : ℤ) ^ j * (grass (c - j - r) : ℤ) := by
    have hdisj : (Finset.range (c + 1) : Set ℕ).PairwiseDisjoint
        (fun j => (Finset.univ : Finset P).powersetCard j) := by
      intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro J hi hj
      exact hij ((Finset.mem_powersetCard.mp hi).2.symm.trans (Finset.mem_powersetCard.mp hj).2)
    have hbiU : (Finset.range (c + 1)).biUnion
        (fun j => (Finset.univ : Finset P).powersetCard j) = (Finset.univ : Finset P).powerset := by
      ext J
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
        Finset.mem_powerset, Finset.subset_univ, true_and]
      constructor
      · intro _; trivial
      · intro _
        refine ⟨J.card, ?_, rfl⟩
        have hle : J.card ≤ Fintype.card P := Finset.card_le_univ J
        rw [Fintype.card_coe] at hle
        omega
    rw [← hbiU, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun J hJ => ?_
    rw [(Finset.mem_powersetCard.mp hJ).2]
  rw [hgroup]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul]
  ring

lemma cutoff_imp_count {n m d : ℕ} (hn : 0 < n) (hd : 2 ≤ d) (h : Fin n → (Fin m → ZMod 2))
    [Fintype (Submodule (ZMod 2) (Fin n → ZMod 2))] :
    let F := ZMod 2
    let A := Fin m → F
    let W := Fin n → F
    let D := Submodule.span F (Set.range h)
    let r := Module.finrank F D
    let rankOn := fun S : Finset (Fin n) =>
      Module.finrank F (Submodule.span F
        (↑((parts hn S).image (fun C => ∑ i ∈ C, h i)) : Set A))
    let grass := fun q : ℕ =>
      Nat.card {U : Submodule F (Fin q → F) // Module.finrank F U = d}
    let good := fun U : Submodule F W => Module.finrank F U = d ∧
      (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next hn i) = x (next hn i) * y i)
    (∀ S : Finset (Fin n), S ≠ Finset.univ → rankOn S < r → (parts hn S).card - rankOn S < d) →
    (((Finset.univ : Finset (Submodule F W)).filter good).card : ℤ) =
      ∑ c ∈ Finset.Icc 1 (n / 2), (2 : ℤ) * Nat.choose n (2 * c) *
        (∑ j ∈ Finset.range (c + 1), (-1 : ℤ) ^ j * Nat.choose c j * grass (c - j - r)) := by
  intro F A W D r rankOn grass good hcutoff

  let goodSet := (Finset.univ : Finset (Submodule F W)).filter good
  let suppsOf (c : ℕ) : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => S ≠ Finset.univ ∧ (parts hn S).card = c)
  have hpart : (goodSet.card : ℤ) =
      ∑ c ∈ Finset.Icc 1 (n / 2),
        ∑ S ∈ suppsOf c, ((goodSet.filter (fun U => supp U = S)).card : ℤ) := by
    have hnat : goodSet.card =
        ∑ c ∈ Finset.Icc 1 (n / 2),
          ∑ S ∈ suppsOf c, (goodSet.filter (fun U => supp U = S)).card := by
      have h1 := Finset.card_eq_sum_card_fiberwise (s := goodSet)
        (t := (Finset.Icc 1 (n / 2)).biUnion suppsOf) (f := supp) (by
          intro U hU
          have hgood := (Finset.mem_filter.mp hU).2
          have hconst := (good_const_iff hn U).mp hgood.2.2
          obtain ⟨hne, hge1, hle⟩ := good_supp_props hn hd U hgood.1 hconst
          exact Finset.mem_biUnion.mpr ⟨(parts hn (supp U)).card,
            Finset.mem_Icc.mpr ⟨hge1, hle⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, rfl⟩⟩)
      rw [h1, Finset.sum_biUnion]
      intro c₁ _ c₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro S h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2)
    rw [hnat]
    push_cast
    rfl
  change (goodSet.card : ℤ) = _
  rw [hpart]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
  have hinner : ∀ S ∈ suppsOf c,
      ((goodSet.filter (fun U => supp U = S)).card : ℤ) =
        ∑ j ∈ Finset.range (c + 1), (-1 : ℤ) ^ j * Nat.choose c j * grass (c - j - r) := by
    intro S hS
    obtain ⟨_, hSne, hSc⟩ := Finset.mem_filter.mp hS
    have hcard_eq : (goodSet.filter (fun U => supp U = S)).card =
        Nat.card {U : Submodule F W //
          Module.finrank F U = d ∧ (∀ x ∈ U, inParity h x) ∧
          (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next hn i) = x (next hn i) * y i) ∧
          supp U = S} := by
      rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
      exact Fintype.card_congr
        { toFun := fun ⟨U, hU⟩ => ⟨U, by
            have h1 := Finset.mem_filter.mp hU
            have h2 := (Finset.mem_filter.mp h1.1).2
            exact ⟨h2.1, h2.2.1, h2.2.2, h1.2⟩⟩
          invFun := fun ⟨U, hU⟩ => ⟨U, Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU.1, hU.2.1, hU.2.2.1⟩, hU.2.2.2⟩⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun ⟨_, _⟩ => rfl }
    rw [hcard_eq]
    dsimp only [F, W, r, grass]
    rw [← hSc]
    exact card_good_fixed_supp hn h S hSne hcutoff
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul,
    card_supports_with_parts hn c hc1]
  push_cast
  ring

end Part2

end

end PEqualNP.Outside.L_lib_874_aux

theorem PEqualNP.Outside.L_lib_874 : (∀ (n m d : ℕ) (hn : 0 < n), 2 ≤ d →
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  let W := Fin n → F
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let ix := fun j : ℕ => (⟨j % n, Nat.mod_lt _ hn⟩ : Fin n)
  let next := fun i : Fin n => ix (i.val+1)
  let parts := fun S : Finset (Fin n) =>
    let step := fun i j : Fin n => i ∈ S ∧ j ∈ S ∧ (next i = j ∨ next j = i)
    S.image (fun v => S.filter (fun u => Relation.ReflTransGen step v u))
  ∀ h : Fin n → A,
    let D := Submodule.span F (Set.range h)
    let r := Module.finrank F D
    let rankOn := fun S : Finset (Fin n) =>
      Module.finrank F (Submodule.span F
        (↑((parts S).image (fun C => ∑ i ∈ C, h i)) : Set A))
    let cutoff := ∀ S : Finset (Fin n), S ≠ Finset.univ →
      rankOn S < r → (parts S).card - rankOn S < d
    let localSpan := ∃ b : ℕ, 0 < b ∧ (2*b+1)*(n-2*d) < n ∧
      ∀ i : Fin n, Submodule.span F (Set.range
        (fun j : Fin b => h (ix (i.val+2*j.val)))) = D
    let grass := fun q : ℕ =>
      Nat.card {U : Submodule F (Fin q → F) // Module.finrank F U = d}
    let good := fun U : Submodule F W => Module.finrank F U = d ∧
      (∀ x ∈ U, ∀ b : Fin m, (∑ i, h i b * x i) = 0) ∧
      (∀ x ∈ U, ∀ y ∈ U, ∀ i, x i * y (next i) = x (next i) * y i)
    (localSpan → cutoff) ∧ (cutoff →
      (((Finset.univ : Finset (Submodule F W)).filter good).card : ℤ) =
        ∑ c ∈ Finset.Icc 1 (n/2), (2:ℤ)*Nat.choose n (2*c) *
          (∑ j ∈ Finset.range (c+1), (-1:ℤ)^j * Nat.choose c j * grass (c-j-r)))) := by
  intro n m d hn hd
  dsimp only
  intro h
  have hparts_eq : ∀ S : Finset (Fin n),
      @Finset.image (Fin n) (Finset (Fin n)) (fun a b => Classical.propDecidable (a = b))
        (fun v => @Finset.filter (Fin n)
          (fun u => Relation.ReflTransGen
            (fun i j => i ∈ S ∧ j ∈ S ∧
              ((⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = j ∨
                (⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = i)) v u)
          (fun u => Classical.propDecidable _) S) S =
      PEqualNP.Outside.L_lib_874_aux.parts hn S := by
    intro S
    ext C
    simp only [PEqualNP.Outside.L_lib_874_aux.parts, PEqualNP.Outside.L_lib_874_aux.comp,
      Finset.mem_image]
    constructor <;> (rintro ⟨v, hv, rfl⟩; refine ⟨v, hv, ?_⟩; ext u; simp only [Finset.mem_filter]; rfl)
  have hrank_eq : ∀ S : Finset (Fin n),
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (↑(@Finset.image (Finset (Fin n)) (Fin m → ZMod 2) (fun a b => Classical.propDecidable (a = b))
          (fun C => ∑ i ∈ C, h i)
          (@Finset.image (Fin n) (Finset (Fin n)) (fun a b => Classical.propDecidable (a = b))
            (fun v => @Finset.filter (Fin n)
              (fun u => Relation.ReflTransGen
                (fun i j => i ∈ S ∧ j ∈ S ∧
                  ((⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = j ∨
                    (⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = i)) v u)
              (fun u => Classical.propDecidable _) S) S)) : Set (Fin m → ZMod 2))) =
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (↑((PEqualNP.Outside.L_lib_874_aux.parts hn S).image (fun C => ∑ i ∈ C, h i)) :
          Set (Fin m → ZMod 2))) := by
    intro S
    have hset : (↑(@Finset.image (Finset (Fin n)) (Fin m → ZMod 2)
          (fun a b => Classical.propDecidable (a = b)) (fun C => ∑ i ∈ C, h i)
          (@Finset.image (Fin n) (Finset (Fin n)) (fun a b => Classical.propDecidable (a = b))
            (fun v => @Finset.filter (Fin n)
              (fun u => Relation.ReflTransGen
                (fun i j => i ∈ S ∧ j ∈ S ∧
                  ((⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = j ∨
                    (⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = i)) v u)
              (fun u => Classical.propDecidable _) S) S)) : Set (Fin m → ZMod 2)) =
        ↑((PEqualNP.Outside.L_lib_874_aux.parts hn S).image (fun C => ∑ i ∈ C, h i)) := by
      rw [hparts_eq S]
      ext v
      simp only [Finset.mem_coe, Finset.mem_image]
    exact congrArg (fun s : Set (Fin m → ZMod 2) =>
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) s)) hset
  refine ⟨?_, ?_⟩
  · intro hloc S hS hlt
    rw [hrank_eq S] at hlt ⊢
    rw [hparts_eq S]
    exact PEqualNP.Outside.L_lib_874_aux.localSpan_imp_cutoff (d := d) hn h hloc S hS hlt
  · intro hcut
    have hcut' : ∀ S : Finset (Fin n), S ≠ Finset.univ →
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          (↑((PEqualNP.Outside.L_lib_874_aux.parts hn S).image (fun C => ∑ i ∈ C, h i)) :
            Set (Fin m → ZMod 2))) <
          Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range h)) →
        (PEqualNP.Outside.L_lib_874_aux.parts hn S).card -
          Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
            (↑((PEqualNP.Outside.L_lib_874_aux.parts hn S).image (fun C => ∑ i ∈ C, h i)) :
              Set (Fin m → ZMod 2))) < d := by
      intro S hS hlt
      have hres := hcut S hS (by rw [hrank_eq S]; exact hlt)
      rwa [hrank_eq S, hparts_eq S] at hres
    have hmain := @PEqualNP.Outside.L_lib_874_aux.cutoff_imp_count n m d hn hd h
      (Fintype.ofFinite _) hcut'
    convert hmain using 1
    congr 1
    congr 1
    ext U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
