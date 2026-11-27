import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25811_aux

namespace Extract

open Finset

def dist {α : Type*} [Fintype α] (f g : α → Bool) : ℕ :=
  (univ.filter fun i => f i ≠ g i).card

theorem dist_triangle {α : Type*} [Fintype α] (f g h : α → Bool) :
    dist f h ≤ dist f g + dist g h := by
  classical
  apply le_trans (card_le_card (t := (univ.filter fun i => f i ≠ g i) ∪
      (univ.filter fun i => g i ≠ h i)) _ ) (card_union_le _ _)
  intro i hi
  simp only [mem_filter, mem_univ, true_and, mem_union] at hi ⊢
  by_cases e : f i = g i
  · exact Or.inr fun eq => hi (e.trans eq)
  · exact Or.inl e

theorem dist_symm {α : Type*} [Fintype α] (f g : α → Bool) : dist f g = dist g f := by
  simp [dist, ne_comm]

theorem dist_le_of_agree {α : Type*} [Fintype α] (f g : α → Bool) (s : Finset α)
    (h : ∀ i ∉ s, f i = g i) : dist f g ≤ s.card := by
  apply card_le_card
  intro i hi
  by_contra hs
  exact (mem_filter.mp hi).2 (h i hs)

theorem good_dist {α : Type*} [Fintype α] (f g f' g' : α → Bool) (v : ℕ)
    (hv : 0 < v) (hf : dist f f' < v) (hg : dist g g' < v)
    (hd : 17 + 2 * (v - 1) ≤ dist f' g') : 17 ≤ dist f g := by
  have h1 := dist_triangle f' f g'
  have h2 := dist_triangle f g g'
  rw [dist_symm f' f] at h1
  omega

theorem error_rows {α : Type*} [Fintype α] (H T : α → α → Bool) (v : ℕ) :
    (univ.filter fun i => v ≤ dist (H i) (T i)).card ≤
      (univ.filter (fun z : α × α => H z.1 z.2 ≠ T z.1 z.2)).card / v ∨ v = 0 := by
  classical
  by_cases hv : v = 0
  · exact Or.inr hv
  left
  rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hv)]
  let s := univ.filter fun i => v ≤ dist (H i) (T i)
  let E := univ.filter fun z : α × α => H z.1 z.2 ≠ T z.1 z.2
  change s.card * v ≤ E.card
  have he : E.card = ∑ i : α, dist (H i) (T i) := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => mem_univ _)]
    apply sum_congr rfl
    intro i _
    have hm : (E.filter fun z => z.1 = i) =
        (univ.filter fun j => H i j ≠ T i j).map
          ⟨fun j => (i,j), fun _ _ h => congrArg Prod.snd h⟩ := by
      ext ⟨x,y⟩
      simp only [E, mem_filter, mem_univ, true_and, mem_map]
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨y, h, rfl⟩
      · rintro ⟨j, h, heq⟩
        cases heq
        exact ⟨h, rfl⟩
    rw [hm, card_map]
    rfl
  rw [he, ← sum_const_nat (f := fun _ : α => v) (fun _ _ => rfl)]
  exact (sum_le_sum fun i hi => (mem_filter.mp hi).2).trans
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.zero_le _)

theorem error_transpose {α : Type*} [Fintype α] (H T : α → α → Bool) :
    (univ.filter (fun z : α × α => H z.2 z.1 ≠ T z.2 z.1)).card =
      (univ.filter (fun z : α × α => H z.1 z.2 ≠ T z.1 z.2)).card := by
  classical
  apply card_bij' (fun z _ => z.swap) (fun z _ => z.swap)
  all_goals simp_all

theorem ordered_pairs {α : Type*} [LinearOrder α] (s : Finset α) (h : s.card ≤ 3) :
    ((s ×ˢ s).filter fun z => z.1 < z.2).card ≤ s.card := by
  let A := (s ×ˢ s).filter fun z => z.1 < z.2
  let B := A.map (Equiv.prodComm α α).toEmbedding
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro z hz ha
    obtain ⟨w, hw, rfl⟩ := mem_map.mp ha
    exact (not_lt_of_gt (mem_filter.mp hw).2) (mem_filter.mp hz).2
  have hsub : A ∪ B ⊆ s.offDiag := by
    intro z hz
    rw [mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨hh, hlt⟩ := mem_filter.mp hz
      exact mem_offDiag.mpr ⟨(mem_product.mp hh).1, (mem_product.mp hh).2, ne_of_lt hlt⟩
    · obtain ⟨w, hw, rfl⟩ := mem_map.mp hz
      obtain ⟨hh, hlt⟩ := mem_filter.mp hw
      exact mem_offDiag.mpr ⟨(mem_product.mp hh).2, (mem_product.mp hh).1, ne_of_gt hlt⟩
  have hb : B.card = A.card := card_map _
  have hh := card_le_card hsub
  rw [card_union_of_disjoint hAB, hb, offDiag_card] at hh
  change A.card ≤ s.card
  interval_cases hm : s.card <;> omega

theorem conflict_bound {α : Type*} [LinearOrder α] (T H : α → α → Bool)
    (π : Equiv.Perm α) (S : Finset α) (p : α → ℕ)
    (hm : ∀ t, (S.filter fun i => p i = t).card ≤ 3)
    (hs : ∀ i ∈ S, ∀ j ∈ S, p i ≠ p j → H i (π j) = H j (π i))
    (U : Finset α) (hU : U ⊆ S) :
    ((U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))).card ≤
      U.card + ((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).card := by
  classical
  let A := (U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))
  let E := (U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))
  let same := A.filter fun z => p z.1 = p z.2
  let diff := A.filter fun z => p z.1 ≠ p z.2
  have hpart : same.card + diff.card = A.card := card_filter_add_card_filter_not ..
  have hsame : same.card ≤ U.card := by
    rw [card_eq_sum_card_fiberwise (f := fun z : α × α => p z.1) (t := U.image p),
      card_eq_sum_card_image p U]
    · apply sum_le_sum
      intro t _
      let V := U.filter fun i => p i = t
      change (same.filter fun z => p z.1 = t).card ≤ V.card
      have hv : V.card ≤ 3 := (card_le_card (filter_subset_filter _ hU)).trans (hm t)
      apply le_trans (card_le_card (t := (V ×ˢ V).filter fun z => z.1 < z.2) ?_) (ordered_pairs V hv)
      intro z hz
      rcases mem_filter.mp hz with ⟨hz, hzt⟩
      rcases mem_filter.mp hz with ⟨hz, hze⟩
      rcases mem_filter.mp hz with ⟨hz, hlt, _⟩
      rcases mem_product.mp hz with ⟨hi, hj⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨hi,hzt⟩,
        mem_filter.mpr ⟨hj,hze.symm.trans hzt⟩⟩, hlt⟩
    · intro z hz
      exact mem_image_of_mem p (mem_product.mp (mem_filter.mp (mem_filter.mp hz).1).1).1
  have hdiff : diff.card ≤ E.card := by
    let f : α × α → α × α := fun z => if T z.1 (π z.2) ≠ H z.1 (π z.2) then z else z.swap
    apply card_le_card_of_injOn f
    · intro z hz
      rcases mem_filter.mp hz with ⟨hz, hne⟩
      rcases mem_filter.mp hz with ⟨hz, _, htt⟩
      rcases mem_product.mp hz with ⟨hi,hj⟩
      by_cases he : T z.1 (π z.2) ≠ H z.1 (π z.2)
      · change f z ∈ E
        simp only [f, ite_eq_left he]
        exact mem_filter.mpr ⟨hz, he⟩
      · have he' : T z.2 (π z.1) ≠ H z.2 (π z.1) := by
          intro hk
          exact htt ((not_ne_iff.mp he).trans ((hs _ (hU hi) _ (hU hj) hne).trans hk.symm))
        change f z ∈ E
        simp only [f, ite_eq_right he]
        exact mem_filter.mpr ⟨mem_product.mpr ⟨hj, hi⟩, he'⟩
    · intro a ha b hb hab
      have ha' := (mem_filter.mp (mem_filter.mp ha).1).2.1
      have hb' := (mem_filter.mp (mem_filter.mp hb).1).2.1
      unfold f at hab
      split at hab <;> split at hab
      · exact hab
      · subst a
        exact (lt_asymm hb' ha').elim
      · subst b
        exact (lt_asymm ha' hb').elim
      · exact congrArg Prod.swap hab
  change A.card ≤ U.card + E.card
  omega

theorem match_keys {α κ : Type*} [Fintype α] [DecidableEq α] [DecidableEq κ]
    (A B : Finset α) (a b : α → κ) (ha : Set.InjOn a A) (hb : Set.InjOn b B) :
    ∃ (π : Equiv.Perm α) (S : Finset α),
      S.card + (A.image a ∪ B.image b).card = A.card + B.card ∧
      S ⊆ A ∧ ∀ i ∈ S, π i ∈ B ∧ a i = b (π i) := by
  classical
  let S := A.filter fun i => a i ∈ B.image b
  have hm : ∀ i ∈ S, ∃ j ∈ B, b j = a i := fun i hi => mem_image.mp (mem_filter.mp hi).2
  let f : α → α := fun i => if h : i ∈ S then (hm i h).choose else i
  have hf : ∀ i ∈ S, f i ∈ B ∧ b (f i) = a i := by
    intro i hi
    simpa only [f, dite_eq_left hi] using (hm i hi).choose_spec
  have hinj : Set.InjOn f S := by
    intro i hi j hj hij
    apply ha (filter_subset _ _ hi) (filter_subset _ _ hj)
    rw [← (hf i hi).2, ← (hf j hj).2, hij]
  obtain ⟨π, hπ⟩ := exists_equiv_extend_of_card_eq (t := univ) (by simp)
    (show S.image f ⊆ univ from subset_univ _) hinj
  let idu : (univ : Finset α) ≃ α :=
    ⟨Subtype.val, fun x => ⟨x, mem_univ x⟩, fun _ => rfl, fun _ => rfl⟩
  refine ⟨π.trans idu, S, ?_, filter_subset _ _, ?_⟩
  · have hS : S.image a = A.image a ∩ B.image b := by
      ext k
      simp only [S, mem_image, mem_filter, mem_inter]
      constructor
      · rintro ⟨i, ⟨hi, hk⟩, rfl⟩
        exact ⟨⟨i, hi, rfl⟩, hk⟩
      · rintro ⟨⟨i, hi, rfl⟩, hk⟩
        exact ⟨i, ⟨hi, hk⟩, rfl⟩
    have hk := card_union_add_card_inter (A.image a) (B.image b)
    rw [← hS, card_image_of_injOn (ha.mono (filter_subset _ _)),
      card_image_of_injOn ha, card_image_of_injOn hb] at hk
    simpa [S, add_comm] using hk
  · intro i hi
    change (π i : α) ∈ B ∧ a i = b (π i : α)
    rw [hπ i hi]
    exact ⟨(hf i hi).1, (hf i hi).2.symm⟩

open Finset

inductive Op where
  | raw
  | lit (b : Bool)
  | one (f : Bool → Bool) (a : ℕ)
  | two (f : Bool → Bool → Bool) (a b : ℕ)

def Op.pin : Op → Bool → Option ℕ
  | .one _ a, s => if s then none else some a
  | .two _ a b, s => some (if s then b else a)
  | _, _ => none

def Op.arity : Op → ℕ
  | .raw | .lit _ => 0
  | .one .. => 1
  | .two .. => 2

def Op.value : Op → Bool → (ℕ → Bool) → Bool
  | .raw, x, _ => x
  | .lit b, _, _ => b
  | .one f a, _, v => f (v a)
  | .two f a b, _, v => f (v a) (v b)

structure Net where
  code : ℕ → Op
  out : ℕ
  back : ∀ {w s a}, (code w).pin s = some a → a < w

def Net.run (N : Net) (x : ℕ → Bool) (w : ℕ) : Bool :=
  (N.code w).value (x w) fun a => if a < w then N.run x a else false
termination_by w

theorem Net.run_eq (N : Net) (x : ℕ → Bool) (w : ℕ) :
    N.run x w = (N.code w).value (x w) (N.run x) := by
  rw [Net.run]
  cases h : N.code w with
  | raw => rfl
  | lit b => rfl
  | one f a =>
    have ha : a < w := N.back (s := false) (by simp [h, Op.pin])
    simp [Op.value, ha]
  | two f a b =>
    have ha : a < w := N.back (s := false) (by simp [h, Op.pin])
    have hb : b < w := N.back (s := true) (by simp [h, Op.pin])
    simp [Op.value, ha, hb]

inductive Net.Reach (N : Net) : ℕ → Prop where
  | top : Reach N N.out
  | child {w a s : _} : Reach N w → (N.code w).pin s = some a → Reach N a

theorem Net.reach_le (N : Net) {w : ℕ} (hw : N.Reach w) : w ≤ N.out := by
  induction hw with
  | top => rfl
  | child _ hp ih => exact (N.back hp).le.trans ih

noncomputable section

def Net.live (N : Net) : Finset ℕ := by
  classical
  exact (range (N.out + 1)).filter N.Reach

@[simp] theorem Net.mem_live (N : Net) {a} : a ∈ N.live ↔ N.Reach a := by
  classical
  simp only [live, mem_filter, mem_range]
  exact ⟨And.right, fun h => ⟨Nat.lt_succ_of_le (N.reach_le h), h⟩⟩

def Net.edges (N : Net) : Finset (ℕ × Bool) :=
  (N.live ×ˢ univ).filter fun z => ((N.code z.1).pin z.2).isSome

def Net.src (N : Net) (e : ℕ × Bool) : ℕ := ((N.code e.1).pin e.2).getD 0

theorem Net.pin_src {N : Net} {e} (he : e ∈ N.edges) :
    (N.code e.1).pin e.2 = some (N.src e) := by
  have h := (mem_filter.mp he).2
  cases hc : (N.code e.1).pin e.2 <;> simp_all [Net.src]

theorem Net.edge_of_pin {N : Net} {w s a} (hw : w ∈ N.live)
    (h : (N.code w).pin s = some a) : (w,s) ∈ N.edges ∧ N.src (w,s) = a := by
  simp [Net.edges, Net.src, hw, h]

theorem Net.edge_live {N : Net} {e} (he : e ∈ N.edges) : e.1 ∈ N.live :=
  (mem_product.mp (mem_filter.mp he).1).1

theorem Net.src_live {N : Net} {e} (he : e ∈ N.edges) : N.src e ∈ N.live :=
  N.mem_live.mpr (.child (N.mem_live.mp (N.edge_live he)) (N.pin_src he))

def Net.uses (N : Net) (a : ℕ) : Finset (ℕ × Bool) := N.edges.filter fun e => N.src e = a

def Net.deg (N : Net) (a : ℕ) : ℕ := (N.uses a).card

def Net.shared (N : Net) (a : ℕ) : Prop := 2 ≤ N.deg a

instance (N : Net) (a : ℕ) : Decidable (N.shared a) :=
  inferInstanceAs (Decidable (2 ≤ N.deg a))

theorem Net.deg_pos {N : Net} {a} (ha : a ∈ N.live) (hne : a ≠ N.out) : 0 < N.deg a := by
  rcases N.mem_live.mp ha with ht | @⟨w, a, s, hw, hp⟩
  · exact (hne rfl).elim
  · obtain ⟨he, hs⟩ := N.edge_of_pin (N.mem_live.mpr hw) hp
    exact card_pos.mpr ⟨(w,s), mem_filter.mpr ⟨he, hs⟩⟩

theorem Net.not_out_src {N : Net} {e} (he : e ∈ N.edges) : N.src e ≠ N.out := by
  have hlt := N.back (N.pin_src he)
  have hle := N.reach_le (N.mem_live.mp (N.edge_live he))
  omega

theorem Net.deg_out (N : Net) : N.deg N.out = 0 := by
  rw [Net.deg, card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  exact N.not_out_src (mem_filter.mp he).1 (mem_filter.mp he).2

theorem Net.use_unique {N : Net} {e e' : ℕ × Bool} (he : e ∈ N.edges) (he' : e' ∈ N.edges)
    (hs : N.src e = N.src e') (hc : ¬N.shared (N.src e)) : e = e' := by
  by_contra h
  have hsub : {e,e'} ⊆ N.uses (N.src e) := by simp [insert_subset_iff, Net.uses, he, he', hs]
  have hcard := card_le_card hsub
  exact hc (by simpa [h, Net.deg, Net.shared] using hcard)

def Net.excess (N : Net) : ℕ := ∑ a ∈ N.live, (N.deg a - 1)

theorem Net.card_pin_fiber (N : Net) {w : ℕ} (hw : w ∈ N.live) :
    (N.edges.filter fun e => e.1 = w).card = (N.code w).arity := by
  let f : Bool ↪ ℕ × Bool := ⟨fun b => (w,b), fun _ _ h => congrArg Prod.snd h⟩
  have hh : (N.edges.filter fun e => e.1 = w) =
      (univ.filter fun s => ((N.code w).pin s).isSome).map f := by
    ext ⟨p,s⟩
    simp only [Net.edges, mem_filter, mem_product, mem_univ, and_true, true_and, mem_map]
    constructor
    · rintro ⟨⟨_,h⟩,rfl⟩
      exact ⟨s,h,rfl⟩
    · rintro ⟨t,h,he⟩
      cases he
      exact ⟨⟨hw,h⟩,rfl⟩
  rw [hh, card_map]
  cases N.code w <;> simp [Op.pin, Op.arity]
  have h : ({s ∈ ({true,false} : Finset Bool) | s = false} : Finset Bool) = {false} := by
    ext s; cases s <;> simp
  rw [h, card_singleton]

theorem Net.ledger (N : Net) :
    N.excess + (N.live.filter fun a => (N.code a).arity = 0).card =
      (N.live.filter fun a => (N.code a).arity = 2).card + 1 := by
  classical
  have h1 : N.edges.card = ∑ a ∈ N.live, N.deg a :=
    card_eq_sum_card_fiberwise (f := N.src) fun _ ha => N.src_live ha
  have h2 : N.edges.card = ∑ a ∈ N.live, (N.code a).arity := by
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := N.live) fun _ he => N.edge_live he]
    exact sum_congr rfl fun _ ha => N.card_pin_fiber ha
  have ho : N.out ∈ N.live := N.mem_live.mpr .top
  have h3 : (∑ a ∈ N.live, N.deg a) + 1 = N.excess + N.live.card := by
    have hh : (∑ a ∈ N.live, (N.deg a + if a = N.out then 1 else 0)) =
        ∑ a ∈ N.live, ((N.deg a - 1) + 1) := by
      apply sum_congr rfl
      intro a ha
      by_cases h : a = N.out
      · subst a; simp [N.deg_out]
      · have := N.deg_pos ha h
        simp only [ite_eq_right h]; omega
    simpa [sum_add_distrib, ho, Net.excess] using hh
  have h4 : (∑ a ∈ N.live, (N.code a).arity) + (N.live.filter fun a => (N.code a).arity = 0).card =
      N.live.card + (N.live.filter fun a => (N.code a).arity = 2).card := by
    have hh : (∑ a ∈ N.live, ((N.code a).arity + if (N.code a).arity = 0 then 1 else 0)) =
        ∑ a ∈ N.live, (1 + if (N.code a).arity = 2 then 1 else 0) := by
      apply sum_congr rfl
      intro a _
      cases N.code a <;> simp [Op.arity]
    simpa [sum_add_distrib, sum_filter] using hh
  omega

theorem Net.shared_le (N : Net) : (N.live.filter N.shared).card ≤ N.excess := by
  classical
  calc
    _ = ∑ a ∈ N.live.filter N.shared, 1 := by simp
    _ ≤ ∑ a ∈ N.live.filter N.shared, (N.deg a - 1) := by
      apply sum_le_sum
      intro a ha
      exact Nat.le_sub_of_add_le (mem_filter.mp ha).2
    _ ≤ N.excess := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

def Net.cut (N : Net) (bad : Finset ℕ) (a : ℕ) : Prop := N.shared a ∨ a ∈ bad

def Net.holeEdges (N : Net) (bad : Finset ℕ) : Finset (ℕ × Bool) := by
  classical
  exact N.edges.filter fun e => N.cut bad (N.src e)

theorem Net.cut_edges_le (N : Net) (bad : Finset ℕ) :
    (N.holeEdges bad).card ≤ 2 * N.excess + bad.card := by
  classical
  rw [card_eq_sum_card_fiberwise (s := N.holeEdges bad) (f := N.src) (t := N.live)
    (fun _ he => N.src_live (mem_filter.mp he).1)]
  have hb : (∑ a ∈ N.live, (if a ∈ bad then 1 else 0)) ≤ bad.card := by
    rw [← sum_filter]
    simpa using (card_le_card (show N.live.filter (· ∈ bad) ⊆ bad from fun _ h => (mem_filter.mp h).2))
  have hh : (∑ a ∈ N.live, ((N.holeEdges bad).filter fun e => N.src e = a).card) ≤
      ∑ a ∈ N.live, (2 * (N.deg a - 1) + if a ∈ bad then 1 else 0) := by
    apply sum_le_sum
    intro a _
    by_cases hc : N.cut bad a
    · have hEq : ((N.holeEdges bad).filter fun e => N.src e = a) = N.uses a := by
        ext e
        simp only [Net.holeEdges, Net.uses, mem_filter]
        grind
      rw [hEq, ← Net.deg]
      rcases hc with he | he
      · have : 2 ≤ N.deg a := he
        omega
      · simp [he]; omega
    · have he : ((N.holeEdges bad).filter fun e => N.src e = a) = ∅ := by
        ext e
        simp only [Net.holeEdges, mem_filter, notMem_empty, iff_false]
        grind
      simp [he]
  rw [sum_add_distrib, ← mul_sum, ← Net.excess] at hh
  omega

end

open Finset

structure Frag where
  raw : Finset ℕ
  hole : Option ℕ
  f : (ℕ → Bool) → Bool → Bool
  congrRaw : ∀ (x y : ℕ → Bool), (∀ a ∈ raw, x a = y a) → ∀ b, f x b = f y b
  ignore : hole = none → ∀ x b c, f x b = f x c

def Frag.eval (F : Frag) (x y : ℕ → Bool) : Bool := F.f x (F.hole.elim false y)

def Frag.bit (a : ℕ) : Frag := by
  refine ⟨{a}, none, fun x _ => x a, ?_, fun _ _ _ _ => rfl⟩
  exact fun x y h _ => h a (mem_singleton_self a)

def Frag.lit (b : Bool) : Frag :=
  ⟨∅, none, fun _ _ => b, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

def Frag.entry (a : ℕ) : Frag :=
  ⟨∅, some a, fun _ b => b, fun _ _ _ _ => rfl, fun h => by cases h⟩

def Frag.unary (f : Bool → Bool) (A : Frag) : Frag :=
  ⟨A.raw, A.hole, fun x b => f (A.f x b),
    fun x y h b => congrArg f (A.congrRaw x y h b),
    fun h x b c => congrArg f (A.ignore h x b c)⟩

def Frag.binary (f : Bool → Bool → Bool) (A B : Frag) : Frag := by
  refine ⟨A.raw ∪ B.raw, A.hole.or B.hole, fun x b => f (A.f x b) (B.f x b), ?_, ?_⟩
  · intro x y h b
    rw [A.congrRaw x y (fun a ha => h a (mem_union_left _ ha)),
      B.congrRaw x y (fun a ha => h a (mem_union_right _ ha))]
  · intro h x b c
    have ha : A.hole = none := by cases ah : A.hole <;> simp_all [Option.or]
    have hb : B.hole = none := by simpa [ha, Option.or] using h
    rw [A.ignore ha x b c, B.ignore hb x b c]

theorem Frag.binary_eval (f : Bool → Bool → Bool) (A B : Frag) (x y : ℕ → Bool)
    (h : ¬(A.hole.isSome && B.hole.isSome) = true) :
    (Frag.binary f A B).eval x y = f (A.eval x y) (B.eval x y) := by
  obtain ⟨as, ah, af, ac, ai⟩ := A
  obtain ⟨bs, bh, bf, bc, bi⟩ := B
  cases ah <;> cases bh <;> simp_all [Frag.eval, Frag.binary, Option.or]
  all_goals first | rw [ai rfl] | rw [bi rfl]

noncomputable section

def Net.mask (N : Net) (bad : Finset ℕ) (a : ℕ) (F : Frag) : Frag := by
  classical
  exact if N.cut bad a then Frag.entry a else F

def Net.build (N : Net) (bad : Finset ℕ) (w : ℕ) : Bool × Frag :=
  let arg := fun a => N.mask bad a (if a < w then (N.build bad a).2 else Frag.lit false)
  match N.code w with
  | .raw => (false, Frag.bit w)
  | .lit b => (false, Frag.lit b)
  | .one f a =>
    (false, Frag.unary f (arg a))
  | .two f a b =>
    let A := arg a
    let B := arg b
    if A.hole.isSome && B.hole.isSome then (true, Frag.entry w) else (false, Frag.binary f A B)
termination_by w

def Net.frag (N : Net) (bad : Finset ℕ) (w : ℕ) : Frag := (N.build bad w).2

def Net.join (N : Net) (bad : Finset ℕ) (w : ℕ) : Prop := (N.build bad w).1 = true

def Net.arg (N : Net) (bad : Finset ℕ) (w : ℕ) : Frag := N.mask bad w (N.frag bad w)

theorem Net.build_raw {N : Net} {bad : Finset ℕ} {w} (h : N.code w = .raw) :
    N.build bad w = (false, Frag.bit w) := by
  rw [Net.build]; simp only [h]

theorem Net.build_lit {N : Net} {bad : Finset ℕ} {w b} (h : N.code w = .lit b) :
    N.build bad w = (false, Frag.lit b) := by
  rw [Net.build]; simp only [h]

theorem Net.build_one {N : Net} {bad : Finset ℕ} {w f a} (h : N.code w = .one f a) :
    N.build bad w = (false, Frag.unary f (N.arg bad a)) := by
  have ha : a < w := N.back (s := false) (by simp [h, Op.pin])
  rw [Net.build]; simp only [h, Net.arg, Net.frag, ite_eq_left ha]

theorem Net.build_two {N : Net} {bad : Finset ℕ} {w f a b} (h : N.code w = .two f a b) :
    N.build bad w = if (N.arg bad a).hole.isSome && (N.arg bad b).hole.isSome then
      (true, Frag.entry w) else (false, Frag.binary f (N.arg bad a) (N.arg bad b)) := by
  have ha : a < w := N.back (s := false) (by simp [h, Op.pin])
  have hb : b < w := N.back (s := true) (by simp [h, Op.pin])
  rw [Net.build]; simp only [h, Net.arg, Net.frag, ite_eq_left ha, ite_eq_left hb]
  split <;> simp_all

theorem Net.arg_eval {N : Net} {bad : Finset ℕ} {w} {x : ℕ → Bool}
    (h : (N.frag bad w).eval x (N.run x) = N.run x w) :
    (N.arg bad w).eval x (N.run x) = N.run x w := by
  classical
  by_cases hc : N.cut bad w
  · simp [Net.arg, Net.mask, hc, Frag.eval, Frag.entry]
  · simpa [Net.arg, Net.mask, hc] using h

theorem Net.frag_eval (N : Net) (bad : Finset ℕ) (x : ℕ → Bool) (w : ℕ) :
    (N.frag bad w).eval x (N.run x) = N.run x w := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    conv_rhs => rw [Net.run_eq]
    cases h : N.code w with
    | raw => simp [Net.frag, N.build_raw h, Frag.eval, Frag.bit, Op.value]
    | lit b => simp [Net.frag, N.build_lit h, Frag.eval, Frag.lit, Op.value]
    | one f a =>
      rw [Op.value, Net.frag, N.build_one h]
      have ha := N.arg_eval (ih a (N.back (s := false) (by simp [h, Op.pin])))
      exact congrArg f ha
    | two f a b =>
      rw [Op.value, Net.frag, N.build_two h]
      split
      · change N.run x w = f (N.run x a) (N.run x b)
        rw [Net.run_eq, h, Op.value]
      · rename_i hp
        rw [Frag.binary_eval _ _ _ _ _ hp, N.arg_eval (ih a (N.back (s := false) (by simp [h, Op.pin]))),
          N.arg_eval (ih b (N.back (s := true) (by simp [h, Op.pin])))]

theorem Net.join_entry {N : Net} {bad : Finset ℕ} {w} (h : N.join bad w) :
    N.frag bad w = Frag.entry w := by
  cases he : N.code w with
  | raw => simp [Net.join, N.build_raw he] at h
  | lit b => simp [Net.join, N.build_lit he] at h
  | one f a => simp [Net.join, N.build_one he] at h
  | two f a b =>
    simp only [Net.join, Net.frag, N.build_two he] at h ⊢
    split at h <;> simp_all

theorem Net.join_two {N : Net} {bad : Finset ℕ} {w f a b} (h : N.code w = .two f a b) :
    N.join bad w ↔ (N.arg bad a).hole.isSome ∧ (N.arg bad b).hole.isSome := by
  unfold Net.join
  rw [N.build_two h]
  split <;> simp_all

theorem Net.hole_back {N : Net} {bad : Finset ℕ} {w a}
    (h : (N.frag bad w).hole = some a) :
    a ≤ w ∧ (N.cut bad a ∨ N.join bad a) ∧
      (w ∈ N.live → a ∈ N.live) ∧ (a = w → N.join bad w) := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hc (v : ℕ) {s : Bool} (hp : (N.code w).pin s = some v) (hh : (N.arg bad v).hole = some a) :
        a ≤ w ∧ (N.cut bad a ∨ N.join bad a) ∧
          (w ∈ N.live → a ∈ N.live) ∧ (a = w → N.join bad w) := by
      have hv := N.back hp
      have he (hw : w ∈ N.live) : v ∈ N.live := N.mem_live.mpr (.child (N.mem_live.mp hw) hp)
      by_cases hv' : N.cut bad v
      · have : v = a := by simpa [Net.arg, Net.mask, hv', Frag.entry] using hh
        subst a
        exact ⟨hv.le, Or.inl hv', he, fun h => (hv.ne h).elim⟩
      · obtain ⟨ha, hb, hreach, _⟩ := ih v hv (by simpa [Net.arg, Net.mask, hv'] using hh)
        have hlt := ha.trans_lt hv
        exact ⟨hlt.le, hb, fun hw => hreach (he hw), fun h => (hlt.ne h).elim⟩
    cases hw : N.code w with
    | raw => simp [Net.frag, N.build_raw hw, Frag.bit] at h
    | lit b => simp [Net.frag, N.build_lit hw, Frag.lit] at h
    | one f v =>
      apply hc v (s := false) (by simp [hw, Op.pin])
      simpa [Net.frag, N.build_one hw, Frag.unary] using h
    | two f v u =>
      by_cases hj : N.join bad w
      · have : w = a := by simpa [N.join_entry hj, Frag.entry] using h
        subst a
        exact ⟨le_rfl, Or.inr hj, id, fun _ => hj⟩
      · have hn : ¬((N.arg bad v).hole.isSome && (N.arg bad u).hole.isSome) = true := by
          simpa [N.join_two hw] using hj
        simp only [Net.frag, N.build_two hw, ite_eq_right hn, Frag.binary] at h
        cases he : (N.arg bad v).hole with
        | none => exact hc u (s := true) (by simp [hw, Op.pin]) (by simpa [he, Option.or] using h)
        | some k => exact hc v (s := false) (by simp [hw, Op.pin]) (by simpa [he, Option.or] using h)

theorem Net.hole_lt {N : Net} {bad : Finset ℕ} {w a} (hj : ¬N.join bad w)
    (h : (N.frag bad w).hole = some a) : a < w := by
  obtain ⟨h₁, _, _, h₂⟩ := N.hole_back h
  exact lt_of_le_of_ne h₁ (fun e => hj (h₂ e))

end

open Finset

noncomputable section

def Net.terminal (N : Net) (bad : Finset ℕ) (a : ℕ) : Prop :=
  N.cut bad a ∨ a = N.out ∨ ∃ e ∈ N.edges, N.src e = a ∧ N.join bad e.1

def Net.root (N : Net) (bad : Finset ℕ) (w : ℕ) : Prop :=
  w ∈ N.live ∧ N.terminal bad w ∧ ¬N.join bad w ∧
    ¬(N.code w = .raw ∧ N.cut bad w) ∧ (N.frag bad w).raw.Nonempty

def Net.roots (N : Net) (bad : Finset ℕ) : Finset ℕ := by
  classical
  exact N.live.filter (N.root bad)

@[simp] theorem Net.mem_roots {N : Net} {bad : Finset ℕ} {w} :
    w ∈ N.roots bad ↔ N.root bad w := by
  classical
  exact ⟨fun h => (mem_filter.mp h).2, fun h => mem_filter.mpr ⟨h.1,h⟩⟩

structure Net.Link (N : Net) (bad : Finset ℕ) (a w : ℕ) : Prop where
  edge : ∃ e ∈ N.edges, N.src e = a ∧ e.1 = w
  uncut : ¬N.cut bad a
  unjoined : ¬N.join bad w

inductive Net.Route (N : Net) (bad : Finset ℕ) : ℕ → ℕ → Prop where
  | nil (a : ℕ) : Route N bad a a
  | cons {a p w : ℕ} : N.Link bad a p → Route N bad p w → Route N bad a w

theorem Net.Route.snoc {N : Net} {bad : Finset ℕ} {a w p : ℕ}
    (h : N.Route bad a w) (hp : N.Link bad w p) : N.Route bad a p := by
  induction h with
  | nil w => exact .cons hp (.nil p)
  | cons h _ ih => exact .cons h (ih hp)

theorem Net.link_not_terminal {N : Net} {bad : Finset ℕ} {a w} (h : N.Link bad a w) :
    ¬N.terminal bad a := by
  rcases h.edge with ⟨e,he,hsa,hpa⟩
  rintro (hc | ho | ⟨e',he',hs',hj⟩)
  · exact h.uncut hc
  · exact N.not_out_src he (hsa.trans ho)
  · have hEq := N.use_unique he he' (hsa.trans hs'.symm) (fun hh => h.uncut (Or.inl (hsa ▸ hh)))
    exact h.unjoined (hpa ▸ hEq.symm ▸ hj)

theorem Net.link_unique {N : Net} {bad : Finset ℕ} {a w w'}
    (h : N.Link bad a w) (h' : N.Link bad a w') : w = w' := by
  rcases h.edge with ⟨e,he,hsa,rfl⟩
  rcases h'.edge with ⟨e',he',hsa',rfl⟩
  exact congrArg Prod.fst (N.use_unique he he' (hsa.trans hsa'.symm)
    (fun hh => h.uncut (Or.inl (hsa ▸ hh))))

theorem Net.Route.unique {N : Net} {bad : Finset ℕ} {a w w'}
    (h : N.Route bad a w) (h' : N.Route bad a w')
    (hw : N.terminal bad w) (hw' : N.terminal bad w') : w = w' := by
  induction h generalizing w' with
  | nil a =>
    cases h' with
    | nil => rfl
    | cons h _ => exact (N.link_not_terminal h hw).elim
  | cons h _ ih =>
    cases h' with
    | nil => exact (N.link_not_terminal h hw').elim
    | cons h' hp' =>
      have he := N.link_unique h h'
      subst he
      exact ih hp' hw hw'

theorem Net.find_terminal (N : Net) (bad : Finset ℕ) {a} (ha : a ∈ N.live) :
    ∃ w ∈ N.live, N.terminal bad w ∧ N.Route bad a w := by
  classical
  by_cases h : N.terminal bad a
  · exact ⟨a,ha,h,.nil a⟩
  · have hd := N.deg_pos ha (fun he => h (Or.inr (Or.inl he)))
    obtain ⟨e,he'⟩ := card_pos.mp hd
    obtain ⟨he,hs⟩ := mem_filter.mp he'
    have ha' : e.1 ∈ N.live := N.edge_live he
    obtain ⟨w,hw,ht,hr⟩ := N.find_terminal bad ha'
    exact ⟨w,hw,ht,.cons ⟨⟨e,he,hs,rfl⟩, fun hc => h (Or.inl hc),
      fun hj => h (Or.inr (Or.inr ⟨e,he,hs,hj⟩))⟩ hr⟩
termination_by N.out - a
decreasing_by
  have hlt := N.back (N.pin_src he)
  have hle := N.reach_le (N.mem_live.mp ha')
  omega

theorem Net.mem_arg_raw {N : Net} {bad : Finset ℕ} {a z} :
    a ∈ (N.arg bad z).raw ↔ ¬N.cut bad z ∧ a ∈ (N.frag bad z).raw := by
  classical
  by_cases h : N.cut bad z <;> simp [Net.arg, Net.mask, h, Frag.entry]

theorem Net.pin_into_frag {N : Net} {bad : Finset ℕ} {a w p s} (hj : ¬N.join bad p)
    (hp : (N.code p).pin s = some w) (ha : a ∈ (N.arg bad w).raw) :
    a ∈ (N.frag bad p).raw := by
  cases h : N.code p with
  | raw => simp [h, Op.pin] at hp
  | lit b => simp [h, Op.pin] at hp
  | one f v =>
    cases s <;> simp [h, Op.pin] at hp
    subst w
    simpa [Net.frag, N.build_one h, Frag.unary] using ha
  | two f v u =>
    have hn : ¬((N.arg bad v).hole.isSome && (N.arg bad u).hole.isSome) = true := by
      simpa [N.join_two h] using hj
    cases s <;> simp [h, Op.pin] at hp <;> subst w
    · simp only [Net.frag, N.build_two h, ite_eq_right hn, Frag.binary]
      exact mem_union_left _ ha
    · simp only [Net.frag, N.build_two h, ite_eq_right hn, Frag.binary]
      exact mem_union_right _ ha

theorem Net.Route.preserves_raw {N : Net} {bad : Finset ℕ} {u w a}
    (h : N.Route bad u w) (ha : a ∈ (N.frag bad u).raw) : a ∈ (N.frag bad w).raw := by
  induction h with
  | nil => exact ha
  | cons h _ ih =>
    obtain ⟨e,he,hs,hp⟩ := h.edge
    apply ih
    exact N.pin_into_frag h.unjoined (hp ▸ hs ▸ N.pin_src he) (N.mem_arg_raw.mpr ⟨h.uncut,ha⟩)

theorem Net.raw_route {N : Net} {bad : Finset ℕ} {w a} (hw : w ∈ N.live)
    (ha : a ∈ (N.frag bad w).raw) : a ∈ N.live ∧ N.code a = .raw ∧ N.Route bad a w := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have step {p s} (hp : (N.code w).pin s = some p) (hj : ¬N.join bad w)
        (hm : a ∈ (N.arg bad p).raw) : a ∈ N.live ∧ N.code a = .raw ∧ N.Route bad a w := by
      obtain ⟨hc, hm'⟩ := N.mem_arg_raw.mp hm
      obtain ⟨he,hs⟩ := N.edge_of_pin hw hp
      obtain ⟨h1,h2,h3⟩ := ih p (N.back hp) (hs ▸ N.src_live he) hm'
      exact ⟨h1,h2,h3.snoc ⟨⟨(w,s),he,hs,rfl⟩,hc,hj⟩⟩
    cases hh : N.code w with
    | raw =>
      have he : a = w := by simpa [Net.frag, N.build_raw hh, Frag.bit] using ha
      subst a
      exact ⟨hw,hh,.nil _⟩
    | lit b => simp [Net.frag, N.build_lit hh, Frag.lit] at ha
    | one f p =>
      apply step (p := p) (s := false) (by simp [hh, Op.pin]) (by simp [Net.join, N.build_one hh])
      simpa [Net.frag, N.build_one hh, Frag.unary] using ha
    | two f p q =>
      by_cases h : N.join bad w
      · simp [N.join_entry h, Frag.entry] at ha
      · have hn : ¬((N.arg bad p).hole.isSome && (N.arg bad q).hole.isSome) = true := by
          simpa [N.join_two hh] using h
        simp only [Net.frag, N.build_two hh, ite_eq_right hn, Frag.binary, mem_union] at ha
        exact ha.elim (step (p := p) (s := false) (by simp [hh, Op.pin]) h)
          (step (p := q) (s := true) (by simp [hh, Op.pin]) h)

theorem Net.root_support {N : Net} {bad : Finset ℕ} {a w}
    (hw : N.root bad w) (ha : a ∈ (N.frag bad w).raw) :
    a ∈ N.live ∧ N.code a = .raw ∧ ¬N.cut bad a := by
  obtain ⟨h1,h2,h3⟩ := N.raw_route hw.1 ha
  refine ⟨h1,h2,?_⟩
  cases h3 with
  | nil => exact fun hh => hw.2.2.2.1 ⟨h2,hh⟩
  | cons hh _ => exact hh.uncut

theorem Net.owner_exists {N : Net} {bad : Finset ℕ} {a} (ha : a ∈ N.live)
    (hr : N.code a = .raw) (hc : ¬N.cut bad a) :
    ∃! w, N.root bad w ∧ a ∈ (N.frag bad w).raw := by
  obtain ⟨w,hw,ht,hp⟩ := N.find_terminal bad ha
  have hbit : a ∈ (N.frag bad a).raw := by simp [Net.frag, N.build_raw hr, Frag.bit]
  have hm := hp.preserves_raw hbit
  have hj : ¬N.join bad w := fun h => by simp [N.join_entry h, Frag.entry] at hm
  have hn : ¬(N.code w = .raw ∧ N.cut bad w) := by
    rintro ⟨hrw,hcw⟩
    have he : a = w := by simpa [Net.frag, N.build_raw hrw, Frag.bit] using hm
    exact hc (he ▸ hcw)
  refine ⟨w, ⟨⟨hw,ht,hj,hn,⟨a,hm⟩⟩,hm⟩, ?_⟩
  intro w' hh
  exact (N.raw_route hh.1.1 hh.2).2.2.unique hp hh.1.2.1 ht

theorem Net.transfer {N : Net} {bad : Finset ℕ} (x y : ℕ → Bool)
    (hr : ∀ a ∈ N.live, N.code a = .raw → N.cut bad a → x a = y a)
    (hk : ∀ w, N.root bad w → ∀ b, (N.frag bad w).f x b = (N.frag bad w).f y b) :
    N.run x N.out = N.run y N.out := by
  have all (w : ℕ) (hw : w ∈ N.live) (ht : N.terminal bad w ∨ N.join bad w) :
      N.run x w = N.run y w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hj : N.join bad w
      · have descend {s a} (hp : (N.code w).pin s = some a) : N.run x a = N.run y a := by
          obtain ⟨he,hs⟩ := N.edge_of_pin hw hp
          exact ih a (N.back hp) (hs ▸ N.src_live he) (Or.inl (Or.inr (Or.inr ⟨(w,s),he,hs,hj⟩)))
        rw [Net.run_eq N x w, Net.run_eq N y w]
        cases he : N.code w with
        | raw => simp [Net.join, N.build_raw he] at hj
        | lit b => rfl
        | one f a => simp [Net.join, N.build_one he] at hj
        | two f a b =>
          simp only [Op.value]
          rw [descend (s := false) (by simp [he, Op.pin]), descend (s := true) (by simp [he, Op.pin])]
      · have ht' := ht.resolve_right hj
        by_cases hc : N.code w = .raw ∧ N.cut bad w
        · rw [Net.run_eq N x w, Net.run_eq N y w, hc.1, Op.value, Op.value]
          exact hr w hw hc.1 hc.2
        · rw [← N.frag_eval bad x w, ← N.frag_eval bad y w]
          have hf (b : Bool) : (N.frag bad w).f x b = (N.frag bad w).f y b := by
            by_cases hh : (N.frag bad w).raw.Nonempty
            · exact hk w ⟨hw,ht',hj,hc,hh⟩ b
            · exact (N.frag bad w).congrRaw x y (fun a ha => (hh ⟨a,ha⟩).elim) b
          unfold Frag.eval
          rw [hf]
          congr 1
          cases he : (N.frag bad w).hole with
          | none => rfl
          | some a =>
            have hb := (N.hole_back he).2.1
            have ha := N.hole_lt hj he
            have hl := (N.hole_back he).2.2.1 hw
            exact ih a ha hl (hb.imp Or.inl id)
  exact all N.out (N.mem_live.mpr .top) (Or.inl (Or.inr (Or.inl rfl)))

theorem Net.diff_routes {N : Net} {bad : Finset ℕ} (x y : ℕ → Bool) (w : ℕ)
    (hr : ∀ a ∈ N.live, N.code a = .raw → x a ≠ y a → N.Route bad a w) :
    ∀ t ∈ N.live, (t < w ∨ N.run x w = N.run y w) → N.run x t ≠ N.run y t →
      ¬N.join bad t ∧ N.Route bad t w := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht hb hd
    have pass {a s} (hp : (N.code t).pin s = some a) (h : N.run x a ≠ N.run y a) :
        ¬N.join bad t ∧ N.Route bad t w := by
      obtain ⟨he,hs⟩ := N.edge_of_pin ht hp
      have ha := N.back hp
      have hbw : a < w ∨ N.run x w = N.run y w := hb.imp (ha.trans ·) id
      have hh := (ih a ha (hs ▸ N.src_live he) hbw h).2
      cases hh with
      | nil => exact (hb.elim (fun hlt => (Nat.lt_asymm hlt ha).elim) (fun heq => (h heq).elim))
      | cons hl hr =>
        obtain ⟨e',he',hs',ht'⟩ := hl.edge
        have hslot := N.use_unique he' he (hs'.trans hs.symm)
          (fun h => hl.uncut (Or.inl (hs' ▸ h)))
        have heq : _ = t := ht'.symm.trans (congrArg Prod.fst hslot)
        exact heq ▸ ⟨hl.unjoined,hr⟩
    rw [Net.run_eq N x t, Net.run_eq N y t] at hd
    cases hh : N.code t with
    | raw => exact ⟨by simp [Net.join, N.build_raw hh], hr t ht hh (by simpa [hh, Op.value] using hd)⟩
    | lit b => simp [hh, Op.value] at hd
    | one f a =>
      simp only [hh, Op.value] at hd
      apply pass (a := a) (s := false) (by simp [hh, Op.pin])
      intro h; exact hd (congrArg f h)
    | two f a b =>
      simp only [hh, Op.value] at hd
      by_cases ha : N.run x a = N.run y a
      · apply pass (a := b) (s := true) (by simp [hh, Op.pin])
        intro hb; exact hd (congrArg₂ f ha hb)
      · exact pass (a := a) (s := false) (by simp [hh, Op.pin]) ha

theorem Net.transfer_local {N : Net} {bad : Finset ℕ} (x y : ℕ → Bool) (w : ℕ)
    (hw : w ∈ N.live) (hj : ¬N.join bad w)
    (hr : ∀ a ∈ N.live, N.code a = .raw → x a ≠ y a → N.Route bad a w)
    (hf : ∀ b, (N.frag bad w).f x b = (N.frag bad w).f y b) :
    N.run x N.out = N.run y N.out := by
  have he : N.run x w = N.run y w := by
    rw [← N.frag_eval bad x w, ← N.frag_eval bad y w]
    unfold Frag.eval
    rw [hf]
    congr 1
    cases hh : (N.frag bad w).hole with
    | none => rfl
    | some a =>
      by_contra h
      obtain ⟨_,he,hl,_⟩ := N.hole_back hh
      have hd := N.diff_routes x y w hr a (hl hw) (Or.inl (N.hole_lt hj hh)) h
      rcases he with hc | hc
      · cases hd.2 with
        | nil => exact (hj ((N.hole_back hh).2.2.2 rfl)).elim
        | cons he _ => exact he.uncut hc
      · exact hd.1 hc
  by_contra hh
  have hd := (N.diff_routes x y w hr N.out (N.mem_live.mpr .top) (Or.inr he) hh).2
  cases hd with
  | nil => exact hh he
  | cons hd _ =>
    exact N.link_not_terminal hd (Or.inr (Or.inl rfl))

end

open Finset

noncomputable section

theorem Net.arg_cut {N : Net} {bad : Finset ℕ} {a} (h : N.cut bad a) :
    N.arg bad a = Frag.entry a := by
  classical
  simp [Net.arg, Net.mask, h]

theorem Net.arg_uncut {N : Net} {bad : Finset ℕ} {a} (h : ¬N.cut bad a) :
    N.arg bad a = N.frag bad a := by
  classical
  simp [Net.arg, Net.mask, h]

theorem Net.pin_join {N : Net} {bad : Finset ℕ} {w s a}
    (hj : N.join bad w) (hp : (N.code w).pin s = some a) :
    (N.arg bad a).hole.isSome := by
  cases h : N.code w with
  | raw => simp [h, Op.pin] at hp
  | lit b => simp [h, Op.pin] at hp
  | one f b => simp [Net.join, N.build_one h] at hj
  | two f b c =>
    have hh := (N.join_two h).mp hj
    cases s <;> simp [h, Op.pin] at hp <;> subst a
    · exact hh.1
    · exact hh.2

theorem Net.join_arity {N : Net} {bad : Finset ℕ} {w} (h : N.join bad w) :
    (N.code w).arity = 2 := by
  cases he : N.code w with
  | raw => simp [Net.join, N.build_raw he] at h
  | lit b => simp [Net.join, N.build_lit he] at h
  | one f a => simp [Net.join, N.build_one he] at h
  | two f a b => rfl

theorem Net.has_input_hole {N : Net} {bad : Finset ℕ} {w} (hj : ¬N.join bad w)
    (hh : (N.frag bad w).hole.isSome) :
    ∃ s a, (N.code w).pin s = some a ∧ (N.arg bad a).hole.isSome := by
  cases h : N.code w with
  | raw => simp [Net.frag, N.build_raw h, Frag.bit] at hh
  | lit b => simp [Net.frag, N.build_lit h, Frag.lit] at hh
  | one f a =>
    exact ⟨false,a,by simp [Op.pin], by simpa [Net.frag, N.build_one h, Frag.unary] using hh⟩
  | two f a b =>
    have hn : ¬((N.arg bad a).hole.isSome && (N.arg bad b).hole.isSome) = true := by
      simpa [N.join_two h] using hj
    by_cases ha : (N.arg bad a).hole.isSome
    · exact ⟨false,a,by simp [Op.pin],ha⟩
    · have he : (N.arg bad a).hole = none := by
        cases he : (N.arg bad a).hole <;> simp_all
      exact ⟨true,b,by simp [Op.pin],by
        simpa [Net.frag, N.build_two h, ite_eq_right hn, Frag.binary, he, Option.or] using hh⟩

def Net.pure (N : Net) (bad : Finset ℕ) : Finset ℕ :=
  (N.roots bad).filter fun w => (N.frag bad w).hole = none

def Net.unary (N : Net) (bad : Finset ℕ) : Finset ℕ :=
  (N.roots bad).filter fun w => (N.frag bad w).hole.isSome

theorem Net.pure_bound (N : Net) (bad : Finset ℕ) (hb : ∀ a ∈ bad, N.code a = .raw) :
    (N.pure bad).card ≤ 2 * N.excess + 1 := by
  classical
  have hsub : N.pure bad ⊆ insert N.out (N.live.filter N.shared) := by
    intro w hw
    obtain ⟨hr,hh⟩ := mem_filter.mp hw
    have hr' := N.mem_roots.mp hr
    rcases hr'.2.1 with hc | h | ⟨e,he,hs,hj⟩
    · rcases hc with hv | hv
      · exact mem_insert_of_mem (mem_filter.mpr ⟨hr'.1,hv⟩)
      · exact (hr'.2.2.2.1 ⟨hb _ hv,Or.inr hv⟩).elim
    · exact mem_insert.mpr (Or.inl h)
    · by_cases hc : N.cut bad w
      · rcases hc with hc | hc
        · exact mem_insert_of_mem (mem_filter.mpr ⟨hr'.1,hc⟩)
        · exact (hr'.2.2.2.1 ⟨hb _ hc,Or.inr hc⟩).elim
      · have hp := N.pin_join hj (N.pin_src he)
        rw [hs, N.arg_uncut hc, hh] at hp
        contradiction
  have h₁ := card_le_card hsub
  have h₂ := card_insert_le N.out (N.live.filter N.shared)
  have h₃ := N.shared_le
  omega

theorem Net.unary_bound (N : Net) (bad : Finset ℕ) :
    (N.unary bad).card ≤ 4 * N.excess + 2 * bad.card := by
  classical
  let J := N.live.filter (N.join bad)
  let U := N.live.filter fun w => ¬N.join bad w ∧ (N.frag bad w).hole.isSome
  let End := U.filter fun w => N.cut bad w ∨ w = N.out
  let E := N.edges.filter fun e => (N.arg bad (N.src e)).hole.isSome
  let Jedge := N.edges.filter fun e => e.1 ∈ J
  have hJedge : Jedge.card = 2 * J.card := by
    rw [card_eq_sum_card_fiberwise (s := Jedge) (f := Prod.fst) (t := J)
      (fun _ he => (mem_filter.mp he).2)]
    have hs : (∑ w ∈ J, (Jedge.filter fun e => e.1 = w).card) = ∑ _ ∈ J, 2 := by
      apply sum_congr rfl
      intro w hw
      have hm : (Jedge.filter fun e => e.1 = w) = N.edges.filter fun e => e.1 = w := by
        ext e
        simp only [Jedge, mem_filter]
        grind
      rw [hm, N.card_pin_fiber (mem_filter.mp hw).1, N.join_arity (mem_filter.mp hw).2]
    simpa [Nat.mul_comm] using hs
  have hJsub : Jedge ⊆ E := by
    intro e he
    obtain ⟨he,hw⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨he,N.pin_join (mem_filter.mp hw).2 (N.pin_src he)⟩
  have hLower : 2 * J.card + U.card ≤ E.card := by
    let Eother := E.filter fun e => e.1 ∈ U
    have hUimg : U ⊆ Eother.image Prod.fst := by
      intro w hw
      obtain ⟨hw',hj,hh⟩ := mem_filter.mp hw
      obtain ⟨s,a,hp,ha⟩ := N.has_input_hole hj hh
      obtain ⟨he,hs⟩ := N.edge_of_pin hw' hp
      exact mem_image.mpr ⟨(w,s),mem_filter.mpr ⟨mem_filter.mpr ⟨he,hs ▸ ha⟩,hw⟩,rfl⟩
    have hUle := (card_le_card hUimg).trans card_image_le
    have hdis : Disjoint Jedge Eother := by
      apply disjoint_left.mpr
      intro e he he'
      exact (mem_filter.mp (mem_filter.mp he').2).2.1 (mem_filter.mp (mem_filter.mp he).2).2
    have hs : Jedge ∪ Eother ⊆ E := union_subset hJsub (filter_subset _ _)
    have h := card_le_card hs
    rw [card_union_of_disjoint hdis, hJedge] at h
    omega
  have hUpper : E.card + End.card ≤ (N.holeEdges bad).card + J.card + U.card := by
    let Q := E.filter fun e => ¬N.cut bad (N.src e)
    have hpart : (E.filter fun e => N.cut bad (N.src e)).card + Q.card = E.card :=
      card_filter_add_card_filter_not ..
    have hb : (E.filter fun e => N.cut bad (N.src e)).card ≤ (N.holeEdges bad).card :=
      card_le_card fun _ h => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp h).1).1,(mem_filter.mp h).2⟩
    have hinj : Set.InjOn N.src Q := by
      intro e he f hf h
      have h₁ := mem_filter.mp he
      have h₂ := mem_filter.mp hf
      exact N.use_unique (mem_filter.mp h₁.1).1 (mem_filter.mp h₂.1).1 h (fun hh => h₁.2 (Or.inl hh))
    have hdis : Disjoint (Q.image N.src) End := by
      apply disjoint_left.mpr
      intro w hw ha
      obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨he,hn⟩ := mem_filter.mp he
      exact (mem_filter.mp ha).2.elim hn (N.not_out_src (mem_filter.mp he).1)
    have hsub : Q.image N.src ∪ End ⊆ J ∪ U := by
      intro w hw
      rcases mem_union.mp hw with hh | hh
      · obtain ⟨e,he,rfl⟩ := mem_image.mp hh
        obtain ⟨he,hc⟩ := mem_filter.mp he
        obtain ⟨he, hh⟩ := mem_filter.mp he
        rw [N.arg_uncut hc] at hh
        by_cases hj : N.join bad (N.src e)
        · exact mem_union_left _ (mem_filter.mpr ⟨N.src_live he,hj⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨N.src_live he,hj,hh⟩)
      · exact mem_union_right _ (mem_filter.mp hh).1
    have h := (card_le_card hsub).trans (card_union_le J U)
    rw [card_union_of_disjoint hdis, card_image_of_injOn hinj] at h
    omega
  have hRoots : (N.unary bad).card ≤ End.card + 2 * J.card := by
    have hsub : N.unary bad ⊆ End ∪ Jedge.image N.src := by
      intro w hw
      obtain ⟨hr,hh⟩ := mem_filter.mp hw
      have hr' := N.mem_roots.mp hr
      have hU : w ∈ U := mem_filter.mpr ⟨hr'.1,hr'.2.2.1,hh⟩
      rcases hr'.2.1 with hc | ho | ⟨e,he,hs,hj⟩
      · exact mem_union_left _ (mem_filter.mpr ⟨hU,Or.inl hc⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨hU,Or.inr ho⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨e,mem_filter.mpr ⟨he,
          mem_filter.mpr ⟨N.edge_live he,hj⟩⟩,hs⟩)
    have h := (card_le_card hsub).trans (card_union_le End (Jedge.image N.src))
    have hc := card_image_le (s := Jedge) (f := N.src)
    omega
  have hB := N.cut_edges_le bad
  omega

end

open Finset PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) : W (gs ++ [g]) x = stp (W gs x) g := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [stp, ih]; omega

theorem getD_app_l (l l' : List Bool) (i : ℕ) (h : i < l.length) : (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_m (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem W_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]; exact ih

theorem W_stable (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (W (gs ++ [g]) x).getD i false = (W gs x).getD i false := by
  rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]

theorem W_take (gs : List Gate) (x : List Bool) (k i : ℕ) (hi : i < x.length + k) :
    (W gs x).getD i false = (W (gs.take k) x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    by_cases hk : k ≤ gs.length
    · rw [List.take_append_of_le_length hk, W_stable _ _ _ _ (by omega)]; exact ih
    · rw [List.take_of_length_le (by simp; omega)]

theorem W_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (W (gs.take j) x).getD i false) := by
  have h1 : gs.take (j + 1) = gs.take j ++ [gs[j]] := by
    rw [List.take_add_one]; simp [List.getElem?_eq_getElem hj]
  rw [W_take gs x (j + 1) _ (by omega), h1, W_snoc, stp]
  have hl : (W (gs.take j) x).length = x.length + j := by
    rw [W_len, List.length_take]; omega
  rw [← hl, getD_app_m]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = (decide (i = u.val) || decide (i = n + v.val)) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    have : i ≠ n + v.val := by omega
    simp [h, this, Fin.ext_iff]
  · rw [List.getElem?_append_right (by simpa using h)]
    have hu : i ≠ u.val := by have := u.isLt; omega
    by_cases h2 : i - n < m
    · simp [h2, hu, Fin.ext_iff]; omega
    · have : i ≠ n + v.val := by have := v.isLt; omega
      simp [h2, hu, this]

def prevWire (w i : ℕ) : ℕ := if i + 1 < w then i + 1 else 0

def ofGate (w : ℕ) (g : Gate) : Op :=
  match g.inputs with
  | [] => .lit (g.op.eval [])
  | [a] => .one (fun p => g.op.eval [p]) (prevWire w a)
  | [a,b] => .two (fun p q => g.op.eval [p,q]) (prevWire w a) (prevWire w b)
  | _ => .lit false

theorem ofGate_arity (w : ℕ) (g : Gate) (h : g.inputs.length ≤ 2) :
    (ofGate w g).arity = g.inputs.length := by
  rcases hi : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
  all_goals simp [ofGate, hi, Op.arity] at h ⊢

def codeAt (k : ℕ) (C : Circuit) (w : ℕ) : Op :=
  if w = 0 then .lit false else if w ≤ k then .raw else
    (C.gates[w - (k + 1)]?).elim (.lit false) (ofGate w)

theorem prevWire_lt {w i : ℕ} (hw : 0 < w) : prevWire w i < w := by
  unfold prevWire; split <;> omega

theorem ofGate_back {w a s} (g : Gate) (hw : 0 < w)
    (h : (ofGate w g).pin s = some a) : a < w := by
  rcases hi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨c,l⟩⟩⟩
  all_goals cases s <;> simp [ofGate, hi, Op.pin] at h
  all_goals subst a; exact prevWire_lt hw

def ofCircuit (k : ℕ) (C : Circuit) : Net where
  code := codeAt k C
  out := if C.output < k + C.gates.length then C.output + 1 else 0
  back := by
    intro w s a h
    by_cases h0 : w = 0
    · simp [codeAt, h0, Op.pin] at h
    by_cases hk : w ≤ k
    · simp [codeAt, h0, hk, Op.pin] at h
    cases he : C.gates[w-(k+1)]? with
    | none => simp [codeAt, h0, hk, he, Op.pin] at h
    | some g => exact ofGate_back g (Nat.pos_of_ne_zero h0) (by simpa [codeAt, h0, hk, he] using h)

theorem codeAt_raw {k : ℕ} {C : Circuit} {w : ℕ} :
    (ofCircuit k C).code w = .raw ↔ 0 < w ∧ w ≤ k := by
  by_cases h0 : w = 0
  · simp [ofCircuit, codeAt, h0]
  by_cases hk : w ≤ k
  · simp [ofCircuit, codeAt, h0, hk, Nat.pos_of_ne_zero h0]
  cases he : C.gates[w-(k+1)]? with
  | none => simp [ofCircuit, codeAt, h0, hk, he]
  | some g =>
    rcases hi : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨c,l⟩⟩⟩ <;>
      simp [ofCircuit, codeAt, h0, hk, he, ofGate, hi]

theorem codeAt_g {k w : ℕ} {C : Circuit} (hk : k < w) (hj : w - (k+1) < C.gates.length) :
    (ofCircuit k C).code w = ofGate w (C.gates[w-(k+1)]) := by
  simp [ofCircuit, codeAt, show w ≠ 0 by omega, show ¬w ≤ k by omega, hj]

theorem ofCircuit_value (C : Circuit) (x : List Bool) (X : ℕ → Bool)
    (hx : ∀ i < x.length, X (i+1) = x.getD i false)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (w : ℕ) (hw : w ≤ x.length + C.gates.length) :
    (ofCircuit x.length C).run X w = if w = 0 then false else (W C.gates x).getD (w-1) false := by
  let N := ofCircuit x.length C
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h0 : w = 0
    · simp [Net.run_eq, ofCircuit, codeAt, h0, Op.value]
    by_cases hr : w ≤ x.length
    · have hw' : w - 1 < x.length := by omega
      simp only [Net.run_eq, (codeAt_raw.mpr ⟨Nat.pos_of_ne_zero h0,hr⟩), Op.value, ite_eq_right h0]
      rw [W_lt _ _ _ hw']
      simpa [show w - 1 + 1 = w by omega] using hx (w-1) hw'
    have hj : w - (x.length+1) < C.gates.length := by omega
    let j := w - (x.length+1)
    have hi : j < C.gates.length := hj
    let g := C.gates[j]
    have hg' := hg g (List.getElem_mem hi)
    have hwj : w - 1 = x.length + j := by dsimp [j]; omega
    have hread (a : ℕ) : N.run X (prevWire w a) = (W (C.gates.take j) x).getD a false := by
      by_cases ha : a + 1 < w
      · rw [prevWire, ite_eq_left ha, ih _ ha (by omega), ite_eq_right (by omega), show a + 1 - 1 = a by omega]
        exact W_take _ _ _ _ (by omega)
      · rw [prevWire, ite_eq_right ha, ih 0 (by omega) (by omega), ite_eq_left rfl]
        exact (getD_big _ _ (by rw [W_len, List.length_take]; omega)).symm
    rw [ite_eq_right h0, hwj, W_val _ _ _ hi, Net.run_eq, codeAt_g (Nat.lt_of_not_ge hr) hj]
    change (ofGate w g).value (X w) (N.run X) = g.op.eval (g.inputs.map fun a => (W (C.gates.take j) x).getD a false)
    rcases hh : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c,l⟩⟩⟩
    all_goals simp [ofGate, hh, Op.value, hread] at hg' ⊢

theorem ofCircuit_eval (C : Circuit) (x : List Bool) (X : ℕ → Bool)
    (hx : ∀ i < x.length, X (i+1) = x.getD i false)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (ofCircuit x.length C).run X (ofCircuit x.length C).out = C.eval x := by
  change (ofCircuit x.length C).run X _ = (W C.gates x).getD C.output false
  by_cases ho : C.output < x.length + C.gates.length
  · have hout : (ofCircuit x.length C).out = C.output + 1 := by simp [ofCircuit, ho]
    rw [hout, ofCircuit_value C x X hx hg _ (by omega)]
    simp
  · have hout : (ofCircuit x.length C).out = 0 := by simp [ofCircuit, ho]
    rw [hout, ofCircuit_value C x X hx hg _ (by omega), ite_eq_left rfl]
    exact (getD_big _ _ (by rw [W_len]; omega)).symm

theorem ofCircuit_bin (k : ℕ) (C : Circuit) (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ((ofCircuit k C).live.filter fun a => ((ofCircuit k C).code a).arity = 2).card ≤
      C.gates.countP (fun g => g.inputs.length == 2) := by
  classical
  let N := ofCircuit k C
  let B := N.live.filter fun a => (N.code a).arity = 2
  let D := (univ : Finset (Fin C.gates.length)).filter fun j => C.gates[j].inputs.length = 2
  have hb (w) (hw : w ∈ B) : k < w ∧ w - (k+1) < C.gates.length := by
    obtain ⟨hl,ho⟩ := mem_filter.mp hw
    have hp := N.reach_le (N.mem_live.mp hl)
    have hk : k < w := by
      by_contra! hc
      by_cases h0 : w = 0 <;> simp [N, ofCircuit, codeAt, h0, hc, Op.arity] at ho
    constructor
    · exact hk
    · unfold N ofCircuit at hp
      by_cases ht : C.output < k + C.gates.length <;> simp [ht] at hp <;> omega
  have hB : B.card ≤ D.card := by
    by_cases hnil : C.gates.length = 0
    · have hempty : B = ∅ := eq_empty_iff_forall_notMem.mpr fun w hw => by have := (hb w hw).2; omega
      simp [hempty]
    let f : ℕ → Fin C.gates.length := fun w => if h : w ∈ B then ⟨w-(k+1),(hb w h).2⟩ else ⟨0, Nat.pos_of_ne_zero hnil⟩
    apply card_le_card_of_injOn f
    · intro w hw
      change f w ∈ D
      have hf : f w = ⟨w-(k+1),(hb w hw).2⟩ := dite_eq_left hw
      rw [hf]
      apply mem_filter.mpr ⟨mem_univ _,?_⟩
      have ho := (mem_filter.mp hw).2
      have hn := hg _ (List.getElem_mem (hb w hw).2)
      rwa [codeAt_g (hb w hw).1 (hb w hw).2, ofGate_arity _ _ hn] at ho
    · intro w hw v hv he
      have hw' : w ∈ B := hw
      have hv' : v ∈ B := hv
      have hf (u) (hu : u ∈ B) : (f u).val = u - (k+1) := by simp only [f, dite_eq_left hu]
      have h := (hf w hw').symm.trans ((congrArg Fin.val he).trans (hf v hv'))
      have h1 := (hb w hw).1
      have h2 := (hb v hv).1
      omega
  apply hB.trans_eq
  change (univ.filter fun j : Fin C.gates.length => C.gates[j].inputs.length = 2).card = _
  rw [card_eq_sum_ones, sum_filter]
  have hlist (l : List Gate) : (∑ j : Fin l.length, if l[j].inputs.length = 2 then 1 else 0) =
      l.countP (fun g => g.inputs.length == 2) := by
    induction l with
    | nil => simp
    | cons g gs ih =>
      let f (j : Fin (gs.length + 1)) : ℕ := if (g :: gs)[j].inputs.length = 2 then 1 else 0
      change (∑ j, f j) = _
      rw [Fin.sum_univ_succ f, List.countP_cons]
      change (if g.inputs.length = 2 then 1 else 0) +
        (∑ j : Fin gs.length, if gs[j].inputs.length = 2 then 1 else 0) = _
      rw [ih]
      by_cases he : g.inputs.length = 2 <;> simp [he, Nat.add_comm]
  exact hlist C.gates

open Finset

def address {n : ℕ} (s : Bool) (i : Fin n) : ℕ := if s then n + i.val + 1 else i.val + 1

theorem address_inj {n : ℕ} (s : Bool) : Function.Injective (address (n := n) s) := by
  intro i j h
  apply Fin.ext
  cases s <;> (simp [address] at h; omega)

theorem address_pos {n : ℕ} (s : Bool) (i : Fin n) : 0 < address s i := by
  cases s <;> simp [address]

theorem address_le {n : ℕ} (s : Bool) (i : Fin n) : address s i ≤ n+n := by
  have := i.isLt
  cases s
  all_goals simp [address]
  omega

theorem address_surj {n w : ℕ} (hw : 0 < w ∧ w ≤ n+n) :
    ∃ (s : Bool) (i : Fin n), address s i = w := by
  by_cases h : w ≤ n
  · exact ⟨false, ⟨w-1, by omega⟩, by simp [address]; omega⟩
  · exact ⟨true, ⟨w-n-1, by omega⟩, by simp [address]; omega⟩

def twice (a b z : ℕ) : Bool := decide (z = a ∨ z = b)

def once (a z : ℕ) : Bool := decide (z = a)

def view {n : ℕ} (N : Net) (s : Bool) (i j : Fin n) : Bool :=
  N.run (twice (address s i) (address (!s) j)) N.out

def bank {n : ℕ} (s : Bool) (F : Frag) : Finset (Fin n) :=
  univ.filter fun i => address s i ∈ F.raw

theorem bank_le {n : ℕ} (s : Bool) (F : Frag) : (bank (n := n) s F).card ≤ F.raw.card := by
  apply card_le_card_of_injOn (address s)
  · exact fun i hi => (mem_filter.mp hi).2
  · exact (address_inj s).injOn

theorem raw_le_banks {n : ℕ} (F : Frag) (h : ∀ w ∈ F.raw, 0 < w ∧ w ≤ n+n) :
    F.raw.card ≤ (bank (n := n) false F).card + (bank (n := n) true F).card := by
  let A := (bank (n := n) false F).image (address false)
  let B := (bank (n := n) true F).image (address true)
  have hsub : F.raw ⊆ A ∪ B := by
    intro w hw
    obtain ⟨s,i,rfl⟩ := address_surj (h w hw)
    cases s
    · exact mem_union_left _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hw⟩,rfl⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hw⟩,rfl⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans_eq (by
    simp [A, B, card_image_of_injective, address_inj]))

def key (F : Frag) (x : ℕ → Bool) : Bool × Bool := (F.f x false, F.f x true)

theorem key_apply {F : Frag} {x y : ℕ → Bool} (h : key F x = key F y) (b : Bool) :
    F.f x b = F.f y b := by
  cases b
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

def baseline (F : Frag) : Bool × Bool := key F (fun _ => false)

theorem key_diag {F : Frag} (h : F.hole = none) (x : ℕ → Bool) : (key F x).1 = (key F x).2 :=
  F.ignore h x false true

def keySpace (F : Frag) : Finset (Bool × Bool) :=
  if F.hole = none then {(false,false),(true,true)} else univ

theorem key_mem (F : Frag) (x : ℕ → Bool) : key F x ∈ keySpace F := by
  by_cases h : F.hole = none
  · have he := key_diag h x
    cases hp : key F x with
    | mk a b =>
      rw [hp] at he
      cases a <;> cases b <;> simp_all [keySpace]
  · simp [keySpace, h]

theorem keySpace_card (F : Frag) : (keySpace F).card = if F.hole = none then 2 else 4 := by
  by_cases h : F.hole = none <;> simp [keySpace, h, Fintype.card_prod]

theorem twice_eq_once {F : Frag} {a b : ℕ} (hb : b ∉ F.raw) (β : Bool) :
    F.f (twice a b) β = F.f (once a) β := by
  apply F.congrRaw
  intro z hz
  have hn : z ≠ b := fun h => hb (h ▸ hz)
  simp [twice, once, hn]

theorem once_eq_base {F : Frag} {a : ℕ} (ha : a ∉ F.raw) (β : Bool) :
    F.f (once a) β = F.f (fun _ => false) β := by
  apply F.congrRaw
  intro z hz
  simp [once, show z ≠ a from fun he => ha (he ▸ hz)]

theorem twice_comm (a b : ℕ) : twice a b = twice b a := by
  funext z
  simp [twice, or_comm]

theorem twice_same {a b c z : ℕ} (ha : z ≠ a) (hb : z ≠ b) :
    twice a c z = twice b c z := by simp [twice, ha, hb]

def Far {n : ℕ} (N : Net) (bad : Finset ℕ) : Prop :=
  ∀ s (i j : Fin n), i ≠ j → address s i ∉ bad → address s j ∉ bad →
    17 ≤ dist (view N s i) (view N s j)

def RawBank (n : ℕ) (N : Net) : Prop := ∀ a, N.code a = .raw ↔ 0 < a ∧ a ≤ n+n

def Net.Private (N : Net) (bad : Finset ℕ) (a : ℕ) : Prop :=
  a ∈ N.live ∧ N.code a = .raw ∧ ¬N.cut bad a

theorem Net.private_raw {N : Net} {bad : Finset ℕ} {w a} (hw : w ∈ N.live)
    (hs : ¬(N.code w = .raw ∧ N.cut bad w)) (ha : a ∈ (N.frag bad w).raw) : N.Private bad a := by
  obtain ⟨hl,hr,hp⟩ := N.raw_route hw ha
  refine ⟨hl,hr,?_⟩
  cases hp with
  | nil => exact fun hh => hs ⟨hr,hh⟩
  | cons h _ => exact h.uncut

theorem local_profile {n : ℕ} {N : Net} {bad : Finset ℕ} {s : Bool} {i j : Fin n} {w : ℕ}
    (hw : w ∈ N.live) (hs : ¬N.join bad w)
    (hi : address s i ∈ (N.frag bad w).raw) (hj : address s j ∈ (N.frag bad w).raw)
    (hk : key (N.frag bad w) (once (address s i)) = key (N.frag bad w) (once (address s j))) :
    dist (view N s i) (view N s j) ≤ (bank (n := n) (!s) (N.frag bad w)).card := by
  apply dist_le_of_agree
  intro z hz
  have hh : address (!s) z ∉ (N.frag bad w).raw := fun h => hz (mem_filter.mpr ⟨mem_univ _,h⟩)
  apply N.transfer_local _ _ w hw hs
  · intro a ha hr hd
    by_cases he : a = address s i
    · exact he.symm ▸ (N.raw_route hw hi).2.2
    by_cases he' : a = address s j
    · exact he'.symm ▸ (N.raw_route hw hj).2.2
    exact (hd (twice_same he he')).elim
  · intro bit
    rw [twice_eq_once hh, twice_eq_once hh, key_apply hk]

theorem bank_keys_inj {n : ℕ} {N : Net} {bad : Finset ℕ} {w : ℕ} (hF : Far (n := n) N bad)
    (hw : w ∈ N.live) (hs : ¬(N.code w = .raw ∧ N.cut bad w))
    (hJ : ¬N.join bad w) (hB : (N.frag bad w).raw.card ≤ 16) (s : Bool) :
    Set.InjOn (fun i : Fin n => key (N.frag bad w) (once (address s i))) (bank (n := n) s (N.frag bad w)) := by
  intro i hi j hj hkey
  by_contra hne
  have hi' := (mem_filter.mp hi).2
  have hj' := (mem_filter.mp hj).2
  have hd := hF s i j hne (fun h => (N.private_raw hw hs hi').2.2 (Or.inr h))
    (fun h => (N.private_raw hw hs hj').2.2 (Or.inr h))
  have hd' := (local_profile hw hJ hi' hj' hkey).trans (bank_le (!s) _)
  omega

theorem frag_small {n : ℕ} {N : Net} {bad : Finset ℕ} (hR : RawBank n N) (hF : Far (n := n) N bad)
    (w : ℕ) (hw : w ∈ N.live) :
    (N.frag bad w).raw.card ≤ if (N.frag bad w).hole = none then 4 else 8 := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have descend {a s} (h : (N.code w).pin s = some a) : (N.arg bad a).raw.card ≤ 8 := by
      have ha := N.mem_live.mpr (.child (N.mem_live.mp hw) h)
      have hI := ih a (N.back h) ha
      by_cases hc : N.cut bad a
      · simp [N.arg_cut hc, Frag.entry]
      · rw [N.arg_uncut hc]
        exact hI.trans (by split <;> omega)
    have finish (h₁ : ¬(N.code w = .raw ∧ N.cut bad w)) (hJ : ¬N.join bad w)
        (hm : (N.frag bad w).raw.card ≤ 16) :
        (N.frag bad w).raw.card ≤ if (N.frag bad w).hole = none then 4 else 8 := by
      let F := N.frag bad w
      have cardSide (s : Bool) : (bank (n := n) s F).card ≤ (keySpace F).card := by
        apply card_le_card_of_injOn (fun i => key F (once (address s i)))
        · exact fun i _ => key_mem F _
        · exact bank_keys_inj hF hw h₁ hJ hm s
      have hL := raw_le_banks F (fun a ha => (hR a).mp (N.raw_route hw ha).2.1)
      have hA := cardSide false
      have hB := cardSide true
      rw [keySpace_card] at hA hB
      change F.raw.card ≤ if F.hole = none then 4 else 8
      by_cases hh : F.hole = none
      · rw [ite_eq_left hh] at hA hB ⊢
        omega
      · rw [ite_eq_right hh] at hA hB ⊢
        omega
    cases h : N.code w with
    | raw => simp [Net.frag, N.build_raw h, Frag.bit]
    | lit b => simp [Net.frag, N.build_lit h, Frag.lit]
    | one f a =>
      apply finish (by simp [h]) (by simp [Net.join, N.build_one h])
      simpa [Net.frag, N.build_one h, Frag.unary] using
        (descend (a := a) (s := false) (by simp [h, Op.pin])).trans (show 8 ≤ 16 by omega)
    | two f a b =>
      by_cases hj : N.join bad w
      · simp [N.join_entry hj, Frag.entry]
      apply finish (by simp [h]) hj
      have hn : ¬((N.arg bad a).hole.isSome && (N.arg bad b).hole.isSome) = true := by
        simpa [N.join_two h] using hj
      simp only [Net.frag, N.build_two h, ite_eq_right hn, Frag.binary]
      have ha := descend (a := a) (s := false) (by simp [h, Op.pin])
      have hb := descend (a := b) (s := true) (by simp [h, Op.pin])
      exact (card_union_le _ _).trans (by omega)

theorem Net.agree_live {N : Net} (x y : ℕ → Bool)
    (h : ∀ a ∈ N.live, N.code a = .raw → x a = y a) : N.run x N.out = N.run y N.out := by
  have all (w) (hw : w ∈ N.live) : N.run x w = N.run y w := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      have descend {a s} (he : (N.code w).pin s = some a) : N.run x a = N.run y a :=
        ih a (N.back he) (N.mem_live.mpr (.child (N.mem_live.mp hw) he))
      rw [Net.run_eq N x w, Net.run_eq N y w]
      cases he : N.code w with
      | raw => exact h w hw he
      | lit b => rfl
      | one f a => exact congrArg f (descend (a := a) (s := false) (by simp [he, Op.pin]))
      | two f a b =>
        exact congrArg₂ f (descend (a := a) (s := false) (by simp [he, Op.pin]))
          (descend (a := b) (s := true) (by simp [he, Op.pin]))
  exact all N.out (N.mem_live.mpr .top)

open Finset

noncomputable section

def owner (N : Net) (bad : Finset ℕ) (a : ℕ) : ℕ := by
  classical
  exact if h : N.Private bad a then (N.owner_exists h.1 h.2.1 h.2.2).exists.choose else 0

theorem owner_spec {N : Net} {bad : Finset ℕ} {a : ℕ} (h : N.Private bad a) :
    N.root bad (owner N bad a) ∧ a ∈ (N.frag bad (owner N bad a)).raw := by
  classical
  simpa only [owner, dite_eq_left h] using (N.owner_exists h.1 h.2.1 h.2.2).exists.choose_spec

theorem owner_eq {N : Net} {bad : Finset ℕ} {a w : ℕ} (hw : N.root bad w)
    (ha : a ∈ (N.frag bad w).raw) : owner N bad a = w := by
  have hh := owner_spec (N.root_support hw ha)
  exact (N.raw_route hh.1.1 hh.2).2.2.unique (N.raw_route hw.1 ha).2.2 hh.1.2.1 hw.2.1

def privateSide {n : ℕ} (N : Net) (bad : Finset ℕ) (s : Bool) : Finset (Fin n) := by
  classical
  exact univ.filter fun i => N.Private bad (address s i)

theorem mem_privateSide {n : ℕ} {N : Net} {bad : Finset ℕ} {s : Bool} {i : Fin n} :
    i ∈ privateSide N bad s ↔ N.Private bad (address s i) := by
  classical
  simp [privateSide]

def signature (N : Net) (bad : Finset ℕ) (a : ℕ) : ℕ × (Bool × Bool) :=
  let w := owner N bad a
  (w, key (N.frag bad w) (once a))

def ordinary {n : ℕ} (N : Net) (bad : Finset ℕ) (s : Bool) : Finset (Fin n) :=
  (privateSide N bad s).filter fun i =>
    (signature N bad (address s i)).2 ≠ baseline (N.frag bad (owner N bad (address s i)))

def unused {n : ℕ} (N : Net) (bad : Finset ℕ) (s : Bool) : Finset (Fin n) :=
  univ.filter fun i => address s i ∉ N.live ∧ address s i ∉ bad

theorem unused_le {n : ℕ} {N : Net} {bad : Finset ℕ} (hF : Far (n := n) N bad) (s : Bool) :
    (unused (n := n) N bad s).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  by_contra hn
  obtain ⟨_,hi',hi''⟩ := mem_filter.mp hi
  obtain ⟨_,hj',hj''⟩ := mem_filter.mp hj
  have hd := hF s i j hn hi'' hj''
  have he : view N s i = view N s j := by
    funext z
    apply N.agree_live _ _
    intro a ha _
    exact twice_same (fun h => hi' (h ▸ ha)) (fun h => hj' (h ▸ ha))
  simp [he, dist] at hd

theorem cover_raw {n : ℕ} {N : Net} {bad X : Finset ℕ} (hF : Far (n := n) N bad)
    (h : ∀ a ∈ N.live, N.code a = .raw → a ∉ bad → a ∈ X)
    (hR : RawBank n N) : 2*n ≤ X.card + bad.card + 2 := by
  classical
  let A := (unused (n := n) N bad false).image (address false)
  let B := (unused (n := n) N bad true).image (address true)
  have hsub : (range (n+n+1)).erase 0 ⊆ X ∪ bad ∪ A ∪ B := by
    intro w hw
    have hb : 0 < w ∧ w ≤ n+n := by
      have := mem_erase.mp hw
      have := mem_range.mp this.2
      omega
    by_cases hbad : w ∈ bad
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hbad))
    by_cases hl : w ∈ N.live
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (h w hl ((hR w).mpr hb) hbad)))
    obtain ⟨s,i,rfl⟩ := address_surj hb
    cases s
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hl,hbad⟩,rfl⟩))
    · exact mem_union_right _ (mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hl,hbad⟩,rfl⟩)
  have hc := card_le_card hsub
  rw [card_erase_of_mem (by simp : 0 ∈ range (n+n+1)), card_range] at hc
  have hu := card_union_le (X ∪ bad ∪ A) B
  have hv := card_union_le (X ∪ bad) A
  have hx := card_union_le X bad
  have ha := (card_image_le (s := unused (n := n) N bad false) (f := address false)).trans (unused_le hF false)
  have hb := (card_image_le (s := unused (n := n) N bad true) (f := address true)).trans (unused_le hF true)
  change A.card ≤ 1 at ha
  change B.card ≤ 1 at hb
  omega

theorem private_lower {n : ℕ} {N : Net} {bad : Finset ℕ} (hF : Far (n := n) N bad) (hR : RawBank n N) :
    2*n ≤ (privateSide (n := n) N bad false).card + (privateSide (n := n) N bad true).card +
      N.excess + bad.card + 2 := by
  classical
  let A := (privateSide (n := n) N bad false).image (address false)
  let B := (privateSide (n := n) N bad true).image (address true)
  let X := A ∪ B ∪ N.live.filter N.shared
  have h := cover_raw hF (X := X) (fun w hl hr hb => by
    by_cases hc : N.shared w
    · exact mem_union_right _ (mem_filter.mpr ⟨hl,hc⟩)
    have hp : N.Private bad w := ⟨hl,hr,fun he => he.elim hc hb⟩
    obtain ⟨s,i,rfl⟩ := address_surj ((hR w).mp hr)
    cases s
    · exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨i,mem_privateSide.mpr hp,rfl⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨i,mem_privateSide.mpr hp,rfl⟩))) hR
  have hx := card_union_le (A ∪ B) (N.live.filter N.shared)
  have hu := card_union_le A B
  have ha := card_image_le (s := privateSide (n := n) N bad false) (f := address false)
  have hb := card_image_le (s := privateSide (n := n) N bad true) (f := address true)
  have hd := N.shared_le
  change 2*n ≤ X.card + bad.card + 2 at h
  change X.card ≤ _ at hx
  change A.card ≤ _ at ha
  change B.card ≤ _ at hb
  omega

theorem private_sig_inj {n : ℕ} {N : Net} {bad : Finset ℕ} (hF : Far (n := n) N bad)
    (hR : RawBank n N) (s : Bool) :
    Set.InjOn (fun i : Fin n => signature N bad (address s i)) (privateSide (n := n) N bad s) := by
  intro i hi j hj hk
  have hi' := owner_spec (mem_privateSide.mp hi)
  have hj' := owner_spec (mem_privateSide.mp hj)
  have hw : owner N bad (address s i) = owner N bad (address s j) := congrArg Prod.fst hk
  have hk' := congrArg Prod.snd hk
  change key (N.frag bad (owner N bad (address s i))) (once (address s i)) =
    key (N.frag bad (owner N bad (address s j))) (once (address s j)) at hk'
  rw [← hw] at hk' hj'
  have h8 := frag_small hR hF _ hi'.1.1
  have h16 : (N.frag bad (owner N bad (address s i))).raw.card ≤ 16 := h8.trans (by split <;> omega)
  exact bank_keys_inj hF hi'.1.1 hi'.1.2.2.2.1 hi'.1.2.2.1 h16 s
    (mem_filter.mpr ⟨mem_univ _,hi'.2⟩) (mem_filter.mpr ⟨mem_univ _,hj'.2⟩) hk'

theorem baseline_le {n : ℕ} {N : Net} {bad : Finset ℕ} (hF : Far (n := n) N bad)
    (hR : RawBank n N) (s : Bool) :
    ((privateSide (n := n) N bad s).filter fun i => (signature N bad (address s i)).2 =
      baseline (N.frag bad (owner N bad (address s i)))).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  by_contra hn
  let a := address s i
  let b := address s j
  obtain ⟨hi',hiK⟩ := mem_filter.mp hi
  obtain ⟨hj',hjK⟩ := mem_filter.mp hj
  have hpa := mem_privateSide.mp hi'
  have hpb := mem_privateSide.mp hj'
  let wa := owner N bad a
  let wb := owner N bad b
  have ha8 : (N.frag bad wa).raw.card ≤ 8 := (frag_small hR hF _ (owner_spec hpa).1.1).trans (by split <;> omega)
  have hb8 : (N.frag bad wb).raw.card ≤ 8 := (frag_small hR hF _ (owner_spec hpb).1.1).trans (by split <;> omega)
  let O := bank (n := n) (!s) (N.frag bad wa) ∪ bank (n := n) (!s) (N.frag bad wb)
  have hO : O.card ≤ 16 := (card_union_le _ _).trans (Nat.add_le_add ((bank_le _ _).trans ha8) ((bank_le _ _).trans hb8))
  have hdist := hF s i j hn (fun h => hpa.2.2 (Or.inr h)) (fun h => hpb.2.2 (Or.inr h))
  have hbd : dist (view N s i) (view N s j) ≤ O.card := by
    apply dist_le_of_agree
    intro z hz
    let c := address (!s) z
    have hcA : c ∉ (N.frag bad wa).raw := fun h => hz (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩))
    have hcB : c ∉ (N.frag bad wb).raw := fun h => hz (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩))
    apply N.transfer _ _
    · intro v _ _ hv
      exact twice_same (fun h => hpa.2.2 (h ▸ hv)) (fun h => hpb.2.2 (h ▸ hv))
    · intro w hw bit
      let F := N.frag bad w
      have hsingle (d : ℕ) (hk : key (N.frag bad (owner N bad d)) (once d) =
          baseline (N.frag bad (owner N bad d))) : F.f (once d) bit = F.f (fun _ => false) bit := by
        by_cases hd : d ∈ F.raw
        · have he := owner_eq hw hd
          rw [he] at hk
          exact key_apply hk bit
        · exact once_eq_base hd bit
      by_cases hc : c ∈ F.raw
      · have ha' : a ∉ F.raw := fun h => hcA (by
          change c ∈ (N.frag bad (owner N bad a)).raw
          rwa [owner_eq hw h])
        have hb' : b ∉ F.raw := fun h => hcB (by
          change c ∈ (N.frag bad (owner N bad b)).raw
          rwa [owner_eq hw h])
        change F.f (twice a c) bit = F.f (twice b c) bit
        rw [twice_comm a c, twice_comm b c, twice_eq_once ha', twice_eq_once hb']
      · rw [twice_eq_once hc, twice_eq_once hc, hsingle _ hiK, hsingle _ hjK]
  omega

theorem ordinary_lower {n : ℕ} {N : Net} {bad : Finset ℕ} (hF : Far (n := n) N bad) (hR : RawBank n N) :
    2*n ≤ (ordinary (n := n) N bad false).card + (ordinary (n := n) N bad true).card +
      N.excess + bad.card + 4 := by
  have hl := private_lower hF hR
  have hp (s : Bool) : (privateSide (n := n) N bad s).card ≤ (ordinary (n := n) N bad s).card + 1 := by
    have hh := card_filter_add_card_filter_not (s := privateSide (n := n) N bad s)
      (p := fun i => (signature N bad (address s i)).2 = baseline (N.frag bad (owner N bad (address s i))))
    have hb := baseline_le hF hR s
    change _ + (ordinary (n := n) N bad s).card = _ at hh
    omega
  have ha := hp false
  have hb := hp true
  omega

def allowedKeys (N : Net) (bad : Finset ℕ) (w : ℕ) : Finset (Bool × Bool) :=
  (keySpace (N.frag bad w)).erase (baseline (N.frag bad w))

theorem allowed_card (N : Net) (bad : Finset ℕ) (w : ℕ) :
    (allowedKeys N bad w).card = if (N.frag bad w).hole = none then 1 else 3 := by
  rw [allowedKeys, baseline, card_erase_of_mem (key_mem _ _), keySpace_card]
  split <;> rfl

theorem ordinary_allowed {n : ℕ} {N : Net} {bad : Finset ℕ} {s : Bool} {i : Fin n}
    (hi : i ∈ ordinary N bad s) : (signature N bad (address s i)).2 ∈
      allowedKeys N bad (owner N bad (address s i)) :=
  mem_erase.mpr ⟨(mem_filter.mp hi).2, key_mem _ _⟩

def tag (w : ℕ) : (Bool × Bool) ↪ ℕ × (Bool × Bool) :=
  ⟨fun k => (w,k), fun _ _ h => congrArg Prod.snd h⟩

theorem ordinary_union {n : ℕ} (N : Net) (bad : Finset ℕ) :
    (((ordinary (n := n) N bad false).image (fun i => signature N bad (address false i))) ∪
      ((ordinary (n := n) N bad true).image (fun i => signature N bad (address true i)))).card ≤
      (N.pure bad).card + 3 * (N.unary bad).card := by
  classical
  let A (s : Bool) := (ordinary (n := n) N bad s).image (fun i => signature N bad (address s i))
  let B := (N.roots bad).biUnion fun w => (allowedKeys N bad w).map (tag w)
  have hs (s) : A s ⊆ B := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    have hp := owner_spec (mem_privateSide.mp (mem_filter.mp hi).1)
    exact mem_biUnion.mpr ⟨_, N.mem_roots.mpr hp.1, mem_map.mpr ⟨_, ordinary_allowed hi, rfl⟩⟩
  have hb : B.card ≤ (N.pure bad).card + 3 * (N.unary bad).card := by
    apply card_biUnion_le.trans
    simp only [card_map, allowed_card]
    rw [Net.pure, Net.unary, card_eq_sum_ones, card_eq_sum_ones, sum_filter, sum_filter, mul_sum, ← sum_add_distrib]
    exact le_of_eq (sum_congr rfl fun w _ => by cases (N.frag bad w).hole <;> simp)
  exact (card_le_card (union_subset (hs false) (hs true))).trans hb

theorem matched_view {n : ℕ} {N : Net} {bad : Finset ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (h : ∀ i ∈ S, i ∈ ordinary N bad false ∧ π i ∈ ordinary N bad true ∧
      signature N bad (address false i) = signature N bad (address true (π i))) :
    ∀ i ∈ S, ∀ j ∈ S, owner N bad (address false i) ≠ owner N bad (address false j) →
      view N false i (π j) = view N false j (π i) := by
  intro i hi j hj hd
  let a := address false i
  let a' := address true (π i)
  let b := address false j
  let b' := address true (π j)
  let wa := owner N bad a
  let wb := owner N bad b
  obtain ⟨hi,hi',hA⟩ := h i hi
  obtain ⟨hj,hj',hB⟩ := h j hj
  have hwa : wa = owner N bad a' := congrArg Prod.fst hA
  have hwb : wb = owner N bad b' := congrArg Prod.fst hB
  have haK := congrArg Prod.snd hA
  have hbK := congrArg Prod.snd hB
  change key (N.frag bad wa) (once a) = key (N.frag bad (owner N bad a')) (once a') at haK
  change key (N.frag bad wb) (once b) = key (N.frag bad (owner N bad b')) (once b') at hbK
  rw [← hwa] at haK
  rw [← hwb] at hbK
  change N.run (twice a b') N.out = N.run (twice b a') N.out
  apply N.transfer _ _
  · intro z _ _ hz
    have hn (s : Bool) (i : Fin n) (hi : i ∈ ordinary N bad s) : z ≠ address s i := by
      intro hEq
      exact (mem_privateSide.mp (mem_filter.mp hi).1).2.2 (hEq ▸ hz)
    simp [twice, a, a', b, b', hn _ _ hi, hn _ _ hi', hn _ _ hj, hn _ _ hj']
  · intro w hw bit
    have apart {t : ℕ} (ht : owner N bad t ≠ w) : t ∉ (N.frag bad w).raw :=
      fun hn => ht (owner_eq hw hn)
    by_cases hwA : w = wa
    · subst w
      have h1 : b ∉ (N.frag bad wa).raw := apart (Ne.symm hd)
      have h2 : b' ∉ (N.frag bad wa).raw := apart (hwb ▸ (Ne.symm hd))
      rw [twice_eq_once h2, twice_comm b a', twice_eq_once h1, key_apply haK]
    by_cases hwB : w = wb
    · subst w
      have h1 : a ∉ (N.frag bad wb).raw := apart hd
      have h2 : a' ∉ (N.frag bad wb).raw := apart (hwa ▸ hd)
      rw [twice_comm a b', twice_eq_once h1, twice_eq_once h2, key_apply hbK]
    · have h1 : a ∉ (N.frag bad w).raw := apart (Ne.symm hwA)
      have h2 : b ∉ (N.frag bad w).raw := apart (Ne.symm hwB)
      have h3 : a' ∉ (N.frag bad w).raw := apart (hwa ▸ Ne.symm hwA)
      have h4 : b' ∉ (N.frag bad w).raw := apart (hwb ▸ Ne.symm hwB)
      rw [twice_eq_once h4, twice_eq_once h3, once_eq_base h1, once_eq_base h2]

theorem structural {n b : ℕ} (N : Net) (bad : Finset ℕ) (hF : Far (n := n) N bad)
    (hR : RawBank n N) (hbad : ∀ w ∈ bad, N.code w = .raw)
    (hb : (N.live.filter fun a => (N.code a).arity = 2).card ≤ b) :
    ∃ (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (piece : Fin n → ℕ),
      32*n ≤ 15*b+50+22*bad.card+S.card ∧
      (∀ t, (S.filter fun i => piece i = t).card ≤ 3) ∧
      (∀ i ∈ S, ∀ j ∈ S, piece i ≠ piece j → view N false i (π j) = view N false j (π i)) := by
  classical
  let A := ordinary (n := n) N bad false
  let B := ordinary (n := n) N bad true
  let a (i : Fin n) := signature N bad (address false i)
  let c (i : Fin n) := signature N bad (address true i)
  have ha := (private_sig_inj hF hR false).mono (filter_subset _ _ : A ⊆ _)
  have hc := (private_sig_inj hF hR true).mono (filter_subset _ _ : B ⊆ _)
  obtain ⟨π,S,hcount,hS,hmatch⟩ := match_keys A B a c ha hc
  refine ⟨π,S,fun i => owner N bad (address false i), ?_, ?_, ?_⟩
  · have hpart := ordinary_lower hF hR
    have hk := ordinary_union (n := n) N bad
    have hp := N.pure_bound bad hbad
    have hu := N.unary_bound bad
    have hd := N.ledger
    have hl := cover_raw hF (X := N.live.filter fun a => (N.code a).arity = 0)
      (fun w hw hr _ => mem_filter.mpr ⟨hw,by simp [hr,Op.arity]⟩) hR
    change 2*n ≤ A.card + B.card + N.excess + bad.card + 4 at hpart
    change (A.image a ∪ B.image c).card ≤ _ at hk
    omega
  · intro t
    let U := S.filter fun i => owner N bad (address false i) = t
    have hinj : Set.InjOn (fun i => (a i).2) U := by
      intro i hi j hj h
      have h₁ := mem_filter.mp hi
      have h₂ := mem_filter.mp hj
      apply ha (hS h₁.1) (hS h₂.1)
      exact Prod.ext (h₁.2.trans h₂.2.symm) h
    apply le_trans (card_le_card_of_injOn (fun i => (a i).2) (t := allowedKeys N bad t) ?_ hinj)
      (by rw [allowed_card]; split <;> omega)
    intro i hi
    change (a i).2 ∈ allowedKeys N bad t
    rw [← (mem_filter.mp hi).2]
    exact ordinary_allowed (hS (mem_filter.mp hi).1)
  · exact matched_view π S (fun i hi => ⟨hS hi,hmatch i hi⟩)

end

open Finset PEqualNP.CircuitLowerBounds

theorem view_left {n : ℕ} (C : Circuit) (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (i j : Fin n) :
    view (ofCircuit (n+n) C) false i j = C.eval (PEqualNP.Represents.oneEach i j) := by
  let x := PEqualNP.Represents.oneEach i j
  let X := twice (address false i) (address true j)
  have hlen : x.length = n + n := by simp [x, PEqualNP.Represents.oneEach]
  have hx (k : ℕ) (_ : k < x.length) : X (k+1) = x.getD k false := by
    change twice (address false i) (address true j) (k+1) = _
    rw [show x = PEqualNP.Represents.oneEach i j from rfl, oneEach_getD]
    simp [twice, address]
  change (ofCircuit (n+n) C).run X (ofCircuit (n+n) C).out = C.eval x
  simpa only [hlen] using ofCircuit_eval C x X hx hg

theorem view_right {n : ℕ} (C : Circuit) (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (i j : Fin n) :
    view (ofCircuit (n+n) C) true i j = C.eval (PEqualNP.Represents.oneEach j i) := by
  change (ofCircuit (n+n) C).run (twice (address true i) (address false j)) _ = _
  rw [twice_comm]
  exact view_left C hg j i

theorem marked_results {n : ℕ} (T : Fin n → Fin n → Bool) (C : Circuit) (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (H : Fin n → Fin n → Bool) (hH : ∀ i j, H i j = C.eval (PEqualNP.Represents.oneEach i j))
    (v : ℕ) (hv : 0 < v)
    (hr : ∀ i j, i ≠ j → 17 + 2*(v-1) ≤ dist (T i) (T j))
    (hc : ∀ i j, i ≠ j → 17 + 2*(v-1) ≤ dist (fun z => T z i) (fun z => T z j)) :
    ∃ bad : Finset ℕ, Far (n := n) (ofCircuit (n+n) C) bad ∧
      (∀ a ∈ bad, (ofCircuit (n+n) C).code a = .raw) ∧
      bad.card ≤ 2 * ((univ.filter fun z : Fin n × Fin n => H z.1 z.2 ≠ T z.1 z.2).card / v) := by
  let R := univ.filter fun i => v ≤ dist (H i) (T i)
  let L := univ.filter fun i => v ≤ dist (fun z => H z i) (fun z => T z i)
  let bad := R.image (address false) ∪ L.image (address true)
  have hR (i : Fin n) (hi : address false i ∉ bad) : dist (H i) (T i) < v := by
    apply Nat.lt_of_not_ge
    intro he
    exact hi (mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,he⟩)))
  have hL (i : Fin n) (hi : address true i ∉ bad) : dist (fun z => H z i) (fun z => T z i) < v := by
    apply Nat.lt_of_not_ge
    intro he
    exact hi (mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _,he⟩)))
  refine ⟨bad, ?_, ?_, ?_⟩
  · intro s i j hij hi hj
    cases s
    · have h₁ : view (ofCircuit (n+n) C) false i = H i := funext fun z => (view_left C hg i z).trans (hH i z).symm
      have h₂ : view (ofCircuit (n+n) C) false j = H j := funext fun z => (view_left C hg j z).trans (hH j z).symm
      rw [h₁,h₂]
      exact good_dist (H i) (H j) (T i) (T j) v hv (hR i hi) (hR j hj) (hr i j hij)
    · have h₁ : view (ofCircuit (n+n) C) true i = fun z => H z i := funext fun z => (view_right C hg i z).trans (hH z i).symm
      have h₂ : view (ofCircuit (n+n) C) true j = fun z => H z j := funext fun z => (view_right C hg j z).trans (hH z j).symm
      rw [h₁,h₂]
      exact good_dist (fun z => H z i) (fun z => H z j) (fun z => T z i) (fun z => T z j) v hv
        (hL i hi) (hL j hj) (hc i j hij)
  · intro w hw
    change w ∈ R.image (address false) ∪ L.image (address true) at hw
    rcases mem_union.mp hw with hw | hw <;> obtain ⟨i,_,rfl⟩ := mem_image.mp hw
    · exact codeAt_raw.mpr ⟨address_pos false i,address_le false i⟩
    · exact codeAt_raw.mpr ⟨address_pos true i,address_le true i⟩
  · let e := (univ.filter fun z : Fin n × Fin n => H z.1 z.2 ≠ T z.1 z.2).card
    have hr' : R.card ≤ e / v := (error_rows H T v).resolve_right (Nat.ne_of_gt hv)
    have hl' : L.card ≤ e / v := by
      have ht := (error_rows (fun i j => H j i) (fun i j => T j i) v).resolve_right (Nat.ne_of_gt hv)
      rwa [error_transpose H T] at ht
    exact (card_union_le _ _).trans (by
      have h1 := card_image_le (s := R) (f := address false)
      have h2 := card_image_le (s := L) (f := address true)
      change _ ≤ 2 * (e / v)
      omega)


theorem main : ∀ n : ℕ, 2 ≤ n →
  let I := Fin n
  ∀ (T : I → I → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) →
    let H := fun i j : I => C.eval (PEqualNP.Represents.oneEach i j)
    let e := (Finset.univ.filter (fun z : I × I => H z.1 z.2 ≠ T z.1 z.2)).card
    let b := C.gates.countP (fun gate => gate.inputs.length == 2)
    ∀ v : ℕ, 0 < v →
      (∀ i j : I, i ≠ j → 17+2*(v-1) ≤ (Finset.univ.filter (fun z : I => T i z ≠ T j z)).card) →
      (∀ i j : I, i ≠ j → 17+2*(v-1) ≤ (Finset.univ.filter (fun z : I => T z i ≠ T z j)).card) →
      ∃ (π : Equiv.Perm I) (S : Finset I) (piece : I → ℕ),
        32*n ≤ 15*b+50+44*(e/v)+S.card ∧
        (∀ t : ℕ, (S.filter (fun i => piece i = t)).card ≤ 3) ∧
        (∀ i ∈ S, ∀ j ∈ S, piece i ≠ piece j → H i (π j) = H j (π i)) ∧
        ∀ U : Finset I, U ⊆ S →
          ((U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))).card ≤
            U.card + ((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).card := by
  classical
  intro n _ I T C hg H e b v hv hrow hcol
  obtain ⟨bad, hfar, hbad, hcount⟩ := marked_results
    T C hg H (fun _ _ => rfl) v hv hrow hcol
  obtain ⟨π,S,p,hS,hcap,hsym⟩ := structural
    (ofCircuit (n+n) C) bad hfar
    (fun _ => codeAt_raw) hbad
    (ofCircuit_bin _ C hg)
  have hHsym : ∀ i ∈ S, ∀ j ∈ S, p i ≠ p j → H i (π j) = H j (π i) := by
    intro i hi j hj hp
    simpa only [view_left C hg] using hsym i hi j hj hp
  refine ⟨π,S,p,?_,hcap,hHsym,?_⟩
  · change 32 * n ≤ 15 * b + 50 + 44 * (e / v) + S.card
    change bad.card ≤ 2 * (e / v) at hcount
    change 32 * n ≤ 15 * b + 50 + 22 * bad.card + S.card at hS
    omega
  · exact conflict_bound T H π S p hcap hHsym

end Extract

namespace Hist
namespace Arithmetic25855
theorem finish (p n b d A B q a m e u : Nat)
    (labels : 32*n ≤ p+15*b+50+44*d+A+B)
    (conflicts : p^2 ≤ 4*(e+u)+(4+4*q+2*a*m)*p) :
    (32*n-(15*b+54+44*d+A+B+4*q+2*a*m))^2 ≤ 4*(e+u) := by
  let t := 4+4*q+2*a*m
  let s := 32*n-(15*b+54+44*d+A+B+4*q+2*a*m)
  change s^2 ≤ _
  by_cases hs : s = 0
  · simp [hs]
  have h : s+t ≤ p := by dsimp [s,t] at *; omega
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le h
  change p^2 ≤ 4*(e+u)+t*p at conflicts
  rw [hj] at conflicts
  nlinarith [Nat.zero_le (s*t), Nat.zero_le (s*j), Nat.zero_le (j*t), Nat.zero_le (j*j)]
end Arithmetic25855


open Finset Real
open scoped BigOperators
namespace Histogram25855

noncomputable def sign (b : Bool) : ℝ := if b then -1 else 1

private theorem sign_xor (b c : Bool) : sign (xor b c) = sign b * sign c := by
  cases b <;> cases c <;> norm_num [sign]

private theorem squareSign (b : Bool) : sign b * sign b = 1 := by
  cases b <;> norm_num [sign]

private theorem cube_mgf {k : Nat} (w : Fin k → ℝ) :
    (∑ z : Fin k → Bool, exp (∑ l, w l * sign (z l))) ≤
      2^k * exp ((∑ l, w l ^ 2)/2) := by
  calc
    _ = ∏ l, ∑ b : Bool, exp (w l * sign b) := by
      rw [Fintype.prod_sum]; simp only [Real.exp_sum]
    _ ≤ ∏ l, (2 * exp (w l ^ 2 / 2)) := by
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro l hl
      simp [sign]
      linarith [show (exp (w l) + exp (-w l)) / 2 ≤ exp (w l ^ 2 / 2) by
        simpa only [← Real.cosh_eq] using Real.cosh_le_exp_half_sq (w l)]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [← Real.exp_sum, Finset.sum_div]

private theorem word_inj {k} : Function.Injective
    (fun x : Fin (2 ^ k) => fun l : Fin k => x.val.testBit l.val) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact congrFun h ⟨i,hi⟩
  · have hki : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le hki),
        Nat.testBit_eq_false_of_lt (y.isLt.trans_le hki)]

private theorem subcube_mgf {ι : Type*} [DecidableEq ι] {k : Nat}
    (S : Finset ι) (row : ι → Fin (2^k)) (inj : Set.InjOn row S)
    (w : Fin k → ℝ) :
    (∑ i ∈ S, exp (∑ l, w l * sign ((row i).val.testBit l))) ≤
      2^k * exp ((∑ l, w l ^ 2)/2) := by
  classical
  let word (i : ι) (l : Fin k) := (row i).val.testBit l.val
  have hw : Set.InjOn word S := fun _ h _ h' e => inj h h' (word_inj e)
  calc
    _ = ∑ z ∈ S.image word, exp (∑ l, w l * sign (z l)) := (Finset.sum_image hw).symm
    _ ≤ ∑ z : Fin k → Bool, exp (∑ l, w l * sign (z l)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; positivity)
    _ ≤ _ := cube_mgf w


theorem energy {ι : Type*} [DecidableEq ι] {k : Nat}
    (S : Finset ι) (row : ι → Fin (2^k)) (inj : Set.InjOn row S)
    (flip : ι → Bool) (hS : S.Nonempty) :
    (∑ l : Fin k, (∑ i ∈ S, sign (flip i) * sign ((row i).val.testBit l)) ^ 2) ≤
      2 * (S.card : ℝ)^2 * Real.log (2 * 2^k / S.card) := by
  classical
  let m := (S.card : ℝ)
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Finset.card_pos.mpr hS
  let w (l : Fin k) := (∑ i ∈ S, sign (flip i) * sign ((row i).val.testBit l)) / m
  let E := ∑ l, w l ^ 2
  let U (i : ι) := ∑ l, w l * sign ((row i).val.testBit l)
  have hsum : (∑ i ∈ S, sign (flip i) * U i) = m * E := by
    simp only [U, Finset.mul_sum]
    rw [Finset.sum_comm]
    dsimp only [E]; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    calc
      _ = w l * ∑ i ∈ S, sign (flip i) * sign ((row i).val.testBit l) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ = m * w l ^ 2 := by dsimp [w]; field_simp
  have hj : exp E ≤ (1/m) * ∑ i ∈ S, exp (sign (flip i) * U i) := by
    have h := convexOn_exp.map_sum_le (t := S) (p := fun i => sign (flip i) * U i)
      (w := fun _ => (1/m : ℝ)) (by intros; positivity) (by simp; field_simp; rfl)
      (by intros; trivial)
    simp only [smul_eq_mul, ← Finset.mul_sum, hsum] at h
    convert h using 2; field_simp
  have hs : (∑ i ∈ S, exp (sign (flip i) * U i)) ≤
      2 * 2^k * exp (E/2) := by
    calc
      _ ≤ ∑ i ∈ S, (exp (U i) + exp (-U i)) := by
        apply Finset.sum_le_sum; intro i hi
        cases hv : flip i <;> simp [sign] <;> positivity
      _ = _ := Finset.sum_add_distrib
      _ ≤ _ := by
        have h₁ := subcube_mgf S row inj w
        have h₂ := subcube_mgf S row inj (fun l => -w l)
        simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at h₂
        change (∑ i ∈ S, exp (U i)) ≤ 2^k * exp (E/2) at h₁
        change (∑ i ∈ S, exp (-U i)) ≤ 2^k * exp (E/2) at h₂
        linarith
  have hexp : exp (E/2) ≤ 2 * 2^k / m := by
    apply (le_of_mul_le_mul_right (a := exp (E/2)) · (Real.exp_pos _))
    rw [← Real.exp_add, show E/2+E/2=E by ring]
    calc
      exp E ≤ _ := hj
      _ ≤ (1/m) * (2 * 2^k * exp (E/2)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have hlog := (Real.le_log_iff_exp_le (by positivity : 0 < (2:ℝ) * 2^k / m)).mpr hexp
  have hsc : (∑ l : Fin k, (∑ i ∈ S, sign (flip i) * sign ((row i).val.testBit l))^2) = m^2 * E := by
    dsimp only [E]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intros; dsimp only [w]; field_simp
  rw [hsc]; change m ^ 2 * E ≤ 2 * m ^ 2 * log (2 * 2 ^ k / m)
  nlinarith [mul_nonneg (sq_nonneg m) (sub_nonneg.mpr hlog)]

private theorem log_cap {m M : ℝ} {a : Nat} (hm : 0 < m) (h : m ≤ M) (ha : 3 ≤ a) :
    m * log (2 * 2^a * M / m) ≤ a * M := by
  have hM := hm.trans_le h
  have hlog : log 2 * (1 + a) ≤ a := by
    have h₁ := Real.log_two_lt_d9
    have h₂ : (3:ℝ) ≤ a := by exact_mod_cast ha
    nlinarith [mul_nonneg (by linarith : 0 ≤ 0.7 - log 2) (show 0 ≤ (a:ℝ) by positivity)]
  have hml := Real.log_le_sub_one_of_pos (div_pos hM hm)
  have hbound := mul_le_mul_of_nonneg_left hml hm.le
  have hcancel : m * (M/m-1) = M-m := by field_simp
  rw [hcancel] at hbound
  rw [show 2 * 2^a * M / m = (2*2^a) * (M/m) by ring, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have h₃ : 1 ≤ (a:ℝ) := by exact_mod_cast (by omega : 1 ≤ a)
  nlinarith [mul_le_mul_of_nonneg_left hlog hm.le, mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr h₃)]

private theorem gram {p k : Nat} (addr : Fin p → Fin k) (b : Fin p → Fin k → ℝ) :
    (∑ i, ∑ j, b i (addr j) * b j (addr i)) ≤
      ∑ t : Fin k, ∑ l : Fin k, (∑ i : Fin p with addr i = t, b i l)^2 := by
  classical
  let S (t : Fin k) := univ.filter (fun i => addr i = t)
  let V (t l : Fin k) := ∑ i ∈ S t, b i l
  have group (f : Fin p → ℝ) : ∑ i, f i = ∑ t, ∑ i ∈ S t, f i :=
    (Finset.sum_fiberwise univ addr f).symm
  have heq : (∑ i, ∑ j, b i (addr j) * b j (addr i)) = ∑ t, ∑ l, V t l * V l t := by
    rw [group]; apply sum_congr rfl; intro t _
    calc
      _ = ∑ i ∈ S t, ∑ l, ∑ j ∈ S l, b i l * b j t := by
        apply sum_congr rfl; intro i hi
        rw [group]; apply sum_congr rfl; intro l _
        apply sum_congr rfl; intro j hj
        rw [(mem_filter.mp hi).2, (mem_filter.mp hj).2]
      _ = _ := by
        rw [sum_comm]; apply sum_congr rfl; intro l _
        simp only [V, Finset.sum_mul, Finset.mul_sum]
        exact sum_comm
  rw [heq]
  change _ ≤ ∑ t, ∑ l, V t l ^ 2
  have hh : (∑ t, ∑ l, 2 * (V t l * V l t)) ≤ ∑ t, ∑ l, (V t l ^ 2 + V l t ^ 2) :=
    sum_le_sum fun t _ => sum_le_sum fun l _ => by nlinarith [sq_nonneg (V t l - V l t)]
  have sw : (∑ t, ∑ l, V l t ^ 2) = ∑ t, ∑ l, V t l ^ 2 := sum_comm
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, sw] at hh
  linarith

private theorem bias {p k a : Nat} (ha : 3 ≤ a) (row : Fin p → Fin (2^k))
    (hr : Function.Injective row) (flip : Fin p → Bool) (addr : Fin p → Fin k)
    (M : Nat) (hM : 2^a * M = 2^k)
    (cap : ∀ t, (univ.filter (fun i => addr i = t)).card ≤ M) :
    let b (i : Fin p) (l : Fin k) := sign (flip i) * sign ((row i).val.testBit l)
    (∑ i, ∑ j, b i (addr j) * b j (addr i)) ≤ 2 * a * M * p := by
  classical
  intro b
  let S (t : Fin k) := univ.filter (fun i => addr i = t)
  have factor : (2:ℝ)^a * M = 2^k := by exact_mod_cast hM
  have whole : (∑ t, ((S t).card : ℝ)) = p := by
    simpa [S] using (Finset.sum_fiberwise (univ : Finset (Fin p)) addr (fun _ => (1:ℝ)))
  refine (gram addr b).trans ?_
  calc
    _ ≤ ∑ t, (2 * a * M * ((S t).card : ℝ)) := by
      apply sum_le_sum; intro t _
      by_cases hs : (S t).Nonempty
      · have he := energy (S t) row hr.injOn flip hs
        have hm : (0:ℝ) < (S t).card := by exact_mod_cast Finset.card_pos.mpr hs
        have hc : ((S t).card : ℝ) ≤ M := by exact_mod_cast cap t
        have hl := log_cap hm hc ha
        rw [mul_assoc 2 ((2:ℝ)^a) (M:ℝ), factor] at hl
        exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hl hm.le])
      · have hz := Finset.not_nonempty_iff_eq_empty.mp hs
        change (∑ l, (∑ i ∈ S t, b i l)^2) ≤ _
        simp [hz]
    _ = _ := by rw [← Finset.mul_sum, whole]

private theorem residue_cap {p k a : Nat} (hk : 2^a ≤ k) (col : Fin p → Fin (2^k))
    (hc : Function.Injective col) (j : Fin k) :
    (univ.filter (fun i => (col i).val % 2^a = j.val)).card ≤ 2^k / 2^a := by
  let r := 2^a
  have hr : 0 < r := by positivity
  have hak : a ≤ k := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans hk
  have hd : r ∣ 2^k := pow_dvd_pow 2 hak
  have prod := Nat.div_mul_cancel hd
  have h := Finset.card_le_card_of_injOn (s := univ.filter (fun i => (col i).val % r = j.val))
    (t := range (2^k/r)) (fun i => (col i).val/r) (by
      intro i _; apply mem_range.mpr; apply (Nat.div_lt_iff_lt_mul hr).mpr
      rw [prod]; exact (col i).isLt) (by
      intro i hi l hl eq; apply hc; apply Fin.ext
      have h₁ := (mem_filter.mp hi).2; have h₂ := (mem_filter.mp hl).2
      have e₁ := Nat.div_add_mod (col i).val r; have e₂ := Nat.div_add_mod (col l).val r
      change (col i).val / r = (col l).val / r at eq
      rw [h₁] at e₁; rw [h₂, ← eq] at e₂; omega)
  simpa [r] using h

private theorem orientation_sum {p : Nat} (F : Fin p → Fin p → Bool) :
    (∑ i, ∑ j, sign (F i j) * sign (F j i)) =
      (p:ℝ)^2 - 4 * ((univ.filter (fun z : Fin p × Fin p =>
         z.1 < z.2 ∧ F z.1 z.2 ≠ F z.2 z.1)).card : ℝ) := by
  classical
  let d (i j : Fin p) : ℝ := if i < j ∧ F i j ≠ F j i then 1 else 0
  have cell (i j : Fin p) : sign (F i j) * sign (F j i) = 1 - 2 * d i j - 2 * d j i := by
    rcases lt_trichotomy i j with h|rfl|h
    · have hn := not_lt_of_ge h.le
      cases h₁ : F i j <;> cases h₂ : F j i <;> norm_num [sign,d,h,hn,h₁,h₂]
    · simp [d,squareSign]
    · have hn := not_lt_of_ge h.le
      cases h₁ : F i j <;> cases h₂ : F j i <;> norm_num [sign,d,h,hn,h₁,h₂]
  have sum_d : (∑ i, ∑ j, d i j) =
      ((univ.filter (fun z : Fin p × Fin p => z.1 < z.2 ∧ F z.1 z.2 ≠ F z.2 z.1)).card : ℝ) := by
    rw [← Fintype.sum_prod_type' (fun i j => d i j)]; simp [d]
  have sw : (∑ i, ∑ j, d j i) = ∑ i, ∑ j, d i j := sum_comm
  simp only [cell, Finset.sum_sub_distrib, ← Finset.mul_sum, sw, sum_d]
  simp; ring


theorem orientation {k a p : Nat} (ha : 0 < a) (hk : 2^a ≤ k)
    (row col : Fin p → Fin (2^k)) (hr : Function.Injective row) (hc : Function.Injective col)
    (f g : Fin (2^k) → Bool) :
    let F (i j : Fin p) := xor ((row i).val.testBit ((col j).val % 2^a))
      (xor (f (row i)) (g (col j)))
    p^2 ≤ 4 * (univ.filter (fun z : Fin p × Fin p => z.1 < z.2 ∧ F z.1 z.2 ≠ F z.2 z.1)).card
          + 2*a*(2^k / 2^a)*p := by
  classical
  intro F
  let M := 2^k / 2^a
  have hak : a ≤ k := Nat.lt_two_pow_self.le.trans hk
  have hM : 2^a * M = 2^k := Nat.mul_div_cancel' (pow_dvd_pow 2 hak)
  by_cases hbig : 3 ≤ a
  · let addr (i : Fin p) : Fin k := ⟨(col i).val % 2^a, (Nat.mod_lt _ (by positivity)).trans_le hk⟩
    let flip (i : Fin p) := xor (f (row i)) (g (col i))
    have cap (j : Fin k) : (univ.filter (fun i => addr i = j)).card ≤ M := by
      simpa [addr, Fin.ext_iff, M] using residue_cap hk col hc j
    have e := bias hbig row hr flip addr M hM cap
    let b (i : Fin p) (l : Fin k) := sign (flip i) * sign ((row i).val.testBit l)
    have hcell (i j : Fin p) : b i (addr j) * b j (addr i) = sign (F i j) * sign (F j i) := by
      simp only [b, flip, addr, F, sign_xor]; ring
    change (∑ i, ∑ j, b i (addr j) * b j (addr i)) ≤ _ at e
    simp_rw [hcell] at e
    rw [orientation_sum] at e
    exact_mod_cast (sub_le_iff_le_add'.mp e)
  · have hp : p ≤ 2^k := by simpa using Fintype.card_le_of_injective row hr
    have h : 2^a ≤ 2*a := by interval_cases a <;> decide
    have hp' : p ≤ 2*a*M := hp.trans (hM ▸ Nat.mul_le_mul_right M h)
    exact (show p^2 ≤ 2*a*M*p by nlinarith [Nat.mul_le_mul_right p hp']).trans (Nat.le_add_left _ _)

end Histogram25855

end Hist

namespace Border

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

lemma lt_two_pow_iff_testBit (m : ℕ) :
    ∀ x : ℕ, x < 2 ^ m ↔ ∀ i : ℕ, m ≤ i → x.testBit i = false := by
  induction m with
  | zero =>
    intro x
    constructor
    · intro hx i _
      have hx0 : x = 0 := by omega
      subst hx0; simp
    · intro h
      have hx0 : x = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i; simpa using h i (Nat.zero_le i)
      omega
  | succ m ih =>
    intro x
    constructor
    · intro hx i hi
      cases i with
      | zero => omega
      | succ j =>
        rw [Nat.testBit_succ]
        have hdiv : x / 2 < 2 ^ m := by rw [pow_succ] at hx; omega
        exact (ih (x / 2)).mp hdiv j (by omega)
    · intro h
      have hdiv : x / 2 < 2 ^ m := by
        apply (ih (x / 2)).mpr
        intro j hj
        have := h (j + 1) (by omega)
        rwa [Nat.testBit_succ] at this
      rw [pow_succ]; omega

lemma xor_lt_two_pow {x y m : ℕ} (hx : x < 2 ^ m) (hy : y < 2 ^ m) :
    x ^^^ y < 2 ^ m := by
  rw [lt_two_pow_iff_testBit] at hx hy ⊢
  intro i hi
  rw [Nat.testBit_xor, hx i hi, hy i hi]; rfl

lemma mod_two_pow_succ (m : ℕ) :
    ∀ v : ℕ, v % 2 ^ (m + 1) = v % 2 ^ m + if v.testBit m then 2 ^ m else 0 := by
  induction m with
  | zero =>
    intro v
    simp only [pow_zero, Nat.mod_one, zero_add, pow_one, Nat.testBit_zero, decide_eq_true_eq]
    split_ifs <;> omega
  | succ m ih =>
    intro v
    have h1 : v % 2 ^ (m + 2) = v % 2 + 2 * ((v / 2) % 2 ^ (m + 1)) := by
      have hpow : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
      rw [hpow]
      have hdm := Nat.div_add_mod (v % (2 * 2 ^ (m + 1))) 2
      rw [Nat.mod_mul_right_div_self,
          Nat.mod_mod_of_dvd v (Nat.dvd_mul_right 2 (2 ^ (m + 1)))] at hdm
      omega
    have h2 : v % 2 ^ (m + 1) = v % 2 + 2 * ((v / 2) % 2 ^ m) := by
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      rw [hpow]
      have hdm := Nat.div_add_mod (v % (2 * 2 ^ m)) 2
      rw [Nat.mod_mul_right_div_self,
          Nat.mod_mod_of_dvd v (Nat.dvd_mul_right 2 (2 ^ m))] at hdm
      omega
    rw [h1, h2, ih (v / 2), Nat.testBit_succ]
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    split_ifs <;> omega

lemma tableIndex_succ {k : ℕ} (u : Fin (k + 1) → Bool) :
    tableIndex u = (if u 0 = true then 1 else 0) + 2 * tableIndex (fun i : Fin k => u i.succ) := by
  unfold tableIndex
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.val_succ, pow_succ]
  split_ifs <;> ring

lemma tableIndex_lt {k : ℕ} (u : Fin k → Bool) : tableIndex u < 2 ^ k := by
  induction k with
  | zero => simp [tableIndex]
  | succ k ih =>
    rw [tableIndex_succ, pow_succ]
    have h := ih (fun i : Fin k => u i.succ)
    split_ifs <;> omega

lemma testBit_tableIndex {k : ℕ} :
    ∀ (u : Fin k → Bool) (j : ℕ),
      (tableIndex u).testBit j = if h : j < k then u ⟨j, h⟩ else false := by
  induction k with
  | zero => intro u j; simp [tableIndex]
  | succ k ih =>
    intro u j
    rw [tableIndex_succ]
    cases j with
    | zero =>
      simp only [Nat.testBit_zero, Nat.zero_lt_succ, dite_true]
      cases hu : u 0 <;> simp [hu]
    | succ j =>
      rw [Nat.testBit_succ]
      have hdiv : ((if u 0 = true then 1 else 0) + 2 * tableIndex (fun i : Fin k => u i.succ)) / 2 =
          tableIndex (fun i : Fin k => u i.succ) := by
        split_ifs <;> omega
      rw [hdiv, ih (fun i : Fin k => u i.succ) j]
      by_cases hj : j < k
      · have hj1 : j + 1 < k + 1 := by omega
        simp [hj, hj1, Fin.succ]
      · have hj1 : ¬ (j + 1 < k + 1) := by omega
        simp [hj, hj1]

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_nil (w : List Bool) : wf [] w = w := rfl

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wf_append (gs1 gs2 : List Gate) (w : List Bool) :
    wf (gs1 ++ gs2) w = wf gs2 (wf gs1 w) := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih => intro w; rw [wf_cons, ih]; simp; omega

lemma getD_snoc_lt (L : List Bool) (a : Bool) (i : ℕ) (h : i < L.length) :
    (L ++ [a]).getD i false = L.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma wf_getD_lt (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [wf_cons, ih]
    · exact getD_snoc_lt _ _ _ hi
    · simp; omega

def Mono2List (gs : List Gate) : Prop :=
  ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma Mono2List.to_monotone2 {gs : List Gate} (h : Mono2List gs) (out : ℕ) :
    Monotone2 ⟨gs, out⟩ := by
  intro g hg
  have ⟨hop, hlen⟩ := h g hg
  exact ⟨by rcases hop with h1 | h1 <;> simp [h1], hlen⟩

lemma Mono2List.nil : Mono2List [] := fun _ hg => by simp at hg

lemma Mono2List.append {gs1 gs2 : List Gate} (h1 : Mono2List gs1) (h2 : Mono2List gs2) :
    Mono2List (gs1 ++ gs2) := by
  intro g hg
  rcases List.mem_append.mp hg with hg1 | hg2
  · exact h1 g hg1
  · exact h2 g hg2

def gAnd (u v : ℕ) : Gate := ⟨GateOp.and, [u, v]⟩
def gOr (u v : ℕ) : Gate := ⟨GateOp.or, [u, v]⟩

lemma mono2_gAnd (u v : ℕ) : Mono2List [gAnd u v] := by
  intro g hg; simp at hg; subst hg; simp [gAnd]

lemma mono2_gOr (u v : ℕ) : Mono2List [gOr u v] := by
  intro g hg; simp at hg; subst hg; simp [gOr]

lemma wf_gAnd_eq (u v : ℕ) (w : List Bool) :
    (wf [gAnd u v] w).getD w.length false = (w.getD u false && w.getD v false) := by
  simp [wf, gAnd, GateOp.eval]

lemma wf_gOr_eq (u v : ℕ) (w : List Bool) :
    (wf [gOr u v] w).getD w.length false = (w.getD u false || w.getD v false) := by
  simp [wf, gOr, GateOp.eval]

lemma buildMux (base s ns t f : ℕ) (hs : s < base) (hns : ns < base) (ht : t < base) (hf : f < base) :
    ∃ (gs : List Gate) (out : ℕ),
      Mono2List gs ∧ gs.length = 3 ∧ out < base + 3 ∧
      ∀ (w : List Bool), w.length = base → w.getD ns false = !(w.getD s false) →
        (wf gs w).getD out false = if w.getD s false then w.getD t false else w.getD f false := by
  let gs : List Gate := [gAnd s t, gAnd ns f, gOr base (base + 1)]
  refine ⟨gs, base + 2, ?_, rfl, by omega, ?_⟩
  · intro g hg
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> simp [gAnd, gOr]
  · intro w hw hneg
    have hsplit : gs = ([gAnd s t] ++ [gAnd ns f]) ++ [gOr base (base + 1)] := rfl
    rw [hsplit, wf_append, wf_append]
    let w1 := wf [gAnd s t] w
    let w2 := wf [gAnd ns f] w1
    have hw1 : w1.length = base + 1 := by simp [w1, wf_len, hw]
    have hw2 : w2.length = base + 2 := by simp [w2, wf_len, hw1]
    have hv1 : w1.getD base false = (w.getD s false && w.getD t false) := by
      rw [← hw, wf_gAnd_eq]
    have hv2 : w2.getD (base + 1) false = (w.getD ns false && w.getD f false) := by
      rw [← hw1, wf_gAnd_eq, wf_getD_lt [gAnd s t] w ns (by omega), wf_getD_lt [gAnd s t] w f (by omega)]
    rw [← hw2, wf_gOr_eq, wf_getD_lt [gAnd ns f] w1 base (by omega), hv1, hv2, hneg]
    cases w.getD s false <;> cases w.getD t false <;> cases w.getD f false <;> rfl

lemma buildDualXor (base p np q nq : ℕ)
    (hp : p < base) (hnp : np < base) (hq : q < base) (hnq : nq < base) :
    ∃ (gs : List Gate) (outP outN : ℕ),
      Mono2List gs ∧ gs.length = 6 ∧ outP < base + 6 ∧ outN < base + 6 ∧
      ∀ (w : List Bool), w.length = base →
        w.getD np false = !(w.getD p false) → w.getD nq false = !(w.getD q false) →
        (wf gs w).getD outP false = xor (w.getD p false) (w.getD q false) ∧
        (wf gs w).getD outN false = !(xor (w.getD p false) (w.getD q false)) := by
  let gs : List Gate :=
    [gAnd p nq, gAnd np q, gOr base (base + 1),
     gAnd p q, gAnd np nq, gOr (base + 3) (base + 4)]
  refine ⟨gs, base + 2, base + 5, ?_, rfl, by omega, by omega, ?_⟩
  · intro g hg
    simp only [gs, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gAnd, gOr]
  · intro w hw hnpw hnqw
    let w1 := wf [gAnd p nq] w
    let w2 := wf [gAnd np q] w1
    let w3 := wf [gOr base (base + 1)] w2
    let w4 := wf [gAnd p q] w3
    let w5 := wf [gAnd np nq] w4
    let w6 := wf [gOr (base + 3) (base + 4)] w5
    have hw1 : w1.length = base + 1 := by simp [w1, wf_len, hw]
    have hw2 : w2.length = base + 2 := by simp [w2, wf_len, hw1]
    have hw3 : w3.length = base + 3 := by simp [w3, wf_len, hw2]
    have hw4 : w4.length = base + 4 := by simp [w4, wf_len, hw3]
    have hw5 : w5.length = base + 5 := by simp [w5, wf_len, hw4]
    have hwf : wf gs w = w6 := by
      have hsp : gs = (((([gAnd p nq] ++ [gAnd np q]) ++ [gOr base (base + 1)]) ++
          [gAnd p q]) ++ [gAnd np nq]) ++ [gOr (base + 3) (base + 4)] := rfl
      simp only [hsp, wf_append, w1, w2, w3, w4, w5, w6]
    have hv1 : w1.getD base false = (w.getD p false && w.getD nq false) := by
      rw [← hw, wf_gAnd_eq]
    have hv2 : w2.getD (base + 1) false = (w.getD np false && w.getD q false) := by
      rw [← hw1, wf_gAnd_eq, wf_getD_lt [gAnd p nq] w np (by omega), wf_getD_lt [gAnd p nq] w q (by omega)]
    have hv3 : w3.getD (base + 2) false =
        ((w.getD p false && w.getD nq false) || (w.getD np false && w.getD q false)) := by
      rw [← hw2, wf_gOr_eq, wf_getD_lt [gAnd np q] w1 base (by omega), hv1, hv2]
    have hw3_eq : w3 = wf ([gAnd p nq] ++ [gAnd np q] ++ [gOr base (base + 1)]) w := by
      simp only [w3, w2, w1, wf_append]
    have hv4 : w4.getD (base + 3) false = (w.getD p false && w.getD q false) := by
      rw [← hw3, wf_gAnd_eq, hw3_eq, wf_getD_lt _ w p (by omega), wf_getD_lt _ w q (by omega)]
    have hw4_eq : w4 = wf (([gAnd p nq] ++ [gAnd np q] ++ [gOr base (base + 1)]) ++ [gAnd p q]) w := by
      simp only [w4, w3, w2, w1, wf_append]
    have hv5 : w5.getD (base + 4) false = (w.getD np false && w.getD nq false) := by
      rw [← hw4, wf_gAnd_eq, hw4_eq, wf_getD_lt _ w np (by omega), wf_getD_lt _ w nq (by omega)]
    have hv6 : w6.getD (base + 5) false =
        ((w.getD p false && w.getD q false) || (w.getD np false && w.getD nq false)) := by
      rw [← hw5, wf_gOr_eq, wf_getD_lt [gAnd np nq] w4 (base + 3) (by omega), hv4, hv5]
    have hw6_from3 : w6 = wf ([gAnd p q] ++ [gAnd np nq] ++ [gOr (base + 3) (base + 4)]) w3 := by
      simp only [w6, w5, w4, wf_append]
    rw [hwf, hv6, hw6_from3, wf_getD_lt _ w3 (base + 2) (by omega), hv3, hnpw, hnqw]
    cases w.getD p false <;> cases w.getD q false <;> simp

lemma buildMuxTree (a : ℕ) :
    ∀ (base : ℕ) (selP selN leaf : ℕ → ℕ),
      (∀ j < a, selP j < base ∧ selN j < base) →
      (∀ t < 2 ^ a, leaf t < base) →
      ∃ (gs : List Gate) (out : ℕ),
        Mono2List gs ∧ gs.length = 3 * (2 ^ a - 1) ∧ out < base + gs.length ∧
        ∀ (w : List Bool) (v : ℕ),
          w.length = base →
          (∀ j < a, w.getD (selP j) false = v.testBit j ∧ w.getD (selN j) false = !(v.testBit j)) →
          (wf gs w).getD out false = w.getD (leaf (v % 2 ^ a)) false := by
  induction a with
  | zero =>
    intro base selP selN leaf _ hleaf
    refine ⟨[], leaf 0, Mono2List.nil, by simp, by simpa using hleaf 0 (by simp), ?_⟩
    intro w v _ _
    simp [wf, pow_zero, Nat.mod_one]
  | succ a ih =>
    intro base selP selN leaf hsel hleaf
    have hpow : 2 ^ (a + 1) = 2 ^ a + 2 ^ a := by ring
    obtain ⟨gs1, out1, hmono1, hlen1, hout1, heval1⟩ :=
      ih base selP selN leaf
        (fun j hj => hsel j (by omega))
        (fun t ht => hleaf t (by omega))
    let base1 := base + gs1.length
    obtain ⟨gs2, out2, hmono2, hlen2, hout2, heval2⟩ :=
      ih base1 selP selN (fun t => leaf (2 ^ a + t))
        (fun j hj => by have := hsel j (by omega); omega)
        (fun t ht => by have := hleaf (2 ^ a + t) (by omega); omega)
    let base2 := base1 + gs2.length
    have hsela := hsel a (Nat.lt_succ_self a)
    obtain ⟨gs3, out3, hmono3, hlen3, hout3, heval3⟩ :=
      buildMux base2 (selP a) (selN a) out2 out1
        (by omega) (by omega) (by omega) (by omega)
    have hpos : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    refine ⟨gs1 ++ gs2 ++ gs3, out3,
      (hmono1.append hmono2).append hmono3,
      by simp only [List.length_append, hlen1, hlen2, hlen3]; omega,
      by simp only [List.length_append, hlen1, hlen2, hlen3, base1, base2] at hout3 ⊢; omega, ?_⟩
    intro w v hw hvb
    rw [wf_append, wf_append]
    let w1 := wf gs1 w
    let w2 := wf gs2 w1
    have hw1 : w1.length = base1 := by rw [wf_len, hw]
    have hw2 : w2.length = base2 := by rw [wf_len, hw1]
    have hw2_eq : w2 = wf (gs1 ++ gs2) w := (wf_append gs1 gs2 w).symm
    have hread : ∀ u < base, w2.getD u false = w.getD u false := by
      intro u hu; rw [hw2_eq]; exact wf_getD_lt (gs1 ++ gs2) w u (by omega)
    have hneg : w2.getD (selN a) false = !(w2.getD (selP a) false) := by
      rw [hread _ hsela.1, hread _ hsela.2, (hvb a (Nat.lt_succ_self a)).1, (hvb a (Nat.lt_succ_self a)).2]
    rw [heval3 w2 hw2 hneg, hread _ hsela.1, (hvb a (Nat.lt_succ_self a)).1]
    have h1 : w2.getD out1 false = w.getD (leaf (v % 2 ^ a)) false := by
      rw [wf_getD_lt gs2 w1 out1 (by omega)]
      exact heval1 w v hw (fun j hj => hvb j (by omega))
    have h2 : w2.getD out2 false = w.getD (leaf (2 ^ a + v % 2 ^ a)) false := by
      have hvb1 : ∀ j < a, w1.getD (selP j) false = v.testBit j ∧ w1.getD (selN j) false = !(v.testBit j) := by
        intro j hj
        have hltj := hsel j (by omega)
        rw [wf_getD_lt gs1 w (selP j) (by omega), wf_getD_lt gs1 w (selN j) (by omega)]
        exact hvb j (by omega)
      rw [heval2 w1 v hw1 hvb1, wf_getD_lt gs1 w (leaf (2 ^ a + v % 2 ^ a))
        (by have := hleaf (2 ^ a + v % 2 ^ a) (by have := Nat.mod_lt v (Nat.two_pow_pos a); omega); omega)]
    rw [h1, h2, mod_two_pow_succ a v]
    cases v.testBit a <;> simp [Nat.add_comm]

lemma list_all_congr {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp), ih (fun a ha => h a (by simp [ha]))]

lemma list_any_congr {α : Type*} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [h x (by simp), ih (fun a ha => h a (by simp [ha]))]

lemma buildFoldAnd (ws : List ℕ) :
    ∀ (base accW : ℕ), accW < base → (∀ u ∈ ws, u < base) →
    ∃ (gs : List Gate) (out : ℕ),
      Mono2List gs ∧ gs.length = ws.length ∧ out < base + gs.length ∧
      ∀ (w : List Bool), w.length = base →
        (wf gs w).getD out false = (w.getD accW false && ws.all (fun u => w.getD u false)) := by
  induction ws with
  | nil =>
    intro base accW hacc _
    refine ⟨[], accW, Mono2List.nil, rfl, by simpa using hacc, fun w _ => by simp [wf]⟩
  | cons u us ih =>
    intro base accW hacc hws
    have hu : u < base := hws u (by simp)
    obtain ⟨gs, out, hmono, hlen, hout, heval⟩ :=
      ih (base + 1) base (by omega) (fun v hv => by have := hws v (by simp [hv]); omega)
    refine ⟨[gAnd accW u] ++ gs, out, (mono2_gAnd accW u).append hmono, by simp [hlen],
      by simp [hlen]; omega, ?_⟩
    intro w hw
    rw [wf_append]
    have hlen1 : (wf [gAnd accW u] w).length = base + 1 := by simp [wf_len, hw]
    rw [heval _ hlen1, ← hw, wf_gAnd_eq]
    have hall : us.all (fun v => (wf [gAnd accW u] w).getD v false) =
        us.all (fun v => w.getD v false) := by
      apply list_all_congr; intro v hv
      have hv_lt : v < base := hws v (by simp [hv])
      rw [wf_getD_lt [gAnd accW u] w v (by omega)]
    rw [hall, List.all_cons, Bool.and_assoc]

lemma buildFoldOr (ws : List ℕ) :
    ∀ (base accW : ℕ), accW < base → (∀ u ∈ ws, u < base) →
    ∃ (gs : List Gate) (out : ℕ),
      Mono2List gs ∧ gs.length = ws.length ∧ out < base + gs.length ∧
      ∀ (w : List Bool), w.length = base →
        (wf gs w).getD out false = (w.getD accW false || ws.any (fun u => w.getD u false)) := by
  induction ws with
  | nil =>
    intro base accW hacc _
    refine ⟨[], accW, Mono2List.nil, rfl, by simpa using hacc, fun w _ => by simp [wf]⟩
  | cons u us ih =>
    intro base accW hacc hws
    have hu : u < base := hws u (by simp)
    obtain ⟨gs, out, hmono, hlen, hout, heval⟩ :=
      ih (base + 1) base (by omega) (fun v hv => by have := hws v (by simp [hv]); omega)
    refine ⟨[gOr accW u] ++ gs, out, (mono2_gOr accW u).append hmono, by simp [hlen],
      by simp [hlen]; omega, ?_⟩
    intro w hw
    rw [wf_append]
    have hlen1 : (wf [gOr accW u] w).length = base + 1 := by simp [wf_len, hw]
    rw [heval _ hlen1, ← hw, wf_gOr_eq]
    have hany : us.any (fun v => (wf [gOr accW u] w).getD v false) =
        us.any (fun v => w.getD v false) := by
      apply list_any_congr; intro v hv
      have hv_lt : v < base := hws v (by simp [hv])
      rw [wf_getD_lt [gOr accW u] w v (by omega)]
    rw [hany, List.any_cons, Bool.or_assoc]

lemma buildDualAnd2 (n base : ℕ) (ap an bp bn : ℕ → ℕ)
    (hbd : ∀ i < n, ap i < base ∧ an i < base ∧ bp i < base ∧ bn i < base) :
    ∃ (gs : List Gate) (ps : List (ℕ × ℕ)),
      Mono2List gs ∧ gs.length = 2 * n ∧ ps.length = n ∧
      (∀ t ∈ ps, t.1 < base + gs.length ∧ t.2 < base + gs.length) ∧
      ∀ (w : List Bool), w.length = base →
        (∀ i < n, w.getD (an i) false = !(w.getD (ap i) false) ∧
                  w.getD (bn i) false = !(w.getD (bp i) false)) →
        (∀ t ∈ ps, (wf gs w).getD t.2 false = !((wf gs w).getD t.1 false)) ∧
        ps.countP (fun t => (wf gs w).getD t.1 false) =
          (List.range n).countP (fun i => w.getD (ap i) false && w.getD (bp i) false) := by
  induction n with
  | zero =>
    refine ⟨[], [], Mono2List.nil, rfl, rfl, by simp, fun w _ _ => by simp⟩
  | succ n ih =>
    obtain ⟨gs, ps, hmono, hlen, hplen, hplt, heval⟩ := ih (fun i hi => hbd i (by omega))
    let b := base + 2 * n
    let step : List Gate := [gAnd (ap n) (bp n), gOr (an n) (bn n)]
    have hsm : Mono2List step := by
      intro g hg; simp only [step, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp [gAnd, gOr]
    refine ⟨gs ++ step, ps ++ [(b, b + 1)], hmono.append hsm,
      by simp [hlen, step]; omega, by simp [hplen], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · have := hplt t ht; simp [hlen, step] at this ⊢; omega
      · simp [hlen, step, b]; omega
    · intro w hw hneg
      rw [wf_append]
      let w0 := wf gs w
      have hw0 : w0.length = b := by rw [wf_len, hw, hlen]
      have hread : ∀ u < base, w0.getD u false = w.getD u false :=
        fun u hu => wf_getD_lt gs w u (by omega)
      have hstep_sp : step = [gAnd (ap n) (bp n)] ++ [gOr (an n) (bn n)] := rfl
      let w1 := wf [gAnd (ap n) (bp n)] w0
      have hw1 : w1.length = b + 1 := by simp [w1, wf_len, hw0]
      have hbdn := hbd n (Nat.lt_succ_self n)
      have hnegn := hneg n (Nat.lt_succ_self n)
      have hv_p : (wf step w0).getD b false = (w.getD (ap n) false && w.getD (bp n) false) := by
        rw [hstep_sp, wf_append, wf_getD_lt [gOr (an n) (bn n)] w1 b (by omega),
            ← hw0, wf_gAnd_eq, hread _ hbdn.1, hread _ hbdn.2.2.1]
      have hv_n : (wf step w0).getD (b + 1) false = !((wf step w0).getD b false) := by
        rw [hv_p, hstep_sp, wf_append, ← hw1, wf_gOr_eq,
            wf_getD_lt [gAnd (ap n) (bp n)] w0 (an n) (by omega),
            wf_getD_lt [gAnd (ap n) (bp n)] w0 (bn n) (by omega),
            hread _ hbdn.2.1, hread _ hbdn.2.2.2, hnegn.1, hnegn.2]
        cases w.getD (ap n) false <;> cases w.getD (bp n) false <;> rfl
      have ⟨hih_neg, hih_cnt⟩ := heval w hw (fun i hi => hneg i (by omega))
      constructor
      · intro t ht
        simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · have hlt := hplt t ht
          rw [wf_getD_lt step w0 t.1 (by omega), wf_getD_lt step w0 t.2 (by omega)]
          exact hih_neg t ht
        · exact hv_n
      · rw [List.countP_append, List.countP_singleton, List.range_succ, List.countP_append,
            List.countP_singleton, hv_p]
        have hsame : ps.countP (fun t => (wf step w0).getD t.1 false) =
            ps.countP (fun t => w0.getD t.1 false) := by
          rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
          congr 1; apply List.filter_congr
          intro t ht; have hlt := hplt t ht
          rw [wf_getD_lt step w0 t.1 (by omega)]
        rw [hsame, hih_cnt]

lemma buildDualAnd3 (n base : ℕ) (ap an bp bn cp cn : ℕ → ℕ)
    (hbd : ∀ i < n, ap i < base ∧ an i < base ∧ bp i < base ∧ bn i < base ∧ cp i < base ∧ cn i < base) :
    ∃ (gs : List Gate) (ps : List (ℕ × ℕ)),
      Mono2List gs ∧ gs.length = 4 * n ∧ ps.length = n ∧
      (∀ t ∈ ps, t.1 < base + gs.length ∧ t.2 < base + gs.length) ∧
      ∀ (w : List Bool), w.length = base →
        (∀ i < n, w.getD (an i) false = !(w.getD (ap i) false) ∧
                  w.getD (bn i) false = !(w.getD (bp i) false) ∧
                  w.getD (cn i) false = !(w.getD (cp i) false)) →
        (∀ t ∈ ps, (wf gs w).getD t.2 false = !((wf gs w).getD t.1 false)) ∧
        ps.countP (fun t => (wf gs w).getD t.1 false) =
          (List.range n).countP (fun i => w.getD (ap i) false && w.getD (bp i) false && w.getD (cp i) false) := by
  induction n with
  | zero =>
    refine ⟨[], [], Mono2List.nil, rfl, rfl, by simp, fun w _ _ => by simp⟩
  | succ n ih =>
    obtain ⟨gs, ps, hmono, hlen, hplen, hplt, heval⟩ := ih (fun i hi => hbd i (by omega))
    let b := base + 4 * n
    let step : List Gate := [gAnd (ap n) (bp n), gAnd b (cp n), gOr (an n) (bn n), gOr (b + 2) (cn n)]
    have hsm : Mono2List step := by
      intro g hg; simp only [step, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl <;> simp [gAnd, gOr]
    refine ⟨gs ++ step, ps ++ [(b + 1, b + 3)], hmono.append hsm,
      by simp [hlen, step]; omega, by simp [hplen], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_append, List.mem_singleton] at ht
      rcases ht with ht | rfl
      · have := hplt t ht; simp [hlen, step] at this ⊢; omega
      · simp [hlen, step, b]; omega
    · intro w hw hneg
      rw [wf_append]
      let w0 := wf gs w
      have hw0 : w0.length = b := by rw [wf_len, hw, hlen]
      have hread : ∀ u < base, w0.getD u false = w.getD u false :=
        fun u hu => wf_getD_lt gs w u (by omega)
      let w1 := wf [gAnd (ap n) (bp n)] w0
      let w2 := wf [gAnd b (cp n)] w1
      let w3 := wf [gOr (an n) (bn n)] w2
      let w4 := wf [gOr (b + 2) (cn n)] w3
      have hw1 : w1.length = b + 1 := by simp [w1, wf_len, hw0]
      have hw2 : w2.length = b + 2 := by simp [w2, wf_len, hw1]
      have hw3 : w3.length = b + 3 := by simp [w3, wf_len, hw2]
      have hwf : wf step w0 = w4 := by
        have hsp : step = (([gAnd (ap n) (bp n)] ++ [gAnd b (cp n)]) ++ [gOr (an n) (bn n)]) ++ [gOr (b + 2) (cn n)] := rfl
        simp only [hsp, wf_append, w1, w2, w3, w4]
      have hbdn := hbd n (Nat.lt_succ_self n)
      have hnegn := hneg n (Nat.lt_succ_self n)
      have hv1 : w1.getD b false = (w.getD (ap n) false && w.getD (bp n) false) := by
        rw [← hw0, wf_gAnd_eq, hread _ hbdn.1, hread _ hbdn.2.2.1]
      have hv2 : w2.getD (b + 1) false = (w.getD (ap n) false && w.getD (bp n) false && w.getD (cp n) false) := by
        rw [← hw1, wf_gAnd_eq, hv1, wf_getD_lt [gAnd (ap n) (bp n)] w0 (cp n) (by omega), hread _ hbdn.2.2.2.2.1]
      have hw2_eq : w2 = wf ([gAnd (ap n) (bp n)] ++ [gAnd b (cp n)]) w0 := by simp only [w2, w1, wf_append]
      have hv3 : w3.getD (b + 2) false = (w.getD (an n) false || w.getD (bn n) false) := by
        rw [← hw2, wf_gOr_eq, hw2_eq, wf_getD_lt _ w0 (an n) (by omega), wf_getD_lt _ w0 (bn n) (by omega),
            hread _ hbdn.2.1, hread _ hbdn.2.2.2.1]
      have hw3_eq : w3 = wf (([gAnd (ap n) (bp n)] ++ [gAnd b (cp n)]) ++ [gOr (an n) (bn n)]) w0 := by
        simp only [w3, w2, w1, wf_append]
      have hv4 : w4.getD (b + 3) false = ((w.getD (an n) false || w.getD (bn n) false) || w.getD (cn n) false) := by
        rw [← hw3, wf_gOr_eq, hv3, hw3_eq, wf_getD_lt _ w0 (cn n) (by omega), hread _ hbdn.2.2.2.2.2]
      have hw4_from2 : w4 = wf ([gOr (an n) (bn n)] ++ [gOr (b + 2) (cn n)]) w2 := by
        simp only [w4, w3, wf_append]
      have hv_p : (wf step w0).getD (b + 1) false =
          (w.getD (ap n) false && w.getD (bp n) false && w.getD (cp n) false) := by
        rw [hwf, hw4_from2, wf_getD_lt _ w2 (b + 1) (by omega), hv2]
      have hv_n : (wf step w0).getD (b + 3) false = !((wf step w0).getD (b + 1) false) := by
        rw [hwf, hv4, ← hwf, hv_p, hnegn.1, hnegn.2.1, hnegn.2.2]
        cases w.getD (ap n) false <;> cases w.getD (bp n) false <;> cases w.getD (cp n) false <;> rfl
      have ⟨hih_neg, hih_cnt⟩ := heval w hw (fun i hi => hneg i (by omega))
      constructor
      · intro t ht
        simp only [List.mem_append, List.mem_singleton] at ht
        rcases ht with ht | rfl
        · have hlt := hplt t ht
          rw [wf_getD_lt step w0 t.1 (by omega), wf_getD_lt step w0 t.2 (by omega)]
          exact hih_neg t ht
        · exact hv_n
      · rw [List.countP_append, List.countP_singleton, List.range_succ, List.countP_append,
            List.countP_singleton, hv_p]
        have hsame : ps.countP (fun t => (wf step w0).getD t.1 false) =
            ps.countP (fun t => w0.getD t.1 false) := by
          rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
          congr 1; apply List.filter_congr
          intro t ht; have hlt := hplt t ht
          rw [wf_getD_lt step w0 t.1 (by omega)]
        rw [hsame, hih_cnt]

lemma xor_mod2_add (b : Bool) (n : ℕ) :
    xor b (n % 2 == 1) = ((n + if b then 1 else 0) % 2 == 1) := by
  cases b <;> rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, Nat.add_mod]

lemma xor_assoc_bool (a b c : Bool) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

lemma buildParity (ps : List (ℕ × ℕ)) :
    ∀ (base accP accN : ℕ), accP < base → accN < base →
      (∀ t ∈ ps, t.1 < base ∧ t.2 < base) →
      ∃ (gs : List Gate) (outP outN : ℕ),
        Mono2List gs ∧ gs.length = 6 * ps.length ∧
        outP < base + gs.length ∧ outN < base + gs.length ∧
        ∀ (w : List Bool), w.length = base →
          w.getD accN false = !(w.getD accP false) →
          (∀ t ∈ ps, w.getD t.2 false = !(w.getD t.1 false)) →
          (wf gs w).getD outP false =
            xor (w.getD accP false) (ps.countP (fun t => w.getD t.1 false) % 2 == 1) ∧
          (wf gs w).getD outN false = !((wf gs w).getD outP false) := by
  induction ps with
  | nil =>
    intro base accP accN hp hn _
    refine ⟨[], accP, accN, Mono2List.nil, rfl, by simpa using hp, by simpa using hn, ?_⟩
    intro w _ hneg _
    exact ⟨by simp [wf], by simpa [wf] using hneg⟩
  | cons t ts ih =>
    intro base accP accN hp hn hps
    have ht := hps t (by simp)
    obtain ⟨gs1, p1, n1, hmono1, hlen1, hp1, hn1, heval1⟩ :=
      buildDualXor base accP accN t.1 t.2 hp hn ht.1 ht.2
    obtain ⟨gs2, outP, outN, hmono2, hlen2, houtP, houtN, heval2⟩ :=
      ih (base + 6) p1 n1 hp1 hn1 (fun u hu => by have := hps u (by simp [hu]); omega)
    refine ⟨gs1 ++ gs2, outP, outN, hmono1.append hmono2,
      by simp [hlen1, hlen2]; omega,
      by simp [hlen1, hlen2] at houtP ⊢; omega,
      by simp [hlen1, hlen2] at houtN ⊢; omega, ?_⟩
    intro w hw hneg hts
    rw [wf_append]
    let w1 := wf gs1 w
    have hw1 : w1.length = base + 6 := by rw [wf_len, hw, hlen1]
    have h1 := heval1 w hw hneg (hts t (by simp))
    have hts1 : ∀ u ∈ ts, w1.getD u.2 false = !(w1.getD u.1 false) := by
      intro u hu
      have hlu := hps u (by simp [hu])
      rw [wf_getD_lt gs1 w u.1 (by omega), wf_getD_lt gs1 w u.2 (by omega)]
      exact hts u (by simp [hu])
    have h2 := heval2 w1 hw1 (by rw [h1.1, h1.2]) hts1
    have hcnt : ts.countP (fun u => w1.getD u.1 false) = ts.countP (fun u => w.getD u.1 false) := by
      rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
      congr 1; apply List.filter_congr
      intro u hu; have hlu := hps u (by simp [hu])
      exact wf_getD_lt gs1 w u.1 (by omega)
    refine ⟨?_, h2.2⟩
    rw [h2.1, h1.1, hcnt, List.countP_cons, xor_assoc_bool, xor_mod2_add]

lemma range_filter_card_eq_countP (n : ℕ) (P : ℕ → Bool) :
    ((Finset.range n).filter (fun l => P l = true)).card = (List.range n).countP P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.filter_insert, List.range_succ, List.countP_append, List.countP_singleton]
    cases h : P n
    · simp [ih]
    · simp [Finset.card_insert_of_notMem, ih]

set_option maxHeartbeats 800000 in
lemma circuit_size (k a d : ℕ) (ha : 0 < a) (hak : 2 ^ a ≤ k) (hd : 0 < d) (hdk : 2 * d + 1 ≤ k) :
    let N := 2 ^ k
    let m := k - d
    let h := 2 ^ m
    let low := fun (i j : Fin N) =>
      ((Finset.range m).filter (fun l => i.val.testBit l && j.val.testBit l)).card
    let cross := fun (i j : Fin N) => ((Finset.range d).filter (fun l =>
      i.val.testBit (m + l) && j.val.testBit 0 && j.val.testBit (l + 1))).card
    let tag := fun (left right : Fin N) => (low left right + cross left right + cross right left) % 2 == 1
    let r := 2 ^ a
    let G := fun (x y : Fin N) => if x.val < h ∨ y.val < h then tag x y else x.val.testBit (y.val % r)
    PEqualNP.Represents.HasLitSize (k + k) (PEqualNP.Represents.adjFun (k := k) (l := k) G)
      (3 * (r - 1) + 8 * k + 16 * d + 8) := by
  intro N m h low cross tag r G
  have hm_ge2 : 2 ≤ m := by omega
  have hbase_eq : 4 * k = (k + k) + (k + k) := by omega
  let base0 := 4 * k
  obtain ⟨gs_sel, w_sel, hm_sel, hl_sel, hlt_sel, hev_sel⟩ :=
    buildMuxTree a base0 (fun j => k + j) (fun j => 3 * k + j) (fun t => t)
      (fun j hj => by have : j < 2 ^ a := lt_trans hj Nat.lt_two_pow_self; omega)
      (fun t ht => by omega)
  let base1 := base0 + gs_sel.length
  let xLtTail := (List.range (d - 1)).map (fun j => 2 * k + m + 1 + j)
  let xGeTail := (List.range (d - 1)).map (fun j => m + 1 + j)
  let yLtTail := (List.range (d - 1)).map (fun j => 3 * k + m + 1 + j)
  let yGeTail := (List.range (d - 1)).map (fun j => k + m + 1 + j)
  obtain ⟨gs_xlt, w_xlt, hm_xlt, hl_xlt, hlt_xlt, hev_xlt⟩ :=
    buildFoldAnd xLtTail base1 (2 * k + m) (by omega) (by
      intro u hu; simp only [xLtTail, List.mem_map, List.mem_range] at hu
      obtain ⟨j, hj, rfl⟩ := hu; omega)
  let base2 := base1 + gs_xlt.length
  obtain ⟨gs_xge, w_xge, hm_xge, hl_xge, hlt_xge, hev_xge⟩ :=
    buildFoldOr xGeTail base2 m (by omega) (by
      intro u hu; simp only [xGeTail, List.mem_map, List.mem_range] at hu
      obtain ⟨j, hj, rfl⟩ := hu; omega)
  let base3 := base2 + gs_xge.length
  obtain ⟨gs_ylt, w_ylt, hm_ylt, hl_ylt, hlt_ylt, hev_ylt⟩ :=
    buildFoldAnd yLtTail base3 (3 * k + m) (by omega) (by
      intro u hu; simp only [yLtTail, List.mem_map, List.mem_range] at hu
      obtain ⟨j, hj, rfl⟩ := hu; omega)
  let base4 := base3 + gs_ylt.length
  obtain ⟨gs_yge, w_yge, hm_yge, hl_yge, hlt_yge, hev_yge⟩ :=
    buildFoldOr yGeTail base4 (k + m) (by omega) (by
      intro u hu; simp only [yGeTail, List.mem_map, List.mem_range] at hu
      obtain ⟨j, hj, rfl⟩ := hu; omega)
  let base5 := base4 + gs_yge.length
  let gs_b : List Gate := [gOr w_xlt w_ylt, gAnd w_xge w_yge]
  have hm_b : Mono2List gs_b := by
    intro g hg; simp only [gs_b, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp [gAnd, gOr]
  let w_B := base5
  let w_nB := base5 + 1
  let base6 := base5 + 2
  obtain ⟨gs_low, ps_low, hm_low, hl_low, hpl_low, hlt_low, hev_low⟩ :=
    buildDualAnd2 m base6 (fun l => l) (fun l => 2 * k + l) (fun l => k + l) (fun l => 3 * k + l)
      (fun l hl => by omega)
  let base7 := base6 + gs_low.length
  obtain ⟨gs_c1, ps_c1, hm_c1, hl_c1, hpl_c1, hlt_c1, hev_c1⟩ :=
    buildDualAnd3 d base7
      (fun l => m + l) (fun l => 2 * k + m + l)
      (fun _ => k) (fun _ => 3 * k)
      (fun l => k + l + 1) (fun l => 3 * k + l + 1)
      (fun l hl => by omega)
  let base8 := base7 + gs_c1.length
  obtain ⟨gs_c2, ps_c2, hm_c2, hl_c2, hpl_c2, hlt_c2, hev_c2⟩ :=
    buildDualAnd3 d base8
      (fun l => k + m + l) (fun l => 3 * k + m + l)
      (fun _ => 0) (fun _ => 2 * k)
      (fun l => l + 1) (fun l => 2 * k + l + 1)
      (fun l hl => by omega)
  let base9 := base8 + gs_c2.length
  let allPs := ps_low ++ ps_c1 ++ ps_c2
  have hall_len : allPs.length = k + d := by simp [allPs, hpl_low, hpl_c1, hpl_c2]; omega
  have hall_ne : allPs ≠ [] := by intro h0; rw [h0] at hall_len; simp at hall_len; omega
  cases hall_eq : allPs with
  | nil => exact absurd hall_eq hall_ne
  | cons p0 prest =>
    have hprest_len : prest.length = k + d - 1 := by rw [hall_eq] at hall_len; simp at hall_len; omega
    have hall_lt : ∀ t ∈ allPs, t.1 < base9 ∧ t.2 < base9 := by
      intro t ht
      simp only [allPs, List.mem_append] at ht
      rcases ht with (ht | ht) | ht
      · have := hlt_low t ht; omega
      · have := hlt_c1 t ht; omega
      · have := hlt_c2 t ht; omega
    have hp0_lt : p0.1 < base9 ∧ p0.2 < base9 := hall_lt p0 (by rw [hall_eq]; simp)
    have hprest_lt : ∀ t ∈ prest, t.1 < base9 ∧ t.2 < base9 :=
      fun t ht => hall_lt t (by rw [hall_eq]; simp [ht])
    obtain ⟨gs_par, w_tag, w_ntag, hm_par, hl_par, hlt_tag, _, hev_par⟩ :=
      buildParity prest base9 p0.1 p0.2 hp0_lt.1 hp0_lt.2 hprest_lt
    let base10 := base9 + gs_par.length
    obtain ⟨gs_out, w_out, hm_out, hl_out, _, hev_out⟩ :=
      buildMux base10 w_B w_nB w_tag w_sel
        (by omega) (by omega) (by omega) (by omega)
    let gs_all := gs_sel ++ gs_xlt ++ gs_xge ++ gs_ylt ++ gs_yge ++ gs_b ++
                  gs_low ++ gs_c1 ++ gs_c2 ++ gs_par ++ gs_out
    have hm_all : Mono2List gs_all :=
      (((((((((hm_sel.append hm_xlt).append hm_xge).append hm_ylt).append hm_yge).append hm_b).append
        hm_low).append hm_c1).append hm_c2).append hm_par).append hm_out
    refine ⟨⟨gs_all, w_out⟩, hm_all.to_monotone2 w_out, ?_, ?_⟩
    · change gs_all.length ≤ 3 * (r - 1) + 8 * k + 16 * d + 8
      simp only [gs_all, List.length_append, hl_sel, hl_xlt, hl_xge, hl_ylt, hl_yge, gs_b,
        List.length_cons, List.length_nil, hl_low, hl_c1, hl_c2, hl_par, hl_out,
        xLtTail, xGeTail, yLtTail, yGeTail, List.length_map, List.length_range, hprest_len]
      change 3 * (r - 1) + (d - 1) + (d - 1) + (d - 1) + (d - 1) + 2 +
        2 * m + 4 * d + 4 * d + 6 * (k + d - 1) + 3 ≤ 3 * (r - 1) + 8 * k + 16 * d + 8
      omega
    · intro z
      let w0 : List Bool := List.ofFn z ++ List.ofFn (fun i => !z i)
      let xNat := tableIndex (fun i : Fin k => z (Fin.castAdd k i))
      let yNat := tableIndex (fun j : Fin k => z (Fin.natAdd k j))
      let xFin : Fin N := Fin.ofNat N xNat
      let yFin : Fin N := Fin.ofNat N yNat
      have hxlt : xNat < N := tableIndex_lt _
      have hylt : yNat < N := tableIndex_lt _
      have hxval : xFin.val = xNat := Nat.mod_eq_of_lt hxlt
      have hyval : yFin.val = yNat := Nat.mod_eq_of_lt hylt
      have hw0_len : w0.length = base0 := by simp [w0, base0]; omega
      have hget_x : ∀ j < k, w0.getD j false = xFin.val.testBit j := by
        intro j hj
        rw [hxval, testBit_tableIndex]; simp only [hj, dite_true]
        have hlt : j < (List.ofFn z).length := by simp; omega
        rw [show w0 = List.ofFn z ++ List.ofFn (fun i => !z i) from rfl,
            List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_ofFn]
        simp [Fin.castAdd, show j < k + k by omega]
      have hget_y : ∀ j < k, w0.getD (k + j) false = yFin.val.testBit j := by
        intro j hj
        rw [hyval, testBit_tableIndex]; simp only [hj, dite_true]
        have hlt : k + j < (List.ofFn z).length := by simp; omega
        rw [show w0 = List.ofFn z ++ List.ofFn (fun i => !z i) from rfl,
            List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_ofFn]
        simp [Fin.natAdd, show k + j < k + k by omega]
      have hget_nx : ∀ j < k, w0.getD (2 * k + j) false = !(xFin.val.testBit j) := by
        intro j hj
        rw [hxval, testBit_tableIndex]; simp only [hj, dite_true]
        have hle : (List.ofFn z).length ≤ 2 * k + j := by simp; omega
        rw [show w0 = List.ofFn z ++ List.ofFn (fun i => !z i) from rfl,
            List.getD_eq_getElem?_getD, List.getElem?_append_right hle, List.length_ofFn,
            show 2 * k + j - (k + k) = j by omega, List.getElem?_ofFn]
        simp [Fin.castAdd, show j < k + k by omega]
      have hget_ny : ∀ j < k, w0.getD (3 * k + j) false = !(yFin.val.testBit j) := by
        intro j hj
        rw [hyval, testBit_tableIndex]; simp only [hj, dite_true]
        have hle : (List.ofFn z).length ≤ 3 * k + j := by simp; omega
        rw [show w0 = List.ofFn z ++ List.ofFn (fun i => !z i) from rfl,
            List.getD_eq_getElem?_getD, List.getElem?_append_right hle, List.length_ofFn,
            show 3 * k + j - (k + k) = k + j by omega, List.getElem?_ofFn]
        simp [Fin.natAdd, show k + j < k + k by omega]
      let w1 := wf gs_sel w0
      let w2 := wf gs_xlt w1
      let w3 := wf gs_xge w2
      let w4 := wf gs_ylt w3
      let w5 := wf gs_yge w4
      let w6 := wf gs_b w5
      let w7 := wf gs_low w6
      let w8 := wf gs_c1 w7
      let w9 := wf gs_c2 w8
      let w10 := wf gs_par w9
      let w11 := wf gs_out w10
      have hw1 : w1.length = base1 := by rw [wf_len, hw0_len]
      have hw2 : w2.length = base2 := by rw [wf_len, hw1]
      have hw3 : w3.length = base3 := by rw [wf_len, hw2]
      have hw4 : w4.length = base4 := by rw [wf_len, hw3]
      have hw5 : w5.length = base5 := by rw [wf_len, hw4]
      have hw6 : w6.length = base6 := by rw [wf_len, hw5]; rfl
      have hw7 : w7.length = base7 := by rw [wf_len, hw6]
      have hw8 : w8.length = base8 := by rw [wf_len, hw7]
      have hw9 : w9.length = base9 := by rw [wf_len, hw8]
      have hw10 : w10.length = base10 := by rw [wf_len, hw9]
      have hpres : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
          (wf gs w).getD i false = w.getD i false := wf_getD_lt
      have hbase_read : ∀ (w' : List Bool) (gs' : List Gate), w' = wf gs' w0 →
          ∀ i < base0, w'.getD i false = w0.getD i false := by
        intro w' gs' heq i hi; rw [heq]; exact wf_getD_lt gs' w0 i (by omega)
      have hv_sel : w1.getD w_sel false = xFin.val.testBit (yFin.val % r) := by
        have h1 := hev_sel w0 yFin.val hw0_len (fun j hj => by
          have hjlt : j < k := lt_of_lt_of_le (lt_trans hj Nat.lt_two_pow_self) hak
          exact ⟨hget_y j hjlt, hget_ny j hjlt⟩)
        rw [h1]
        exact hget_x (yFin.val % r) (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos a)) hak)
      have hlt_h_iff : ∀ u : Fin N, (decide (u.val < h)) =
          (!(u.val.testBit m) && (List.range (d - 1)).all (fun j => !(u.val.testBit (m + 1 + j)))) := by
        intro u
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_iff, lt_two_pow_iff_testBit m u.val, Bool.and_eq_true, List.all_eq_true]
        simp only [Bool.not_eq_true', List.mem_range]
        constructor
        · intro hall
          exact ⟨hall m le_rfl, fun j hj => hall (m + 1 + j) (by omega)⟩
        · rintro ⟨hm0, hrest⟩ i hi
          by_cases hik : i < k
          · by_cases him : i = m
            · subst him; exact hm0
            · have := hrest (i - m - 1) (by omega)
              rwa [show m + 1 + (i - m - 1) = i by omega] at this
          · exact ((lt_two_pow_iff_testBit k u.val).mp u.isLt) i (by omega)
      have hge_h_iff : ∀ u : Fin N, (!(decide (u.val < h))) =
          (u.val.testBit m || (List.range (d - 1)).any (fun j => u.val.testBit (m + 1 + j))) := by
        intro u
        rw [hlt_h_iff u]
        simp only [Bool.not_and, Bool.not_not]
        congr 1
        induction (List.range (d - 1)) with
        | nil => rfl
        | cons x xs ih => simp [Bool.not_and, ih]
      have hv_xlt : w2.getD w_xlt false = decide (xFin.val < h) := by
        rw [hev_xlt w1 hw1, wf_getD_lt gs_sel w0 (2 * k + m) (by omega), hget_nx m (by omega),
            hlt_h_iff xFin]
        congr 1
        simp only [xLtTail, List.all_map]
        apply list_all_congr; intro j hj
        have hj' : j < d - 1 := List.mem_range.mp hj
        simp only [Function.comp_apply]
        rw [wf_getD_lt gs_sel w0 (2 * k + m + 1 + j) (by omega),
            show 2 * k + m + 1 + j = 2 * k + (m + 1 + j) by omega, hget_nx (m + 1 + j) (by omega)]
      have hv_xge : w3.getD w_xge false = !(decide (xFin.val < h)) := by
        have hw2_eq : w2 = wf (gs_sel ++ gs_xlt) w0 := by simp only [w2, w1, wf_append]
        rw [hev_xge w2 hw2, hbase_read w2 _ hw2_eq m (by omega), hget_x m (by omega), hge_h_iff xFin]
        congr 1
        simp only [xGeTail, List.any_map]
        apply list_any_congr; intro j hj
        have hj' : j < d - 1 := List.mem_range.mp hj
        simp only [Function.comp_apply]
        rw [hbase_read w2 _ hw2_eq (m + 1 + j) (by omega), hget_x (m + 1 + j) (by omega)]
      have hv_ylt : w4.getD w_ylt false = decide (yFin.val < h) := by
        have hw3_eq : w3 = wf (gs_sel ++ gs_xlt ++ gs_xge) w0 := by simp only [w3, w2, w1, wf_append]
        rw [hev_ylt w3 hw3, hbase_read w3 _ hw3_eq (3 * k + m) (by omega), hget_ny m (by omega),
            hlt_h_iff yFin]
        congr 1
        simp only [yLtTail, List.all_map]
        apply list_all_congr; intro j hj
        have hj' : j < d - 1 := List.mem_range.mp hj
        simp only [Function.comp_apply]
        rw [hbase_read w3 _ hw3_eq (3 * k + m + 1 + j) (by omega),
            show 3 * k + m + 1 + j = 3 * k + (m + 1 + j) by omega, hget_ny (m + 1 + j) (by omega)]
      have hv_yge : w5.getD w_yge false = !(decide (yFin.val < h)) := by
        have hw4_eq : w4 = wf (gs_sel ++ gs_xlt ++ gs_xge ++ gs_ylt) w0 := by
          simp only [w4, w3, w2, w1, wf_append]
        rw [hev_yge w4 hw4, hbase_read w4 _ hw4_eq (k + m) (by omega), hget_y m (by omega), hge_h_iff yFin]
        congr 1
        simp only [yGeTail, List.any_map]
        apply list_any_congr; intro j hj
        have hj' : j < d - 1 := List.mem_range.mp hj
        simp only [Function.comp_apply]
        rw [hbase_read w4 _ hw4_eq (k + m + 1 + j) (by omega),
            show k + m + 1 + j = k + (m + 1 + j) by omega, hget_y (m + 1 + j) (by omega)]
      have hv_B : w6.getD w_B false = (decide (xFin.val < h) || decide (yFin.val < h)) := by
        have hsp : gs_b = [gOr w_xlt w_ylt] ++ [gAnd w_xge w_yge] := rfl
        have h5_xlt : w5.getD w_xlt false = decide (xFin.val < h) := by
          have : w5 = wf (gs_xge ++ gs_ylt ++ gs_yge) w2 := by simp only [w5, w4, w3, wf_append]
          rw [this, wf_getD_lt _ w2 w_xlt (hw2 ▸ hlt_xlt), hv_xlt]
        have h5_ylt : w5.getD w_ylt false = decide (yFin.val < h) := by
          rw [wf_getD_lt gs_yge w4 w_ylt (hw4 ▸ hlt_ylt), hv_ylt]
        change (wf gs_b w5).getD base5 false = _
        rw [hsp, wf_append, wf_getD_lt [gAnd w_xge w_yge] _ base5 (by rw [wf_len, hw5]; simp),
            ← hw5, wf_gOr_eq, h5_xlt, h5_ylt]
      have hv_nB : w6.getD w_nB false = !(w6.getD w_B false) := by
        rw [hv_B]
        have hsp : gs_b = [gOr w_xlt w_ylt] ++ [gAnd w_xge w_yge] := rfl
        have h5_xge : w5.getD w_xge false = !(decide (xFin.val < h)) := by
          have : w5 = wf (gs_ylt ++ gs_yge) w3 := by simp only [w5, w4, wf_append]
          rw [this, wf_getD_lt _ w3 w_xge (hw3 ▸ hlt_xge), hv_xge]
        let w5b := wf [gOr w_xlt w_ylt] w5
        have hw5b : w5b.length = base5 + 1 := by simp [w5b, wf_len, hw5]
        have hwxge_lt : w_xge < w5.length := by rw [hw5]; exact lt_of_lt_of_le hlt_xge (by dsimp only [base5, base4, base3]; omega)
        have hwyge_lt : w_yge < w5.length := by rw [hw5]; exact hlt_yge
        change (wf gs_b w5).getD (base5 + 1) false = _
        rw [hsp, wf_append, ← hw5b, wf_gAnd_eq,
            wf_getD_lt [gOr w_xlt w_ylt] w5 w_xge hwxge_lt,
            wf_getD_lt [gOr w_xlt w_ylt] w5 w_yge hwyge_lt, h5_xge, hv_yge]
        cases decide (xFin.val < h) <;> cases decide (yFin.val < h) <;> rfl
      have hw6_eq : w6 = wf (gs_sel ++ gs_xlt ++ gs_xge ++ gs_ylt ++ gs_yge ++ gs_b) w0 := by
        simp only [w6, w5, w4, w3, w2, w1, wf_append]
      have hw7_eq : w7 = wf (gs_sel ++ gs_xlt ++ gs_xge ++ gs_ylt ++ gs_yge ++ gs_b ++ gs_low) w0 := by
        simp only [w7, hw6_eq, wf_append]
      have hw8_eq : w8 = wf (gs_sel ++ gs_xlt ++ gs_xge ++ gs_ylt ++ gs_yge ++ gs_b ++ gs_low ++ gs_c1) w0 := by
        simp only [w8, hw7_eq, wf_append]
      have hget_y0 : w0.getD k false = yFin.val.testBit 0 := by
        simpa using hget_y 0 (by omega)
      have hget_ny0 : w0.getD (3 * k) false = !(yFin.val.testBit 0) := by
        simpa using hget_ny 0 (by omega)
      have hget_nx0 : w0.getD (2 * k) false = !(xFin.val.testBit 0) := by
        simpa using hget_nx 0 (by omega)
      have hlow_ev := hev_low w6 hw6 (fun l hl => by
        rw [hbase_read w6 _ hw6_eq l (by omega), hbase_read w6 _ hw6_eq (2 * k + l) (by omega),
            hbase_read w6 _ hw6_eq (k + l) (by omega), hbase_read w6 _ hw6_eq (3 * k + l) (by omega),
            hget_x l (by omega), hget_nx l (by omega), hget_y l (by omega), hget_ny l (by omega)]
        exact ⟨rfl, rfl⟩)
      have hc1_ev := hev_c1 w7 hw7 (fun l hl => by
        rw [hbase_read w7 _ hw7_eq (m + l) (by omega), hbase_read w7 _ hw7_eq (2 * k + m + l) (by omega),
            hbase_read w7 _ hw7_eq k (by omega), hbase_read w7 _ hw7_eq (3 * k) (by omega),
            hbase_read w7 _ hw7_eq (k + l + 1) (by omega), hbase_read w7 _ hw7_eq (3 * k + l + 1) (by omega),
            show 2 * k + m + l = 2 * k + (m + l) by omega,
            show k + l + 1 = k + (l + 1) by omega, show 3 * k + l + 1 = 3 * k + (l + 1) by omega,
            hget_x (m + l) (by omega), hget_nx (m + l) (by omega),
            hget_y0, hget_ny0,
            hget_y (l + 1) (by omega), hget_ny (l + 1) (by omega)]
        exact ⟨rfl, rfl, rfl⟩)
      have hc2_ev := hev_c2 w8 hw8 (fun l hl => by
        rw [hbase_read w8 _ hw8_eq (k + m + l) (by omega), hbase_read w8 _ hw8_eq (3 * k + m + l) (by omega),
            hbase_read w8 _ hw8_eq 0 (by omega), hbase_read w8 _ hw8_eq (2 * k) (by omega),
            hbase_read w8 _ hw8_eq (l + 1) (by omega), hbase_read w8 _ hw8_eq (2 * k + l + 1) (by omega),
            show k + m + l = k + (m + l) by omega, show 3 * k + m + l = 3 * k + (m + l) by omega,
            show 2 * k + l + 1 = 2 * k + (l + 1) by omega,
            hget_y (m + l) (by omega), hget_ny (m + l) (by omega),
            hget_x 0 (by omega), hget_nx0,
            hget_x (l + 1) (by omega), hget_nx (l + 1) (by omega)]
        exact ⟨rfl, rfl, rfl⟩)
      have hall_neg : ∀ t ∈ allPs, w9.getD t.2 false = !(w9.getD t.1 false) := by
        intro t ht
        simp only [allPs, List.mem_append] at ht
        rcases ht with (ht | ht) | ht
        · have hlt := hlt_low t ht
          have hw9_7 : w9 = wf (gs_c1 ++ gs_c2) w7 := by simp only [w9, w8, wf_append]
          rw [hw9_7, wf_getD_lt _ w7 t.1 (hw7 ▸ hlt.1), wf_getD_lt _ w7 t.2 (hw7 ▸ hlt.2)]
          exact hlow_ev.1 t ht
        · have hlt := hlt_c1 t ht
          rw [wf_getD_lt gs_c2 w8 t.1 (hw8 ▸ hlt.1), wf_getD_lt gs_c2 w8 t.2 (hw8 ▸ hlt.2)]
          exact hc1_ev.1 t ht
        · exact hc2_ev.1 t ht
      have hall_cnt : allPs.countP (fun t => w9.getD t.1 false) =
          low xFin yFin + cross xFin yFin + cross yFin xFin := by
        simp only [allPs, List.countP_append]
        have h1 : ps_low.countP (fun t => w9.getD t.1 false) = low xFin yFin := by
          have hw9_7 : w9 = wf (gs_c1 ++ gs_c2) w7 := by simp only [w9, w8, wf_append]
          have hs : ps_low.countP (fun t => w9.getD t.1 false) = ps_low.countP (fun t => w7.getD t.1 false) := by
            rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
            congr 1; apply List.filter_congr; intro t ht
            have hlt := hlt_low t ht; rw [hw9_7, wf_getD_lt _ w7 t.1 (hw7 ▸ hlt.1)]
          rw [hs, hlow_ev.2]
          dsimp only [low]
          rw [range_filter_card_eq_countP]
          rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
          congr 1; apply List.filter_congr; intro l hl
          have hl' : l < m := List.mem_range.mp hl
          rw [hbase_read w6 _ hw6_eq l (by omega), hbase_read w6 _ hw6_eq (k + l) (by omega),
              hget_x l (by omega), hget_y l (by omega)]
        have h2 : ps_c1.countP (fun t => w9.getD t.1 false) = cross xFin yFin := by
          have hs : ps_c1.countP (fun t => w9.getD t.1 false) = ps_c1.countP (fun t => w8.getD t.1 false) := by
            rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
            congr 1; apply List.filter_congr; intro t ht
            have hlt := hlt_c1 t ht; rw [wf_getD_lt gs_c2 w8 t.1 (hw8 ▸ hlt.1)]
          rw [hs, hc1_ev.2]
          dsimp only [cross]
          rw [range_filter_card_eq_countP]
          rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
          congr 1; apply List.filter_congr; intro l hl
          have hl' : l < d := List.mem_range.mp hl
          rw [hbase_read w7 _ hw7_eq (m + l) (by omega), hbase_read w7 _ hw7_eq k (by omega),
              hbase_read w7 _ hw7_eq (k + l + 1) (by omega),
              show k + l + 1 = k + (l + 1) by omega,
              hget_x (m + l) (by omega), hget_y0, hget_y (l + 1) (by omega)]
        have h3 : ps_c2.countP (fun t => w9.getD t.1 false) = cross yFin xFin := by
          rw [hc2_ev.2]
          dsimp only [cross]
          rw [range_filter_card_eq_countP]
          rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
          congr 1; apply List.filter_congr; intro l hl
          have hl' : l < d := List.mem_range.mp hl
          rw [hbase_read w8 _ hw8_eq (k + m + l) (by omega), hbase_read w8 _ hw8_eq 0 (by omega),
              hbase_read w8 _ hw8_eq (l + 1) (by omega), show k + m + l = k + (m + l) by omega,
              hget_y (m + l) (by omega), hget_x 0 (by omega), hget_x (l + 1) (by omega)]
        rw [h1, h2, h3]
      have hv_tag : w10.getD w_tag false = tag xFin yFin := by
        have hpar := hev_par w9 hw9 (hall_neg p0 (by rw [hall_eq]; simp))
          (fun t ht => hall_neg t (by rw [hall_eq]; simp [ht]))
        rw [hpar.1]
        dsimp only [tag]
        rw [← hall_cnt, hall_eq, List.countP_cons, xor_mod2_add]
      have hw11_eq : wf gs_all w0 = w11 := by
        simp only [gs_all, wf_append, w11, w10, w9, w8, w7, w6, w5, w4, w3, w2, w1]
      have hw10_from6 : w10 = wf (gs_low ++ gs_c1 ++ gs_c2 ++ gs_par) w6 := by
        simp only [w10, w9, w8, w7, wf_append]
      have hw10_from1 : w10 = wf (gs_xlt ++ gs_xge ++ gs_ylt ++ gs_yge ++ gs_b ++
          gs_low ++ gs_c1 ++ gs_c2 ++ gs_par) w1 := by
        simp only [w10, w9, w8, w7, w6, w5, w4, w3, w2, wf_append]
      have h10_B : w10.getD w_B false = (decide (xFin.val < h) || decide (yFin.val < h)) := by
        rw [hw10_from6, wf_getD_lt _ w6 w_B (by rw [hw6]; dsimp only [w_B, base6]; omega), hv_B]
      have h10_nB : w10.getD w_nB false = !(w10.getD w_B false) := by
        rw [hw10_from6, wf_getD_lt _ w6 w_B (by rw [hw6]; dsimp only [w_B, base6]; omega),
            wf_getD_lt _ w6 w_nB (by rw [hw6]; dsimp only [w_nB, base6]; omega), hv_nB]
      have h10_sel : w10.getD w_sel false = xFin.val.testBit (yFin.val % r) := by
        rw [hw10_from1, wf_getD_lt _ w1 w_sel (hw1 ▸ hlt_sel), hv_sel]
      change (wf gs_all w0).getD w_out false = adjFun G z
      rw [hw11_eq, hev_out w10 hw10 h10_nB, h10_B, hv_tag, h10_sel]
      change (if (decide (xFin.val < h) || decide (yFin.val < h)) = true then tag xFin yFin
        else xFin.val.testBit (yFin.val % r)) = G xFin yFin
      dsimp only [G]
      by_cases hcond : xFin.val < h ∨ yFin.val < h
      · simp [hcond]
      · simp [hcond]

lemma card_filter_eq_half_of_involution {α : Type*} [DecidableEq α] (S : Finset α)
    (f : α → α) (P : α → Bool) (c : Bool)
    (hmem : ∀ x ∈ S, f x ∈ S) (hinv : ∀ x ∈ S, f (f x) = x) (hflip : ∀ x ∈ S, P (f x) = !(P x)) :
    2 * (S.filter (fun x => P x ≠ c)).card = S.card := by
  have hbij : (S.filter (fun x => P x ≠ c)).card = (S.filter (fun x => P x = c)).card := by
    apply Finset.card_bij (fun x _ => f x)
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      refine ⟨hmem x hx.1, ?_⟩
      rw [hflip x hx.1]
      cases hpx : P x <;> cases c <;> simp_all
    · intro x hx y hy hxy
      simp only [Finset.mem_filter] at hx hy
      have := congrArg f hxy
      rwa [hinv x hx.1, hinv y hy.1] at this
    · intro y hy
      simp only [Finset.mem_filter] at hy
      refine ⟨f y, ?_, hinv y hy.1⟩
      simp only [Finset.mem_filter]
      refine ⟨hmem y hy.1, ?_⟩
      rw [hflip y hy.1, hy.2]
      cases c <;> decide
  have hsum := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => P x = c)
  simp only [ne_eq] at hbij ⊢
  omega

lemma mod2_beq_flip {a b : ℕ} (h : (a + b) % 2 = 1) : (a % 2 == 1) = !(b % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp_all [Nat.add_mod]

lemma card_filter_toggle (S : Finset ℕ) (t : ℕ) (ht : t ∈ S) (p q : ℕ → Bool)
    (heq : ∀ l ∈ S, l ≠ t → p l = q l) :
    (S.filter (fun l => p l = true)).card + (if q t then 1 else 0) =
    (S.filter (fun l => q l = true)).card + (if p t then 1 else 0) := by
  have hsplit : ∀ f : ℕ → Bool,
      (S.filter (fun l => f l = true)).card =
      ((S.erase t).filter (fun l => f l = true)).card + (if f t then 1 else 0) := by
    intro f
    have h1 : S = insert t (S.erase t) := (Finset.insert_erase ht).symm
    conv_lhs => rw [h1, Finset.filter_insert]
    cases hf : f t
    · simp
    · simp [Finset.card_insert_of_notMem]
  rw [hsplit p, hsplit q]
  have herase : (S.erase t).filter (fun l => p l = true) = (S.erase t).filter (fun l => q l = true) := by
    apply Finset.filter_congr
    intro l hl
    rw [heq l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl)]
  rw [herase]; omega

lemma testBit_xor_two_pow (z t s : ℕ) :
    (z ^^^ 2 ^ t).testBit s = if s = t then !(z.testBit t) else z.testBit s := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : s = t
  · subst h; simp
  · have h' : t ≠ s := fun e => h e.symm
    simp [h, h']

lemma tag_dist (k d : ℕ) (hd : 0 < d) (hdk : 2 * d + 1 ≤ k) :
    let N := 2 ^ k
    let m := k - d
    let h := 2 ^ m
    let δ := 2 ^ (m - 2)
    let low := fun (i j : Fin N) =>
      ((Finset.range m).filter (fun l => i.val.testBit l && j.val.testBit l)).card
    let cross := fun (i j : Fin N) => ((Finset.range d).filter (fun l =>
      i.val.testBit (m + l) && j.val.testBit 0 && j.val.testBit (l + 1))).card
    let tag := fun (left right : Fin N) => (low left right + cross left right + cross right left) % 2 == 1
    ∀ (i j : Fin N), i ≠ j → ∀ (c : Bool),
      δ ≤ (Finset.univ.filter (fun z : Fin N => z.val < h ∧ xor (tag i z) (tag j z) ≠ c)).card := by
  intro N m h δ low cross tag i j hij c
  have hm2 : 2 ≤ m := by omega
  have hmk : m ≤ k := by omega
  have hleN : h ≤ N := Nat.pow_le_pow_right (by decide) hmk
  have h4d : h = 4 * δ := by
    have : m = (m - 2) + 2 := by omega
    conv_lhs => dsimp only [h]; rw [this, pow_add]
    ring
  have h2d : 2 ^ (m - 1) = 2 * δ := by
    have : m - 1 = (m - 2) + 1 := by omega
    conv_lhs => rw [this, pow_add]
    ring
  have hcross_zero : ∀ (z u : Fin N), z.val < h → cross z u = 0 := by
    intro z u hz
    dsimp only [cross]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro l hl
    have htb : z.val.testBit (m + l) = false :=
      (lt_two_pow_iff_testBit m z.val).mp hz (m + l) (by omega)
    simp [htb]
  have hxor_tag : ∀ z : Fin N, z.val < h →
      xor (tag i z) (tag j z) = ((low i z + cross i z + low j z + cross j z) % 2 == 1) := by
    intro z hz
    dsimp only [tag]
    rw [hcross_zero z i hz, hcross_zero z j hz, add_zero, add_zero]
    have hmod : ∀ a b : ℕ, xor ((a % 2 == 1)) ((b % 2 == 1)) = ((a + b) % 2 == 1) := by
      intro a b
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
        simp [ha, hb, Nat.add_mod]
    rw [hmod]
    congr 2; omega
  let flipFin (t : ℕ) (ht : t < m) (z : Fin N) : Fin N :=
    if hz : z.val < h then ⟨z.val ^^^ 2 ^ t,
      lt_of_lt_of_le (xor_lt_two_pow hz (Nat.pow_lt_pow_right (by decide) ht)) hleN⟩
    else z
  have hflip_lt : ∀ t (ht : t < m) (z : Fin N), z.val < h → (flipFin t ht z).val < h := by
    intro t ht z hz
    simp only [flipFin, hz, ↓reduceDIte]
    exact xor_lt_two_pow hz (Nat.pow_lt_pow_right (by decide) ht)
  have hflip_val : ∀ t (ht : t < m) (z : Fin N), z.val < h → (flipFin t ht z).val = z.val ^^^ 2 ^ t := by
    intro t ht z hz; simp only [flipFin, hz, ↓reduceDIte]
  have hflip_inv : ∀ t (ht : t < m) (z : Fin N), z.val < h → flipFin t ht (flipFin t ht z) = z := by
    intro t ht z hz
    have hlt := hflip_lt t ht z hz
    apply Fin.ext
    rw [hflip_val t ht _ hlt, hflip_val t ht z hz]
    apply Nat.eq_of_testBit_eq; intro s
    simp only [Nat.testBit_xor]
    cases z.val.testBit s <;> cases (2 ^ t).testBit s <;> rfl
  by_cases hcase1 : ∃ t, 1 ≤ t ∧ t < m ∧ i.val.testBit t ≠ j.val.testBit t
  · obtain ⟨t, ht1, htm, hne⟩ := hcase1
    let S0 : Finset (Fin N) := Finset.univ.filter (fun z : Fin N => z.val < h ∧ z.val.testBit 0 = false)
    have hS0_card : S0.card = 2 ^ (m - 1) := by
      have hbij : S0.card = (Finset.univ : Finset (Fin (2 ^ (m - 1)))).card := by
        apply Finset.card_bij (fun z hz => ⟨z.val / 2, by
          have hz1 := (Finset.mem_filter.mp hz).2.1
          omega⟩)
        · intro _ _; exact Finset.mem_univ _
        · intro x hx y hy hxy
          have hx0 := (Finset.mem_filter.mp hx).2.2
          have hy0 := (Finset.mem_filter.mp hy).2.2
          have hxm : x.val % 2 = 0 := by simp [Nat.testBit_zero] at hx0; omega
          have hym : y.val % 2 = 0 := by simp [Nat.testBit_zero] at hy0; omega
          have hdiv : x.val / 2 = y.val / 2 := congrArg Fin.val hxy
          apply Fin.ext; omega
        · intro u _
          have hu2 : 2 * u.val < h := by have := u.isLt; omega
          refine ⟨⟨2 * u.val, lt_of_lt_of_le hu2 hleN⟩, ?_, ?_⟩
          · simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and, hu2, Nat.testBit_zero, decide_eq_false_iff_not]
            omega
          · apply Fin.ext; simp
      rw [hbij, Finset.card_univ, Fintype.card_fin]
    have hhalf := card_filter_eq_half_of_involution S0 (flipFin t htm) (fun z => xor (tag i z) (tag j z)) c
      (fun z hz => by
        have ⟨hlt, hb0⟩ := (Finset.mem_filter.mp hz).2
        simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hflip_lt t htm z hlt, ?_⟩
        simp only [flipFin, hlt, ↓reduceDIte, testBit_xor_two_pow, show (0 : ℕ) ≠ t by omega, ↓reduceIte, hb0])
      (fun z hz => hflip_inv t htm z (Finset.mem_filter.mp hz).2.1)
      (fun z hz => by
        have ⟨hlt, hb0⟩ := (Finset.mem_filter.mp hz).2
        have hlt' := hflip_lt t htm z hlt
        have hb0' : (flipFin t htm z).val.testBit 0 = false := by
          simp only [flipFin, hlt, ↓reduceDIte, testBit_xor_two_pow, show (0 : ℕ) ≠ t by omega, ↓reduceIte, hb0]
        rw [hxor_tag _ hlt', hxor_tag _ hlt]
        have hc0 : ∀ u : Fin N, cross u z = 0 ∧ cross u (flipFin t htm z) = 0 := by
          intro u; constructor <;>
            (dsimp only [cross]; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro l _; simp [hb0, hb0'])
        rw [(hc0 i).1, (hc0 i).2, (hc0 j).1, (hc0 j).2]
        have hti := card_filter_toggle (Finset.range m) t (Finset.mem_range.mpr htm)
          (fun l => i.val.testBit l && (flipFin t htm z).val.testBit l)
          (fun l => i.val.testBit l && z.val.testBit l)
          (fun l _ hlt_ne => by rw [hflip_val t htm z hlt, testBit_xor_two_pow]; simp [hlt_ne])
        have htj := card_filter_toggle (Finset.range m) t (Finset.mem_range.mpr htm)
          (fun l => j.val.testBit l && (flipFin t htm z).val.testBit l)
          (fun l => j.val.testBit l && z.val.testBit l)
          (fun l _ hlt_ne => by rw [hflip_val t htm z hlt, testBit_xor_two_pow]; simp [hlt_ne])
        have htb_t : (flipFin t htm z).val.testBit t = !(z.val.testBit t) := by
          rw [hflip_val t htm z hlt, testBit_xor_two_pow]; simp
        change low i (flipFin t htm z) + _ = low i z + _ at hti
        change low j (flipFin t htm z) + _ = low j z + _ at htj
        rw [htb_t] at hti htj
        apply mod2_beq_flip
        cases hi : i.val.testBit t <;> cases hj : j.val.testBit t
        · exact absurd (hi.trans hj.symm) hne
        · cases hzt : z.val.testBit t <;> simp only [hi, hj, hzt, Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hti htj <;> omega
        · cases hzt : z.val.testBit t <;> simp only [hi, hj, hzt, Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hti htj <;> omega
        · exact absurd (hi.trans hj.symm) hne)
    have hsub : S0.filter (fun z => xor (tag i z) (tag j z) ≠ c) ⊆
        Finset.univ.filter (fun z : Fin N => z.val < h ∧ xor (tag i z) (tag j z) ≠ c) := by
      intro z hz
      simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact ⟨hz.1.1, hz.2⟩
    have hle := Finset.card_le_card hsub
    omega
  · push Not at hcase1
    by_cases hcase2 : ∃ l, l < d ∧ i.val.testBit (m + l) ≠ j.val.testBit (m + l)
    · obtain ⟨l0, hl0d, hne⟩ := hcase2
      have ht1 : 1 ≤ l0 + 1 := by omega
      have htm : l0 + 1 < m := by omega
      let S1 : Finset (Fin N) := Finset.univ.filter (fun z : Fin N => z.val < h ∧ z.val.testBit 0 = true)
      have hS1_card : S1.card = 2 ^ (m - 1) := by
        have hbij : S1.card = (Finset.univ : Finset (Fin (2 ^ (m - 1)))).card := by
          apply Finset.card_bij (fun z hz => ⟨z.val / 2, by
            have hz1 := (Finset.mem_filter.mp hz).2.1
            omega⟩)
          · intro _ _; exact Finset.mem_univ _
          · intro x hx y hy hxy
            have hx0 := (Finset.mem_filter.mp hx).2.2
            have hy0 := (Finset.mem_filter.mp hy).2.2
            have hxm : x.val % 2 = 1 := by simp [Nat.testBit_zero] at hx0; exact hx0
            have hym : y.val % 2 = 1 := by simp [Nat.testBit_zero] at hy0; exact hy0
            have hdiv : x.val / 2 = y.val / 2 := congrArg Fin.val hxy
            apply Fin.ext; omega
          · intro u _
            have hu2 : 2 * u.val + 1 < h := by have := u.isLt; omega
            refine ⟨⟨2 * u.val + 1, lt_of_lt_of_le hu2 hleN⟩, ?_, ?_⟩
            · simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and, hu2, Nat.testBit_zero, decide_eq_true_eq]
              omega
            · apply Fin.ext; simp; omega
        rw [hbij, Finset.card_univ, Fintype.card_fin]
      have hhalf := card_filter_eq_half_of_involution S1 (flipFin (l0 + 1) htm) (fun z => xor (tag i z) (tag j z)) c
        (fun z hz => by
          have ⟨hlt, hb0⟩ := (Finset.mem_filter.mp hz).2
          simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨hflip_lt (l0 + 1) htm z hlt, ?_⟩
          simp only [flipFin, hlt, ↓reduceDIte, testBit_xor_two_pow, show (0 : ℕ) ≠ l0 + 1 by omega, ↓reduceIte, hb0])
        (fun z hz => hflip_inv (l0 + 1) htm z (Finset.mem_filter.mp hz).2.1)
        (fun z hz => by
          have ⟨hlt, hb0⟩ := (Finset.mem_filter.mp hz).2
          have hlt' := hflip_lt (l0 + 1) htm z hlt
          have hb0' : (flipFin (l0 + 1) htm z).val.testBit 0 = true := by
            simp only [flipFin, hlt, ↓reduceDIte, testBit_xor_two_pow, show (0 : ℕ) ≠ l0 + 1 by omega, ↓reduceIte, hb0]
          rw [hxor_tag _ hlt', hxor_tag _ hlt]
          have htb_t : (flipFin (l0 + 1) htm z).val.testBit (l0 + 1) = !(z.val.testBit (l0 + 1)) := by
            rw [hflip_val (l0 + 1) htm z hlt, testBit_xor_two_pow]; simp
          have hlow_i := card_filter_toggle (Finset.range m) (l0 + 1) (Finset.mem_range.mpr htm)
            (fun l => i.val.testBit l && (flipFin (l0 + 1) htm z).val.testBit l)
            (fun l => i.val.testBit l && z.val.testBit l)
            (fun l _ hlt_ne => by rw [hflip_val (l0 + 1) htm z hlt, testBit_xor_two_pow]; simp [hlt_ne])
          have hlow_j := card_filter_toggle (Finset.range m) (l0 + 1) (Finset.mem_range.mpr htm)
            (fun l => j.val.testBit l && (flipFin (l0 + 1) htm z).val.testBit l)
            (fun l => j.val.testBit l && z.val.testBit l)
            (fun l _ hlt_ne => by rw [hflip_val (l0 + 1) htm z hlt, testBit_xor_two_pow]; simp [hlt_ne])
          have hcr_i := card_filter_toggle (Finset.range d) l0 (Finset.mem_range.mpr hl0d)
            (fun l => i.val.testBit (m + l) && (flipFin (l0 + 1) htm z).val.testBit 0 && (flipFin (l0 + 1) htm z).val.testBit (l + 1))
            (fun l => i.val.testBit (m + l) && z.val.testBit 0 && z.val.testBit (l + 1))
            (fun l _ hne' => by
              rw [hb0, hb0', hflip_val (l0 + 1) htm z hlt, testBit_xor_two_pow]; simp [hne'])
          have hcr_j := card_filter_toggle (Finset.range d) l0 (Finset.mem_range.mpr hl0d)
            (fun l => j.val.testBit (m + l) && (flipFin (l0 + 1) htm z).val.testBit 0 && (flipFin (l0 + 1) htm z).val.testBit (l + 1))
            (fun l => j.val.testBit (m + l) && z.val.testBit 0 && z.val.testBit (l + 1))
            (fun l _ hne' => by
              rw [hb0, hb0', hflip_val (l0 + 1) htm z hlt, testBit_xor_two_pow]; simp [hne'])
          have heq_t : i.val.testBit (l0 + 1) = j.val.testBit (l0 + 1) := hcase1 (l0 + 1) ht1 htm
          change low i (flipFin (l0 + 1) htm z) + _ = low i z + _ at hlow_i
          change low j (flipFin (l0 + 1) htm z) + _ = low j z + _ at hlow_j
          change cross i (flipFin (l0 + 1) htm z) + _ = cross i z + _ at hcr_i
          change cross j (flipFin (l0 + 1) htm z) + _ = cross j z + _ at hcr_j
          rw [htb_t, heq_t] at hlow_i
          rw [htb_t] at hlow_j
          rw [hb0, hb0', htb_t] at hcr_i hcr_j
          have hlow_even : (low i (flipFin (l0 + 1) htm z) + low j (flipFin (l0 + 1) htm z) +
              (low i z + low j z)) % 2 = 0 := by omega
          apply mod2_beq_flip
          cases hi_m : i.val.testBit (m + l0) <;> cases hj_m : j.val.testBit (m + l0)
          · exact absurd (hi_m.trans hj_m.symm) hne
          · cases hzt : z.val.testBit (l0 + 1) <;>
              simp only [hi_m, hj_m, hzt, Bool.false_and, Bool.true_and, Bool.and_true, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcr_i hcr_j <;> omega
          · cases hzt : z.val.testBit (l0 + 1) <;>
              simp only [hi_m, hj_m, hzt, Bool.false_and, Bool.true_and, Bool.and_true, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcr_i hcr_j <;> omega
          · exact absurd (hi_m.trans hj_m.symm) hne)
      have hsub : S1.filter (fun z => xor (tag i z) (tag j z) ≠ c) ⊆
          Finset.univ.filter (fun z : Fin N => z.val < h ∧ xor (tag i z) (tag j z) ≠ c) := by
        intro z hz
        simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact ⟨hz.1.1, hz.2⟩
      have hle := Finset.card_le_card hsub
      omega
    · push Not at hcase2
      have hne0 : i.val.testBit 0 ≠ j.val.testBit 0 := by
        intro heq0
        apply hij
        apply Fin.ext
        apply Nat.eq_of_testBit_eq
        intro s
        by_cases hs0 : s = 0
        · subst hs0; exact heq0
        · by_cases hsm : s < m
          · exact hcase1 s (by omega) hsm
          · by_cases hsk : s < k
            · have := hcase2 (s - m) (by omega)
              rwa [show m + (s - m) = s by omega] at this
            · rw [(lt_two_pow_iff_testBit k i.val).mp i.isLt s (by omega),
                  (lt_two_pow_iff_testBit k j.val).mp j.isLt s (by omega)]
      let Sall : Finset (Fin N) := Finset.univ.filter (fun z : Fin N => z.val < h)
      have hSall_card : Sall.card = h := by
        have hbij : Sall.card = (Finset.univ : Finset (Fin h)).card := by
          apply Finset.card_bij (fun z hz => ⟨z.val, (Finset.mem_filter.mp hz).2⟩)
          · intro _ _; exact Finset.mem_univ _
          · intro x _ y _ hxy; exact Fin.ext (congrArg (@Fin.val h) hxy)
          · intro u _; exact ⟨⟨u.val, lt_of_lt_of_le u.isLt hleN⟩, by simp [Sall, u.isLt], rfl⟩
        rw [hbij, Finset.card_univ, Fintype.card_fin]
      have h0m : 0 < m := by omega
      have hhalf := card_filter_eq_half_of_involution Sall (flipFin 0 h0m) (fun z => xor (tag i z) (tag j z)) c
        (fun z hz => by
          simp only [Sall, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          exact hflip_lt 0 h0m z hz)
        (fun z hz => hflip_inv 0 h0m z (Finset.mem_filter.mp hz).2)
        (fun z hz => by
          have hlt := (Finset.mem_filter.mp hz).2
          have hlt' := hflip_lt 0 h0m z hlt
          rw [hxor_tag _ hlt', hxor_tag _ hlt]
          have hcr_eq : ∀ w : Fin N, cross i w = cross j w := by
            intro w; dsimp only [cross]; congr 1; apply Finset.filter_congr
            intro l hl; rw [hcase2 l (Finset.mem_range.mp hl)]
          rw [hcr_eq z, hcr_eq (flipFin 0 h0m z)]
          have htb0 : (flipFin 0 h0m z).val.testBit 0 = !(z.val.testBit 0) := by
            rw [hflip_val 0 h0m z hlt, testBit_xor_two_pow]; simp
          have hlow_i := card_filter_toggle (Finset.range m) 0 (Finset.mem_range.mpr h0m)
            (fun l => i.val.testBit l && (flipFin 0 h0m z).val.testBit l)
            (fun l => i.val.testBit l && z.val.testBit l)
            (fun l _ hne' => by rw [hflip_val 0 h0m z hlt, testBit_xor_two_pow]; simp [hne'])
          have hlow_j := card_filter_toggle (Finset.range m) 0 (Finset.mem_range.mpr h0m)
            (fun l => j.val.testBit l && (flipFin 0 h0m z).val.testBit l)
            (fun l => j.val.testBit l && z.val.testBit l)
            (fun l _ hne' => by rw [hflip_val 0 h0m z hlt, testBit_xor_two_pow]; simp [hne'])
          change low i (flipFin 0 h0m z) + _ = low i z + _ at hlow_i
          change low j (flipFin 0 h0m z) + _ = low j z + _ at hlow_j
          rw [htb0] at hlow_i hlow_j
          apply mod2_beq_flip
          cases hi0 : i.val.testBit 0 <;> cases hj0 : j.val.testBit 0
          · exact absurd (hi0.trans hj0.symm) hne0
          · cases hz0 : z.val.testBit 0 <;> simp only [hi0, hj0, hz0, Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlow_i hlow_j <;> omega
          · cases hz0 : z.val.testBit 0 <;> simp only [hi0, hj0, hz0, Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hlow_i hlow_j <;> omega
          · exact absurd (hi0.trans hj0.symm) hne0)
      have hsub : Sall.filter (fun z => xor (tag i z) (tag j z) ≠ c) ⊆
          Finset.univ.filter (fun z : Fin N => z.val < h ∧ xor (tag i z) (tag j z) ≠ c) := by
        intro z hz
        simp only [Sall, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact hz
      have hle := Finset.card_le_card hsub
      omega

lemma row_col_dist (k a d : ℕ) (hd : 0 < d) (hdk : 2 * d + 1 ≤ k) (f g : Fin (2 ^ k) → Bool) :
    let N := 2 ^ k
    let m := k - d
    let h := 2 ^ m
    let δ := 2 ^ (m - 2)
    let low := fun (i j : Fin N) =>
      ((Finset.range m).filter (fun l => i.val.testBit l && j.val.testBit l)).card
    let cross := fun (i j : Fin N) => ((Finset.range d).filter (fun l =>
      i.val.testBit (m + l) && j.val.testBit 0 && j.val.testBit (l + 1))).card
    let tag := fun (left right : Fin N) => (low left right + cross left right + cross right left) % 2 == 1
    let r := 2 ^ a
    let G := fun (x y : Fin N) => if x.val < h ∨ y.val < h then tag x y else x.val.testBit (y.val % r)
    let T := fun (x y : Fin N) => xor (G x y) (xor (f x) (g y))
    (∀ i j : Fin N, i ≠ j → δ ≤ (Finset.univ.filter (fun z : Fin N => T i z ≠ T j z)).card) ∧
    (∀ i j : Fin N, i ≠ j → δ ≤ (Finset.univ.filter (fun z : Fin N => T z i ≠ T z j)).card) := by
  intro N m h δ low cross tag r G T
  have htag_symm : ∀ x y : Fin N, tag x y = tag y x := by
    intro x y
    dsimp only [tag, low]
    have hlow_s : ((Finset.range m).filter (fun l => x.val.testBit l && y.val.testBit l)) =
        ((Finset.range m).filter (fun l => y.val.testBit l && x.val.testBit l)) := by
      apply Finset.filter_congr; intro l _; rw [Bool.and_comm]
    rw [hlow_s]
    congr 2; omega
  have hxor_cancel : ∀ a b c d e : Bool, xor a (xor c e) = xor b (xor d e) → xor a b = xor c d := by
    decide
  have hxor_cancel' : ∀ a b c d e : Bool, xor a (xor e c) = xor b (xor e d) → xor a b = xor c d := by
    decide
  constructor
  · intro i j hij
    have h1 := tag_dist k d hd hdk i j hij (xor (f i) (f j))
    apply h1.trans
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    dsimp only [T, G]
    have hi : i.val < h ∨ z.val < h := Or.inr hz.1
    have hj : j.val < h ∨ z.val < h := Or.inr hz.1
    simp only [hi, hj, ↓reduceIte]
    intro heq
    exact hz.2 (hxor_cancel _ _ _ _ _ heq)
  · intro i j hij
    have h1 := tag_dist k d hd hdk i j hij (xor (g i) (g j))
    apply h1.trans
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    dsimp only [T, G]
    have hi : z.val < h ∨ i.val < h := Or.inl hz.1
    have hj : z.val < h ∨ j.val < h := Or.inl hz.1
    simp only [hi, hj, ↓reduceIte, htag_symm z i, htag_symm z j]
    intro heq
    exact hz.2 (hxor_cancel' _ _ _ _ _ heq)

end Border

namespace Assembly

open Finset

theorem main_proof : ∀ (k a d : ℕ), (0 < a ∧ 2 ^ a ≤ k ∧ 0 < d ∧ 2 * d + 1 ≤ k) →
    let N := 2 ^ k
    let m := k - d
    let h := 2 ^ m
    let δ := 2 ^ (m - 2)
    let low := fun (i j : Fin N) =>
      ((Finset.range m).filter (fun l => i.val.testBit l && j.val.testBit l)).card
    let cross := fun (i j : Fin N) => ((Finset.range d).filter (fun l =>
      i.val.testBit (m + l) && j.val.testBit 0 && j.val.testBit (l + 1))).card
    let tag := fun (left right : Fin N) => (low left right + cross left right + cross right left) % 2 == 1
    let r := 2 ^ a
    let G := fun (x y : Fin N) => if x.val < h ∨ y.val < h then tag x y else x.val.testBit (y.val % r)
    PEqualNP.Represents.HasLitSize (k + k) (PEqualNP.Represents.adjFun (k := k) (l := k) G)
      (3 * (r - 1) + 8 * k + 16 * d + 8) ∧
    ∀ (f g : Fin N → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) →
      let e := (Finset.univ.filter (fun p : Fin N × Fin N =>
        C.eval (PEqualNP.Represents.oneEach p.1 p.2) ≠
          xor (G p.1 p.2) (xor (f p.1) (g p.2)))).card
      let b := C.gates.countP (fun gate => gate.inputs.length == 2)
      ∀ v : ℕ, 0 < v → 17 + 2 * (v - 1) ≤ δ →
        (32 * N - (15 * b + 54 + 44 * (e / v) + 2 * h + 2 * a * (N / r))) ^ 2 ≤ 4 * e := by
  classical
  intro k a d ⟨ha, hak, hd, hdk⟩ N m h δ low cross tag r G
  refine ⟨Border.circuit_size k a d ha hak hd hdk, ?_⟩
  intro f g C hfan e b v hv hvd
  let T : Fin N → Fin N → Bool := fun x y => xor (G x y) (xor (f x) (g y))
  let H : Fin N → Fin N → Bool := fun x y => C.eval (PEqualNP.Represents.oneEach x y)
  have hNge2 : 2 ≤ N := by
    have hk1 : 1 ≤ k := by omega
    have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk1
    simpa [N] using this
  have ⟨hrowD, hcolD⟩ := Border.row_col_dist k a d hd hdk f g
  obtain ⟨π, S, piece, hS, _, _, hconf⟩ :=
    Extract.main N hNge2 T C hfan v hv
      (fun i j hij => hvd.trans (hrowD i j hij))
      (fun i j hij => hvd.trans (hcolD i j hij))
  let A : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => x.val < h)
  have hleN : h ≤ N := Nat.pow_le_pow_right (by decide) (by omega)
  have hA_card : A.card = h := by
    have hbij : A.card = (Finset.univ : Finset (Fin h)).card := by
      apply Finset.card_bij (fun z hz => ⟨z.val, (Finset.mem_filter.mp hz).2⟩)
      · intro _ _; exact Finset.mem_univ _
      · intro x _ y _ hxy; exact Fin.ext (congrArg (@Fin.val h) hxy)
      · intro u _; exact ⟨⟨u.val, lt_of_lt_of_le u.isLt hleN⟩, by simp [A, u.isLt], rfl⟩
    rw [hbij, Finset.card_univ, Fintype.card_fin]
  let U : Finset (Fin N) := S.filter (fun i => i ∉ A ∧ π i ∉ A)
  have hUS : U ⊆ S := Finset.filter_subset _ S
  have hS_le : S.card ≤ U.card + 2 * h := by
    have hsub : S \ U ⊆ A ∪ A.image π.symm := by
      intro i hi
      have hiS := (Finset.mem_sdiff.mp hi).1
      have hiU := (Finset.mem_sdiff.mp hi).2
      simp only [U, Finset.mem_filter, hiS, true_and, not_and_or, not_not] at hiU
      rw [Finset.mem_union]
      rcases hiU with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Finset.mem_image.mpr ⟨π i, h2, by simp⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le A (A.image π.symm)
    have h3 : (A.image π.symm).card ≤ A.card := Finset.card_image_le
    have h4 : (S \ U).card + U.card = S.card := Finset.card_sdiff_add_card_eq_card hUS
    omega
  let p := U.card
  let emb : Fin p ↪o Fin N := U.orderEmbOfFin rfl
  let row : Fin p → Fin N := fun i => emb i
  let col : Fin p → Fin N := fun i => π (emb i)
  have hrow_inj : Function.Injective row := emb.injective
  have hcol_inj : Function.Injective col := π.injective.comp emb.injective
  have hrow_mem : ∀ i : Fin p, row i ∈ U := fun i => U.orderEmbOfFin_mem rfl i
  let F : Fin N → Fin N → Bool := fun x y => xor (x.val.testBit (y.val % r)) (xor (f x) (g y))
  have hTF : ∀ i j : Fin p, T (row i) (col j) = F (row i) (col j) := by
    intro i j
    have hi := (Finset.mem_filter.mp (hrow_mem i)).2.1
    have hj := (Finset.mem_filter.mp (hrow_mem j)).2.2
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    dsimp only [T, F, G]
    have hnot : ¬ ((row i).val < h ∨ (col j).val < h) := not_or.mpr ⟨hi, hj⟩
    simp only [hnot, ↓reduceIte]
  have herr_le : ((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).card ≤ e := by
    apply Finset.card_le_card_of_injOn (fun z => (z.1, π z.2))
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact Ne.symm hz.2
    · intro x _ y _ hxy
      have h1 := congrArg Prod.fst hxy
      have h2 := π.injective (congrArg Prod.snd hxy)
      exact Prod.ext h1 h2
  have hdis_eq :
      (Finset.univ.filter (fun z : Fin p × Fin p => z.1 < z.2 ∧ F (row z.1) (col z.2) ≠ F (row z.2) (col z.1))).card =
      ((U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))).card := by
    apply Finset.card_bij (fun z _ => (row z.1, row z.2))
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hz ⊢
      refine ⟨⟨hrow_mem z.1, hrow_mem z.2⟩, emb.lt_iff_lt.mpr hz.1, ?_⟩
      simpa only [row, col, hTF] using hz.2
    · intro x _ y _ hxy
      exact Prod.ext (hrow_inj (congrArg Prod.fst hxy)) (hrow_inj (congrArg Prod.snd hxy))
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_product] at hw
      have hrange := U.range_orderEmbOfFin rfl
      have hw1 : w.1 ∈ Set.range emb := by rw [hrange]; exact hw.1.1
      have hw2 : w.2 ∈ Set.range emb := by rw [hrange]; exact hw.1.2
      obtain ⟨i, hi⟩ := hw1
      obtain ⟨j, hj⟩ := hw2
      refine ⟨(i, j), ?_, Prod.ext hi hj⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨emb.lt_iff_lt.mp (by rw [hi, hj]; exact hw.2.1), ?_⟩
      rw [← hTF i j, ← hTF j i]
      dsimp only [row, col]
      rw [hi, hj]
      exact hw.2.2
  have hconf_U := hconf U hUS
  have horient := Hist.Histogram25855.orientation ha hak row col hrow_inj hcol_inj f g
  have hlabels : 32 * N ≤ p + 15 * b + 50 + 44 * (e / v) + h + h := by
    change 32 * N ≤ 15 * b + 50 + 44 * (e / v) + S.card at hS
    omega
  have hconflicts : p ^ 2 ≤ 4 * (e + 0) + (4 + 4 * 0 + 2 * a * (N / r)) * p := by
    dsimp only at horient
    change p ^ 2 ≤ 4 * (Finset.univ.filter (fun z : Fin p × Fin p =>
      z.1 < z.2 ∧ F (row z.1) (col z.2) ≠ F (row z.2) (col z.1))).card + 2 * a * (N / r) * p at horient
    rw [hdis_eq] at horient
    change ((U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))).card ≤
      p + ((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).card at hconf_U
    nlinarith
  have hfin := Hist.Arithmetic25855.finish p N b (e / v) h h 0 a (N / r) e 0 hlabels hconflicts
  have heq1 : 15 * b + 54 + 44 * (e / v) + h + h + 4 * 0 + 2 * a * (N / r) =
      15 * b + 54 + 44 * (e / v) + 2 * h + 2 * a * (N / r) := by ring
  rw [heq1, add_zero] at hfin
  exact hfin

end Assembly

end PEqualNP.Outside.L_meta_25811_aux

theorem PEqualNP.Outside.L_meta_25811 : (∀ (k a d : ℕ), (0 < a ∧ 2^a ≤ k ∧ 0 < d ∧ 2*d+1 ≤ k) →
  let N := 2^k
  let m := k-d
  let h := 2^m
  let δ := 2^(m-2)
  let low := fun (i j : Fin N) =>
    ((Finset.range m).filter (fun l => i.val.testBit l && j.val.testBit l)).card
  let cross := fun (i j : Fin N) => ((Finset.range d).filter (fun l =>
    i.val.testBit (m+l) && j.val.testBit 0 && j.val.testBit (l+1))).card
  let tag := fun (left right : Fin N) => (low left right + cross left right + cross right left)%2 == 1
  let r := 2^a
  let G := fun (x y : Fin N) => if x.val < h ∨ y.val < h then tag x y
    else x.val.testBit (y.val % r)
  PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) G)
    (3*(r-1)+8*k+16*d+8) ∧
  ∀ (f g : Fin N → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) →
    let e := (Finset.univ.filter (fun p : Fin N × Fin N =>
      C.eval (PEqualNP.Represents.oneEach p.1 p.2) ≠
        xor (G p.1 p.2) (xor (f p.1) (g p.2)))).card
    let b := C.gates.countP (fun gate => gate.inputs.length == 2)
    ∀ v : ℕ, 0 < v → 17+2*(v-1) ≤ δ →
      (32*N-(15*b+54+44*(e/v)+2*h+2*a*(N/r)))^2 ≤ 4*e) :=
  PEqualNP.Outside.L_meta_25811_aux.Assembly.main_proof
