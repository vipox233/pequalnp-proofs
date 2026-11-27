import PEqualNP.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.CharP.Two

namespace PEqualNP.Outside.L_meta_25879_aux.Extraction

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

end PEqualNP.Outside.L_meta_25879_aux.Extraction

namespace PEqualNP.Outside.L_meta_25879_aux

theorem extraction : ∀ n : ℕ, 2 ≤ n →
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
  obtain ⟨bad, hfar, hbad, hcount⟩ := PEqualNP.Outside.L_meta_25879_aux.Extraction.marked_results
    T C hg H (fun _ _ => rfl) v hv hrow hcol
  obtain ⟨π,S,p,hS,hcap,hsym⟩ := PEqualNP.Outside.L_meta_25879_aux.Extraction.structural
    (PEqualNP.Outside.L_meta_25879_aux.Extraction.ofCircuit (n+n) C) bad hfar
    (fun _ => PEqualNP.Outside.L_meta_25879_aux.Extraction.codeAt_raw) hbad
    (PEqualNP.Outside.L_meta_25879_aux.Extraction.ofCircuit_bin _ C hg)
  have hHsym : ∀ i ∈ S, ∀ j ∈ S, p i ≠ p j → H i (π j) = H j (π i) := by
    intro i hi j hj hp
    simpa only [PEqualNP.Outside.L_meta_25879_aux.Extraction.view_left C hg] using hsym i hi j hj hp
  refine ⟨π,S,p,?_,hcap,hHsym,?_⟩
  · change 32 * n ≤ 15 * b + 50 + 44 * (e / v) + S.card
    change bad.card ≤ 2 * (e / v) at hcount
    change 32 * n ≤ 15 * b + 50 + 22 * bad.card + S.card at hS
    omega
  · exact PEqualNP.Outside.L_meta_25879_aux.Extraction.conflict_bound T H π S p hcap hHsym

end PEqualNP.Outside.L_meta_25879_aux

namespace PEqualNP.Outside.L_meta_25879_aux.Moment

def dfact (m : ℕ) : ℕ := ∏ i ∈ Finset.range m, (2 * i + 1)

lemma dfact_pos (m : ℕ) : 0 < dfact m := by
  unfold dfact
  apply Finset.prod_pos
  intro i _
  omega

lemma two_mul_factorial_eq (m : ℕ) : (2 * m).factorial = 2 ^ m * m.factorial * dfact m := by
  induction m with
  | zero => simp [dfact]
  | succ m ih =>
    have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [h1, Nat.factorial_succ, Nat.factorial_succ, ih]
    have hdf : dfact (m + 1) = dfact m * (2 * m + 1) := Finset.prod_range_succ _ m
    rw [hdf, pow_succ, Nat.factorial_succ]
    ring

lemma choose_two_mul_dfact_le (m r : ℕ) (hr : r ≤ m) :
    Nat.choose (2 * m) (2 * r) * dfact r ≤ dfact m * Nat.choose m r := by
  have heq : Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r) = dfact m * Nat.choose m r := by
    have hpos : 0 < 2 ^ m * r.factorial * (m - r).factorial := by
      positivity
    apply Nat.eq_of_mul_eq_mul_left hpos
    have h1 : 2 ^ m * r.factorial * (m - r).factorial *
        (Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r)) =
        Nat.choose (2 * m) (2 * r) * (2 * r).factorial * (2 * (m - r)).factorial := by
      rw [two_mul_factorial_eq r, two_mul_factorial_eq (m - r)]
      have hp : 2 ^ r * 2 ^ (m - r) = 2 ^ m := by
        rw [← pow_add, Nat.add_sub_cancel' hr]
      calc 2 ^ m * r.factorial * (m - r).factorial *
              (Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r))
          = (2 ^ r * 2 ^ (m - r)) * r.factorial * (m - r).factorial *
              (Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r)) := by rw [hp]
        _ = Nat.choose (2 * m) (2 * r) * (2 ^ r * r.factorial * dfact r) *
              (2 ^ (m - r) * (m - r).factorial * dfact (m - r)) := by ring
    have h2 : Nat.choose (2 * m) (2 * r) * (2 * r).factorial * (2 * (m - r)).factorial =
        (2 * m).factorial := by
      have hsub : 2 * m - 2 * r = 2 * (m - r) := by omega
      rw [← hsub]
      exact Nat.choose_mul_factorial_mul_factorial (by omega)
    have h3 : 2 ^ m * r.factorial * (m - r).factorial * (dfact m * Nat.choose m r) =
        (2 * m).factorial := by
      rw [two_mul_factorial_eq m]
      have hcm := Nat.choose_mul_factorial_mul_factorial hr
      calc 2 ^ m * r.factorial * (m - r).factorial * (dfact m * Nat.choose m r)
          = 2 ^ m * (Nat.choose m r * r.factorial * (m - r).factorial) * dfact m := by ring
        _ = 2 ^ m * m.factorial * dfact m := by rw [hcm]
    rw [h1, h2, h3]
  have hd : 1 ≤ dfact (m - r) := dfact_pos (m - r)
  calc Nat.choose (2 * m) (2 * r) * dfact r
      = Nat.choose (2 * m) (2 * r) * dfact r * 1 := (Nat.mul_one _).symm
    _ ≤ Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r) := Nat.mul_le_mul_left _ hd
    _ = dfact m * Nat.choose m r := heq

lemma nat_le_of_pow_le_pow {a b n : ℕ} (hn : n ≠ 0) (h : a ^ n ≤ b ^ n) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  exact Nat.not_lt.mpr h (Nat.pow_lt_pow_left hlt hn)

lemma dfact_le_pow (a : ℕ) : dfact a ≤ a ^ a := by
  have hsq : (dfact a) ^ 2 ≤ (a ^ a) ^ 2 := by
    have hrev : dfact a = ∏ i ∈ Finset.range a, (2 * (a - 1 - i) + 1) := by
      unfold dfact
      rw [← Finset.prod_range_reflect (fun i => 2 * i + 1) a]
    have hpair : (dfact a) ^ 2 = ∏ i ∈ Finset.range a, ((2 * i + 1) * (2 * (a - 1 - i) + 1)) := by
      rw [sq]
      conv_lhs => rhs; rw [hrev]
      unfold dfact
      rw [← Finset.prod_mul_distrib]
    rw [hpair]
    have hbound : ∏ i ∈ Finset.range a, ((2 * i + 1) * (2 * (a - 1 - i) + 1)) ≤
        ∏ _i ∈ Finset.range a, a ^ 2 := by
      apply Finset.prod_le_prod
      intro i hi
      have hia : i < a := Finset.mem_range.mp hi
      have hsum : (2 * i + 1) + (2 * (a - 1 - i) + 1) = 2 * a := by omega
      have hle : 4 * ((2 * i + 1) * (2 * (a - 1 - i) + 1)) ≤ ((2 * i + 1) + (2 * (a - 1 - i) + 1)) ^ 2 := by
        zify
        nlinarith [sq_nonneg ((2 * (i : ℤ) + 1) - (2 * ((a - 1 - i : ℕ) : ℤ) + 1))]
      rw [hsum] at hle
      have : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
      omega
    calc ∏ i ∈ Finset.range a, ((2 * i + 1) * (2 * (a - 1 - i) + 1))
        ≤ ∏ _i ∈ Finset.range a, a ^ 2 := hbound
      _ = (a ^ 2) ^ a := by simp
      _ = (a ^ a) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  exact nat_le_of_pow_le_pow (by omega : 2 ≠ 0) hsq

lemma even_pow_add_sub (X a : ℤ) (m : ℕ) :
    (X + a) ^ (2 * m) + (X - a) ^ (2 * m) =
      2 * ∑ r ∈ Finset.range (m + 1), (Nat.choose (2 * m) (2 * r) : ℤ) * X ^ (2 * r) * a ^ (2 * (m - r)) := by
  have h1 : (X + a) ^ (2 * m) =
      ∑ j ∈ Finset.range (2 * m + 1), X ^ j * a ^ (2 * m - j) * (Nat.choose (2 * m) j : ℤ) := by
    exact add_pow X a (2 * m)
  have h2 : (X - a) ^ (2 * m) =
      ∑ j ∈ Finset.range (2 * m + 1), X ^ j * (-a) ^ (2 * m - j) * (Nat.choose (2 * m) j : ℤ) := by
    rw [sub_eq_add_neg]; exact add_pow X (-a) (2 * m)
  rw [h1, h2, ← Finset.sum_add_distrib]
  have hcomb : ∀ j ∈ Finset.range (2 * m + 1),
      X ^ j * a ^ (2 * m - j) * (Nat.choose (2 * m) j : ℤ) +
      X ^ j * (-a) ^ (2 * m - j) * (Nat.choose (2 * m) j : ℤ) =
      if Even j then 2 * ((Nat.choose (2 * m) j : ℤ) * X ^ j * a ^ (2 * m - j)) else 0 := by
    intro j hj
    have hjle : j ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hev : Even j
    · simp only [hev, ite_true]
      rcases hev with ⟨r, rfl⟩
      have hsub : 2 * m - (r + r) = 2 * (m - r) := by omega
      rw [hsub, pow_mul, pow_mul, neg_sq]
      ring
    · simp only [hev, ite_false]
      have hodd : Odd (2 * m - j) := by
        rw [Nat.not_even_iff_odd] at hev
        rcases hev with ⟨r, rfl⟩
        exact ⟨m - r - 1, by omega⟩
      rw [Odd.neg_pow hodd]
      ring
  rw [Finset.sum_congr rfl hcomb, ← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_bij (fun j _ => j / 2) ?_ ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjr, _⟩
    have hjlt : j < 2 * m + 1 := Finset.mem_range.mp hjr
    exact Finset.mem_range.mpr (by omega)
  · intro j₁ hj₁ j₂ hj₂ hdiv
    rcases (Finset.mem_filter.mp hj₁).2 with ⟨r₁, rfl⟩
    rcases (Finset.mem_filter.mp hj₂).2 with ⟨r₂, rfl⟩
    omega
  · intro r hr
    have hrm : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    refine ⟨2 * r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨r, by omega⟩⟩, by omega⟩
  · intro j hj
    rcases (Finset.mem_filter.mp hj).2 with ⟨r, rfl⟩
    have hdiv : (r + r) / 2 = r := by omega
    have hr2 : r + r = 2 * r := by omega
    have hsub : 2 * m - 2 * r = 2 * (m - r) := by omega
    rw [hdiv, hr2, hsub]

def bitSign (b : Bool) : ℤ := if b then -1 else 1

lemma bitSign_xor (a b : Bool) : bitSign (Bool.xor a b) = bitSign a * bitSign b := by
  cases a <;> cases b <;> rfl

lemma bitSign_sq (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> rfl

lemma cube_moment_bool (k : ℕ) : ∀ (m : ℕ) (v : Fin k → ℤ),
    (∑ z : Fin k → Bool, (∑ l : Fin k, v l * bitSign (z l)) ^ (2 * m)) ≤
      (2 ^ k : ℤ) * (dfact m : ℤ) * (∑ l : Fin k, (v l) ^ 2) ^ m := by
  induction k with
  | zero =>
    intro m v
    cases m with
    | zero => simp [dfact]
    | succ m =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_pow (by omega : 2 * (m + 1) ≠ 0),
        Finset.sum_const_zero, zero_pow (by omega : m + 1 ≠ 0), mul_zero, le_refl]
  | succ k ih =>
    intro m v
    let eSplit : ((Fin k → Bool) × Bool) ≃ (Fin (k + 1) → Bool) :=
      { toFun := fun p => Fin.snoc p.1 p.2,
        invFun := fun z => (Fin.init z, z (Fin.last k)),
        left_inv := fun ⟨z', b⟩ => by
          ext i
          · simp [Fin.init_snoc]
          · simp [Fin.snoc_last],
        right_inv := fun z => Fin.snoc_init_self z }
    rw [← Equiv.sum_comp eSplit, Fintype.sum_prod_type]
    have hinner : ∀ z' : Fin k → Bool,
        (∑ b : Bool, (∑ l : Fin (k + 1), v l * bitSign (eSplit (z', b) l)) ^ (2 * m)) =
        ((∑ l : Fin k, v l.castSucc * bitSign (z' l)) + v (Fin.last k)) ^ (2 * m) +
        ((∑ l : Fin k, v l.castSucc * bitSign (z' l)) - v (Fin.last k)) ^ (2 * m) := by
      intro z'
      rw [Fintype.sum_bool]
      have htrue : (∑ l : Fin (k + 1), v l * bitSign (eSplit (z', true) l)) =
          (∑ l : Fin k, v l.castSucc * bitSign (z' l)) - v (Fin.last k) := by
        rw [Fin.sum_univ_castSucc]
        simp only [eSplit, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last, bitSign, ite_true]
        ring
      have hfalse : (∑ l : Fin (k + 1), v l * bitSign (eSplit (z', false) l)) =
          (∑ l : Fin k, v l.castSucc * bitSign (z' l)) + v (Fin.last k) := by
        rw [Fin.sum_univ_castSucc]
        simp only [eSplit, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last, bitSign, Bool.false_eq_true, ite_false]
        ring
      rw [htrue, hfalse, add_comm]
    simp_rw [hinner, even_pow_add_sub]
    rw [← Finset.mul_sum, Finset.sum_comm]
    set S : ℤ := ∑ l : Fin k, (v l.castSucc) ^ 2
    set a : ℤ := v (Fin.last k)
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hterm_le : ∀ r ∈ Finset.range (m + 1),
        (∑ z' : Fin k → Bool, (Nat.choose (2 * m) (2 * r) : ℤ) *
          (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r) * a ^ (2 * (m - r))) ≤
        (2 ^ k : ℤ) * (dfact m : ℤ) * ((Nat.choose m r : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) := by
      intro r hr
      have hrm : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hpull : (∑ z' : Fin k → Bool, (Nat.choose (2 * m) (2 * r) : ℤ) *
          (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r) * a ^ (2 * (m - r))) =
          ((Nat.choose (2 * m) (2 * r) : ℤ) * a ^ (2 * (m - r))) *
          ∑ z' : Fin k → Bool, (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro z' _; ring
      rw [hpull]
      have hca_nn : 0 ≤ (Nat.choose (2 * m) (2 * r) : ℤ) * a ^ (2 * (m - r)) := by
        apply mul_nonneg (Nat.cast_nonneg _)
        rw [pow_mul]; exact pow_nonneg (sq_nonneg a) _
      have hih := ih r (fun l => v l.castSucc)
      have hstep1 := mul_le_mul_of_nonneg_left hih hca_nn
      have hch : (Nat.choose (2 * m) (2 * r) : ℤ) * (dfact r : ℤ) ≤
          (dfact m : ℤ) * (Nat.choose m r : ℤ) := by
        exact_mod_cast choose_two_mul_dfact_le m r hrm
      have hpow_nn : 0 ≤ (2 ^ k : ℤ) * S ^ r * (a ^ 2) ^ (m - r) :=
        mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hS_nn _)) (pow_nonneg (sq_nonneg a) _)
      have hstep2 := mul_le_mul_of_nonneg_right hch hpow_nn
      have hsqa : a ^ (2 * (m - r)) = (a ^ 2) ^ (m - r) := pow_mul a 2 (m - r)
      calc ((Nat.choose (2 * m) (2 * r) : ℤ) * a ^ (2 * (m - r))) *
              ∑ z' : Fin k → Bool, (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r)
          ≤ ((Nat.choose (2 * m) (2 * r) : ℤ) * a ^ (2 * (m - r))) *
              ((2 ^ k : ℤ) * (dfact r : ℤ) * S ^ r) := hstep1
        _ = ((Nat.choose (2 * m) (2 * r) : ℤ) * (dfact r : ℤ)) *
              ((2 ^ k : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) := by rw [hsqa]; ring
        _ ≤ ((dfact m : ℤ) * (Nat.choose m r : ℤ)) *
              ((2 ^ k : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) := hstep2
        _ = (2 ^ k : ℤ) * (dfact m : ℤ) * ((Nat.choose m r : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) := by ring
    have hsum_le : (∑ r ∈ Finset.range (m + 1), ∑ z' : Fin k → Bool,
        (Nat.choose (2 * m) (2 * r) : ℤ) *
          (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r) * a ^ (2 * (m - r))) ≤
        ∑ r ∈ Finset.range (m + 1),
          (2 ^ k : ℤ) * (dfact m : ℤ) * ((Nat.choose m r : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) :=
      Finset.sum_le_sum hterm_le
    have hbinom : (∑ r ∈ Finset.range (m + 1),
        (Nat.choose m r : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) = (S + a ^ 2) ^ m := by
      rw [add_pow]
      apply Finset.sum_congr rfl; intro r _; ring
    have hS_full : (∑ l : Fin (k + 1), (v l) ^ 2) = S + a ^ 2 := Fin.sum_univ_castSucc _
    rw [← Finset.mul_sum, hbinom] at hsum_le
    rw [hS_full]
    calc 2 * ∑ r ∈ Finset.range (m + 1), ∑ z' : Fin k → Bool,
            (Nat.choose (2 * m) (2 * r) : ℤ) *
              (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r) * a ^ (2 * (m - r))
        ≤ 2 * ((2 ^ k : ℤ) * (dfact m : ℤ) * (S + a ^ 2) ^ m) :=
          mul_le_mul_of_nonneg_left hsum_le (by norm_num)
      _ = (2 ^ (k + 1) : ℤ) * (dfact m : ℤ) * (S + a ^ 2) ^ m := by rw [pow_succ]; ring

lemma fin_pow2_equiv_bits (k : ℕ) :
    Function.Bijective (fun (x : Fin (2 ^ k)) (l : Fin k) => x.val.testBit l.val) := by
  have hcard : Fintype.card (Fin (2 ^ k)) = Fintype.card (Fin k → Bool) := by
    simp
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, hcard⟩
  intro x y hxy
  ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact congrFun hxy ⟨i, hi⟩
  · have hx : x.val < 2 ^ i := lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    have hy : y.val < 2 ^ i := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

lemma cube_moment_fin (k m : ℕ) (v : Fin k → ℤ) :
    (∑ z : Fin (2 ^ k), (∑ l : Fin k, v l * bitSign (z.val.testBit l.val)) ^ (2 * m)) ≤
      (2 ^ k : ℤ) * (dfact m : ℤ) * (∑ l : Fin k, (v l) ^ 2) ^ m := by
  let e : Fin (2 ^ k) ≃ (Fin k → Bool) := Equiv.ofBijective _ (fin_pow2_equiv_bits k)
  have heq : (∑ z : Fin (2 ^ k), (∑ l : Fin k, v l * bitSign (z.val.testBit l.val)) ^ (2 * m)) =
      ∑ z : Fin k → Bool, (∑ l : Fin k, v l * bitSign (z l)) ^ (2 * m) :=
    Equiv.sum_comp e (fun z : Fin k → Bool => (∑ l : Fin k, v l * bitSign (z l)) ^ (2 * m))
  rw [heq]
  exact cube_moment_bool k m v

lemma chebyshev_pow {ι : Type*} (I : Finset ι) (w a : ι → ℚ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (ha : ∀ i ∈ I, 0 ≤ a i) (m : ℕ) :
    (∑ i ∈ I, w i * a i ^ m) * (∑ i ∈ I, w i * a i) ≤
      (∑ i ∈ I, w i) * (∑ i ∈ I, w i * a i ^ (m + 1)) := by
  have hdiff : 2 * ((∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1)) -
      (∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j)) =
      ∑ i ∈ I, ∑ j ∈ I, w i * w j * (a i ^ m - a j ^ m) * (a i - a j) := by
    have h1 : (∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1)) =
        ∑ i ∈ I, ∑ j ∈ I, w i * w j * a j ^ (m + 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have h2 : (∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1)) =
        ∑ i ∈ I, ∑ j ∈ I, w i * w j * a i ^ (m + 1) := by
      rw [h1, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    have h3 : (∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j) =
        ∑ i ∈ I, ∑ j ∈ I, w i * w j * a i ^ m * a j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have h4 : (∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j) =
        ∑ i ∈ I, ∑ j ∈ I, w i * w j * a j ^ m * a i := by
      rw [h3, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    have hL : 2 * ((∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1)) -
        (∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j)) =
        ((∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1)) + (∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1))) -
        ((∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j) + (∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j)) := by
      ring
    rw [hL]
    conv_lhs =>
      arg 1
      arg 1; rw [h1]
    conv_lhs =>
      arg 1
      arg 2; rw [h2]
    conv_lhs =>
      arg 2
      arg 1; rw [h3]
    conv_lhs =>
      arg 2
      arg 2; rw [h4]
    simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [pow_succ, pow_succ]
    ring
  have hnn : 0 ≤ ∑ i ∈ I, ∑ j ∈ I, w i * w j * (a i ^ m - a j ^ m) * (a i - a j) := by
    apply Finset.sum_nonneg; intro i hi
    apply Finset.sum_nonneg; intro j hj
    have hwi := hw i hi
    have hwj := hw j hj
    have hai := ha i hi
    have haj := ha j hj
    have hprod : 0 ≤ (a i ^ m - a j ^ m) * (a i - a j) := by
      rcases le_total (a i) (a j) with hle | hle
      · have hpm : a i ^ m ≤ a j ^ m := pow_le_pow_left₀ hai hle m
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hpm) (sub_nonpos.mpr hle)
      · have hpm : a j ^ m ≤ a i ^ m := pow_le_pow_left₀ haj hle m
        exact mul_nonneg (sub_nonneg.mpr hpm) (sub_nonneg.mpr hle)
    have : w i * w j * (a i ^ m - a j ^ m) * (a i - a j) =
        (w i * w j) * ((a i ^ m - a j ^ m) * (a i - a j)) := by ring
    rw [this]
    exact mul_nonneg (mul_nonneg hwi hwj) hprod
  linarith

lemma weighted_pow_mean {ι : Type*} (I : Finset ι) (w a : ι → ℚ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (ha : ∀ i ∈ I, 0 ≤ a i) :
    ∀ m : ℕ, 0 < m →
      (∑ i ∈ I, w i * a i) ^ m ≤ (∑ i ∈ I, w i) ^ (m - 1) * (∑ i ∈ I, w i * a i ^ m) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp
    | succ m =>
      have hih := ih (by omega)
      have hsum_nn : 0 ≤ ∑ i ∈ I, w i * a i := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (ha i hi))
      have hw_nn : 0 ≤ ∑ i ∈ I, w i := Finset.sum_nonneg hw
      have h1 : (∑ i ∈ I, w i * a i) ^ (m + 2) ≤
          (∑ i ∈ I, w i) ^ m * ((∑ i ∈ I, w i * a i ^ (m + 1)) * (∑ i ∈ I, w i * a i)) := by
        rw [pow_succ]
        calc (∑ i ∈ I, w i * a i) ^ (m + 1) * (∑ i ∈ I, w i * a i)
            ≤ ((∑ i ∈ I, w i) ^ m * (∑ i ∈ I, w i * a i ^ (m + 1))) * (∑ i ∈ I, w i * a i) :=
              mul_le_mul_of_nonneg_right hih hsum_nn
          _ = (∑ i ∈ I, w i) ^ m * ((∑ i ∈ I, w i * a i ^ (m + 1)) * (∑ i ∈ I, w i * a i)) := by ring
      have h2 := chebyshev_pow I w a hw ha (m + 1)
      calc (∑ i ∈ I, w i * a i) ^ (m + 2)
          ≤ (∑ i ∈ I, w i) ^ m * ((∑ i ∈ I, w i * a i ^ (m + 1)) * (∑ i ∈ I, w i * a i)) := h1
        _ ≤ (∑ i ∈ I, w i) ^ m * ((∑ i ∈ I, w i) * (∑ i ∈ I, w i * a i ^ (m + 2))) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg hw_nn m)
        _ = (∑ i ∈ I, w i) ^ (m + 1) * (∑ i ∈ I, w i * a i ^ (m + 2)) := by rw [pow_succ]; ring

lemma group_energy_bound {k : ℕ} (S : Finset (Fin (2 ^ k))) (w : Fin (2 ^ k) → ℤ)
    (hw : ∀ x ∈ S, w x = 1 ∨ w x = -1) (m : ℕ) (hm : 0 < m) :
    let M := fun l : Fin k => ∑ x ∈ S, w x * bitSign (x.val.testBit l.val)
    let L := ∑ l : Fin k, (M l) ^ 2
    L ^ m ≤ (2 ^ k : ℤ) * (dfact m : ℤ) * (S.card : ℤ) ^ (2 * m - 1) := by
  intro M L
  have hL_nn : 0 ≤ L := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hL0 : L = 0
  · rw [hL0, zero_pow (by omega : m ≠ 0)]
    positivity
  · have hL_pos : 0 < L := lt_of_le_of_ne hL_nn (Ne.symm hL0)
    let g : Fin (2 ^ k) → ℤ := fun z => ∑ l : Fin k, M l * bitSign (z.val.testBit l.val)
    have hL_eq : L = ∑ z ∈ S, w z * g z := by
      dsimp only [L, g]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      have : (∑ z ∈ S, w z * (M l * bitSign (z.val.testBit l.val))) =
          M l * ∑ z ∈ S, w z * bitSign (z.val.testBit l.val) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
      rw [this, sq]
    have hL_le_abs : L ≤ ∑ z ∈ S, |g z| := by
      rw [hL_eq]
      apply Finset.sum_le_sum
      intro z hz
      rcases hw z hz with h1 | h2
      · rw [h1, one_mul]; exact le_abs_self _
      · rw [h2, neg_one_mul]; exact neg_le_abs _
    have hL_pow : L ^ (2 * m) ≤ (S.card : ℤ) ^ (2 * m - 1) * ∑ z ∈ S, (g z) ^ (2 * m) := by
      have hq := weighted_pow_mean S (fun _ => (1 : ℚ)) (fun z => (|g z| : ℚ))
        (fun _ _ => zero_le_one) (fun z _ => by exact_mod_cast abs_nonneg (g z)) (2 * m) (by omega)
      have hL_q : (L : ℚ) ≤ ∑ z ∈ S, (|g z| : ℚ) := by exact_mod_cast hL_le_abs
      have hpow_q : (L : ℚ) ^ (2 * m) ≤ (∑ z ∈ S, (|g z| : ℚ)) ^ (2 * m) :=
        pow_le_pow_left₀ (by exact_mod_cast hL_nn) hL_q (2 * m)
      have h1 : (∑ z ∈ S, (1 : ℚ) * (|g z| : ℚ)) = ∑ z ∈ S, (|g z| : ℚ) := by simp
      have h2 : (∑ _z ∈ S, (1 : ℚ)) = (S.card : ℚ) := by simp
      have h3 : (∑ z ∈ S, (1 : ℚ) * (|g z| : ℚ) ^ (2 * m)) = ∑ z ∈ S, ((g z : ℚ) ^ (2 * m)) := by
        apply Finset.sum_congr rfl; intro z _
        rw [one_mul, pow_mul, pow_mul]
        have : (|g z| : ℚ) ^ 2 = (g z : ℚ) ^ 2 := by exact_mod_cast sq_abs (g z)
        rw [this]
      rw [h1, h2, h3] at hq
      have hcomb := le_trans hpow_q hq
      exact_mod_cast hcomb
    have hsum_le_all : (∑ z ∈ S, (g z) ^ (2 * m)) ≤ ∑ z : Fin (2 ^ k), (g z) ^ (2 * m) := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro z
      rw [pow_mul]; exact pow_nonneg (sq_nonneg _) m
    have hcube : (∑ z : Fin (2 ^ k), (g z) ^ (2 * m)) ≤ (2 ^ k : ℤ) * (dfact m : ℤ) * L ^ m :=
      cube_moment_fin k m M
    have hprod : L ^ m * L ^ m ≤ ((2 ^ k : ℤ) * (dfact m : ℤ) * (S.card : ℤ) ^ (2 * m - 1)) * L ^ m := by
      calc L ^ m * L ^ m = L ^ (2 * m) := by rw [← pow_add, two_mul]
        _ ≤ (S.card : ℤ) ^ (2 * m - 1) * ∑ z ∈ S, (g z) ^ (2 * m) := hL_pow
        _ ≤ (S.card : ℤ) ^ (2 * m - 1) * ∑ z : Fin (2 ^ k), (g z) ^ (2 * m) :=
            mul_le_mul_of_nonneg_left hsum_le_all (pow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ (S.card : ℤ) ^ (2 * m - 1) * ((2 ^ k : ℤ) * (dfact m : ℤ) * L ^ m) :=
            mul_le_mul_of_nonneg_left hcube (pow_nonneg (Nat.cast_nonneg _) _)
        _ = ((2 ^ k : ℤ) * (dfact m : ℤ) * (S.card : ℤ) ^ (2 * m - 1)) * L ^ m := by ring
    exact le_of_mul_le_mul_right hprod (pow_pos hL_pos m)

end PEqualNP.Outside.L_meta_25879_aux.Moment

namespace PEqualNP.Outside.L_meta_25879_aux

theorem spectral (k : ℕ) (addr : Fin (2^k) → Fin k) (π : Equiv.Perm (Fin (2^k)))
    (K : Finset (Fin (2^k))) (f g : Fin (2^k) → Bool) (e : ℕ)
    (hs : let B := fun x y : Fin (2^k) => Moment.bitSign (xor (x.val.testBit (addr (π y)).val) (xor (f x) (g y)))
          ((K.card:ℤ)^2 - 4*e) ≤ ∑ x ∈ K, ∑ y ∈ K, B x y * B y x) :
    ∀ a cap : ℕ, 0 < a → 2^k ≤ 2^a*cap → (∀ j, (K.filter (fun i => addr (π i) = j)).card ≤ cap) →
      K.card^2 ≤ 4*e + 2*a*cap*K.card := by
  let N := 2^k
  let h := K.card
  let count := fun (j : Fin k) => (K.filter (fun i => addr (π i) = j)).card
  have hcount_sum : ∑ j : Fin k, count j = h := by
    dsimp only [count, h]
    rw [← Finset.card_biUnion]
    · congr 1
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun ⟨_, hi, _⟩ => hi, fun hi => ⟨addr (π i), hi, rfl⟩⟩
    · intro j₁ _ j₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro i h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hpart1 : ∀ m : ℕ, 0 < m →
      (h ^ 2 - 4 * e) ^ m ≤ N * (∏ i ∈ Finset.range m, (2 * i + 1)) *
        h ^ (m - 1) * (∑ j : Fin k, (count j) ^ m) := by
    intro m hm
    by_cases htriv : h ^ 2 ≤ 4 * e
    · have h0 : h ^ 2 - 4 * e = 0 := Nat.sub_eq_zero_of_le htriv
      rw [h0, zero_pow (by omega : m ≠ 0)]
      exact Nat.zero_le _
    · push Not at htriv
      have hh_pos : 0 < h := by
        by_contra h0; have : h = 0 := by omega
        rw [this] at htriv; simp at htriv
      let σ := Moment.bitSign
      let T : Fin N → Fin N → ℤ := fun x y => σ (xor (x.val.testBit (addr (π y)).val) (xor (f x) (g y)))
      have hquad_ge : ((h : ℤ)^2 - 4*(e:ℤ)) ≤ ∑ x ∈ K, ∑ y ∈ K, T x y * T y x := hs
      let w : Fin N → ℤ := fun x => σ (f x) * σ (g x)
      let Kg : Fin k → Finset (Fin N) := fun j => K.filter (fun i => addr (π i) = j)
      let M : Fin k → Fin k → ℤ := fun j l => ∑ x ∈ Kg j, w x * σ (x.val.testBit l.val)
      let L : Fin k → ℤ := fun j => ∑ l : Fin k, (M j l) ^ 2
      have hT_fact : ∀ x ∈ K, ∀ y ∈ K,
          T x y * T y x = (w x * σ (x.val.testBit (addr (π y)).val)) *
            (w y * σ (y.val.testBit (addr (π x)).val)) := by
        intro x hx y hy
        dsimp only [T, w, σ]
        simp only [PEqualNP.Outside.L_meta_25879_aux.Moment.bitSign_xor]
        ring
      have htr_eq : (∑ x ∈ K, ∑ y ∈ K, T x y * T y x) = ∑ j : Fin k, ∑ l : Fin k, M j l * M l j := by
        have h1 : (∑ x ∈ K, ∑ y ∈ K, T x y * T y x) =
            ∑ x ∈ K, ∑ y ∈ K, (w x * σ (x.val.testBit (addr (π y)).val)) *
              (w y * σ (y.val.testBit (addr (π x)).val)) :=
          Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => hT_fact x hx y hy))
        rw [h1]
        have hpartK : K = Finset.univ.biUnion Kg := by
          ext x
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Kg, Finset.mem_filter]
          exact ⟨fun hx => ⟨addr (π x), hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩
        have hdisjK : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k))) Kg := by
          intro j₁ _ j₂ _ hne
          rw [Function.onFun, Finset.disjoint_left]
          intro x hx1 hx2
          exact hne ((Finset.mem_filter.mp hx1).2.symm.trans (Finset.mem_filter.mp hx2).2)
        conv_lhs =>
          rw [hpartK, Finset.sum_biUnion hdisjK]
        apply Finset.sum_congr rfl
        intro j _
        conv_lhs =>
          arg 2; ext x
          rw [Finset.sum_biUnion hdisjK]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        dsimp only [M]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        have hxj : addr (π x) = j := (Finset.mem_filter.mp hx).2
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        have hyl : addr (π y) = l := (Finset.mem_filter.mp hy).2
        rw [hxj, hyl]
      have htr_le : (∑ j : Fin k, ∑ l : Fin k, M j l * M l j) ≤ ∑ j : Fin k, L j := by
        have h2 : 2 * (∑ j : Fin k, ∑ l : Fin k, M j l * M l j) ≤ 2 * (∑ j : Fin k, L j) := by
          have hsym : (∑ j : Fin k, ∑ l : Fin k, (M l j) ^ 2) = ∑ j : Fin k, L j := by
            rw [Finset.sum_comm]
          have hL2 : 2 * (∑ j : Fin k, L j) = ∑ j : Fin k, ∑ l : Fin k, ((M j l) ^ 2 + (M l j) ^ 2) := by
            simp_rw [Finset.sum_add_distrib, hsym]
            dsimp only [L]; ring
          rw [hL2, Finset.mul_sum]
          apply Finset.sum_le_sum; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro l _
          nlinarith [sq_nonneg (M j l - M l j)]
        linarith
      have hL_sum_ge : ((h : ℤ) ^ 2 - 4 * (e : ℤ)) ≤ ∑ j : Fin k, L j := by
        linarith
      have hL_bd : ∀ j : Fin k, (L j) ^ m ≤
          (N : ℤ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℤ) * (count j : ℤ) ^ (2 * m - 1) := by
        intro j
        have hw1 : ∀ x ∈ Kg j, w x = 1 ∨ w x = -1 := fun x _ => by
          dsimp only [w, σ, PEqualNP.Outside.L_meta_25879_aux.Moment.bitSign]
          split_ifs <;> decide
        exact PEqualNP.Outside.L_meta_25879_aux.Moment.group_energy_bound (Kg j) w hw1 m hm
      have hL_zero : ∀ j : Fin k, count j = 0 → L j = 0 := by
        intro j hc0
        have hKe : Kg j = ∅ := Finset.card_eq_zero.mp hc0
        dsimp only [L, M]
        simp [hKe]
      set posJ := Finset.univ.filter (fun j : Fin k => 0 < count j)
      have hsum_posJ : ∑ j : Fin k, L j = ∑ j ∈ posJ, L j := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hnot
        have hc0 : count j = 0 := by
          have := Finset.mem_filter.not.mp hnot
          simp only [Finset.mem_univ, true_and] at this
          omega
        exact hL_zero j hc0
      have hcount_posJ : ∑ j ∈ posJ, count j = h := by
        rw [← hcount_sum]
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hnot
        have := Finset.mem_filter.not.mp hnot
        simp only [Finset.mem_univ, true_and] at this
        omega
      have hHolder_q : (∑ j ∈ posJ, (L j : ℚ)) ^ m ≤
          (h : ℚ) ^ (m - 1) * ∑ j ∈ posJ, (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1) := by
        have hq := PEqualNP.Outside.L_meta_25879_aux.Moment.weighted_pow_mean posJ
          (fun j => (count j : ℚ)) (fun j => (L j : ℚ) / (count j : ℚ))
          (fun j _ => Nat.cast_nonneg _)
          (fun j _ => div_nonneg (by exact_mod_cast (Finset.sum_nonneg (fun _ _ => sq_nonneg _) : (0 : ℤ) ≤ L j)) (Nat.cast_nonneg _))
          m hm
        have hL1 : (∑ j ∈ posJ, (count j : ℚ) * ((L j : ℚ) / (count j : ℚ))) = ∑ j ∈ posJ, (L j : ℚ) := by
          apply Finset.sum_congr rfl; intro j hj
          have hcpos : (count j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Finset.mem_filter.mp hj).2)
          exact mul_div_cancel₀ _ hcpos
        have hL2 : (∑ j ∈ posJ, (count j : ℚ)) = (h : ℚ) := by exact_mod_cast hcount_posJ
        have hL3 : (∑ j ∈ posJ, (count j : ℚ) * ((L j : ℚ) / (count j : ℚ)) ^ m) =
            ∑ j ∈ posJ, (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1) := by
          apply Finset.sum_congr rfl; intro j hj
          have hcpos : (count j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Finset.mem_filter.mp hj).2)
          rw [div_pow]
          have hpow : (count j : ℚ) ^ m = (count j : ℚ) * (count j : ℚ) ^ (m - 1) := by
            conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
            ring
          rw [hpow]
          field_simp [hcpos]
        rw [hL1, hL2, hL3] at hq
        exact hq
      have hterm_q : ∀ j ∈ posJ,
          (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1) ≤
          (N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) * (count j : ℚ) ^ m := by
        intro j hj
        have hcpos : (0 : ℚ) < (count j : ℚ) := Nat.cast_pos.mpr (Finset.mem_filter.mp hj).2
        have hpow_pos : (0 : ℚ) < (count j : ℚ) ^ (m - 1) := pow_pos hcpos _
        rw [div_le_iff₀ hpow_pos]
        have hbd_q : (L j : ℚ) ^ m ≤
            (N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) * (count j : ℚ) ^ (2 * m - 1) := by
          exact_mod_cast hL_bd j
        have hpow_eq : (count j : ℚ) ^ m * (count j : ℚ) ^ (m - 1) = (count j : ℚ) ^ (2 * m - 1) := by
          rw [← pow_add]; congr 1; omega
        calc (L j : ℚ) ^ m
            ≤ (N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) * (count j : ℚ) ^ (2 * m - 1) := hbd_q
          _ = (N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) * (count j : ℚ) ^ m *
                (count j : ℚ) ^ (m - 1) := by rw [← hpow_eq]; ring
      have hsum_q : (∑ j ∈ posJ, (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1)) ≤
          (N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) * ∑ j : Fin k, (count j : ℚ) ^ m := by
        calc ∑ j ∈ posJ, (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1)
            ≤ ∑ j ∈ posJ, (N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) * (count j : ℚ) ^ m :=
              Finset.sum_le_sum hterm_q
          _ = (N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) * ∑ j ∈ posJ, (count j : ℚ) ^ m := by
              rw [← Finset.mul_sum]
          _ ≤ (N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) * ∑ j : Fin k, (count j : ℚ) ^ m := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Finset.sum_le_univ_sum_of_nonneg
              intro j; positivity
      have hsub_q : ((h ^ 2 - 4 * e : ℕ) : ℚ) ≤ ∑ j ∈ posJ, (L j : ℚ) := by
        have hcast : ((h ^ 2 - 4 * e : ℕ) : ℤ) = (h : ℤ) ^ 2 - 4 * (e : ℤ) := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        have hle_z : ((h ^ 2 - 4 * e : ℕ) : ℤ) ≤ ∑ j ∈ posJ, L j := by
          rw [hcast, ← hsum_posJ]; exact hL_sum_ge
        exact_mod_cast hle_z
      have hfinal_q : ((h ^ 2 - 4 * e : ℕ) : ℚ) ^ m ≤
          (N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) *
            (h : ℚ) ^ (m - 1) * (∑ j : Fin k, (count j : ℚ) ^ m) := by
        calc ((h ^ 2 - 4 * e : ℕ) : ℚ) ^ m
            ≤ (∑ j ∈ posJ, (L j : ℚ)) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) hsub_q m
          _ ≤ (h : ℚ) ^ (m - 1) * ∑ j ∈ posJ, (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1) := hHolder_q
          _ ≤ (h : ℚ) ^ (m - 1) * ((N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) *
                ∑ j : Fin k, (count j : ℚ) ^ m) :=
              mul_le_mul_of_nonneg_left hsum_q (by positivity)
          _ = (N : ℚ) * (PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m : ℚ) *
                (h : ℚ) ^ (m - 1) * (∑ j : Fin k, (count j : ℚ) ^ m) := by ring
      have hfinal_nat : (h ^ 2 - 4 * e) ^ m ≤
          N * PEqualNP.Outside.L_meta_25879_aux.Moment.dfact m * h ^ (m - 1) * (∑ j : Fin k, (count j) ^ m) := by
        exact_mod_cast hfinal_q
      exact hfinal_nat
  intro a cap ha hNcap hcap
  change h ^ 2 ≤ 4 * e + 2 * a * cap * h
  by_cases hh0 : h = 0
  · rw [hh0]; simp
  · by_cases hle : h ^ 2 ≤ 4 * e
    · omega
    · have hp := hpart1 a ha
      have hdf : ∏ i ∈ Finset.range a, (2 * i + 1) ≤ a ^ a :=
        PEqualNP.Outside.L_meta_25879_aux.Moment.dfact_le_pow a
      have hsum_cap : ∑ j : Fin k, (count j) ^ a ≤ h * cap ^ (a - 1) := by
        calc ∑ j : Fin k, (count j) ^ a
            = ∑ j : Fin k, count j * (count j) ^ (a - 1) := by
              apply Finset.sum_congr rfl; intro j _
              conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
              ring
          _ ≤ ∑ j : Fin k, count j * cap ^ (a - 1) := by
              apply Finset.sum_le_sum; intro j _
              exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hcap j) _)
          _ = (∑ j : Fin k, count j) * cap ^ (a - 1) := (Finset.sum_mul _ _ _).symm
          _ = h * cap ^ (a - 1) := by rw [hcount_sum]
      have hpow_le : (h ^ 2 - 4 * e) ^ a ≤ (2 * a * cap * h) ^ a := by
        have h1 : N * (∏ i ∈ Finset.range a, (2 * i + 1)) * h ^ (a - 1) * (∑ j : Fin k, (count j) ^ a) ≤
            (2 ^ a * cap) * a ^ a * h ^ (a - 1) * (h * cap ^ (a - 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hNcap hdf) le_rfl) hsum_cap
        have h2 : (2 ^ a * cap) * a ^ a * h ^ (a - 1) * (h * cap ^ (a - 1)) = (2 * a * cap * h) ^ a := by
          have hhc : h ^ (a - 1) * h = h ^ a := by
            conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
          have hcc : cap * cap ^ (a - 1) = cap ^ a := by
            conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
            ring
          calc (2 ^ a * cap) * a ^ a * h ^ (a - 1) * (h * cap ^ (a - 1))
              = 2 ^ a * a ^ a * (cap * cap ^ (a - 1)) * (h ^ (a - 1) * h) := by ring
            _ = 2 ^ a * a ^ a * cap ^ a * h ^ a := by rw [hcc, hhc]
            _ = (2 * a * cap * h) ^ a := by rw [mul_pow, mul_pow, mul_pow]
        exact le_trans hp (h2 ▸ h1)
      have hsub_le : h ^ 2 - 4 * e ≤ 2 * a * cap * h :=
        PEqualNP.Outside.L_meta_25879_aux.Moment.nat_le_of_pow_le_pow (by omega : a ≠ 0) hpow_le
      omega

end PEqualNP.Outside.L_meta_25879_aux

namespace PEqualNP.Outside.L_meta_25879_aux

lemma occurrence {α : Type*} [DecidableEq α] (G : Finset α) (x : α) (hx : x ∈ G) (t : ℕ) :
    G.card * ((G.powersetCard t).filter (fun D => x ∈ D)).card = t * (G.powersetCard t).card := by
  cases t with
  | zero => simp
  | succ t =>
    have h := Finset.card_filter_powersetCard_subset ({x} : Finset α) G (t+1) (by simpa) (by simp)
    simp only [Finset.singleton_subset_iff, Finset.card_singleton] at h
    rw [h, Finset.card_powersetCard]
    have hg : G.card ≠ 0 := (Finset.card_pos.mpr ⟨x,hx⟩).ne'
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hg
    rw [hn]
    simpa [Nat.mul_comm] using Nat.add_one_mul_choose_eq n t

lemma sum_ite_pair {α : Type*} (S : Finset α) (p : α → Prop) [DecidablePred p] (v w : ℝ) :
    (∑ D ∈ S, if p D then v else w) = S.card * w + ((S.filter p).card : ℝ) * (v-w) := by
  classical
  calc
    _ = ∑ D ∈ S, (w + if p D then v-w else 0) := by
      apply Finset.sum_congr rfl
      intro D _
      by_cases h : p D <;> simp [h]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [mul_sub]

lemma slice_sum {α : Type*} [DecidableEq α] (G : Finset α) (x : α) (t : ℕ) (v w : ℝ) :
    (G.card : ℝ) * (∑ D ∈ G.powersetCard t, if x ∈ D then v else w) =
      ((G.powersetCard t).card : ℝ) * (((G.card : ℝ) - t) * w + t * (if x ∈ G then v else w)) := by
  classical
  by_cases hx : x ∈ G
  · have hh : (G.card : ℝ) * (((G.powersetCard t).filter (fun D => x ∈ D)).card : ℝ) =
        (t : ℝ) * ((G.powersetCard t).card : ℝ) := by exact_mod_cast occurrence G x hx t
    rw [sum_ite_pair, if_pos hx]
    linear_combination (v-w) * hh
  · have he : ∀ D ∈ G.powersetCard t, x ∉ D := fun _ h h' => hx ((Finset.mem_powersetCard.mp h).1 h')
    rw [if_neg hx]
    calc
      _ = (G.card : ℝ) * (∑ _D ∈ G.powersetCard t, w) := by
        congr 1
        apply Finset.sum_congr rfl
        intro D hD
        exact if_neg (he D hD)
      _ = _ := by simp; ring

lemma expected_sum {α β : Type*} [DecidableEq α] (G : Finset α) (t : ℕ) (U : Finset β)
    (key : β → α) (v w : β → ℝ) :
    (G.card : ℝ) * (∑ D ∈ G.powersetCard t, ∑ z ∈ U, if key z ∈ D then v z else w z) =
      ((G.powersetCard t).card : ℝ) * (((G.card : ℝ)-t) * (∑ z ∈ U, w z) +
        t * (∑ z ∈ U, if key z ∈ G then v z else w z)) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  simp_rw [slice_sum]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

def discrepancy {β : Type*} [Fintype β] (key : β → ℕ) (H base : β → Bool) (D : Finset ℕ) : ℕ :=
  (Finset.univ.filter (fun z => H z ≠ xor (base z) (decide (key z ∈ D)))).card

lemma discrepancy_sum {β : Type*} [Fintype β] (key : β → ℕ) (H base : β → Bool) (D : Finset ℕ) :
    (discrepancy key H base D : ℝ) = ∑ z : β, if key z ∈ D then
      (if H z = base z then (1:ℝ) else 0) else (if H z = base z then 0 else 1) := by
  rw [discrepancy, ← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : key z ∈ D <;> cases H z <;> cases base z <;> simp [h]

lemma discrepancy_mean {β : Type*} [Fintype β] (key : β → ℕ) (H base : β → Bool) (G : Finset ℕ) (t : ℕ) :
    (G.card : ℝ) * (∑ D ∈ G.powersetCard t, (discrepancy key H base D : ℝ)) =
      ((G.powersetCard t).card : ℝ) * (((G.card : ℝ)-t) * (discrepancy key H base ∅ : ℝ) +
        t * (discrepancy key H base G : ℝ)) := by
  simp_rw [discrepancy_sum]
  simpa only [Finset.notMem_empty, ite_false] using
    expected_sum G t (Finset.univ : Finset β) key
      (fun z => if H z = base z then (1:ℝ) else 0) (fun z => if H z = base z then 0 else 1)

lemma combine_means {α : Type*} (S : Finset α) (q t : ℕ) {l : ℕ} (p : Fin l → ℝ)
    (e : Fin l → α → ℝ) (x y : Fin l → ℝ)
    (h : ∀ i, (q : ℝ) * (∑ D ∈ S, e i D) = (S.card : ℝ) * (((q : ℝ)-t) * x i + t * y i)) :
    (q : ℝ) * (∑ D ∈ S, ∑ i, p i * e i D) =
      (S.card : ℝ) * (((q : ℝ)-t) * (∑ i, p i * x i) + t * (∑ i, p i * y i)) := by
  rw [Finset.sum_comm, Finset.mul_sum]
  calc
    _ = ∑ i, p i * ((q : ℝ) * ∑ D ∈ S, e i D) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum]; ring
    _ = ∑ i, (S.card : ℝ) * (((q : ℝ)-t) * (p i*x i) + t * (p i*y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [h]; ring
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

lemma sampled_max {α : Type*} (S : Finset α) (hS : S.Nonempty) (q t n : ℕ) (hQ : 0 < q)
    (ht : t ≤ q) (e : α → ℝ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : (n : ℝ)*q ≤ x+y)
    (hm : (q : ℝ) * (∑ D ∈ S, e D) = (S.card : ℝ) * (((q : ℝ)-t)*x+t*y)) :
    ∃ D ∈ S, ((n * min t (q-t) : ℕ) : ℝ) ≤ e D ∧
      (q < 2*t → (n : ℝ)*q < 128*y →
        ((128*(n*(q-t))+n*(2*t-q) : ℕ) : ℝ) < 128*e D) := by
  obtain ⟨D, hmD, hmax⟩ := S.exists_max_image e hS
  have hsum : ∑ d ∈ S, e d ≤ (S.card : ℝ)*e D := by
    simpa only [nsmul_eq_mul] using S.sum_le_card_nsmul e (e D) hmax
  have hq : (0:ℝ) < q := by exact_mod_cast hQ
  have hs : (0:ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have he : (((q : ℝ)-t)*x+t*y) ≤ q * e D := by
    apply le_of_mul_le_mul_left (a := (S.card:ℝ)) _ hs
    rw [← hm]
    calc
      _ ≤ (q : ℝ) * ((S.card:ℝ)*e D) := mul_le_mul_of_nonneg_left hsum hq.le
      _ = _ := by ring
  have ht' : (t:ℝ) ≤ q := by exact_mod_cast ht
  have h0 : (0:ℝ) ≤ t := by positivity
  refine ⟨D, hmD, ?_, ?_⟩
  · apply le_of_mul_le_mul_left (a := (q:ℝ)) _ hq
    by_cases hsmall : 2*t ≤ q
    · rw [min_eq_left (by omega), Nat.cast_mul]
      have h' : (2:ℝ)*t ≤ q := by exact_mod_cast hsmall
      nlinarith only [he, mul_nonneg (sub_nonneg.mpr h') hx, mul_le_mul_of_nonneg_left hxy h0]
    · rw [min_eq_right (by omega), Nat.cast_mul, Nat.cast_sub ht]
      have h' : (q:ℝ) ≤ 2*t := by exact_mod_cast (show q ≤ 2*t by omega)
      nlinarith only [he, mul_nonneg (sub_nonneg.mpr h') hy,
        mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr ht')]
  · intro hlarge hstrict
    have hl : (q:ℝ) < 2*t := by exact_mod_cast hlarge
    push_cast [Nat.cast_sub ht, Nat.cast_sub hlarge.le]
    apply lt_of_mul_lt_mul_left (a := (q:ℝ)) _ hq.le
    nlinarith only [he, mul_lt_mul_of_pos_left hstrict (sub_pos.mpr hl),
      mul_le_mul_of_nonneg_left hxy (sub_nonneg.mpr ht')]

lemma xor_fibres (k : ℕ) (D : Finset ℕ) (hD : D ⊆ Finset.range (2^k)) :
    (Finset.univ.filter (fun z : Fin (2^k) × Fin (2^k) => z.1.val ^^^ z.2.val ∈ D)).card = 2^k * D.card := by
  let S := (Finset.univ : Finset (Fin (2^k))) ×ˢ D
  have bound (p : Fin (2^k) × ℕ) (h : p ∈ S) : p.1.val ^^^ p.2 < 2 ^ k :=
    Nat.xor_lt_two_pow p.1.isLt (Finset.mem_range.mp (hD (Finset.mem_product.mp h).2))
  have twice (x y : ℕ) : x ^^^ (x ^^^ y) = y := by rw [← Nat.xor_assoc]; simp
  calc
    _ = S.card := by
      refine Finset.card_bij' (fun p _ => (p.1, p.1.val ^^^ p.2.val))
        (fun p h => (p.1, (⟨p.1.val ^^^ p.2,bound p h⟩ : Fin (2^k)))) ?_ ?_ ?_ ?_
      · intro p h; exact Finset.mem_product.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2⟩
      · intro p h
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        change p.1.val ^^^ (p.1.val ^^^ p.2) ∈ D
        rw [twice]
        exact (Finset.mem_product.mp h).2
      · intro p _; apply Prod.ext
        · rfl
        · apply Fin.ext; exact twice _ _
      · intro p _; apply Prod.ext
        · rfl
        · exact twice _ _
    _ = _ := by simp [S]

lemma end_dist {β : Type*} [Fintype β] (key : β → ℕ) (H base : β → Bool) (G : Finset ℕ) :
    (Finset.univ.filter (fun z => key z ∈ G)).card ≤ discrepancy key H base ∅ + discrepancy key H base G := by
  simp only [discrepancy, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  by_cases hh : key z ∈ G <;> cases H z <;> cases base z <;> simp [hh]

lemma exact_low {β : Type*} [Fintype β] (key : β → ℕ) (base : β → Bool) (D : Finset ℕ) :
    discrepancy key base base D = (Finset.univ.filter fun z => key z ∈ D).card := by
  unfold discrepancy
  congr 1
  apply Finset.filter_congr
  intro z _
  by_cases h : key z ∈ D <;> cases base z <;> simp [h]

lemma exact_high {β : Type*} [Fintype β] (key : β → ℕ) (base : β → Bool) (G D : Finset ℕ) (hd : D ⊆ G) :
    discrepancy key (fun z => xor (base z) (decide (key z ∈ G))) base D =
      (Finset.univ.filter fun z => key z ∈ G \ D).card := by
  unfold discrepancy
  congr 1
  apply Finset.filter_congr
  intro z _
  by_cases h : key z ∈ D
  · have hh := hd h
    simp [h,hh]
  · by_cases hh : key z ∈ G <;> cases hb : base z <;> simp [h,hh,hb]

lemma unrestricted {β : Type*} [Fintype β] (key : β → ℕ) (base : β → Bool) (G : Finset ℕ)
    (n t : ℕ) (hg : 0 < G.card) (ht : t ≤ G.card)
    (hf : ∀ D ⊆ G, (Finset.univ.filter (fun z => key z ∈ D)).card = n*D.card) :
    (∀ H : β → Bool, n * min t (G.card-t) ≤ (G.powersetCard t).sup (discrepancy key H base)) ∧
    ∃ H : β → Bool, (G.powersetCard t).sup (discrepancy key H base) = n * min t (G.card-t) := by
  have lo (H : β → Bool) : n * min t (G.card-t) ≤ (G.powersetCard t).sup (discrepancy key H base) := by
    have bound := end_dist key H base G
    rw [hf G Finset.Subset.rfl] at bound
    obtain ⟨D,hD,he,_⟩ := sampled_max (G.powersetCard t) (Finset.powersetCard_nonempty.mpr ht)
      G.card t n hg ht (fun D => (discrepancy key H base D : ℝ)) _ _ (by positivity) (by positivity)
      (by exact_mod_cast bound) (discrepancy_mean key H base G t)
    exact le_trans (by exact_mod_cast he : n*min t (G.card-t) ≤ discrepancy key H base D) (Finset.le_sup hD)
  refine ⟨lo, ?_⟩
  by_cases h : t ≤ G.card-t
  · refine ⟨base, le_antisymm (Finset.sup_le ?_) (lo base)⟩
    intro D hD
    obtain ⟨hd,hc⟩ := Finset.mem_powersetCard.mp hD
    rw [exact_low, hf D hd, hc, min_eq_left h]
  · let top := fun z => xor (base z) (decide (key z ∈ G))
    refine ⟨top, le_antisymm (Finset.sup_le ?_) (lo top)⟩
    intro D hD
    obtain ⟨hd,hc⟩ := Finset.mem_powersetCard.mp hD
    dsimp only [top]
    rw [exact_high key base G D hd, hf _ Finset.sdiff_subset, Finset.card_sdiff_of_subset hd, hc, min_eq_right (by omega)]

lemma mixed {β : Type*} [Fintype β] (key : β → ℕ) (base : β → Bool) (G : Finset ℕ)
    (n t : ℕ) (hg : 0 < G.card) (ht : t ≤ G.card)
    (hf : (Finset.univ.filter (fun z => key z ∈ G)).card = n*G.card)
    (l : ℕ) (w : Fin l → ℝ) (H : Fin l → β → Bool) (hw : ∀ i, 0 ≤ w i)
    (hw1 : (∑ i, w i) = 1) (hh : ∀ i, n*G.card < 128*discrepancy key (H i) base G) :
    ∃ D ∈ G.powersetCard t,
      let e := ∑ i, w i * (discrepancy key (H i) base D : ℝ)
      ((n * min t (G.card-t) : ℕ) : ℝ) ≤ e ∧
      (G.card < 2*t → ((128*(n*(G.card-t))+n*(2*t-G.card) : ℕ) : ℝ) < 128*e) := by
  let E := fun (i : Fin l) D => (discrepancy key (H i) base D : ℝ)
  let x := ∑ i, w i * E i ∅
  let y := ∑ i, w i * E i G
  have hxy : (n : ℝ)*G.card ≤ x+y := by
    change _ ≤ (∑ i, _) + ∑ i, _
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i, w i * ((n : ℝ)*G.card) := by rw [← Finset.sum_mul, hw1, one_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        rw [← mul_add]
        have h := end_dist key (H i) base G
        rw [hf] at h
        exact mul_le_mul_of_nonneg_left (by dsimp only [E]; exact_mod_cast h) (hw i)
  have big : (n:ℝ)*G.card < 128*y := by
    have ex : ∃ i, 0 < w i := by
      by_contra! h
      have hz : ∀ i, w i = 0 := fun i => le_antisymm (h i) (hw i)
      simp [hz] at hw1
    obtain ⟨j,hj⟩ := ex
    calc
      _ = ∑ i, w i * ((n:ℝ)*G.card) := by rw [← Finset.sum_mul, hw1, one_mul]
      _ < ∑ i, w i * (128* E i G) := by
        apply Finset.sum_lt_sum
        · intro i _; exact mul_le_mul_of_nonneg_left (by dsimp only [E]; exact_mod_cast (hh i).le) (hw i)
        · exact ⟨j, Finset.mem_univ _, mul_lt_mul_of_pos_left (by dsimp only [E]; exact_mod_cast hh j) hj⟩
      _ = 128*y := by dsimp only [y]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  have hnon (D : Finset ℕ) : 0 ≤ ∑ i, w i * E i D :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _)
  obtain ⟨D,hD,hd,hs⟩ := sampled_max (G.powersetCard t) (Finset.powersetCard_nonempty.mpr ht)
    G.card t n hg ht _ x y (hnon ∅) (hnon G) hxy
    (combine_means _ G.card t w E (fun i => E i ∅) (fun i => E i G) fun i => discrepancy_mean key (H i) base G t)
  exact ⟨D,hD,hd,fun h => hs h big⟩

end PEqualNP.Outside.L_meta_25879_aux

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic

section Field
variable {F : Type*} [Field F] [CharP F 2]

theorem cube_collision {x y h : F} (hn : h ≠ 0)
    (same : (x+h)^3 + x^3 = (y+h)^3 + y^3) : x = y ∨ x = y + h := by
  have fact : h*(x+y)*(x+y+h) = ((x+h)^3+x^3) - ((y+h)^3+y^3) := by
    have two : (2 : F) = 0 := CharTwo.two_eq_zero
    have three : (3 : F) = 1 := by rw [show (3 : F) = 2+1 by norm_num,two,zero_add]
    ring_nf
    simp only [two,three,mul_zero,mul_one,CharTwo.sub_eq_add,add_zero,zero_add]
  rw [same,sub_self] at fact
  rcases mul_eq_zero.mp fact with hy | hy
  · have hxy := (mul_eq_zero.mp hy).resolve_left hn
    left
    calc
      x = x + (y + y) := by rw [CharTwo.add_self_eq_zero,add_zero]
      _ = y := by rw [←add_assoc,hxy,zero_add]
  · right
    calc
      x = x + ((y+h) + (y+h)) := by rw [CharTwo.add_self_eq_zero,add_zero]
      _ = y+h := by rw [←add_assoc,←add_assoc x y h,hy,zero_add]

theorem cube_fibre [DecidableEq F] (A : Finset F) (h b : F) (hn : h ≠ 0) :
    (A.filter (fun x => (x+h)^3+x^3=b)).card ≤ 2 := by
  classical
  by_cases H : (A.filter fun x => (x+h)^3+x^3=b).Nonempty
  · obtain ⟨y,hy⟩ := H
    have target : A.filter (fun x => (x+h)^3+x^3=b) ⊆ {y,y+h} := by
      intro x hx
      have test := cube_collision hn ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
      simpa using test
    exact (Finset.card_le_card target).trans Finset.card_le_two
  · rw [Finset.not_nonempty_iff_eq_empty.mp H]
    simp
end Field

def shift (n : ℕ) (u x : Fin (2^n)) : Fin (2^n) :=
  ⟨u.val ^^^ x.val,Nat.xor_lt_two_pow u.isLt x.isLt⟩

theorem shift_invol (n : ℕ) (u x : Fin (2^n)) : shift n u (shift n u x) = x := by
  apply Fin.ext
  change u.val ^^^ (u.val ^^^ x.val) = x.val
  rw [← Nat.xor_assoc,Nat.xor_self,Nat.zero_xor]

def shiftEquiv (n : ℕ) (u : Fin (2^n)) : Fin (2^n) ≃ Fin (2^n) :=
  ⟨shift n u,shift n u,shift_invol n u,shift_invol n u⟩

theorem shifted_card (n : ℕ) (u : Fin (2^n)) (s : Finset (Fin (2^n))) :
    (s.map (shiftEquiv n u).toEmbedding).card = s.card := Finset.card_map _

theorem prefix_size {Q N : ℕ} (enc : Fin Q ↪ Fin N) {t : ℕ} (ht : t ≤ Q) :
    (((Finset.univ : Finset (Fin Q)).filter (fun i => i.val<t)).image (fun i => (enc i).val)).card=t := by
  have hcard : ((Finset.univ : Finset (Fin Q)).filter (fun i => i.val<t)).card=t := by
    let incl : Fin t ↪ Fin Q := Fin.castLEEmb ht
    have heq : (Finset.univ : Finset (Fin Q)).filter (fun i => i.val<t) =
        (Finset.univ : Finset (Fin t)).map incl := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
      constructor
      · intro h
        exact ⟨⟨i.val,h⟩,Fin.ext rfl⟩
      · rintro ⟨j,rfl⟩
        exact j.isLt
    simp [heq]
  exact (Finset.card_image_of_injective _ (show Function.Injective (fun i : Fin Q => (enc i).val) from Fin.val_injective.comp enc.injective)).trans hcard

end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic

def bitField (b : Bool) : ZMod 2 := if b then 1 else 0

theorem bitField_inj : Function.Injective bitField := by decide +kernel

theorem bitField_xor (x y : Bool) : bitField (xor x y) = bitField x + bitField y := by
  cases x <;> cases y <;> decide

def coords (m : ℕ) (u : Fin (2^m)) (i : Fin m) : ZMod 2 := bitField (u.val.testBit i.val)

theorem coords_inj (m : ℕ) : Function.Injective (coords m) := by
  intro x y eq
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · exact bitField_inj (congrFun eq ⟨i,hi⟩)
  · have le : 2^m ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (x.isLt.trans_le le),Nat.testBit_lt_two_pow (y.isLt.trans_le le)]

noncomputable def wordIso (m : ℕ) : Fin (2^m) ≃ (Fin m → ZMod 2) :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card (coords m)).mpr ⟨coords_inj m,by simp⟩)

section Field
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] {m : ℕ}

noncomputable def fieldWord (B : Module.Basis (Fin m) (ZMod 2) F) : Fin (2^m) ≃ F :=
  (wordIso m).trans B.equivFun.toEquiv.symm

omit [CharP F 2] in
theorem fieldWord_xor (B : Module.Basis (Fin m) (ZMod 2) F) (x y : Fin (2^m)) :
    fieldWord B (shift m x y) = fieldWord B x + fieldWord B y := by
  apply B.equivFun.injective
  rw [map_add]
  change B.equivFun (B.equivFun.symm _) = B.equivFun (B.equivFun.symm _) + B.equivFun (B.equivFun.symm _)
  simp only [LinearEquiv.apply_symm_apply]
  funext i
  change bitField ((x.val ^^^ y.val).testBit i.val) = bitField (x.val.testBit i.val) + bitField (y.val.testBit i.val)
  rw [Nat.testBit_xor]
  exact bitField_xor _ _

noncomputable def cubeWord (B : Module.Basis (Fin m) (ZMod 2) F) (x : Fin (2^m)) : Fin (2^m) :=
  (fieldWord B).symm ((fieldWord B x)^3)

omit [CharP F 2] in
theorem word_zero (B : Module.Basis (Fin m) (ZMod 2) F) :
    fieldWord B ⟨0,by positivity⟩ = 0 := by
  apply B.equivFun.injective
  rw [map_zero]
  change B.equivFun (B.equivFun.symm _) = 0
  rw [LinearEquiv.apply_symm_apply]
  funext i
  simp [wordIso,coords,bitField]

theorem word_collisions (B : Module.Basis (Fin m) (ZMod 2) F)
    (h x y : Fin (2^m)) (hn : h.val ≠ 0)
    (same : shift m (cubeWord B (shift m x h)) (cubeWord B x) =
      shift m (cubeWord B (shift m y h)) (cubeWord B y)) :
    x = y ∨ x = shift m y h := by
  have shifted := congrArg (fieldWord B) same
  simp only [fieldWord_xor,cubeWord,Equiv.apply_symm_apply] at shifted
  have nonzero : fieldWord B h ≠ 0 := by
    intro z
    exact hn (congrArg Fin.val ((fieldWord B).injective (z.trans (word_zero B).symm)))
  rcases cube_collision nonzero shifted with e|e
  · exact Or.inl ((fieldWord B).injective e)
  · exact Or.inr ((fieldWord B).injective (e.trans (fieldWord_xor B y h).symm))

end Field
end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic

def pack {m : ℕ} (lo hi : Fin (2^m)) : ℕ := lo.val+2^m*hi.val

theorem pack_low {m} (lo hi : Fin (2^m)) : pack lo hi % 2^m = lo.val := by
  simp [pack,Nat.mod_eq_of_lt lo.isLt]

theorem pack_high {m} (lo hi : Fin (2^m)) : pack lo hi / 2^m = hi.val := by
  unfold pack
  rw [Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt lo.isLt,Nat.zero_add]

theorem pack_bound {k m : ℕ} (bound : 2*m ≤ k) (lo hi : Fin (2^m)) : pack lo hi < 2^k := by
  have next : lo.val+2^m*hi.val < 2^m*(hi.val+1) := by
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have upper := Nat.mul_le_mul_left (2^m) hi.isLt
  have power : 2^m*2^m ≤ 2^k := by
    rw [←Nat.pow_add]
    apply Nat.pow_le_pow_right (by decide)
    omega
  exact next.trans_le (upper.trans power)

section Field
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] {m : ℕ}

noncomputable def encoded (B : Module.Basis (Fin m) (ZMod 2) F) (x : Fin (2^m)) : ℕ :=
  pack x (cubeWord B x)

noncomputable def prefixEmbedding (B : Module.Basis (Fin m) (ZMod 2) F) (k : ℕ) (hk : 2*m ≤ k) :
    Fin (2^m) ↪ Fin (2^k) :=
  ⟨fun x => ⟨encoded B x,pack_bound hk _ _⟩,by
    intro x y eq
    apply Fin.ext
    have low := congrArg (fun z : Fin (2^k) => z.val % 2^m) eq
    dsimp [encoded] at low
    simpa only [pack_low] using low⟩

theorem shift_cancel {m} (u v : Fin (2^m)) : shift m u (shift m u v) = v := shift_invol m u v

theorem encoded_pair (B : Module.Basis (Fin m) (ZMod 2) F) (u v x y : Fin (2^m)) (neq : u ≠ v)
    (same : encoded B u ^^^ encoded B v = encoded B x ^^^ encoded B y) : u=x ∨ u=y := by
  have low := congrArg (fun z : ℕ => z % 2^m) same
  have high := congrArg (fun z : ℕ => z / 2^m) same
  simp only [encoded,Nat.xor_mod_two_pow,pack_low] at low
  simp only [encoded,Nat.xor_div_two_pow,pack_high] at high
  let h := shift m u v
  have hu : shift m u h = v := shift_cancel _ _
  have hx : shift m x h = y := by
    have e : h = shift m x y := Fin.ext low
    rw [e,shift_cancel]
  have nonzero : h.val ≠ 0 := by
    intro eq
    apply neq
    have valid := congrArg Fin.val hu
    change u.val ^^^ h.val = v.val at valid
    rw [eq,Nat.xor_zero] at valid
    exact Fin.ext valid
  apply (word_collisions B h u x nonzero ?_).imp_right (fun e => e.trans hx)
  rw [hu,hx]
  apply Fin.ext
  exact (Nat.xor_comm _ _).trans (high.trans (Nat.xor_comm _ _))

theorem pair_fibre [DecidableEq F] (B : Module.Basis (Fin m) (ZMod 2) F)
    (A : Finset (Fin (2^m))) (d : ℕ) (nonzero : d ≠ 0) :
    (A.filter fun x => ∃ y ∈ A, encoded B x ^^^ encoded B y = d).card ≤ 2 := by
  classical
  let S := A.filter fun x => ∃ y ∈ A, encoded B x ^^^ encoded B y = d
  change S.card ≤ 2
  by_cases H : S.Nonempty
  · obtain ⟨u,hu⟩ := H
    obtain ⟨v,_,hv⟩ := (Finset.mem_filter.mp hu).2
    have ne : u ≠ v := by
      rintro rfl
      exact nonzero (hv.symm.trans (Nat.xor_self _))
    apply (Finset.card_le_card (t := {u,v}) ?_).trans Finset.card_le_two
    intro x hx
    obtain ⟨y,_,hy⟩ := (Finset.mem_filter.mp hx).2
    have nx : x ≠ y := by
      rintro rfl
      exact nonzero (hy.symm.trans (Nat.xor_self _))
    simpa using encoded_pair B x y u v nx (hy.trans hv.symm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp H]
    simp

end Field

theorem binary_power_basis (m : ℕ) (hm : m ≠ 0) :
    ∃ (B : Module.Basis (Fin m) (ZMod 2) (GaloisField 2 m)) (g : GaloisField 2 m),
      ∀ i : Fin m, B i = g ^ i.val := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod 2) (GaloisField 2 m)
  have eq : pb.dim = m := pb.finrank.symm.trans (GaloisField.finrank 2 hm)
  refine ⟨pb.basis.reindex (finCongr eq),pb.gen,?_⟩
  intro i
  simp [Module.Basis.reindex_apply,pb.basis_eq_pow]
end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic

section Hamming
variable {α : Type*} [Fintype α] [DecidableEq α]

def countValue (p : α → Bool) (v : Bool) : ℕ := (Finset.univ.filter fun x => p x = v).card

theorem perturb (p e : α → Bool) (v : Bool) :
    countValue p v ≤ countValue (fun x => xor (p x) (e x)) v + countValue e true := by
  let A := Finset.univ.filter fun x => p x = v
  let B := Finset.univ.filter fun x => xor (p x) (e x) = v
  let E := Finset.univ.filter fun x => e x = true
  have inc : A ⊆ B ∪ E := by
    intro x hx
    obtain ⟨_,hv⟩ := Finset.mem_filter.mp hx
    cases he : e x with
    | false => exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [he] using hv⟩)
    | true => exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  exact (Finset.card_le_card inc).trans (Finset.card_union_le B E)

theorem balanced_perturb (p e : α → Bool) (d : ℕ)
    (hp : ∀ v, d+countValue e true ≤ countValue p v) :
    ∀ v, d ≤ countValue (fun x => xor (p x) (e x)) v := by
  intro v
  have h := perturb p e v
  have b := hp v
  omega

def marksDiff (A B : Finset α) (x : α) : Bool := xor (decide (x∈A)) (decide (x∈B))

theorem diff_count (A B : Finset α) :
    countValue (marksDiff A B) true + 2*(A ∩ B).card = A.card+B.card := by
  have support : (Finset.univ.filter fun x => marksDiff A B x = true) = (A \ B) ∪ (B \ A) := by
    ext x
    by_cases a : x∈A <;> by_cases b : x∈B <;> simp [marksDiff,a,b]
  have disj : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro x ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  unfold countValue
  rw [support,Finset.card_union_of_disjoint disj]
  have one := Finset.card_sdiff_add_card_inter A B
  have two := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at two
  omega

omit [DecidableEq α] in
theorem count_complement (p : α → Bool) :
    countValue p false + countValue p true = Fintype.card α := by
  have eq := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α)) (fun x => p x = false)
  simpa [countValue] using eq

theorem constant_perturb (A B : Finset α) (t c : ℕ) (hA : A.card=t) (hB : B.card=t)
    (hi : (A ∩ B).card≤c) (big : 4*t ≤ Fintype.card α) :
    ∀ v, 2*(t-c) ≤ countValue (marksDiff A B) v := by
  have d := diff_count A B
  have total := count_complement (marksDiff A B)
  intro v
  cases v <;> omega

theorem common_gauge (a b u v w : Bool) :
    decide (xor a (xor u w) ≠ xor b (xor v w)) = xor (xor a b) (xor u v) := by
  cases a <;> cases b <;> cases u <;> cases v <;> cases w <;> decide

end Hamming
end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic

theorem xor_cross {a b c d : ℕ} (eq : a ^^^ b = c ^^^ d) : b ^^^ d = a ^^^ c := by
  calc
    b ^^^ d = (a ^^^ (a ^^^ b)) ^^^ d := by rw [←Nat.xor_assoc a a,Nat.xor_self,Nat.zero_xor]
    _ = (a ^^^ (c ^^^ d)) ^^^ d := by rw [eq]
    _ = a ^^^ c := by rw [Nat.xor_assoc,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

theorem xor_nonzero {a b : ℕ} (hne : a ≠ b) : a ^^^ b ≠ 0 := by
  intro eq
  apply hne
  calc
    a = a ^^^ (a ^^^ b) := by rw [eq,Nat.xor_zero]
    _ = b := by rw [←Nat.xor_assoc,Nat.xor_self,Nat.zero_xor]

variable {k Q : ℕ}

def translated (enc : Fin Q ↪ Fin (2^k)) (A : Finset (Fin Q)) (x : Fin (2^k)) :
    Finset (Fin (2^k)) := A.image fun u => shift k x (enc u)

theorem translated_card (enc : Fin Q ↪ Fin (2^k)) (A : Finset (Fin Q)) (x : Fin (2^k)) :
    (translated enc A x).card = A.card :=
  Finset.card_image_of_injective _ ((shiftEquiv k x).injective.comp enc.injective)

theorem translated_member (enc : Fin Q ↪ Fin (2^k)) (A : Finset (Fin Q)) (x z : Fin (2^k)) :
    z ∈ translated enc A x ↔ x.val ^^^ z.val ∈ A.image (fun u => (enc u).val) := by
  constructor
  · rintro hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨u,hu,?_⟩
    exact (congrArg Fin.val (shift_invol k x (enc u))).symm
  · intro hz
    obtain ⟨u,hu,hv⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨u,hu,?_⟩
    have eq : enc u = shift k x z := Fin.ext hv
    rw [eq,shift_invol]

theorem overlap_image (enc : Fin Q ↪ Fin (2^k)) (A : Finset (Fin Q)) (x y : Fin (2^k)) :
    translated enc A x ∩ translated enc A y ⊆
      (A.filter (fun u => ∃ v ∈ A, (enc u).val ^^^ (enc v).val = x.val ^^^ y.val)).image
        (fun u => shift k x (enc u)) := by
  intro z hz
  obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hz
  obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp hx
  obtain ⟨v,hv,ev⟩ := Finset.mem_image.mp hy
  refine Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,v,hv,?_⟩,eq⟩
  exact xor_cross (congrArg Fin.val (eq.trans ev.symm))

theorem overlap_at_most (enc : Fin Q ↪ Fin (2^k)) (A : Finset (Fin Q)) (x y : Fin (2^k)) (c : ℕ)
    (bound : (A.filter (fun u => ∃ v ∈ A, (enc u).val ^^^ (enc v).val = x.val ^^^ y.val)).card ≤ c) :
    (translated enc A x ∩ translated enc A y).card ≤ c :=
  (Finset.card_le_card (overlap_image enc A x y)).trans (Finset.card_image_le.trans bound)

theorem address_room (a k : ℕ) (ha : 2 ≤ a) (hk : 2*2^a ≤ k) :
    4*2^(k/2) ≤ 2^(k-a) := by
  have grow : ∀ j : ℕ, 2 ≤ j → j+2 ≤ 2^j := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hj
      by_cases low : 2 ≤ j
      · have old := ih low
        rw [pow_succ]
        omega
      · have eq : j=1 := by omega
        subst j
        decide
  have enough := grow a ha
  have step : 2 + k/2 ≤ k-a := by omega
  calc
    4*2^(k/2) = 2^(2+k/2) := by rw [pow_add]; norm_num
    _ ≤ 2^(k-a) := Nat.pow_le_pow_right (by decide) step

end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic

theorem perturb_selector {α : Type*} [Fintype α] [DecidableEq α] (p : α → Bool) (A B : Finset α)
    (t r : ℕ) (v : Bool) (sizeA : A.card=t) (sizeB : B.card=t) (overlap : (A ∩ B).card ≤ 2)
    (large : (∃ z, p z=v) → 4*t ≤ countValue p v)
    (small : t ≤ r → (A ∩ B).Nonempty → ∃ z, p z=v) :
    2*(if t ≤ r then t else t-2) ≤ countValue (fun z => xor (p z) (marksDiff A B z)) v := by
  have d := diff_count A B
  by_cases yes : ∃ z, p z=v
  · have many := large yes
    have loss := perturb p (marksDiff A B) v
    split <;> omega
  · have equal : countValue (fun z => xor (p z) (marksDiff A B z)) v = countValue (marksDiff A B) true := by
      unfold countValue
      congr 1
      ext z
      have no : p z ≠ v := fun e => yes ⟨_,e⟩
      cases v <;> cases hp : p z <;> cases hn : marksDiff A B z <;> simp_all
    rw [equal]
    split
    · rename_i ht
      have empty := Finset.not_nonempty_iff_eq_empty.mp (fun hit => yes (small ht hit))
      rw [empty,Finset.card_empty] at d
      omega
    · omega

theorem residue_count {k a : ℕ} (ha : a ≤ k) (bit : ℕ → Bool) (v : Bool)
    (j : Fin (2^a)) (hv : bit j.val = v) :
    2^(k-a) ≤ countValue (fun z : Fin (2^k) => bit (z.val % 2^a)) v := by
  have pow : 2^a*2^(k-a)=2^k := by rw [←pow_add];congr 1;omega
  let incl : Fin (2^(k-a)) ↪ Fin (2^k) :=
    ⟨fun u => ⟨j.val+2^a*u.val,by
      rw [←pow]
      calc
        j.val+2^a*u.val < 2^a*(u.val+1) := by rw [Nat.mul_add,Nat.mul_one];omega
        _ ≤ 2^a*2^(k-a) := Nat.mul_le_mul_left _ u.isLt⟩,by
      intro u w eq
      have val := congrArg (fun z : Fin (2^k) => z.val / 2^a) eq
      dsimp only at val
      rw [Nat.add_mul_div_left _ _ (by positivity),Nat.add_mul_div_left _ _ (by positivity)] at val
      exact Fin.ext (Nat.add_left_cancel val)⟩
  have subset : (Finset.univ.map incl) ⊆ (Finset.univ.filter fun z : Fin (2^k) => bit (z.val % 2^a)=v) := by
    intro z hz
    obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change bit ((j.val+2^a*u.val) % 2^a) = v
    simpa [Nat.mod_eq_of_lt j.isLt] using hv
  simpa [countValue] using Finset.card_le_card subset

theorem two_bit_balance {k i j : ℕ} (hi : i < k) (neq : i ≠ j) (v : Bool) :
    2*countValue (fun z : Fin (2^k) => xor (z.val.testBit i) (z.val.testBit j)) v = 2^k := by
  let p := fun z : Fin (2^k) => xor (z.val.testBit i) (z.val.testBit j)
  let w : Fin (2^k) := ⟨2^i,Nat.pow_lt_pow_right (by decide) hi⟩
  have flip (z : Fin (2^k)) : p (shift k w z) = !(p z) := by
    change xor (((2^i) ^^^ z.val).testBit i) (((2^i) ^^^ z.val).testBit j) = !(p z)
    simp only [Nat.testBit_xor,Nat.testBit_two_pow_self,Nat.testBit_two_pow_of_ne neq]
    unfold p
    cases z.val.testBit i <;> cases z.val.testBit j <;> decide
  have eq : countValue p false = countValue p true := by
    apply Finset.card_equiv (shiftEquiv k w)
    intro z
    change z ∈ Finset.univ.filter (fun z => p z=false) ↔ shift k w z ∈ Finset.univ.filter (fun z => p z=true)
    simp [flip]
  have total := count_complement p
  rw [Fintype.card_fin] at total
  change 2*countValue p v=2^k
  cases v <;> omega

end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic

def firstWords (m t : ℕ) := (Finset.univ : Finset (Fin (2^m))).filter fun u => u.val < t

theorem small_collision {k a m t : ℕ} (enc : Fin (2^m) ↪ Fin (2^k)) (low : ∀ u, (enc u).val % 2^m = u.val)
    (x y : Fin (2^k)) (ne : x ≠ y) (ht : t ≤ 2^a)
    (hit : (translated enc (firstWords m t) x ∩ translated enc (firstWords m t) y).Nonempty) :
    0 < (x.val ^^^ y.val) % 2^m ∧ (x.val ^^^ y.val) % 2^m < 2^a := by
  obtain ⟨z,hz⟩ := hit
  obtain ⟨u,hu,_⟩ := Finset.mem_image.mp (overlap_image enc (firstWords m t) x y hz)
  obtain ⟨inA,v,inB,ds⟩ := Finset.mem_filter.mp hu
  have ux := (Finset.mem_filter.mp inA).2
  have vx := (Finset.mem_filter.mp inB).2
  have diff : (x.val ^^^ y.val) % 2^m=u.val ^^^ v.val := by rw [←ds,Nat.xor_mod_two_pow,low,low]
  have unequal : u.val ≠ v.val := by
    intro eq
    have same : u = v := Fin.ext eq
    rw [same,Nat.xor_self] at ds
    exact xor_nonzero (fun ev => ne (Fin.ext ev)) ds.symm
  rw [diff]
  exact ⟨Nat.pos_of_ne_zero (xor_nonzero unequal),Nat.xor_lt_two_pow (ux.trans_le ht) (vx.trans_le ht)⟩

theorem small_diff_residue {d a m : ℕ} (ha : a ≤ m) (hp : 0 < d % 2^m) (width : d % 2^m < 2^a) :
    d % 2^a ≠ 0 := by
  have smaller : d % 2^a = d % 2^m := by
    rw [← Nat.mod_mod_of_dvd d (pow_dvd_pow 2 ha),Nat.mod_eq_of_lt width]
  omega

theorem small_diff_bit {d a m : ℕ} (ha : a < m) (ha' : a < 2^a)
    (hp : 0 < d % 2^m) (width : d % 2^m < 2^a) (v : Bool) :
    ∃ j : Fin (2^a), d.testBit j.val = v := by
  have bit (j : ℕ) (hj : j < m) : (d % 2^m).testBit j = d.testBit j := by
    simp [Nat.testBit_mod_two_pow,hj]
  cases v with
  | false => exact ⟨⟨a,ha'⟩,(bit a ha).symm.trans (Nat.testBit_lt_two_pow width)⟩
  | true =>
    by_contra no
    have zero : d % 2^m=0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < a
      · rw [bit j (hj.trans ha)]
        have neg : d.testBit j ≠ true := fun hh => no ⟨⟨j,hj.trans ha'⟩,hh⟩
        simpa using Bool.eq_false_iff.mpr neg
      · have bigger : 2^a ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
        simp [Nat.testBit_lt_two_pow (width.trans_le bigger)]
    omega

end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic

def baseRow {k : ℕ} (a : ℕ) (x y z : Fin (2^k)) : Bool :=
  (x.val ^^^ y.val).testBit (z.val % 2^a)

def baseCol {k : ℕ} (a : ℕ) (x y z : Fin (2^k)) : Bool :=
  xor (z.val.testBit (x.val % 2^a)) (z.val.testBit (y.val % 2^a))

theorem address_large {k a m t : ℕ} (hm : m=k/2) (ha : 2 ≤ a) (hk : 2*2^a ≤ k) (ht : t ≤ 2^m) :
    4*t ≤ 2^(k-a) ∧ 8*t ≤ 2^k := by
  have hr := address_room a k ha hk
  rw [← hm] at hr
  have low : a < 2^a := Nat.lt_two_pow_self
  have eq : 2^(k-a)*2^a=2^k := by rw [←pow_add];congr 1;omega
  have bound : 2 ≤ 2^a := by
    calc
      2 = 2^1 := by decide
      _ ≤ 2^a := Nat.pow_le_pow_right (by decide) (by omega)
  have doubleBound := Nat.mul_le_mul_left (2^(k-a)) bound
  rw [eq] at doubleBound
  omega

theorem noise_bounds {k a m t : ℕ} (hm : m=k/2) (ha : 2 ≤ a) (hk : 2*2^a ≤ k) (ht : t ≤ 2^m)
    (enc : Fin (2^m) ↪ Fin (2^k)) (hlow : ∀ u, (enc u).val % 2^m=u.val)
    (x y : Fin (2^k)) (ne : x≠y) (v : Bool)
    (lim : (translated enc (firstWords m t) x ∩ translated enc (firstWords m t) y).card ≤ 2) :
    let A := translated enc (firstWords m t) x
    let B := translated enc (firstWords m t) y
    2*(if t ≤ 2^a then t else t-2) ≤ countValue (fun z => xor (baseRow a x y z) (marksDiff A B z)) v ∧
    2*(if t ≤ 2^a then t else t-2) ≤ countValue (fun z => xor (baseCol a x y z) (marksDiff A B z)) v := by
  dsimp only
  have hpow : a < 2^a := Nat.lt_two_pow_self
  have am : a < m := by omega
  have ak : a ≤ k := by omega
  have rk : 2^a ≤ k := by omega
  obtain ⟨room,largeRoom⟩ := address_large hm ha hk ht
  have ca : (firstWords m t).card=t := by
    have sz := prefix_size (Function.Embedding.refl (Fin (2^m))) ht
    simpa [firstWords,Finset.card_image_of_injective _ Fin.val_injective] using sz
  have sizes (z : Fin (2^k)) : (translated enc (firstWords m t) z).card=t := (translated_card ..).trans ca
  have smallInfo := small_collision (a := a) (t := t) enc hlow x y ne
  have col_ne (hs : t ≤ 2^a) (hI : (translated enc (firstWords m t) x ∩ translated enc (firstWords m t) y).Nonempty) :
      x.val % 2^a ≠ y.val % 2^a := by
    obtain ⟨pos,st⟩ := smallInfo hs hI
    have nmod := small_diff_residue am.le pos st
    intro e
    rw [Nat.xor_mod_two_pow,e,Nat.xor_self] at nmod
    exact nmod rfl
  constructor
  · apply perturb_selector _ _ _ t (2^a) v (sizes _) (sizes _) lim
    · rintro ⟨z,hz⟩
      exact room.trans (residue_count ak (fun j => (x.val ^^^ y.val).testBit j) v
        ⟨z.val % 2^a,Nat.mod_lt _ (by positivity)⟩ hz)
    · intro hs hI
      obtain ⟨pos,st⟩ := smallInfo hs hI
      obtain ⟨j,hj⟩ := small_diff_bit am hpow pos st v
      refine ⟨⟨j.val,j.isLt.trans_le (Nat.pow_le_pow_right (by decide) ak)⟩,?_⟩
      simpa [baseRow,Nat.mod_eq_of_lt j.isLt] using hj
  · apply perturb_selector _ _ _ t (2^a) v (sizes _) (sizes _) lim
    · rintro ⟨z,hz⟩
      by_cases same : x.val % 2^a=y.val % 2^a
      · have vf : v=false := by simpa [baseCol,same] using hz.symm
        simp [baseCol,countValue,same,vf]
        omega
      · have small : x.val % 2^a < k := (Nat.mod_lt _ (by positivity)).trans_le rk
        have h := two_bit_balance small same v
        change 4*t ≤ countValue (fun z : Fin (2^k) => xor (z.val.testBit (x.val % 2^a)) (z.val.testBit (y.val % 2^a))) v
        omega
    · intro hs hI
      have diff := col_ne hs hI
      cases v with
      | false => exact ⟨⟨0,by positivity⟩,by simp [baseCol]⟩
      | true =>
        have ix : x.val % 2^a < k := (Nat.mod_lt _ (by positivity)).trans_le rk
        refine ⟨⟨2^(x.val % 2^a),Nat.pow_lt_pow_right (by decide) ix⟩,?_⟩
        simp [baseCol,Nat.testBit_two_pow_of_ne diff]

end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic

def raw {k : ℕ} (a : ℕ) (D : Finset ℕ) (x y : Fin (2^k)) : Bool :=
  xor (x.val.testBit (y.val % 2^a)) (decide ((x.val ^^^ y.val) ∈ D))

def separated {k : ℕ} (a : ℕ) (D : Finset ℕ) (distance : ℕ) : Prop :=
  ∀ f g : Fin (2^k) → Bool,
    let T := fun x y : Fin (2^k) => xor (raw a D x y) (xor (f x) (g y))
    ∀ i j : Fin (2^k), i ≠ j →
      distance ≤ (Finset.univ.filter (fun z => T i z ≠ T j z)).card ∧
      distance ≤ (Finset.univ.filter (fun z => T z i ≠ T z j)).card

theorem bool_pair (a b c d u v w : Bool) :
    (xor (xor a b) (xor u w) ≠ xor (xor c d) (xor v w)) ↔
    xor (xor a c) (xor b d) = !(xor u v) := by decide +revert

theorem geometric_part {k a m t : ℕ} (hm : m=k/2) (ha : 2 ≤ a) (hk : 2*2^a ≤ k) (ht : t ≤ 2^m)
    {F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] (B : Module.Basis (Fin m) (ZMod 2) F) :
    let enc := prefixEmbedding B k (by omega)
    let D := (firstWords m t).image fun u => (enc u).val
    D.card=t ∧ @separated k a D (2*(if t ≤ 2^a then t else t-2)) := by
  classical
  let enc := prefixEmbedding B k (show 2*m ≤ k by omega)
  let A := firstWords m t
  let D := A.image fun u => (enc u).val
  change D.card=t ∧ @separated k a D _
  refine ⟨prefix_size enc ht,?_⟩
  intro f g
  dsimp only
  intro x y ne
  have hlow (u) : (enc u).val % 2^m = u.val := pack_low _ _
  have lim : (translated enc A x ∩ translated enc A y).card ≤ 2 := by
    apply overlap_at_most
    exact pair_fibre B A (x.val ^^^ y.val) (xor_nonzero (fun e => ne (Fin.ext e)))
  have bounds := fun v => noise_bounds hm ha hk ht enc hlow x y ne v lim
  let R := translated enc A x
  let S := translated enc A y
  have mx (z) : (x.val ^^^ z.val ∈ D) ↔ z ∈ R := (translated_member enc A x z).symm
  have my (z) : (y.val ^^^ z.val ∈ D) ↔ z ∈ S := (translated_member enc A y z).symm
  constructor
  · apply (bounds (!(xor (f x) (f y)))).1.trans_eq
    unfold countValue
    congr 1
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    unfold raw baseRow marksDiff
    simp only [Nat.testBit_xor,mx,my]
    exact (bool_pair _ _ _ _ _ _ _).symm
  · apply (bounds (!(xor (g x) (g y)))).2.trans_eq
    unfold countValue
    congr 1
    ext z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    unfold raw baseCol marksDiff
    rw [Nat.xor_comm z.val x.val,Nat.xor_comm z.val y.val,Bool.xor_comm (f z) (g x),Bool.xor_comm (f z) (g y)]
    simp only [mx,my]
    exact (bool_pair _ _ _ _ _ _ _).symm

end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits
open PEqualNP.CircuitLowerBounds

abbrev Sig (X : Type*) := X → Bool
def neg {X} (f : Sig X) : Sig X := fun x => !(f x)
def use {X} (C : List (Sig X)) (f : Sig X) : Prop := f ∈ C ∧ neg f ∈ C
def values {X} (C : List (Sig X)) (x : X) := C.map (fun f => f x)
def run (gs : List Gate) (v : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) v
def good (g : Gate) : Prop := g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Segment {X} (C D : List (Sig X)) (cost : ℕ) : Prop :=
  (∀ f ∈ C, f ∈ D) ∧ ∃ gs : List Gate, gs.length ≤ cost ∧ (∀ g ∈ gs, good g) ∧
    ∀ x, run gs (values C x) = values D x

namespace Segment
variable {X : Type*} {C D E : List (Sig X)} {a b : ℕ}
theorem ident (C : List (Sig X)) : Segment C C 0 :=
  ⟨fun _ h=>h,[],by simp,by simp,fun _=>rfl⟩

theorem trans (left : Segment C D a) (right : Segment D E b) : Segment C E (a+b) := by
  obtain ⟨i,gs,n,ok,eval⟩ := left
  obtain ⟨j,ts,m,ok',eval'⟩ := right
  refine ⟨fun f hf=>j _ (i _ hf),gs++ts,by simpa using Nat.add_le_add n m,?_,?_⟩
  · intro g hg
    exact (List.mem_append.mp hg).elim (ok g) (ok' g)
  · intro x
    change (gs++ts).foldl _ _ = _
    rw [List.foldl_append]
    exact (congrArg (run ts) (eval x)).trans (eval' x)

theorem relax (h : Segment C D a) (le : a≤b) : Segment C D b := by
  obtain ⟨inc,gs,len,ok,eval⟩ := h
  exact ⟨inc,gs,len.trans le,ok,eval⟩

theorem keeps (h : Segment C D a) {f : Sig X} (hf : use C f) : use D f :=
  ⟨h.1 _ hf.1,h.1 _ hf.2⟩
end Segment

theorem use_neg {X} {C : List (Sig X)} {f} (hf : use C f) : use C (neg f) := by
  refine ⟨hf.2,?_⟩
  have eq : neg (neg f) = f := by funext x;simp [neg]
  rw [eq]
  exact hf.1

theorem wire {X} {C : List (Sig X)} {f : Sig X} (hf : f ∈ C) :
    ∃ i : ℕ, ∀ x : X, (values C x).getD i false = f x := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hf
  refine ⟨i.val,fun x => ?_⟩
  rw [←hi]
  simp [values,List.getD_eq_getElem?_getD,List.get_eq_getElem]

theorem append_gate {X} {C : List (Sig X)} (g : Gate) (hg : good g) (f : Sig X)
    (hf : ∀ x, g.op.eval (g.inputs.map fun i => (values C x).getD i false) = f x) :
    Segment C (C++[f]) 1 := by
  refine ⟨fun v hv => List.mem_append_left _ hv,[g],by simp,by simpa,?_⟩
  intro x
  change values C x ++ [g.op.eval _] = _
  rw [hf]
  simp [values]

theorem add_and {X} (C : List (Sig X)) (f g : Sig X) (hf : use C f) (hg : use C g) :
    ∃ D, Segment C D 2 ∧ use D (fun x => f x && g x) := by
  let out : Sig X := fun x => f x && g x
  obtain ⟨i,hi⟩ := wire hf.1
  obtain ⟨j,hj⟩ := wire hg.1
  have s := append_gate (C:=C) ⟨.and,[i,j]⟩ (by simp [good]) out (by
    intro x
    change ((values C x).getD i false && ((values C x).getD j false && true)) = out x
    rw [hi,hj,Bool.and_true])
  obtain ⟨k,hk⟩ := wire (s.keeps hf).2
  obtain ⟨l,hl⟩ := wire (s.keeps hg).2
  have t := append_gate (C:=C++[out]) ⟨.or,[k,l]⟩ (by simp [good]) (neg out) (by
    intro x
    change ((values (C++[out]) x).getD k false || ((values (C++[out]) x).getD l false || false)) = neg out x
    rw [hk,hl,Bool.or_false]
    simp [out,neg,Bool.not_and])
  refine ⟨_,s.trans t,?_⟩
  change use ((C++[out])++[neg out]) out
  exact ⟨t.1 _ (by simp),by simp⟩

theorem add_or {X} (C : List (Sig X)) (f g : Sig X) (hf : use C f) (hg : use C g) :
    ∃ D, Segment C D 2 ∧ use D (fun x => f x || g x) := by
  obtain ⟨D,s,h⟩ := add_and C (neg f) (neg g) (use_neg hf) (use_neg hg)
  refine ⟨D,s,?_⟩
  have eq : neg (fun x => neg f x && neg g x) = (fun x => f x || g x) := by
    funext x;simp [neg,Bool.not_and]
  exact eq ▸ use_neg h

theorem add_xor {X} (C : List (Sig X)) (f g : Sig X) (hf : use C f) (hg : use C g) :
    ∃ D, Segment C D 6 ∧ use D (fun x => xor (f x) (g x)) := by
  obtain ⟨D,s,h⟩ := add_and C f (neg g) hf (use_neg hg)
  obtain ⟨E,t,q⟩ := add_and D (neg f) g (s.keeps (use_neg hf)) (s.keeps hg)
  obtain ⟨H,u,w⟩ := add_or E _ _ (t.keeps h) q
  refine ⟨H,(s.trans t).trans u,?_⟩
  have eq : (fun x => f x && neg g x || neg f x && g x) = (fun x => xor (f x) (g x)) := by
    funext x;unfold neg;cases f x <;> cases g x <;> rfl
  exact eq ▸ w

theorem add_constants {X} (C : List (Sig X)) :
    ∃ D, Segment C D 2 ∧ use D (fun _ => false) ∧ use D (fun _ => true) := by
  let f : Sig X := fun _ => false
  let t : Sig X := fun _ => true
  have s := append_gate (C:=C) ⟨.or,[]⟩ (by simp [good]) f (fun _=>rfl)
  have q := append_gate (C:=C++[f]) ⟨.and,[]⟩ (by simp [good]) t (fun _=>rfl)
  have hf : f ∈ (C++[f])++[t] := q.1 _ (by simp)
  have ht : t ∈ (C++[f])++[t] := by simp
  exact ⟨_,s.trans q,⟨hf,ht⟩,⟨ht,hf⟩⟩

end PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits
open PEqualNP.CircuitLowerBounds

variable {X I : Type*}
abbrev Includes (C D : List (Sig X)) := ∀ f ∈ C, f ∈ D

theorem lift_use {C D : List (Sig X)} (inc : Includes C D) {f} (haveF : use C f) : use D f :=
  ⟨inc _ haveF.1,inc _ haveF.2⟩

theorem gather_list (C : List (Sig X)) (items : List I) (out : I → Sig X) (n : ℕ)
    (step : ∀ i, ∀ D, Includes C D → ∃ E, Segment D E n ∧ use E (out i)) :
    ∃ D, Segment C D (items.length*n) ∧ ∀ i ∈ items, use D (out i) := by
  induction items with
  | nil => exact ⟨C,by simpa using Segment.ident C,by simp⟩
  | cons i is ih =>
    obtain ⟨D,s,olds⟩ := ih
    obtain ⟨E,t,one⟩ := step i D s.1
    refine ⟨E,(s.trans t).relax (by simp [Nat.add_mul]),?_⟩
    intro v h
    rcases List.mem_cons.mp h with rfl | rest
    · exact one
    · exact t.keeps (olds _ rest)

theorem gather [Fintype I] (C : List (Sig X)) (out : I → Sig X) (n : ℕ)
    (step : ∀ i, ∀ D, Includes C D → ∃ E, Segment D E n ∧ use E (out i)) :
    ∃ D, Segment C D (Fintype.card I*n) ∧ ∀ i, use D (out i) := by
  classical
  obtain ⟨D,s,all⟩ := gather_list C (Finset.univ : Finset I).toList out n step
  exact ⟨D,by simpa using s,fun i => all i (by simp)⟩

theorem fold_signals (C : List (Sig X)) (items : List (Sig X)) (op : Bool → Bool → Bool) (start : Bool) (n : ℕ)
    (base : use C (fun _=>start)) (known : ∀ f∈items, use C f)
    (step : ∀ (D : List (Sig X)) f g, use D f → use D g → ∃ E, Segment D E n ∧ use E (fun x=>op (f x) (g x))) :
    ∃ D, Segment C D (items.length*n) ∧ use D (fun x => (items.map fun f=> f x).foldr op start) := by
  induction items with
  | nil => exact ⟨C,by simpa using Segment.ident C,base⟩
  | cons f fs ih =>
    obtain ⟨D,s,h⟩ := ih (fun g hg => known _ (List.mem_cons_of_mem _ hg))
    obtain ⟨E,t,out⟩ := step D f _ (s.keeps (known _ (by simp))) h
    exact ⟨E,(s.trans t).relax (by simp [Nat.add_mul]),out⟩

def initial (n : ℕ) : List (Sig (Fin n → Bool)) :=
  List.ofFn (fun i : Fin n => fun x : Fin n → Bool => x i) ++
  List.ofFn (fun i : Fin n => fun x : Fin n → Bool => !(x i))

theorem input (n : ℕ) (i : Fin n) : use (initial n) (fun x=>x i) := by
  constructor <;> unfold initial
  · exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem finish (n bound : ℕ) (f : Sig (Fin n → Bool)) (D : List (Sig (Fin n → Bool)))
    (s : Segment (initial n) D bound) (output : use D f) : PEqualNP.Represents.HasLitSize n f bound := by
  obtain ⟨_,gs,len,ok,eval⟩ := s
  obtain ⟨i,hi⟩ := wire output.1
  refine ⟨⟨gs,i⟩,ok,len,?_⟩
  intro x
  have start : values (initial n) x = List.ofFn x ++ List.ofFn (fun j => !(x j)) := by
    simp [initial,values,List.map_ofFn,Function.comp_def]
  change (run gs (List.ofFn x ++ List.ofFn (fun j => !(x j)))).getD i false = _
  rw [←start,eval]
  exact hi x

end PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits
variable {X I : Type*}

def nz (u : ZMod 2) := decide (u ≠ 0)

theorem nz_add (u v : ZMod 2) : nz (u+v) = xor (nz u) (nz v) := by decide +revert
theorem nz_mul (u v : ZMod 2) : nz (u*v) = (nz u && nz v) := by decide +revert
theorem nz_bitField (u : Bool) : nz (bitField u) = u := by cases u <;> decide
theorem bitField_nz (u : ZMod 2) : bitField (nz u) = u := by decide +revert

theorem sum_bits [DecidableEq I] (C : List (Sig X)) (s : Finset I) (f : I → X → ZMod 2)
    (base : use C (fun _ => false)) (w : ∀ i, use C (fun x => nz (f i x))) :
    ∃ D, Segment C D (s.card*6) ∧ use D (fun x => nz (∑ i ∈ s, f i x)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨C,by simpa using Segment.ident C,by simpa [nz] using base⟩
  | @insert i s hi ih =>
    obtain ⟨D,old,h⟩ := ih
    obtain ⟨E,one,out⟩ := add_xor D _ _ (old.keeps (w i)) h
    refine ⟨E,(old.trans one).relax (by simp [hi,Nat.add_mul]),?_⟩
    simpa [Finset.sum_insert hi,nz_add] using out

theorem all_bits [DecidableEq I] (C : List (Sig X)) (s : Finset I) (f : I → Sig X)
    (base : use C (fun _=>true)) (w : ∀ i, use C (f i)) :
    ∃ D, Segment C D (s.card*2) ∧ use D (fun x => decide (∀ i∈s, f i x=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨C,by simpa using Segment.ident C,by simpa using base⟩
  | @insert i s hi ih =>
    obtain ⟨D,old,h⟩ := ih
    obtain ⟨E,one,out⟩ := add_and D _ _ (old.keeps (w i)) h
    refine ⟨E,(old.trans one).relax (by simp [hi,Nat.add_mul]),?_⟩
    simpa [Finset.forall_mem_insert] using out

theorem any_bits [DecidableEq I] (C : List (Sig X)) (s : Finset I) (f : I → Sig X)
    (base : use C (fun _=>false)) (w : ∀ i, use C (f i)) :
    ∃ D, Segment C D (s.card*2) ∧ use D (fun x => decide (∃ i∈s, f i x=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨C,by simpa using Segment.ident C,by simpa using base⟩
  | @insert i s hi ih =>
    obtain ⟨D,old,h⟩ := ih
    obtain ⟨E,one,out⟩ := add_or D _ _ (old.keeps (w i)) h
    refine ⟨E,(old.trans one).relax (by simp [hi,Nat.add_mul]),?_⟩
    simpa [Finset.exists_mem_insert] using out

end PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic

def degree {m : ℕ} (p : Fin m × Fin m) : Fin (3*m) := ⟨2*p.1.val+p.2.val,by have := p.1.isLt; have := p.2.isLt; omega⟩
def bucket {m : ℕ} (d : Fin (3*m)) : Finset (Fin m × Fin m) := Finset.univ.filter fun p => degree p = d
def term {m : ℕ} (u : Fin (2^m)) (p : Fin m × Fin m) : ZMod 2 :=
  bitField (u.val.testBit p.1.val && u.val.testBit p.2.val)
def coefficient {m : ℕ} (u : Fin (2^m)) (d : Fin (3*m)) : ZMod 2 := ∑ p ∈ bucket d, term u p

theorem bucket_card {m : ℕ} (d : Fin (3*m)) : (bucket d).card ≤ m := by
  apply (Finset.card_le_card_of_injOn Prod.fst (t := Finset.univ) (fun _ _ => Finset.mem_univ _) ?_).trans_eq (by simp)
  intro p hp q hq he
  have dp := congrArg Fin.val (Finset.mem_filter.mp hp).2
  have dq := congrArg Fin.val (Finset.mem_filter.mp hq).2
  change 2*p.1.val+p.2.val = d.val at dp
  change 2*q.1.val+q.2.val = d.val at dq
  exact Prod.ext he (Fin.ext (by rw [he] at dp; omega))

section
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] {m : ℕ}
theorem cube_expand (B : Module.Basis (Fin m) (ZMod 2) F) (g : F) (basis : ∀ i : Fin m, B i = g^i.val)
    (u : Fin (2^m)) : (fieldWord B u)^3 = ∑ d : Fin (3*m), coefficient u d • (g^d.val) := by
  classical
  let f : Fin m → F := fun i => if u.val.testBit i.val then g^i.val else 0
  have exp : fieldWord B u = ∑ i, f i := by
    change B.equivFun.symm (coords m u) = _
    rw [Module.Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [basis]
    cases h : u.val.testBit i.val <;> simp [coords,bitField,h,f]
  have split (p : Fin m × Fin m) : f p.1 ^ 2 * f p.2 = term u p • (g^(degree p).val) := by
    have hp : g^(2*p.1.val+p.2.val) = (g^p.1.val)^2 * g^p.2.val := by
      rw [pow_add,Nat.mul_comm 2 p.1.val,pow_mul]
    cases h : u.val.testBit p.1.val <;> cases j : u.val.testBit p.2.val <;> simp [term,bitField,degree,f,h,j,hp]
  calc
    (fieldWord B u)^3 = (∑ i, f i)^2 * ∑ i, f i := by rw [exp,pow_succ]
    _ = ∑ i, ∑ j, f i^2 * f j := by
      rw [sum_pow_char]
      simp only [Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ p : Fin m × Fin m, term u p • g^(degree p).val := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => split (i,j)
    _ = ∑ d : Fin (3*m), ∑ p ∈ bucket d, term u p • g^(degree p).val :=
      (Finset.sum_fiberwise Finset.univ degree (fun p => term u p • g^(degree p).val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      rw [coefficient,Finset.sum_smul]
      exact Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]

theorem cube_coord (B : Module.Basis (Fin m) (ZMod 2) F) (g : F) (h : ∀ i : Fin m, B i = g^i.val)
    (u : Fin (2^m)) (j : Fin m) :
    bitField ((cubeWord B u).val.testBit j.val) = ∑ d : Fin (3*m), coefficient u d * (B.equivFun (g^d.val)) j := by
  have e : B.equivFun ((fieldWord B u)^3) = coords m (cubeWord B u) := by
    change B.equivFun _ = (wordIso m) ((wordIso m).symm (B.equivFun _))
    rw [Equiv.apply_symm_apply]
  change (coords m (cubeWord B u)) j = _
  rw [←e,cube_expand B g h,map_sum,Finset.sum_apply]
  exact Finset.sum_congr rfl fun d _ => by rw [map_smul]; rfl
end
end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits
variable {X F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] {m : ℕ}

theorem cube_circuit (C : List (Sig X)) (u : X → Fin (2^m)) (B : Module.Basis (Fin m) (ZMod 2) F)
    (g : F) (basis : ∀ i : Fin m, B i = g^i.val) (zero : use C (fun _=>false))
    (bits : ∀ i : Fin m, use C (fun x => (u x).val.testBit i.val)) :
    ∃ D, Segment C D (38*m^2) ∧ ∀ j : Fin m, use D (fun x => (cubeWord B (u x)).val.testBit j.val) := by
  classical
  obtain ⟨D,s,pairs⟩ := gather (I:=Fin m × Fin m) C (fun p x => nz (term (u x) p)) 2 (by
    intro p D incl
    simpa only [term,nz_bitField] using add_and D _ _ (lift_use incl (bits p.1)) (lift_use incl (bits p.2)))
  obtain ⟨E,t,cs⟩ := gather (I:=Fin (3*m)) D (fun d x => nz (coefficient (u x) d)) (m*6) (by
    intro d E incl
    obtain ⟨H,v,out⟩ := sum_bits E (bucket d) (fun p x => term (u x) p) (lift_use incl (s.keeps zero))
      (fun p => lift_use incl (pairs p))
    exact ⟨H,v.relax (Nat.mul_le_mul_right 6 (bucket_card d)),out⟩)
  obtain ⟨H,v,outs⟩ := gather (I:=Fin m) E (fun j x => (cubeWord B (u x)).val.testBit j.val) (3*m*6) (by
    intro j H incl
    let f := fun (d : Fin (3*m)) (x : X) => coefficient (u x) d * (B.equivFun (g^d.val)) j
    have known (d : Fin (3*m)) : use H (fun x => nz (f d x)) := by
      cases eq : nz ((B.equivFun (g^d.val)) j) <;> simp only [f,nz_mul,eq,Bool.and_false,Bool.and_true]
      · exact lift_use incl (t.keeps (s.keeps zero))
      · exact lift_use incl (cs d)
    obtain ⟨R,q,out⟩ := sum_bits H Finset.univ f (lift_use incl (t.keeps (s.keeps zero))) known
    refine ⟨R,by simpa using q,?_⟩
    have eq : (fun x => nz (∑ d, f d x)) = (fun x => (cubeWord B (u x)).val.testBit j.val) := by
      funext x
      change nz (∑ d, coefficient (u x) d * (B.equivFun (g^d.val)) j) = _
      rw [←cube_coord B g basis,nz_bitField]
    exact eq ▸ out)
  refine ⟨H,((s.trans t).trans v).relax ?_,outs⟩
  simp only [Fintype.card_prod,Fintype.card_fin]
  nlinarith

end PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits
variable {X : Type*}

theorem low_succ (v i : ℕ) : v % 2^(i+1) = v % 2^i + (if v.testBit i then 2^i else 0) := by
  rw [pow_succ,Nat.mod_mul,Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (v / 2^i) (by decide : 0 < 2)
  by_cases e : v / 2^i % 2 = 1
  · simp [e]
  · have z : v / 2^i % 2 = 0 := by omega
    simp [z]

theorem compare_succ (v t i : ℕ) :
    decide (v % 2^(i+1) < t % 2^(i+1)) =
      if t.testBit i then (!(v.testBit i) || decide (v % 2^i<t % 2^i))
      else (!(v.testBit i) && decide (v % 2^i<t % 2^i)) := by
  rw [low_succ,low_succ]
  have hv := Nat.mod_lt v (show 0<2^i by positivity)
  have ht := Nat.mod_lt t (show 0<2^i by positivity)
  cases e : v.testBit i <;> cases h : t.testBit i <;> simp <;> omega

theorem comparator (C : List (Sig X)) (v : X → ℕ) (t m : ℕ)
    (base : use C (fun _=>false)) (bits : ∀ i : Fin m, use C (fun x => (v x).testBit i.val)) :
    ∃ D, Segment C D (m*2) ∧ use D (fun x => decide ((v x) % 2^m<t % 2^m)) := by
  induction m with
  | zero => exact ⟨C,by simpa using Segment.ident C,by simpa [Nat.mod_one] using base⟩
  | succ m ih =>
    obtain ⟨D,s,old⟩ := ih (fun i => bits i.castSucc)
    have bit := use_neg (s.keeps (bits (Fin.last m)))
    cases h : t.testBit m with
    | false =>
      obtain ⟨E,q,out⟩ := add_and D _ _ bit old
      exact ⟨E,(s.trans q).relax (by omega),by simpa only [compare_succ,h,Bool.false_eq_true,ite_false,neg,Fin.val_last] using out⟩
    | true =>
      obtain ⟨E,q,out⟩ := add_or D _ _ bit old
      exact ⟨E,(s.trans q).relax (by omega),by simpa only [compare_succ,h,ite_true,neg,Fin.val_last] using out⟩

theorem word_eq {n : ℕ} (v w : Fin (2^n)) :
    (∀ i : Fin n, v.val.testBit i.val = w.val.testBit i.val) ↔ v = w := by
  constructor
  · intro h
    apply coords_inj n
    funext i
    simp only [coords,h i]
  · rintro rfl i
    rfl

theorem eq_wire (C : List (Sig X)) (n : ℕ) (v w : X → Fin (2^n)) (base : use C (fun _=>true))
    (bv : ∀ i : Fin n, use C (fun x => (v x).val.testBit i.val))
    (bw : ∀ i : Fin n, use C (fun x => (w x).val.testBit i.val)) :
    ∃ D, Segment C D (8*n) ∧ use D (fun x => decide (v x = w x)) := by
  classical
  let f := fun (i : Fin n) (x : X) => decide ((v x).val.testBit i.val = (w x).val.testBit i.val)
  obtain ⟨D,s,early⟩ := gather C f 6 (by
    intro i D inc
    obtain ⟨E,t,h⟩ := add_xor D _ _ (lift_use inc (bv i)) (lift_use inc (bw i))
    have e : neg (fun x => xor ((v x).val.testBit i.val) ((w x).val.testBit i.val)) = f i := by
      funext x
      dsimp only [f,neg]
      cases (v x).val.testBit i.val <;> cases (w x).val.testBit i.val <;> rfl
    exact ⟨E,t,e ▸ use_neg h⟩)
  obtain ⟨E,t,all⟩ := all_bits D Finset.univ f (s.keeps base) early
  refine ⟨E,(s.trans t).relax (by simp; omega),?_⟩
  simpa only [f,decide_eq_true_eq,Finset.mem_univ,true_implies,word_eq] using all
end PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits
variable {X : Type*}

def low (n : ℕ) (v : ℕ) : Fin (2^n) := ⟨v % 2^n,Nat.mod_lt _ (by positivity)⟩
theorem low_bit (n v : ℕ) (i : Fin n) : (low n v).val.testBit i.val = v.testBit i.val := by
  simp [low,Nat.testBit_mod_two_pow,i.isLt]

theorem const_bit {C : List (Sig X)} (z : use C (fun _=>false)) (o : use C (fun _=>true)) (b : Bool) :
    use C (fun _=>b) := by cases b <;> assumption

theorem selector (C : List (Sig X)) (k a : ℕ) (fits : 2^a ≤ k) (left right : X → Fin (2^k))
    (z : use C (fun _=>false)) (o : use C (fun _=>true))
    (l : ∀ i : Fin k, use C (fun x => (left x).val.testBit i.val))
    (r : ∀ i : Fin k, use C (fun x => (right x).val.testBit i.val)) :
    ∃ D, Segment C D ((2^a)*(8*a+2) + 2^a*2) ∧
      use D (fun x => (left x).val.testBit ((right x).val % 2^a)) := by
  classical
  let addr := fun x => low a (right x).val
  have small : a ≤ k := (Nat.le_of_lt (Nat.lt_two_pow_self)).trans fits
  let hit := fun (j : Fin (2^a)) (x : X) => decide (addr x=j) && (left x).val.testBit j.val
  obtain ⟨D,s,known⟩ := gather C hit (8*a+2) (by
    intro j D inc
    have bit (i : Fin a) : use D (fun x => (addr x).val.testBit i.val) := by
      simpa only [addr,low_bit] using lift_use inc (r ⟨i.val,i.isLt.trans_le small⟩)
    obtain ⟨E,q,out⟩ := eq_wire D a addr (fun _=>j) (lift_use inc o) bit
      (fun i=>const_bit (lift_use inc z) (lift_use inc o) _)
    obtain ⟨H,t,both⟩ := add_and E _ _ out (q.keeps (lift_use inc (l ⟨j.val,j.isLt.trans_le fits⟩)))
    exact ⟨H,q.trans t,both⟩)
  obtain ⟨E,t,out⟩ := any_bits D Finset.univ hit (s.keeps z) known
  refine ⟨E,by simpa using s.trans t,?_⟩
  convert out using 1
  funext x
  symm
  cases hv : (left x).val.testBit ((right x).val % 2^a) with
  | true =>
    refine @decide_eq_true _ Finset.decidableExistsAndFinsetCoe ?_
    refine ⟨addr x,Finset.mem_univ _,?_⟩
    simp only [hit,decide_true,Bool.true_and]
    exact hv
  | false =>
    refine @decide_eq_false _ Finset.decidableExistsAndFinsetCoe ?_
    rintro ⟨i,_,hi⟩
    obtain ⟨eq,yes⟩ := Bool.and_eq_true_iff.mp hi
    have e : addr x = i := of_decide_eq_true eq
    subst i
    exact Bool.noConfusion (hv.symm.trans yes)
end PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits
open PEqualNP.MetaComplexity

theorem tableIndex_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
      + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

theorem tableIndex_lt : ∀ {n : ℕ} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n ih =>
    intro x
    rw [tableIndex_succ, pow_succ]
    have := ih (fun i : Fin n => x i.castSucc)
    split <;> omega

theorem testBit_tableIndex : ∀ {n : ℕ} (x : Fin n → Bool) (i : Fin n),
    Nat.testBit (tableIndex x) i = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n ih =>
    intro x i
    have hlt := tableIndex_lt (fun i : Fin n => x i.castSucc)
    rw [tableIndex_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
    · have hj : (j.castSucc : ℕ) = (j : ℕ) := rfl
      rw [hj]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]
        exact ih _ j
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero]
        exact ih _ j

def leftWord (k : ℕ) (x : Fin (k+k) → Bool) : Fin (2^k) :=
  Fin.ofNat _ (tableIndex fun i : Fin k => x (Fin.castAdd k i))
def rightWord (k : ℕ) (x : Fin (k+k) → Bool) : Fin (2^k) :=
  Fin.ofNat _ (tableIndex fun i : Fin k => x (Fin.natAdd k i))

theorem input_words (k : ℕ) :
    (∀ i : Fin k, use (initial (k+k)) (fun x => (leftWord k x).val.testBit i.val)) ∧
    (∀ i : Fin k, use (initial (k+k)) (fun x => (rightWord k x).val.testBit i.val)) := by
  constructor
  · intro i
    simpa only [leftWord,Fin.val_ofNat,Nat.mod_eq_of_lt (tableIndex_lt _),testBit_tableIndex] using input (k+k) (Fin.castAdd k i)
  · intro i
    simpa only [rightWord,Fin.val_ofNat,Nat.mod_eq_of_lt (tableIndex_lt _),testBit_tableIndex] using input (k+k) (Fin.natAdd k i)
end PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits
variable {X F : Type*} [Field F] [Algebra (ZMod 2) F] [CharP F 2] {m k : ℕ}

omit [CharP F 2] in
theorem member_prefix (B : Module.Basis (Fin m) (ZMod 2) F) (hk : 2*m ≤ k) (t : ℕ) (z : Fin (2^k)) :
    z.val ∈ (firstWords m t).image (fun i => ((prefixEmbedding B k hk) i).val) ↔
      (low m z.val).val < t ∧ z = (prefixEmbedding B k hk) (low m z.val) := by
  constructor
  · intro mem
    obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp mem
    have e : low m z.val = u := Fin.ext (by
      change z.val % 2^m = u.val
      rw [←eq]
      exact pack_low _ _)
    rw [e]
    exact ⟨(Finset.mem_filter.mp hu).2,Fin.ext eq.symm⟩
  · rintro ⟨lt,eq⟩
    exact Finset.mem_image.mpr ⟨_,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩,congrArg Fin.val eq.symm⟩

theorem mark_circuit (C : List (Sig X)) (B : Module.Basis (Fin m) (ZMod 2) F)
    (g : F) (basis : ∀ i : Fin m, B i = g^i.val) (hk : 2*m ≤ k) (t : ℕ) (ht : t ≤ 2^m)
    (v : X → Fin (2^k)) (z : use C (fun _=>false)) (o : use C (fun _=>true))
    (bits : ∀ i : Fin k, use C (fun x => (v x).val.testBit i.val)) :
    ∃ D, Segment C D (38*m^2+8*k+m*2+2) ∧ use D (fun x =>
      decide ((v x).val ∈ (firstWords m t).image (fun i=>((prefixEmbedding B k hk) i).val))) := by
  classical
  let u := fun x => low m (v x).val
  let w := fun x => (prefixEmbedding B k hk) (u x)
  have lo (i : Fin m) : use C (fun x => (u x).val.testBit i.val) := by
    simpa only [u,low_bit] using bits ⟨i.val,by have := i.isLt; omega⟩
  obtain ⟨D,s,cube⟩ := cube_circuit C u B g basis z lo
  have packed (i : Fin k) : use D (fun x => (w x).val.testBit i.val) := by
    have e (x : X) : (w x).val.testBit i.val = if i.val < m then (u x).val.testBit i.val
        else (cubeWord B (u x)).val.testBit (i.val-m) := by
      change ((u x).val + 2^m * (cubeWord B (u x)).val).testBit i.val = _
      rw [Nat.add_comm,Nat.testBit_two_pow_mul_add _ (u x).isLt]
    simp only [e]
    by_cases hi : i.val < m
    · simp only [hi,ite_true]
      exact s.keeps (lo ⟨_,hi⟩)
    · simp only [hi,ite_false]
      by_cases hj : i.val-m < m
      · exact cube ⟨_,hj⟩
      · have ez (x : X) : (cubeWord B (u x)).val.testBit (i.val-m) = false :=
          Nat.testBit_lt_two_pow ((cubeWord B (u x)).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
        simpa only [ez] using s.keeps z
  obtain ⟨E,q,matchWord⟩ := eq_wire D k v w (s.keeps o) (fun i=>s.keeps (bits i)) packed
  have cmp : ∃ H, Segment E H (m*2) ∧ use H (fun x => decide ((u x).val < t)) := by
    rcases ht.lt_or_eq with h|rfl
    · obtain ⟨H,p,lt⟩ := comparator E (fun x=>(v x).val) t m (q.keeps (s.keeps z))
        (fun i=>q.keeps (s.keeps (bits ⟨i.val,by have := i.isLt; omega⟩)))
      refine ⟨H,p,?_⟩
      convert lt using 1
      funext x
      apply Bool.eq_iff_iff.mpr
      simp [u,low,Nat.mod_eq_of_lt h]
      exact @decide_eq_true_iff _ _
    · exact ⟨E,(Segment.ident E).relax (Nat.zero_le _),by simpa only [(u _).isLt,decide_true] using q.keeps (s.keeps o)⟩
  obtain ⟨H,p,lt⟩ := cmp
  obtain ⟨R,n,out⟩ := add_and H _ _ lt (p.keeps matchWord)
  refine ⟨R,((s.trans q).trans p).trans n,?_⟩
  simpa only [member_prefix, Bool.decide_and, w,u] using out
end PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits
theorem represent {k a m : ℕ} (hk : 2*m ≤ k) (fits : 2^a ≤ k) {F : Type*}
    [Field F] [Algebra (ZMod 2) F] [CharP F 2] (B : Module.Basis (Fin m) (ZMod 2) F)
    (g : F) (basis : ∀ i : Fin m, B i=g^i.val) (t : ℕ) (ht : t ≤ 2^m) :
    let D := (firstWords m t).image fun u => ((prefixEmbedding B k hk) u).val
    PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k:=k) (l:=k) (raw a D)) (150*(k+1)^2) := by
  classical
  dsimp only
  let C := initial (k+k)
  let v := fun x => shift k (leftWord k x) (rightWord k x)
  obtain ⟨left,right⟩ := input_words k
  obtain ⟨D,s,z,o⟩ := add_constants C
  obtain ⟨E,q,bits⟩ := gather D (fun (i : Fin k) x => (v x).val.testBit i.val) 6 (by
    intro i E inc
    simpa only [v,shift,Nat.testBit_xor] using add_xor E _ _ (lift_use inc (s.keeps (left i))) (lift_use inc (s.keeps (right i))))
  obtain ⟨H,p,mark⟩ := mark_circuit E B g basis hk t ht v (q.keeps z) (q.keeps o) bits
  obtain ⟨R,h,sel⟩ := selector H k a fits (leftWord k) (rightWord k) (p.keeps (q.keeps z)) (p.keeps (q.keeps o))
    (fun i=>p.keeps (q.keeps (s.keeps (left i)))) (fun i=>p.keeps (q.keeps (s.keeps (right i))))
  obtain ⟨W,l,out⟩ := add_xor R _ _ sel (h.keeps mark)
  apply finish (k+k) _ _ W _ out
  apply ((((s.trans q).trans p).trans h).trans l).relax
  simp only [Fintype.card_fin]
  have hm : m ≤ k := by omega
  have ha : a ≤ k := (Nat.le_of_lt Nat.lt_two_pow_self).trans fits
  have mm := Nat.mul_le_mul hm hm
  have ar := Nat.mul_le_mul fits ha
  nlinarith

end PEqualNP.Outside.L_meta_25879_aux.Cubic.Circuits

namespace PEqualNP.Outside.L_meta_25879_aux.Cubic
theorem complete_proof (k a : ℕ) (ha : 2 ≤ a) (hk : 2*2^a ≤ k) :
    ∃ enc : Fin (2^(k/2)) ↪ Fin (2^k), (∀ i, (enc i).val % 2^(k/2) = i.val) ∧
      ∀ t, t ≤ 2^(k/2) → let D := (firstWords (k/2) t).image fun i => (enc i).val
        D.card=t ∧ PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k:=k) (l:=k) (raw a D)) (150*(k+1)^2) ∧
        @separated k a D (2*(if t ≤ 2^a then t else t-2)) := by
  have pos : 0 < 2^a := by positivity
  obtain ⟨B,g,basis⟩ := binary_power_basis (k/2) (by omega)
  let enc := prefixEmbedding B k (show 2*(k/2) ≤ k by omega)
  refine ⟨enc,fun i => pack_low _ _,?_⟩
  intro t ht
  obtain ⟨card,dist⟩ := geometric_part rfl ha hk ht B
  exact ⟨card,Circuits.represent (by omega) (by omega) B g basis t ht,dist⟩
end PEqualNP.Outside.L_meta_25879_aux.Cubic

namespace PEqualNP.Outside.L_meta_25879_aux

theorem supportSeq : (∀ k a : ℕ, (2 ≤ a ∧ 2*2^a ≤ k) →
  let N := 2^k
  let r := 2^a
  let I := Fin N
  let target := fun (D : Finset ℕ) (x y : I) =>
    xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
  let separated := fun (D : Finset ℕ) (d : ℕ) =>
    ∀ f g : I → Bool,
      let T := fun x y : I => xor (target D x y) (xor (f x) (g y))
      ∀ i j : I, i ≠ j →
        d ≤ (Finset.univ.filter (fun z : I => T i z ≠ T j z)).card ∧
        d ≤ (Finset.univ.filter (fun z : I => T z i ≠ T z j)).card
  let Q := 2^(k/2)
  ∃ enc : Fin Q ↪ I,
    (∀ i : Fin Q, (enc i).val % Q = i.val) ∧
    ∀ t : ℕ, t ≤ Q →
      let D := ((Finset.univ : Finset (Fin Q)).filter (fun i => i.val < t)).image (fun i => (enc i).val)
      D.card = t ∧
      PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) (target D))
        (150*(k+1)^2) ∧ separated D (2*(if t ≤ r then t else t-2))) := by
  intro k a h
  exact PEqualNP.Outside.L_meta_25879_aux.Cubic.complete_proof k a h.1 h.2

end PEqualNP.Outside.L_meta_25879_aux

namespace PEqualNP.Outside.L_meta_25879_aux

lemma signDefect : ∀ b c u v : Bool,
    1 - Moment.bitSign b * Moment.bitSign c ≤ (2:ℤ)*
      ((if u ≠ v then 1 else 0) + (if b ≠ u then 1 else 0) + (if c ≠ v then 1 else 0)) := by decide

lemma moment_of_pieces {α : Type*} [Fintype α] [DecidableEq α] (K : Finset α) (π : Equiv.Perm α)
    (B H : α → α → Bool) (p : α → ℕ) (hcap : ∀ t, (K.filter (fun i => p i = t)).card ≤ 3)
    (hsym : ∀ x ∈ K, ∀ y ∈ K, p x ≠ p y → H x (π y) = H y (π x)) :
    let err := (Finset.univ.filter (fun z : α × α => B z.1 z.2 ≠ H z.1 z.2)).card
    (K.card : ℤ)^2 - 4*(3*K.card + 2*(err:ℤ)) ≤
      ∑ x ∈ K, ∑ y ∈ K, Moment.bitSign (B x (π y)) * Moment.bitSign (B y (π x)) := by
  intro err
  let E := fun x y => if B x (π y) ≠ H x (π y) then (1:ℤ) else 0
  let P := fun x y => if p y = p x then (1:ℤ) else 0
  have ene (x y : α) : 0 ≤ E x y := by dsimp [E]; split <;> norm_num
  have ep : (∑ x ∈ K, ∑ y ∈ K, E x y) ≤ (err : ℤ) := by
    calc
      _ ≤ ∑ x ∈ K, ∑ y, E x y := Finset.sum_le_sum fun x _ => Finset.sum_le_univ_sum_of_nonneg (ene x)
      _ ≤ ∑ x, ∑ y, E x y := Finset.sum_le_univ_sum_of_nonneg fun x => Finset.sum_nonneg fun y _ => ene x y
      _ = ∑ x, ∑ y, (if B x y ≠ H x y then (1:ℤ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _; exact Equiv.sum_comp π (fun y => if B x y ≠ H x y then (1:ℤ) else 0)
      _ = _ := by rw [← Fintype.sum_prod_type']; exact Finset.sum_boole _ _
  have pp : (∑ x ∈ K, ∑ y ∈ K, P x y) ≤ (K.card:ℤ)*3 := by
    calc
      _ ≤ ∑ _x ∈ K, (3:ℤ) := by
        apply Finset.sum_le_sum; intro x _
        dsimp only [P]; rw [Finset.sum_boole]; exact_mod_cast hcap (p x)
      _ = _ := by simp
  have point (x) (hx : x ∈ K) (y) (hy : y ∈ K) :
      1 - Moment.bitSign (B x (π y)) * Moment.bitSign (B y (π x)) ≤ 2*(P x y + E x y + E y x) := by
    have hb := signDefect (B x (π y)) (B y (π x)) (H x (π y)) (H y (π x))
    have hp : (if H x (π y) ≠ H y (π x) then (1:ℤ) else 0) ≤ P x y := by
      by_cases h : p y = p x
      · simp only [P,h,ite_true]; split <;> norm_num
      · simp [P,h,hsym x hx y hy (Ne.symm h)]
    dsimp only [E]; linarith only [hb,hp]
  have summed := Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => point x hx y hy))
  have lhs : (∑ x ∈ K, ∑ y ∈ K, (1 - Moment.bitSign (B x (π y))*Moment.bitSign (B y (π x)))) =
      (K.card:ℤ)^2 - ∑ x ∈ K, ∑ y ∈ K, Moment.bitSign (B x (π y))*Moment.bitSign (B y (π x)) := by
    simp [Finset.sum_sub_distrib,sq]
  have swapE : (∑ x ∈ K, ∑ y ∈ K, E y x) = ∑ x ∈ K, ∑ y ∈ K, E x y := Finset.sum_comm
  rw [lhs] at summed
  simp_rw [← Finset.mul_sum,Finset.sum_add_distrib,swapE] at summed
  have ne : (0:ℤ) ≤ err := Nat.cast_nonneg _
  have nk : (0:ℤ) ≤ K.card := Nat.cast_nonneg _
  linarith only [ep,pp,summed,ne,nk]

lemma eight_times (a : ℕ) (ha : 6 ≤ a) : 8*a ≤ 2^a := by
  induction a,ha using Nat.le_induction with
  | base => decide
  | succ a ha ih => rw [pow_succ]; omega

lemma scale_size (a k : ℕ) (ha : 6 ≤ a) (hk : 2*2^a ≤ k) :
    1200 ≤ 2^k ∧ 20 ≤ 2^(k/2) ∧ 1024*2^(k/2) ≤ 2^k := by
  have ar : 64 ≤ 2^a := (Nat.pow_le_pow_right (by decide : 0 < 2) ha : 2^6 ≤ 2^a)
  have h1 := (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 11 ≤ k) : 2^11 ≤ 2^k)
  have h2 := (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 5 ≤ k/2) : 2^5 ≤ 2^(k/2))
  refine ⟨by omega,by omega,?_⟩
  change 2^10 * 2^(k/2) ≤ _
  rw [← pow_add]; apply Nat.pow_le_pow_right (by decide); omega

lemma force_error (n q a cap b v e h : ℕ) (hn : 1200 ≤ n) (hq : 20 ≤ q) (hqn : 1024*q ≤ n)
    (hv : v = q-10) (hb : 16*b ≤ 33*n) (hraw : 32*n ≤ 15*b+50+44*(e/v)+h)
    (hcap : 8*a*cap ≤ n) (hsmall : h ≤ n)
    (hquad : h^2 ≤ 4*(3*h+2*(e+n*q)) + 2*a*cap*h) : n*q < 128*e := by
  by_contra! hbad
  have vpos : 0 < v := by omega
  have v2 : q ≤ 2*v := by omega
  have divbound : 64*(e/v) ≤ n := by
    have he := Nat.div_mul_le_self e v
    have hmul := Nat.mul_le_mul_left n v2
    have hdiv : 64*(e/v)*v ≤ n*v := by nlinarith only [hbad,he,hmul]
    exact Nat.le_of_mul_le_mul_right hdiv vpos
  have nh : n ≤ 3*h := by omega
  have mulcap := Nat.mul_le_mul_right h hcap
  have hs := Nat.mul_le_mul_right h nh
  have n2 := Nat.mul_le_mul nh nh
  have q2 := Nat.mul_le_mul_left n hqn
  have eqb : e ≤ n*q := by omega
  have nqbig := Nat.mul_le_mul_left n (by omega : 1 ≤ q)
  nlinarith only [hquad,mulcap,hs,n2,q2,eqb,hsmall,nqbig,hn]

end PEqualNP.Outside.L_meta_25879_aux

namespace PEqualNP.Outside.L_meta_25879_aux

open PEqualNP.CircuitLowerBounds

def nameKey {k : ℕ} (z : Fin (2^k) × Fin (2^k)) := z.1.val ^^^ z.2.val

def switchedBase {k : ℕ} (a : ℕ) (f g : Fin (2^k) → Bool) (z : Fin (2^k) × Fin (2^k)) :=
  xor (z.1.val.testBit (z.2.val % 2^a)) (xor (f z.1) (g z.2))

lemma full_lower (k a : ℕ) (ha : 6 ≤ a) (hk : 2*2^a ≤ k) (G : Finset ℕ)
    (hrange : G ⊆ Finset.range (2^k)) (hcard : G.card = 2^(k/2)) (f g : Fin (2^k) → Bool)
    (C : Circuit) (fan : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (budget : 16*(C.gates.countP (fun gate => gate.inputs.length == 2)) ≤ 33*(2^k))
    (sep : let T := fun (x y : Fin (2^k)) => xor (switchedBase a f g (x,y)) (decide (nameKey (x,y) ∈ G))
           ∀ i j, i ≠ j → 2*(2^(k/2)-2) ≤ (Finset.univ.filter (fun z => T i z ≠ T j z)).card ∧
             2*(2^(k/2)-2) ≤ (Finset.univ.filter (fun z => T z i ≠ T z j)).card) :
    2^k*G.card < 128*discrepancy nameKey (fun z => C.eval (PEqualNP.Represents.oneEach z.1 z.2)) (switchedBase a f g) G := by
  classical
  let N := 2^k
  let Q := 2^(k/2)
  let r := 2^a
  let I := Fin N
  let B := fun (x y : I) => switchedBase a f g (x,y)
  let T := fun (x y : I) => xor (B x y) (decide (nameKey (x,y) ∈ G))
  let H := fun (i j : I) => C.eval (PEqualNP.Represents.oneEach i j)
  let e := (Finset.univ.filter (fun z : I × I => H z.1 z.2 ≠ T z.1 z.2)).card
  let b := C.gates.countP (fun gate => gate.inputs.length == 2)
  let v := Q-10
  obtain ⟨hn,hq,hqn⟩ := scale_size a k ha hk
  change 1200 ≤ N at hn
  change 20 ≤ Q at hq
  change 1024*Q ≤ N at hqn
  change ∀ i j : I, i ≠ j → 2*(Q-2) ≤ _ ∧ 2*(Q-2) ≤ _ at sep
  have vd : 17+2*(v-1) ≤ 2*(Q-2) := by dsimp [v]; omega
  obtain ⟨π,S,p,hcount,hcap,hsym,_⟩ := extraction N (by omega) T C fan v (by dsimp [v]; omega)
    (fun i j h => vd.trans (sep i j h).1) (fun i j h => vd.trans (sep i j h).2)
  change 32*N ≤ 15*b+50+44*(e/v)+S.card at hcount
  let eb := (Finset.univ.filter (fun z : I × I => B z.1 z.2 ≠ H z.1 z.2)).card
  have he : eb ≤ e+N*Q := by
    have hb : Extraction.dist (fun z : I × I => B z.1 z.2) (fun z => T z.1 z.2) = N*Q := by
      change discrepancy nameKey (switchedBase a f g) (switchedBase a f g) G = _
      rw [exact_low]; exact (xor_fibres k G hrange).trans (congrArg (fun w => 2^k * w) hcard)
    have ht : Extraction.dist (fun z : I × I => T z.1 z.2) (fun z => H z.1 z.2) = e := by
      rw [Extraction.dist_symm]; rfl
    have tri := Extraction.dist_triangle (fun z : I × I => B z.1 z.2) (fun z => T z.1 z.2) (fun z => H z.1 z.2)
    rw [hb,ht] at tri
    exact tri.trans (by omega)
  have ar := eight_times a ha
  have hak : a ≤ k := by omega
  let cap := 2^(k-a)
  let addr := fun x : I => (⟨x.val % r,lt_of_lt_of_le (Nat.mod_lt _ (by positivity : 0 < 2^a)) (by dsimp [r];omega)⟩ : Fin k)
  have prod : r*cap=N := by dsimp only [r,cap,N]; rw [←pow_add,Nat.add_sub_of_le hak]
  have fibre (j : Fin k) : (S.filter (fun i => addr (π i) = j)).card ≤ cap := by
    let F := S.filter (fun i => addr (π i) = j)
    let idx := fun i : I => (π i).val / r
    have bounded (i : I) : idx i < cap := by
      dsimp [idx]; apply (Nat.div_lt_iff_lt_mul (by positivity : 0<2^a)).mpr
      exact lt_of_lt_of_eq (π i).isLt (prod.symm.trans (Nat.mul_comm r cap))
    let map := fun i : I => (⟨idx i,bounded i⟩ : Fin cap)
    have hmap : Set.InjOn map (F : Set I) := by
      intro i hi u hu eq
      have e1 : idx i = idx u := congrArg Fin.val eq
      have e2 : (π i).val % r = (π u).val % r := congrArg Fin.val ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hu).2.symm)
      apply π.injective; apply Fin.ext
      have ei := Nat.mod_add_div (π i).val r
      have eu := Nat.mod_add_div (π u).val r
      change (π i).val / r = (π u).val / r at e1
      rw [e1,e2] at ei; omega
    calc
      _ = (F.image map).card := (Finset.card_image_of_injOn hmap).symm
      _ ≤ Fintype.card (Fin cap) := Finset.card_le_univ _
      _ = _ := Fintype.card_fin _
  let d := 3*S.card+2*eb
  have hm := moment_of_pieces S π B H p hcap hsym
  have hs := spectral k addr π S f (fun y => g (π y)) d (by
    change (S.card:ℤ)^2 - 4*(d:ℤ) ≤ _
    dsimp only [d]; push_cast; exact hm) a cap (by omega) (by exact prod.ge) fibre
  have few : 8*a*cap ≤ N := by rw [←prod]; exact Nat.mul_le_mul_right cap ar
  have final := force_error N Q a cap b v e S.card hn hq hqn rfl budget hcount few
    (by simpa [I] using Finset.card_le_univ S) (by dsimp only [d] at hs; omega)
  rw [hcard]; exact final

end PEqualNP.Outside.L_meta_25879_aux

namespace PEqualNP.Outside.L_meta_25879_aux.Bare

open PEqualNP.CircuitLowerBounds
open Cubic.Circuits

lemma posOr {X : Type*} (C : List (Sig X)) (f g : Sig X) (hf : f ∈ C) (hg : g ∈ C) :
    ∃ D, Segment C D 1 ∧ (fun x => f x || g x) ∈ D := by
  obtain ⟨i,hi⟩ := wire hf
  obtain ⟨j,hj⟩ := wire hg
  let out : Sig X := fun x => f x || g x
  refine ⟨C++[out],append_gate ⟨.or,[i,j]⟩ (by simp [good]) out ?_,by simp [out]⟩
  intro x
  change ((values C x).getD i false || ((values C x).getD j false || false)) = out x
  rw [hi,hj,Bool.or_false]

lemma posAnd {X : Type*} (C : List (Sig X)) (f g : Sig X) (hf : f ∈ C) (hg : g ∈ C) :
    ∃ D, Segment C D 1 ∧ (fun x => f x && g x) ∈ D := by
  obtain ⟨i,hi⟩ := wire hf
  obtain ⟨j,hj⟩ := wire hg
  let out : Sig X := fun x => f x && g x
  refine ⟨C++[out],append_gate ⟨.and,[i,j]⟩ (by simp [good]) out ?_,by simp [out]⟩
  intro x
  change ((values C x).getD i false && ((values C x).getD j false && true)) = out x
  rw [hi,hj,Bool.and_true]

lemma anyPos {X J : Type*} [DecidableEq J] (C : List (Sig X)) (s : Finset J) (f : J → Sig X)
    (hz : (fun _ : X => false) ∈ C) (hf : ∀ i ∈ s, f i ∈ C) :
    ∃ D, Segment C D s.card ∧ (fun x => decide (∃ i ∈ s, f i x = true)) ∈ D := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨C,Segment.ident _,by simpa using hz⟩
  | @insert i s hi ih =>
    obtain ⟨D,sD,hD⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    obtain ⟨E,sE,hE⟩ := posOr D (f i) _ (sD.1 _ (hf i (Finset.mem_insert_self _ _))) hD
    refine ⟨E,by simpa [hi] using sD.trans sE,?_⟩
    convert hE using 1
    funext x; apply Bool.eq_iff_iff.mpr; simp

lemma gather {X J : Type*} [DecidableEq J] (C : List (Sig X)) (S : Finset J) (f : J → Sig X) (c : J → ℕ)
    (step : ∀ i ∈ S, ∀ D, Includes C D → ∃ E, Segment D E (c i) ∧ f i ∈ E) :
    ∃ E, Segment C E (∑ i ∈ S,c i) ∧ ∀ i ∈ S, f i ∈ E := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨C,by simpa using Segment.ident C,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨D,sD,hD⟩ := ih (fun j hj => step j (Finset.mem_insert_of_mem hj))
    obtain ⟨E,sE,hE⟩ := step i (Finset.mem_insert_self _ _) D sD.1
    refine ⟨E,by simpa [hi,Nat.add_comm] using sD.trans sE,?_⟩
    intro j hj; rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hE
    · exact sE.1 _ (hD j hj)

lemma bank {X J T : Type*} [Fintype J] [DecidableEq J] [Fintype T] [DecidableEq T]
    (C : List (Sig X)) (sel : X → J) (cls : J → T) (hz : (fun _ : X => false) ∈ C)
    (hf : ∀ i, (fun x => decide (sel x = i)) ∈ C) :
    ∃ D, Segment C D (Fintype.card J) ∧ ∀ b : T, (fun x => decide (cls (sel x) = b)) ∈ D := by
  classical
  let cell := fun b : T => Finset.univ.filter (fun i => cls i = b)
  have cost : (∑ b : T, (cell b).card) = Fintype.card J := by
    rw [← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ) (f := cls) (fun _ _ => Finset.mem_univ _)).symm
  obtain ⟨D,hD,out⟩ := gather C (Finset.univ : Finset T) (fun b x => decide (cls (sel x) = b))
    (fun b => (cell b).card) (by
      intro b _ D inc
      obtain ⟨E,hE,mem⟩ := anyPos D (cell b) (fun i x => decide (sel x=i)) (inc _ hz) (fun i _ => inc _ (hf i))
      refine ⟨E,hE,?_⟩
      convert mem using 1
      funext x; apply Bool.eq_iff_iff.mpr; simp [cell])
  exact ⟨D,cost ▸ hD,fun b => out b (Finset.mem_univ _)⟩

lemma factorized (n m : ℕ) {R T : Type*} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
    (row : Fin n → R) (col : Fin m → T) (adj : R → T → Bool) :
    ∃ C : Circuit, (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.length ≤ 1+n+m + Fintype.card T*(Fintype.card R+1) + Fintype.card T ∧
      ∀ i j, C.eval (PEqualNP.Represents.oneEach i j) = adj (row i) (col j) := by
  classical
  let X := Fin n × Fin m
  let L : Fin n → Sig X := fun i z => decide (z.1 = i)
  let M : Fin m → Sig X := fun j z => decide (z.2 = j)
  let init := List.ofFn L ++ List.ofFn M
  have st : Segment init (init++[fun _ => false]) 1 := append_gate ⟨.or,[]⟩ (by simp [good]) _ (fun _=>rfl)
  have zin : (fun _ : X => false) ∈ init++[fun _ => false] := by simp
  have hL (i : Fin n) : L i ∈ init := List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have hM (j : Fin m) : M j ∈ init := List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
  obtain ⟨C1,b1,r1⟩ := bank (init++[fun _ => false]) Prod.fst row zin (fun i => st.1 _ (hL i))
  obtain ⟨C2,b2,c2⟩ := bank C1 Prod.snd col (b1.1 _ zin) (fun i => b1.1 _ (st.1 _ (hM i)))
  let leaf : T → Sig X := fun b z => adj (row z.1) b && decide (col z.2 = b)
  obtain ⟨C3,b3,h3⟩ := gather C2 Finset.univ leaf (fun _ => Fintype.card R + 1) (by
    intro b _ D inc
    let sel := Finset.univ.filter (fun i => adj i b = true)
    obtain ⟨E,sE,hE⟩ := anyPos D sel (fun i (z:X) => decide (row z.1 = i))
      (inc _ (b2.1 _ (b1.1 _ zin))) (fun i _ => inc _ (b2.1 _ (r1 i)))
    have he : (fun (z:X) => adj (row z.1) b) ∈ E := by
      convert hE using 1
      funext z; apply Bool.eq_iff_iff.mpr; simp [sel]
    obtain ⟨F,sF,hF⟩ := posAnd E _ _ he (sE.1 _ (inc _ (c2 b)))
    exact ⟨F,(sE.trans sF).relax (by have := Finset.card_le_univ sel; omega),hF⟩)
  obtain ⟨C4,b4,h4⟩ := anyPos C3 Finset.univ leaf (b3.1 _ (b2.1 _ (b1.1 _ zin))) (fun i _ => h3 i (Finset.mem_univ _))
  have out : (fun (z:X) => adj (row z.1) (col z.2)) ∈ C4 := by
    convert h4 using 1
    funext z; apply Bool.eq_iff_iff.mpr; simp [leaf]
  obtain ⟨w,hw⟩ := wire out
  obtain ⟨_,gs,hn,hg,hv⟩ := (((st.trans b1).trans b2).trans b3).trans b4
  refine ⟨⟨gs,w⟩,fun g hg' => (hg g hg').2,?_,?_⟩
  · simpa using hn
  · intro i j
    have vv : values init (i,j) = PEqualNP.Represents.oneEach i j := by
      simp only [values,init,L,M,PEqualNP.Represents.oneEach,List.map_append,List.map_ofFn,Function.comp_def]
      simp [eq_comm]
    change (run gs _).getD w false = _
    rw [← vv, hv]; exact hw (i,j)

lemma small (k a : ℕ) (ha : 6 ≤ a) (hk : 2*2^a ≤ k) (f g : Fin (2^k) → Bool) :
    ∃ C : Circuit, (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) ∧
      16*(C.gates.countP (fun gate => gate.inputs.length == 2)) ≤ 33*(2^k) ∧
      ∀ x y, C.eval (PEqualNP.Represents.oneEach x y) = xor (x.val.testBit (y.val % 2^a)) (xor (f x) (g y)) := by
  let r := 2^a
  let row := fun (x : Fin (2^k)) (j : Fin r) => xor (x.val.testBit j.val) (f x)
  let col := fun y : Fin (2^k) => ((⟨y.val % r,Nat.mod_lt _ (by positivity : 0 < 2^a)⟩ : Fin r), g y)
  obtain ⟨C,hg,hs,h⟩ := factorized _ _ row col (fun u b => xor (u b.1) b.2)
  have hcnt := List.countP_le_length (p := fun gate : Gate => gate.inputs.length == 2) (l := C.gates)
  have hlen : C.gates.length ≤ 1+2^k+2^k+(r*2)*(2^r+1)+r*2 := by simpa [Fintype.card_fun] using hs
  have hr : 64 ≤ r := (Nat.pow_le_pow_right (by decide : 0<2) ha : 2^6 ≤ 2^a)
  have large (j : ℕ) (hj : 16 ≤ j) : 64*j+64 ≤ 2^j := by
    induction j,hj using Nat.le_induction with
    | base => decide
    | succ j hj ih => rw [pow_succ]; omega
  have hpow := large r (by omega)
  have hsq : 2^r * 2^r ≤ 2^k := by rw [←pow_add]; apply Nat.pow_le_pow_right (by decide); omega
  have hmul := Nat.mul_le_mul_right (2^r) hpow
  have hrmul := Nat.mul_le_mul_left r (by omega : 2 ≤ 2^r)
  refine ⟨C,hg,?_,?_⟩
  · nlinarith only [hcnt,hlen,hsq,hmul,hrmul,hpow]
  · intro x y; simpa [row,col,r,Bool.xor_assoc] using h x y

end PEqualNP.Outside.L_meta_25879_aux.Bare

open PEqualNP.Outside.L_meta_25879_aux

theorem PEqualNP.Outside.L_meta_25879 : (∀ k a : ℕ, (6 ≤ a ∧ 2*2^a ≤ k) →
  let N := 2^k
  let r := 2^a
  let I := Fin N
  let target := fun (D : Finset ℕ) (x y : I) =>
    xor (x.val.testBit (y.val % r)) (decide (Nat.xor x.val y.val ∈ D))
  let Q := 2^(k/2)
  let fits := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ 16*(C.gates.countP (fun g => g.inputs.length == 2)) ≤ 33*N
  let table := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : I) =>
    C.eval (PEqualNP.Represents.oneEach x y)
  ∃ Γ : Finset ℕ, Γ ⊆ Finset.range N ∧ Γ.card = Q ∧
    PEqualNP.Represents.HasLitSize (k+k) (PEqualNP.Represents.adjFun (k := k) (l := k) (target Γ))
      (150*(k+1)^2) ∧
    ∀ f g : I → Bool,
      let loss := fun (H : I → I → Bool) (D : Finset ℕ) =>
        (Finset.univ.filter (fun z : I × I => H z.1 z.2 ≠ xor (target D z.1 z.2) (xor (f z.1) (g z.2)))).card
      ∃ C₀, fits C₀ ∧ (∀ D : Finset ℕ, D ⊆ Γ → loss (table C₀) D = N*D.card) ∧
        ∀ t : ℕ, t ≤ Q →
          let sets := Γ.powersetCard t
          let opt := N * min t (Q-t)
          (∀ H : I → I → Bool, opt ≤ sets.sup (loss H)) ∧
          (∃ H : I → I → Bool, sets.sup (loss H) = opt) ∧
          ∀ (l : ℕ) (w : Fin l → ℝ) (C : Fin l → PEqualNP.CircuitLowerBounds.Circuit),
            (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 → (∀ i, fits (C i)) →
            ∃ D ∈ sets,
              let err := ∑ i : Fin l, w i * (loss (table (C i)) D : ℝ)
              (opt : ℝ) ≤ err ∧ (Q < 2*t →
                ((128*(N*(Q-t))+N*(2*t-Q) : ℕ) : ℝ) < 128*err)) := by
  classical
  intro k a hyp N r I target Q fits table
  obtain ⟨enc,_,prefixes⟩ := supportSeq k a ⟨by omega,hyp.2⟩
  let G := ((Finset.univ : Finset (Fin Q)).filter (fun i => i.val < Q)).image (fun i => (enc i).val)
  obtain ⟨hcard,hlit,hsep⟩ := prefixes Q (le_refl _)
  change G.card = Q at hcard
  have hrange : G ⊆ Finset.range N := by
    intro j hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (enc i).isLt
  refine ⟨G,hrange,hcard,hlit,?_⟩
  intro f g loss
  let key : I × I → ℕ := nameKey
  let base : I × I → Bool := switchedBase a f g
  have swapxor : ∀ a b c : Bool, xor (xor a b) c = xor (xor a c) b := by decide
  have transT (D : Finset ℕ) (x y : I) :
      xor (target D x y) (xor (f x) (g y)) = xor (base (x,y)) (decide (key (x,y) ∈ D)) := swapxor _ _ _
  have heq : loss = fun H D => discrepancy key (fun z => H z.1 z.2) base D := by
    funext H D
    unfold discrepancy
    dsimp only [loss]; simp only [transT]
  rw [heq]
  obtain ⟨C0,hfan,hbudget,hrep⟩ := Bare.small k a hyp.1 hyp.2 f g
  have rep : (fun z : I × I => table C0 z.1 z.2) = base := funext (fun z => hrep z.1 z.2)
  have qpos : 0 < G.card := by rw [hcard]; dsimp [Q]; positivity
  have fibres (D : Finset ℕ) (hd : D ⊆ G) : (Finset.univ.filter (fun z => key z ∈ D)).card = N*D.card :=
    xor_fibres k D (hd.trans hrange)
  refine ⟨C0,⟨hfan,hbudget⟩,fun D hd => ?_,?_⟩
  · change discrepancy key (fun z => table C0 z.1 z.2) base D = N*D.card
    rw [rep,exact_low]; exact fibres D hd
  · intro t ht sets opt
    have ht' : t ≤ G.card := by rwa [hcard]
    obtain ⟨lo,⟨optH,exactH⟩⟩ := unrestricted key base G N t qpos ht' fibres
    refine ⟨fun H => ?_,⟨fun x y => optH (x,y),?_⟩,?_⟩
    · simpa only [hcard] using lo (fun z => H z.1 z.2)
    · simpa only [hcard] using exactH
    · intro l w C hw hw1 hc
      have sep : ∀ i j : I, i ≠ j →
          2*(Q-2) ≤ (Finset.univ.filter (fun z => xor (base (i,z)) (decide (key (i,z) ∈ G)) ≠ xor (base (j,z)) (decide (key (j,z) ∈ G)))).card ∧
          2*(Q-2) ≤ (Finset.univ.filter (fun z => xor (base (z,i)) (decide (key (z,i) ∈ G)) ≠ xor (base (z,j)) (decide (key (z,j) ∈ G)))).card := by
        intro i j hij
        have hs := hsep f g i j hij
        have hd : 2*(Q-2) ≤ 2*(if Q ≤ r then Q else Q-2) := by split <;> omega
        simp only [← transT]
        exact ⟨hd.trans hs.1,hd.trans hs.2⟩
      have hard (i : Fin l) : N*G.card < 128*discrepancy key (fun z => table (C i) z.1 z.2) base G :=
        full_lower k a hyp.1 hyp.2 G hrange hcard f g (C i) (hc i).1 (hc i).2 sep
      simpa only [hcard] using (mixed key base G N t qpos ht' (fibres G Finset.Subset.rfl) l w
        (fun i z => table (C i) z.1 z.2) hw hw1 hard)
