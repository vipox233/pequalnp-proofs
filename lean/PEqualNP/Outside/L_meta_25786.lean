import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25786

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

end PEqualNP.Outside.L_meta_25786

theorem PEqualNP.Outside.L_meta_25786 : ∀ n : ℕ, 2 ≤ n →
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
  obtain ⟨bad, hfar, hbad, hcount⟩ := PEqualNP.Outside.L_meta_25786.marked_results
    T C hg H (fun _ _ => rfl) v hv hrow hcol
  obtain ⟨π,S,p,hS,hcap,hsym⟩ := PEqualNP.Outside.L_meta_25786.structural
    (PEqualNP.Outside.L_meta_25786.ofCircuit (n+n) C) bad hfar
    (fun _ => PEqualNP.Outside.L_meta_25786.codeAt_raw) hbad
    (PEqualNP.Outside.L_meta_25786.ofCircuit_bin _ C hg)
  have hHsym : ∀ i ∈ S, ∀ j ∈ S, p i ≠ p j → H i (π j) = H j (π i) := by
    intro i hi j hj hp
    simpa only [PEqualNP.Outside.L_meta_25786.view_left C hg] using hsym i hi j hj hp
  refine ⟨π,S,p,?_,hcap,hHsym,?_⟩
  · change 32 * n ≤ 15 * b + 50 + 44 * (e / v) + S.card
    change bad.card ≤ 2 * (e / v) at hcount
    change 32 * n ≤ 15 * b + 50 + 22 * bad.card + S.card at hS
    omega
  · exact PEqualNP.Outside.L_meta_25786.conflict_bound T H π S p hcap hHsym
