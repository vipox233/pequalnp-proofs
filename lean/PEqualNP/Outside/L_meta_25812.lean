import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25812_aux.Deficit

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

theorem deficit_bound : ∀ n : ℕ, 2 ≤ n →
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
  obtain ⟨bad, hfar, hbad, hcount⟩ := PEqualNP.Outside.L_meta_25812_aux.Deficit.marked_results
    T C hg H (fun _ _ => rfl) v hv hrow hcol
  obtain ⟨π,S,p,hS,hcap,hsym⟩ := PEqualNP.Outside.L_meta_25812_aux.Deficit.structural
    (PEqualNP.Outside.L_meta_25812_aux.Deficit.ofCircuit (n+n) C) bad hfar
    (fun _ => PEqualNP.Outside.L_meta_25812_aux.Deficit.codeAt_raw) hbad
    (PEqualNP.Outside.L_meta_25812_aux.Deficit.ofCircuit_bin _ C hg)
  have hHsym : ∀ i ∈ S, ∀ j ∈ S, p i ≠ p j → H i (π j) = H j (π i) := by
    intro i hi j hj hp
    simpa only [PEqualNP.Outside.L_meta_25812_aux.Deficit.view_left C hg] using hsym i hi j hj hp
  refine ⟨π,S,p,?_,hcap,hHsym,?_⟩
  · change 32 * n ≤ 15 * b + 50 + 44 * (e / v) + S.card
    change bad.card ≤ 2 * (e / v) at hcount
    change 32 * n ≤ 15 * b + 50 + 22 * bad.card + S.card at hS
    omega
  · exact PEqualNP.Outside.L_meta_25812_aux.Deficit.conflict_bound T H π S p hcap hHsym

end PEqualNP.Outside.L_meta_25812_aux.Deficit


namespace PEqualNP.Outside.L_meta_25812

section TagDist

def lowNat (m x y : ℕ) : ℕ :=
  ((Finset.range m).filter (fun l => x.testBit l && y.testBit l)).card

def crossNat (m d x y : ℕ) : ℕ :=
  ((Finset.range d).filter (fun l =>
    x.testBit (m + l) && y.testBit 0 && y.testBit (l + 1))).card

def tagNat (m d x y : ℕ) : Bool :=
  (lowNat m x y + crossNat m d x y + crossNat m d y x) % 2 == 1

lemma lowNat_comm (m x y : ℕ) : lowNat m x y = lowNat m y x := by
  simp only [lowNat, Bool.and_comm]

lemma tagNat_comm (m d x y : ℕ) : tagNat m d x y = tagNat m d y x := by
  simp only [tagNat, lowNat_comm m x y]
  congr 1
  omega

lemma crossNat_eq_zero_of_lt (m d x y : ℕ) (hy : y < 2 ^ m) : crossNat m d y x = 0 := by
  rw [crossNat, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l _
  have h1 : y < 2 ^ (m + l) := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega))
  simp [Nat.testBit_lt_two_pow h1]

lemma parity_add (a b : ℕ) :
    ((a + b) % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
  have ha : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
  have hb : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [Nat.add_mod, ha, hb]

lemma filter_parity_flip_one (s : Finset ℕ) (P Q : ℕ → Bool) (p : ℕ) (hp : p ∈ s)
    (hother : ∀ l ∈ s, l ≠ p → P l = Q l) :
    ((s.filter (fun l => P l = true)).card % 2 == 1) =
      xor ((s.filter (fun l => Q l = true)).card % 2 == 1) (xor (P p) (Q p)) := by
  have hsplitP : (s.filter (fun l => P l = true)).card =
      (if P p = true then 1 else 0) + ((s.erase p).filter (fun l => P l = true)).card := by
    have h1 : s.filter (fun l => P l = true) =
        (if P p = true then {p} else ∅) ∪ ((s.erase p).filter (fun l => P l = true)) := by
      ext l
      by_cases hlp : l = p
      · subst hlp; by_cases hPp : P l = true <;> simp [hp, hPp]
      · by_cases hPp : P p = true <;> simp [hlp, hPp]
    rw [h1, Finset.card_union_of_disjoint]
    · by_cases hPp : P p = true <;> simp [hPp]
    · by_cases hPp : P p = true <;> simp [hPp]
  have hsplitQ : (s.filter (fun l => Q l = true)).card =
      (if Q p = true then 1 else 0) + ((s.erase p).filter (fun l => Q l = true)).card := by
    have h1 : s.filter (fun l => Q l = true) =
        (if Q p = true then {p} else ∅) ∪ ((s.erase p).filter (fun l => Q l = true)) := by
      ext l
      by_cases hlp : l = p
      · subst hlp; by_cases hQp : Q l = true <;> simp [hp, hQp]
      · by_cases hQp : Q p = true <;> simp [hlp, hQp]
    rw [h1, Finset.card_union_of_disjoint]
    · by_cases hQp : Q p = true <;> simp [hQp]
    · by_cases hQp : Q p = true <;> simp [hQp]
  have herase : (s.erase p).filter (fun l => P l = true) = (s.erase p).filter (fun l => Q l = true) := by
    apply Finset.filter_congr
    intro l hl
    rw [hother l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl)]
  rw [hsplitP, hsplitQ, herase]
  have hsucc : ∀ n : ℕ, ((1 + n) % 2 == 1) = !(n % 2 == 1) := by
    intro n; rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.add_mod, h]
  cases hPp : P p <;> cases hQp : Q p <;> simp [hsucc]

lemma lowNat_parity_xor_pow (m x y p : ℕ) (hp : p < m) :
    (lowNat m x (y ^^^ 2 ^ p) % 2 == 1) = xor (lowNat m x y % 2 == 1) (x.testBit p) := by
  have h := filter_parity_flip_one (Finset.range m)
    (fun l => x.testBit l && (y ^^^ 2 ^ p).testBit l)
    (fun l => x.testBit l && y.testBit l) p (Finset.mem_range.mpr hp) (by
      intro l _ hlp
      rw [Nat.testBit_xor, Nat.testBit_two_pow, decide_eq_false (Ne.symm hlp), Bool.xor_false])
  rw [lowNat, lowNat, h, Nat.testBit_xor, Nat.testBit_two_pow, decide_eq_true rfl, Bool.xor_true]
  cases x.testBit p <;> cases y.testBit p <;> simp

lemma crossNat_parity_xor_pow (m d x y p : ℕ) (hp1 : 1 ≤ p) :
    (crossNat m d x (y ^^^ 2 ^ p) % 2 == 1) =
      xor (crossNat m d x y % 2 == 1)
        (decide (p ≤ d) && y.testBit 0 && x.testBit (m + (p - 1))) := by
  have h0 : (y ^^^ 2 ^ p).testBit 0 = y.testBit 0 := by
    rw [Nat.testBit_xor, Nat.testBit_two_pow, decide_eq_false (by omega), Bool.xor_false]
  by_cases hpd : p ≤ d
  · have hmem : p - 1 ∈ Finset.range d := Finset.mem_range.mpr (by omega)
    have h := filter_parity_flip_one (Finset.range d)
      (fun l => x.testBit (m + l) && (y ^^^ 2 ^ p).testBit 0 && (y ^^^ 2 ^ p).testBit (l + 1))
      (fun l => x.testBit (m + l) && y.testBit 0 && y.testBit (l + 1)) (p - 1) hmem (by
        intro l _ hlp
        rw [h0, Nat.testBit_xor, Nat.testBit_two_pow, decide_eq_false (by omega), Bool.xor_false])
    rw [crossNat, crossNat, h, h0]
    have hp' : p - 1 + 1 = p := by omega
    rw [hp', Nat.testBit_xor, Nat.testBit_two_pow, decide_eq_true rfl, Bool.xor_true,
      decide_eq_true hpd]
    cases x.testBit (m + (p - 1)) <;> cases y.testBit 0 <;> cases y.testBit p <;> simp
  · have heq : crossNat m d x (y ^^^ 2 ^ p) = crossNat m d x y := by
      unfold crossNat
      congr 1
      apply Finset.filter_congr
      intro l hl
      have hl' := Finset.mem_range.mp hl
      rw [h0, Nat.testBit_xor, Nat.testBit_two_pow, decide_eq_false (by omega), Bool.xor_false]
    rw [heq, decide_eq_false hpd]
    simp

lemma involution_half_card {α : Type*} [DecidableEq α] (Y : Finset α) (φ : α → α) (P : α → Bool)
    (target : Bool)
    (hmem : ∀ y ∈ Y, φ y ∈ Y)
    (hinv : ∀ y ∈ Y, φ (φ y) = y)
    (hflip : ∀ y ∈ Y, P (φ y) = !(P y)) :
    2 * (Y.filter (fun y => P y = target)).card = Y.card := by
  let A := Y.filter (fun y => P y = target)
  let B := Y.filter (fun y => P y = !target)
  have hAB : A.card = B.card := by
    apply Finset.card_bij (fun y _ => φ y)
    · intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyY, hPy⟩
      exact Finset.mem_filter.mpr ⟨hmem y hyY, by rw [hflip y hyY, hPy]⟩
    · intro y1 hy1 y2 hy2 heq
      have h1 := hinv y1 (Finset.mem_filter.mp hy1).1
      have h2 := hinv y2 (Finset.mem_filter.mp hy2).1
      rw [← h1, ← h2, heq]
    · intro b hb
      rcases Finset.mem_filter.mp hb with ⟨hbY, hPb⟩
      refine ⟨φ b, Finset.mem_filter.mpr ⟨hmem b hbY, ?_⟩, hinv b hbY⟩
      rw [hflip b hbY, hPb, Bool.not_not]
  have hunion : A ∪ B = Y := by
    ext y
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hy
      cases hPy : P y <;> cases target <;> simp [hy]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    have h1 := (Finset.mem_filter.mp hyA).2
    have h2 := (Finset.mem_filter.mp hyB).2
    rw [h1] at h2
    cases target <;> simp at h2
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, ← hAB] at hcard
  change 2 * A.card = Y.card
  omega

lemma nat_xor_cancel (a b : ℕ) : (a ^^^ b) ^^^ b = a := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

lemma tagNat_diff_card (k d : ℕ) (hdk : 2 * d + 1 ≤ k) (hd : 1 ≤ d)
    (x x' : ℕ) (hx : x < 2 ^ k) (hx' : x' < 2 ^ k) (hne : x ≠ x') (target : Bool) :
    2 ^ (k - d) / 4 ≤
      ((Finset.range (2 ^ (k - d))).filter (fun y => xor (tagNat (k - d) d x y) (tagNat (k - d) d x' y) = target)).card := by
  set m := k - d
  have hm_ge : d + 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  let P := fun y => xor (tagNat m d x y) (tagNat m d x' y)
  have htag_lt : ∀ a y, y < 2 ^ m → tagNat m d a y =
      xor (lowNat m a y % 2 == 1) (crossNat m d a y % 2 == 1) := by
    intro a y hy
    rw [tagNat, crossNat_eq_zero_of_lt m d a y hy, add_zero, parity_add]
  by_cases hhi : ∃ l < d, x.testBit (m + l) ≠ x'.testBit (m + l)
  · obtain ⟨l, hld, hlne⟩ := hhi
    set p := l + 1
    have hp1 : 1 ≤ p := by omega
    have hpm : p < m := by omega
    have hpd : p ≤ d := by omega
    have hPflip : ∀ y < 2 ^ m,
        P (y ^^^ 2 ^ p) =
          xor (P y) (xor (xor (x.testBit p) (x'.testBit p))
            (y.testBit 0 && xor (x.testBit (m + l)) (x'.testBit (m + l)))) := by
      intro y hy
      have hy' : y ^^^ 2 ^ p < 2 ^ m := Nat.xor_lt_two_pow hy (Nat.pow_lt_pow_right (by omega) hpm)
      simp only [P, htag_lt x (y ^^^ 2 ^ p) hy', htag_lt x' (y ^^^ 2 ^ p) hy',
        htag_lt x y hy, htag_lt x' y hy,
        lowNat_parity_xor_pow m x y p hpm, lowNat_parity_xor_pow m x' y p hpm,
        crossNat_parity_xor_pow m d x y p hp1, crossNat_parity_xor_pow m d x' y p hp1,
        decide_eq_true hpd, Bool.true_and]
      have hpl : p - 1 = l := by omega
      rw [hpl]
      cases (lowNat m x y % 2 == 1) <;> cases (crossNat m d x y % 2 == 1) <;>
        cases (lowNat m x' y % 2 == 1) <;> cases (crossNat m d x' y % 2 == 1) <;>
        cases x.testBit p <;> cases x'.testBit p <;> cases y.testBit 0 <;>
        cases x.testBit (m + l) <;> cases x'.testBit (m + l) <;> decide
    have hxhi : xor (x.testBit (m + l)) (x'.testBit (m + l)) = true := by
      cases h1 : x.testBit (m + l) <;> cases h2 : x'.testBit (m + l) <;> simp_all
    let b0 : Bool := !(xor (x.testBit p) (x'.testBit p))
    let Y := (Finset.range (2 ^ m)).filter (fun y => y.testBit 0 = b0)
    have hYcard : 2 * Y.card = 2 ^ m := by
      have h := involution_half_card (Finset.range (2 ^ m)) (fun y => y ^^^ 2 ^ 0)
        (fun y => y.testBit 0) b0
        (fun y hy => Finset.mem_range.mpr
          (Nat.xor_lt_two_pow (Finset.mem_range.mp hy) (Nat.pow_lt_pow_right (by omega) (by omega))))
        (fun y _ => nat_xor_cancel y (2 ^ 0))
        (fun y _ => by rw [Nat.testBit_xor, Nat.testBit_two_pow]; simp)
      simpa only [Finset.card_range] using h
    have hYhalf : 2 * (Y.filter (fun y => P y = target)).card = Y.card := by
      apply involution_half_card Y (fun y => y ^^^ 2 ^ p) P target
      · intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyR, hy0⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (Nat.xor_lt_two_pow (Finset.mem_range.mp hyR) (Nat.pow_lt_pow_right (by omega) hpm)), ?_⟩
        rw [Nat.testBit_xor, Nat.testBit_two_pow, decide_eq_false (by omega), Bool.xor_false, hy0]
      · intro y _
        exact nat_xor_cancel y (2 ^ p)
      · intro y hy
        rcases Finset.mem_filter.mp hy with ⟨hyR, hy0⟩
        rw [hPflip y (Finset.mem_range.mp hyR), hy0, hxhi, Bool.and_true]
        simp only [b0]
        cases P y <;> cases (xor (x.testBit p) (x'.testBit p)) <;> decide
    have hsub : Y.filter (fun y => P y = target) ⊆
        (Finset.range (2 ^ m)).filter (fun y => P y = target) := by
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyY, hPy⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyY).1, hPy⟩
    have hle := Finset.card_le_card hsub
    change 2 ^ m / 4 ≤ ((Finset.range (2 ^ m)).filter (fun y => P y = target)).card
    omega
  · push_neg at hhi
    have hcross_eq : ∀ y, crossNat m d x y = crossNat m d x' y := by
      intro y
      unfold crossNat
      congr 1
      apply Finset.filter_congr
      intro l hl
      rw [hhi l (Finset.mem_range.mp hl)]
    have hlo : ∃ p < m, x.testBit p ≠ x'.testBit p := by
      by_contra hall
      push_neg at hall
      apply hne
      apply Nat.eq_of_testBit_eq
      intro q
      by_cases hqm : q < m
      · exact hall q hqm
      · by_cases hqk : q < k
        · have hql : q - m < d := by omega
          have hqm' : m + (q - m) = q := by omega
          rw [← hqm']
          exact hhi (q - m) hql
        · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le hx' (Nat.pow_le_pow_right (by omega) (by omega)))]
    obtain ⟨p, hpm, hpne⟩ := hlo
    have hxlo : xor (x.testBit p) (x'.testBit p) = true := by
      cases h1 : x.testBit p <;> cases h2 : x'.testBit p <;> simp_all
    have hhalf : 2 * ((Finset.range (2 ^ m)).filter (fun y => P y = target)).card = 2 ^ m := by
      have h := involution_half_card (Finset.range (2 ^ m)) (fun y => y ^^^ 2 ^ p) P target
        (fun y hy => Finset.mem_range.mpr
          (Nat.xor_lt_two_pow (Finset.mem_range.mp hy) (Nat.pow_lt_pow_right (by omega) hpm)))
        (fun y _ => nat_xor_cancel y (2 ^ p))
        (fun y hy => by
          have hy' : y < 2 ^ m := Finset.mem_range.mp hy
          have hy'' : y ^^^ 2 ^ p < 2 ^ m :=
            Nat.xor_lt_two_pow hy' (Nat.pow_lt_pow_right (by omega) hpm)
          simp only [P, htag_lt x (y ^^^ 2 ^ p) hy'', htag_lt x' (y ^^^ 2 ^ p) hy'',
            htag_lt x y hy', htag_lt x' y hy',
            lowNat_parity_xor_pow m x y p hpm, lowNat_parity_xor_pow m x' y p hpm,
            hcross_eq (y ^^^ 2 ^ p), hcross_eq y]
          cases (lowNat m x y % 2 == 1) <;> cases (lowNat m x' y % 2 == 1) <;>
            cases (crossNat m d x' y % 2 == 1) <;> cases (crossNat m d x' (y ^^^ 2 ^ p) % 2 == 1) <;>
            cases h1 : x.testBit p <;> cases h2 : x'.testBit p <;> simp_all)
      simpa only [Finset.card_range] using h
    change 2 ^ m / 4 ≤ ((Finset.range (2 ^ m)).filter (fun y => P y = target)).card
    omega

end TagDist

section LevelOne

def signBool (b : Bool) : ℤ := if b then -1 else 1

lemma signBool_sq (b : Bool) : (signBool b) ^ 2 = 1 := by
  cases b <;> decide

lemma signBool_xor (a b : Bool) : signBool (xor a b) = signBool a * signBool b := by
  cases a <;> cases b <;> decide

def chi (k r : ℕ) (t : Fin r) (i : Fin (2 ^ k)) : ℤ :=
  signBool (i.val.testBit t.val)

lemma chi_sq (k r : ℕ) (t : Fin r) (i : Fin (2 ^ k)) : (chi k r t i) ^ 2 = 1 :=
  signBool_sq _

lemma sum_pow_three_le {α : Type*} (s : Finset α) (y : α → ℤ) (hy : ∀ i ∈ s, 0 ≤ y i) :
    (∑ i ∈ s, y i) ^ 3 ≤ (s.card : ℤ) ^ 2 * ∑ i ∈ s, (y i) ^ 3 := by
  have h3 : ∀ a b c : ℤ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 3 * (a * b * c) ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
    intro a b c ha hb hc
    have hnonneg : 0 ≤ (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) := by positivity
    linarith
  have hL : 3 * (∑ i ∈ s, y i) ^ 3 =
      ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, 3 * (y i * y j * y k) := by
    have h1 : (∑ i ∈ s, y i) ^ 3 = ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, y i * y j * y k := by
      simp_rw [pow_three, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [h1, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]
  have hR : ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ((y i) ^ 3 + (y j) ^ 3 + (y k) ^ 3) =
      3 * ((s.card : ℤ) ^ 2 * ∑ i ∈ s, (y i) ^ 3) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      ← Finset.sum_mul]
    ring
  have hle : ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, 3 * (y i * y j * y k) ≤
      ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ((y i) ^ 3 + (y j) ^ 3 + (y k) ^ 3) := by
    apply Finset.sum_le_sum; intro i hi
    apply Finset.sum_le_sum; intro j hj
    apply Finset.sum_le_sum; intro k hk
    exact h3 (y i) (y j) (y k) (hy i hi) (hy j hj) (hy k hk)
  linarith

lemma sum_pow_six_le {α : Type*} (s : Finset α) (x : α → ℤ) :
    (∑ i ∈ s, x i) ^ 6 ≤ (s.card : ℤ) ^ 5 * ∑ i ∈ s, (x i) ^ 6 := by
  have hcs : (∑ i ∈ s, x i) ^ 2 ≤ (s.card : ℤ) * ∑ i ∈ s, (x i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h3 : (∑ i ∈ s, (x i) ^ 2) ^ 3 ≤ (s.card : ℤ) ^ 2 * ∑ i ∈ s, ((x i) ^ 2) ^ 3 :=
    sum_pow_three_le s (fun i => (x i) ^ 2) (fun i _ => sq_nonneg (x i))
  have hcube : ((∑ i ∈ s, x i) ^ 2) ^ 3 ≤ ((s.card : ℤ) * ∑ i ∈ s, (x i) ^ 2) ^ 3 :=
    pow_le_pow_left₀ (sq_nonneg _) hcs 3
  have hpow6 : ∀ i, ((x i) ^ 2) ^ 3 = (x i) ^ 6 := fun i => by ring
  simp_rw [hpow6] at h3
  have hcard_nonneg : (0 : ℤ) ≤ (s.card : ℤ) ^ 3 := by positivity
  calc (∑ i ∈ s, x i) ^ 6 = ((∑ i ∈ s, x i) ^ 2) ^ 3 := by ring
    _ ≤ ((s.card : ℤ) * ∑ i ∈ s, (x i) ^ 2) ^ 3 := hcube
    _ = (s.card : ℤ) ^ 3 * (∑ i ∈ s, (x i) ^ 2) ^ 3 := by ring
    _ ≤ (s.card : ℤ) ^ 3 * ((s.card : ℤ) ^ 2 * ∑ i ∈ s, (x i) ^ 6) :=
        mul_le_mul_of_nonneg_left h3 hcard_nonneg
    _ = (s.card : ℤ) ^ 5 * ∑ i ∈ s, (x i) ^ 6 := by ring

abbrev IsPair4 {α : Type*} (a b c d : α) : Prop :=
  (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c)

abbrev IsPair6 {α : Type*} (t1 t2 t3 t4 t5 t6 : α) : Prop :=
  (t1 = t2 ∧ IsPair4 t3 t4 t5 t6) ∨
  (t1 = t3 ∧ IsPair4 t2 t4 t5 t6) ∨
  (t1 = t4 ∧ IsPair4 t2 t3 t5 t6) ∨
  (t1 = t5 ∧ IsPair4 t2 t3 t4 t6) ∨
  (t1 = t6 ∧ IsPair4 t2 t3 t4 t5)

lemma even4_imp_pair4 {α : Type*} [DecidableEq α] (a b c d : α)
    (h : ∀ t, ([a, b, c, d].count t) % 2 = 0) : IsPair4 a b c d := by
  have ha := h a
  simp only [List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte] at ha
  by_cases hab : a = b
  · left; refine ⟨hab, ?_⟩
    subst hab
    have hc := h c
    simp only [List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte] at hc
    by_cases hca : a = c
    · subst hca
      by_cases had : a = d
      · exact had
      · have hda : d ≠ a := Ne.symm had
        simp [hda] at hc
    · have h1 : (a == c) = false := beq_false_of_ne hca
      by_cases hcd : d = c
      · exact hcd.symm
      · simp [h1, beq_false_of_ne hcd, Bool.false_eq_true] at hc
  · by_cases hac : a = c
    · right; left; refine ⟨hac, ?_⟩
      subst hac
      have hb := h b
      simp only [List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte] at hb
      have h1 : (a == b) = false := beq_false_of_ne hab
      by_cases hbd : d = b
      · exact hbd.symm
      · simp [h1, beq_false_of_ne hbd] at hb
    · by_cases had : a = d
      · right; right; refine ⟨had, ?_⟩
        subst had
        have hb := h b
        simp only [List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte] at hb
        have h1 : (a == b) = false := beq_false_of_ne hab
        by_cases hbc : c = b
        · exact hbc.symm
        · simp [h1, beq_false_of_ne hbc] at hb
      · simp [beq_false_of_ne (Ne.symm hab), beq_false_of_ne (Ne.symm hac),
          beq_false_of_ne (Ne.symm had)] at ha

lemma even6_imp_pair6 {α : Type*} [DecidableEq α] (t1 t2 t3 t4 t5 t6 : α)
    (h : ∀ t, ([t1, t2, t3, t4, t5, t6].count t) % 2 = 0) :
    IsPair6 t1 t2 t3 t4 t5 t6 := by
  have hdrop : ∀ (a b c d e f : α),
      (∀ t, ([a, b, c, d, e, f].count t) % 2 = 0) → a = b →
      ∀ t, ([c, d, e, f].count t) % 2 = 0 := by
    intro a b c d e f hall hab t
    subst hab
    have ht := hall t
    simp only [List.count_cons] at ht ⊢
    omega
  by_cases h12 : t1 = t2
  · exact Or.inl ⟨h12, even4_imp_pair4 t3 t4 t5 t6 (hdrop t1 t2 t3 t4 t5 t6 h h12)⟩
  · by_cases h13 : t1 = t3
    · refine Or.inr (Or.inl ⟨h13, even4_imp_pair4 t2 t4 t5 t6 ?_⟩)
      apply hdrop t1 t3 t2 t4 t5 t6 _ h13
      intro t; have ht := h t; simp only [List.count_cons] at ht ⊢; omega
    · by_cases h14 : t1 = t4
      · refine Or.inr (Or.inr (Or.inl ⟨h14, even4_imp_pair4 t2 t3 t5 t6 ?_⟩))
        apply hdrop t1 t4 t2 t3 t5 t6 _ h14
        intro t; have ht := h t; simp only [List.count_cons] at ht ⊢; omega
      · by_cases h15 : t1 = t5
        · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h15, even4_imp_pair4 t2 t3 t4 t6 ?_⟩)))
          apply hdrop t1 t5 t2 t3 t4 t6 _ h15
          intro t; have ht := h t; simp only [List.count_cons] at ht ⊢; omega
        · by_cases h16 : t1 = t6
          · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h16, even4_imp_pair4 t2 t3 t4 t5 ?_⟩)))
            apply hdrop t1 t6 t2 t3 t4 t5 _ h16
            intro t; have ht := h t; simp only [List.count_cons] at ht ⊢; omega
          · have h1 := h t1
            simp only [List.count_cons, List.count_nil, beq_self_eq_true, ↓reduceIte,
              beq_false_of_ne (Ne.symm h12), beq_false_of_ne (Ne.symm h13),
              beq_false_of_ne (Ne.symm h14), beq_false_of_ne (Ne.symm h15),
              beq_false_of_ne (Ne.symm h16), Bool.false_eq_true] at h1
            omega

lemma prod_pair6_nonneg {α : Type*} (c : α → ℤ) {t1 t2 t3 t4 t5 t6 : α}
    (h : IsPair6 t1 t2 t3 t4 t5 t6) :
    0 ≤ c t1 * c t2 * c t3 * c t4 * c t5 * c t6 := by
  have h4 : ∀ a b d e : α, IsPair4 a b d e → 0 ≤ c a * c b * c d * c e := by
    rintro a b d e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have : c a * c a * c d * c d = (c a * c d) ^ 2 := by ring
      rw [this]; exact sq_nonneg _
    · have : c a * c b * c a * c b = (c a * c b) ^ 2 := by ring
      rw [this]; exact sq_nonneg _
    · have : c a * c b * c b * c a = (c a * c b) ^ 2 := by ring
      rw [this]; exact sq_nonneg _
  rcases h with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
  · have := h4 _ _ _ _ h'; nlinarith [sq_nonneg (c t1)]
  · have := h4 _ _ _ _ h'
    have heq : c t1 * c t2 * c t1 * c t4 * c t5 * c t6 = (c t1) ^ 2 * (c t2 * c t4 * c t5 * c t6) := by ring
    rw [heq]; exact mul_nonneg (sq_nonneg _) this
  · have := h4 _ _ _ _ h'
    have heq : c t1 * c t2 * c t3 * c t1 * c t5 * c t6 = (c t1) ^ 2 * (c t2 * c t3 * c t5 * c t6) := by ring
    rw [heq]; exact mul_nonneg (sq_nonneg _) this
  · have := h4 _ _ _ _ h'
    have heq : c t1 * c t2 * c t3 * c t4 * c t1 * c t6 = (c t1) ^ 2 * (c t2 * c t3 * c t4 * c t6) := by ring
    rw [heq]; exact mul_nonneg (sq_nonneg _) this
  · have := h4 _ _ _ _ h'
    have heq : c t1 * c t2 * c t3 * c t4 * c t5 * c t1 = (c t1) ^ 2 * (c t2 * c t3 * c t4 * c t5) := by ring
    rw [heq]; exact mul_nonneg (sq_nonneg _) this

lemma chi_prod_pair6 (k r : ℕ) (i : Fin (2 ^ k)) {t1 t2 t3 t4 t5 t6 : Fin r}
    (h : IsPair6 t1 t2 t3 t4 t5 t6) :
    chi k r t1 i * chi k r t2 i * chi k r t3 i * chi k r t4 i * chi k r t5 i * chi k r t6 i = 1 := by
  have h4 : ∀ a b d e : Fin r, IsPair4 a b d e →
      chi k r a i * chi k r b i * chi k r d i * chi k r e i = 1 := by
    rintro a b d e (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have : chi k r a i * chi k r a i * chi k r d i * chi k r d i =
          (chi k r a i) ^ 2 * (chi k r d i) ^ 2 := by ring
      rw [this, chi_sq, chi_sq]; ring
    · have : chi k r a i * chi k r b i * chi k r a i * chi k r b i =
          (chi k r a i) ^ 2 * (chi k r b i) ^ 2 := by ring
      rw [this, chi_sq, chi_sq]; ring
    · have : chi k r a i * chi k r b i * chi k r b i * chi k r a i =
          (chi k r a i) ^ 2 * (chi k r b i) ^ 2 := by ring
      rw [this, chi_sq, chi_sq]; ring
  rcases h with ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩
  · have := h4 _ _ _ _ h'
    have heq : chi k r t1 i * chi k r t1 i * chi k r t3 i * chi k r t4 i * chi k r t5 i * chi k r t6 i =
        (chi k r t1 i) ^ 2 * (chi k r t3 i * chi k r t4 i * chi k r t5 i * chi k r t6 i) := by ring
    rw [heq, chi_sq, this]; ring
  · have := h4 _ _ _ _ h'
    have heq : chi k r t1 i * chi k r t2 i * chi k r t1 i * chi k r t4 i * chi k r t5 i * chi k r t6 i =
        (chi k r t1 i) ^ 2 * (chi k r t2 i * chi k r t4 i * chi k r t5 i * chi k r t6 i) := by ring
    rw [heq, chi_sq, this]; ring
  · have := h4 _ _ _ _ h'
    have heq : chi k r t1 i * chi k r t2 i * chi k r t3 i * chi k r t1 i * chi k r t5 i * chi k r t6 i =
        (chi k r t1 i) ^ 2 * (chi k r t2 i * chi k r t3 i * chi k r t5 i * chi k r t6 i) := by ring
    rw [heq, chi_sq, this]; ring
  · have := h4 _ _ _ _ h'
    have heq : chi k r t1 i * chi k r t2 i * chi k r t3 i * chi k r t4 i * chi k r t1 i * chi k r t6 i =
        (chi k r t1 i) ^ 2 * (chi k r t2 i * chi k r t3 i * chi k r t4 i * chi k r t6 i) := by ring
    rw [heq, chi_sq, this]; ring
  · have := h4 _ _ _ _ h'
    have heq : chi k r t1 i * chi k r t2 i * chi k r t3 i * chi k r t4 i * chi k r t5 i * chi k r t1 i =
        (chi k r t1 i) ^ 2 * (chi k r t2 i * chi k r t3 i * chi k r t4 i * chi k r t5 i) := by ring
    rw [heq, chi_sq, this]; ring

lemma sum_chi_prod_six (k r : ℕ) (hrk : r ≤ k) (t1 t2 t3 t4 t5 t6 : Fin r) :
    ∑ i : Fin (2 ^ k),
      chi k r t1 i * chi k r t2 i * chi k r t3 i * chi k r t4 i * chi k r t5 i * chi k r t6 i =
    if IsPair6 t1 t2 t3 t4 t5 t6 then (2 ^ k : ℤ) else 0 := by
  classical
  by_cases hp : IsPair6 t1 t2 t3 t4 t5 t6
  · simp only [hp, ↓reduceIte]
    have h1 : ∀ i : Fin (2 ^ k),
        chi k r t1 i * chi k r t2 i * chi k r t3 i * chi k r t4 i * chi k r t5 i * chi k r t6 i = 1 :=
      fun i => chi_prod_pair6 k r i hp
    simp [h1]
  · simp only [hp, ↓reduceIte]
    have hodd : ∃ t : Fin r, ([t1, t2, t3, t4, t5, t6].count t) % 2 = 1 := by
      by_contra hall
      push_neg at hall
      apply hp
      apply even6_imp_pair6
      intro t
      have := hall t
      omega
    obtain ⟨t, htodd⟩ := hodd
    have htk : t.val < k := lt_of_lt_of_le t.isLt hrk
    let φ : Fin (2 ^ k) → Fin (2 ^ k) := fun i =>
      ⟨i.val ^^^ 2 ^ t.val, Nat.xor_lt_two_pow i.isLt (Nat.pow_lt_pow_right (by omega) htk)⟩
    have hφ_inv : Function.Involutive φ := by
      intro i; apply Fin.ext; exact nat_xor_cancel i.val (2 ^ t.val)
    have hchi_flip : ∀ (s : Fin r) (i : Fin (2 ^ k)),
        chi k r s (φ i) = (if s = t then -1 else 1) * chi k r s i := by
      intro s i
      simp only [chi, φ, Nat.testBit_xor, Nat.testBit_two_pow]
      by_cases hst : s = t
      · subst hst; simp [signBool]; cases i.val.testBit s.val <;> decide
      · have hne : t.val ≠ s.val := fun h => hst (Fin.ext h.symm)
        simp [hst, hne]
    let f : Fin (2 ^ k) → ℤ := fun i =>
      chi k r t1 i * chi k r t2 i * chi k r t3 i * chi k r t4 i * chi k r t5 i * chi k r t6 i
    have hf_neg : ∀ i, f (φ i) = -f i := by
      intro i
      have hprod : (if t1 = t then (-1 : ℤ) else 1) * (if t2 = t then -1 else 1) *
          (if t3 = t then -1 else 1) * (if t4 = t then -1 else 1) *
          (if t5 = t then -1 else 1) * (if t6 = t then -1 else 1) =
          (-1 : ℤ) ^ ([t1, t2, t3, t4, t5, t6].count t) := by
        have hstep : ∀ (a : Fin r) (l : List (Fin r)),
            (if a = t then (-1 : ℤ) else 1) * (-1 : ℤ) ^ (l.count t) =
              (-1 : ℤ) ^ ((a :: l).count t) := by
          intro a l
          by_cases hat : a = t
          · subst hat; simp [pow_succ, mul_comm]
          · simp [hat, beq_false_of_ne hat]
        have hnil : (-1 : ℤ) ^ (([ ] : List (Fin r)).count t) = 1 := by simp
        calc (if t1 = t then (-1 : ℤ) else 1) * (if t2 = t then -1 else 1) *
              (if t3 = t then -1 else 1) * (if t4 = t then -1 else 1) *
              (if t5 = t then -1 else 1) * (if t6 = t then -1 else 1)
            = (if t1 = t then (-1 : ℤ) else 1) * ((if t2 = t then -1 else 1) *
              ((if t3 = t then -1 else 1) * ((if t4 = t then -1 else 1) *
              ((if t5 = t then -1 else 1) * ((if t6 = t then -1 else 1) *
              (-1 : ℤ) ^ (([ ] : List (Fin r)).count t)))))) := by rw [hnil]; ring
          _ = (-1 : ℤ) ^ ([t1, t2, t3, t4, t5, t6].count t) := by
              rw [hstep t6, hstep t5, hstep t4, hstep t3, hstep t2, hstep t1]
      have hneg1 : (-1 : ℤ) ^ ([t1, t2, t3, t4, t5, t6].count t) = -1 := by
        rw [Odd.neg_one_pow (Nat.odd_iff.mpr htodd)]
      show chi k r t1 (φ i) * chi k r t2 (φ i) * chi k r t3 (φ i) *
          chi k r t4 (φ i) * chi k r t5 (φ i) * chi k r t6 (φ i) = -f i
      rw [hchi_flip t1, hchi_flip t2, hchi_flip t3, hchi_flip t4, hchi_flip t5, hchi_flip t6]
      calc ((if t1 = t then -1 else 1) * chi k r t1 i) *
            ((if t2 = t then -1 else 1) * chi k r t2 i) *
            ((if t3 = t then -1 else 1) * chi k r t3 i) *
            ((if t4 = t then -1 else 1) * chi k r t4 i) *
            ((if t5 = t then -1 else 1) * chi k r t5 i) *
            ((if t6 = t then -1 else 1) * chi k r t6 i)
          = ((if t1 = t then (-1 : ℤ) else 1) * (if t2 = t then -1 else 1) *
            (if t3 = t then -1 else 1) * (if t4 = t then -1 else 1) *
            (if t5 = t then -1 else 1) * (if t6 = t then -1 else 1)) * f i := by
              simp only [f]; ring
        _ = -f i := by rw [hprod, hneg1]; ring
    have hsum_eq : ∑ i : Fin (2 ^ k), f (φ i) = ∑ i : Fin (2 ^ k), f i := by
      exact Equiv.sum_comp (Function.Involutive.toPerm φ hφ_inv) f
    have hsum_neg : ∑ i : Fin (2 ^ k), f (φ i) = -∑ i : Fin (2 ^ k), f i := by
      simp_rw [hf_neg, Finset.sum_neg_distrib]
    change ∑ i : Fin (2 ^ k), f i = 0
    linarith

lemma sum_six_match_eq {α : Type*} [Fintype α] [DecidableEq α] (c : α → ℤ)
    (σ : Equiv.Perm (Fin 6)) :
    ∑ f : Fin 6 → α,
      (if f (σ 0) = f (σ 1) ∧ f (σ 2) = f (σ 3) ∧ f (σ 4) = f (σ 5) then
        ∏ m : Fin 6, c (f m) else 0) =
    (∑ t : α, (c t) ^ 2) ^ 3 := by
  let reidx : (Fin 6 → α) ≃ (Fin 6 → α) :=
    { toFun := fun f => f ∘ σ.symm
      invFun := fun f => f ∘ σ
      left_inv := fun f => by ext m; simp
      right_inv := fun f => by ext m; simp }
  have h1 : ∑ f : Fin 6 → α,
      (if f (σ 0) = f (σ 1) ∧ f (σ 2) = f (σ 3) ∧ f (σ 4) = f (σ 5) then
        ∏ m : Fin 6, c (f m) else 0) =
    ∑ f : Fin 6 → α,
      (if f 0 = f 1 ∧ f 2 = f 3 ∧ f 4 = f 5 then ∏ m : Fin 6, c (f m) else 0) := by
    rw [← Equiv.sum_comp reidx]
    apply Finset.sum_congr rfl
    intro f _
    simp only [reidx, Equiv.coe_fn_mk, Function.comp_apply, Equiv.symm_apply_apply]
    congr 1
    exact Equiv.prod_comp σ.symm (fun m => c (f m))
  rw [h1]
  let e : (Fin 6 → α) ≃ (α × α) × (α × α) × (α × α) :=
    { toFun := fun f => ((f 0, f 1), (f 2, f 3), (f 4, f 5))
      invFun := fun p m =>
        match m with
        | ⟨0, _⟩ => p.1.1 | ⟨1, _⟩ => p.1.2
        | ⟨2, _⟩ => p.2.1.1 | ⟨3, _⟩ => p.2.1.2
        | ⟨4, _⟩ => p.2.2.1 | ⟨5, _⟩ => p.2.2.2
      left_inv := fun f => by ext m; fin_cases m <;> rfl
      right_inv := fun p => by rcases p with ⟨⟨a, b⟩, ⟨d, g⟩, ⟨h, k⟩⟩; rfl }
  rw [← Equiv.sum_comp e.symm]
  have hprod6 : ∀ p : (α × α) × (α × α) × (α × α),
      (∏ m : Fin 6, c (e.symm p m)) = c p.1.1 * c p.1.2 * c p.2.1.1 * c p.2.1.2 * c p.2.2.1 * c p.2.2.2 := by
    intro p; rw [Fin.prod_univ_six]; rfl
  simp_rw [hprod6]
  have hcond : ∀ p : (α × α) × (α × α) × (α × α),
      (e.symm p 0 = e.symm p 1 ∧ e.symm p 2 = e.symm p 3 ∧ e.symm p 4 = e.symm p 5) ↔
      (p.1.1 = p.1.2 ∧ p.2.1.1 = p.2.1.2 ∧ p.2.2.1 = p.2.2.2) := fun _ => Iff.rfl
  simp_rw [hcond, Fintype.sum_prod_type]
  have hinner : ∀ a b d e' : α,
      ∑ g : α, ∑ h : α,
        (if a = b ∧ d = e' ∧ g = h then c a * c b * c d * c e' * c g * c h else 0) =
      if a = b ∧ d = e' then c a * c b * c d * c e' * (∑ t : α, (c t) ^ 2) else 0 := by
    intro a b d e'
    by_cases h : a = b ∧ d = e'
    · rw [if_pos h]
      simp only [h, true_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro g _; ring
    · rw [if_neg h]
      have hnot : ∀ g h' : α, ¬ (a = b ∧ d = e' ∧ g = h') := fun _ _ ⟨h1, h2, _⟩ => h ⟨h1, h2⟩
      simp only [hnot, ↓reduceIte, Finset.sum_const_zero]
  simp_rw [hinner]
  have hmid : ∀ a b : α,
      ∑ d : α, ∑ e' : α,
        (if a = b ∧ d = e' then c a * c b * c d * c e' * (∑ t : α, (c t) ^ 2) else 0) =
      if a = b then c a * c b * (∑ t : α, (c t) ^ 2) ^ 2 else 0 := by
    intro a b
    by_cases h : a = b
    · rw [if_pos h]
      simp only [h, true_and, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      calc ∑ d : α, c b * c b * c d * c d * (∑ t : α, (c t) ^ 2)
          = ∑ d : α, (c b * c b * (∑ t : α, (c t) ^ 2)) * (c d) ^ 2 := by
            apply Finset.sum_congr rfl; intro d _; ring
        _ = (c b * c b * (∑ t : α, (c t) ^ 2)) * ∑ d : α, (c d) ^ 2 := (Finset.mul_sum _ _ _).symm
        _ = c b * c b * (∑ t : α, (c t) ^ 2) ^ 2 := by ring
    · rw [if_neg h]
      simp only [h, false_and, ↓reduceIte, Finset.sum_const_zero]
  simp_rw [hmid]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hpull : ∀ a : α, c a * c a * (∑ t : α, (c t) ^ 2) ^ 2 =
      (c a) ^ 2 * (∑ t : α, (c t) ^ 2) ^ 2 := by intro a; ring
  simp_rw [hpull, ← Finset.sum_mul]
  ring

lemma sixth_moment_bound (k r : ℕ) (hrk : r ≤ k) (c : Fin r → ℤ) :
    ∑ i : Fin (2 ^ k), (∑ t : Fin r, c t * chi k r t i) ^ 6 ≤
      15 * (2 ^ k : ℤ) * (∑ t : Fin r, (c t) ^ 2) ^ 3 := by
  classical
  have hexpand : ∀ i : Fin (2 ^ k),
      (∑ t : Fin r, c t * chi k r t i) ^ 6 =
        ∑ f : Fin 6 → Fin r, (∏ m : Fin 6, c (f m)) * (∏ m : Fin 6, chi k r (f m) i) := by
    intro i
    have h1 : (∑ t : Fin r, c t * chi k r t i) ^ 6 =
        ∏ _ : Fin 6, ∑ t : Fin r, c t * chi k r t i := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h1, Fintype.prod_sum]
    apply Finset.sum_congr rfl; intro f _
    rw [Finset.prod_mul_distrib]
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  have hswap :
      ∑ f : Fin 6 → Fin r, ∑ i : Fin (2 ^ k),
        (∏ m : Fin 6, c (f m)) * (∏ m : Fin 6, chi k r (f m) i) =
      (2 ^ k : ℤ) * ∑ f : Fin 6 → Fin r,
        if IsPair6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) then ∏ m : Fin 6, c (f m) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro f _
    rw [← Finset.mul_sum]
    have hchi6 : ∀ i : Fin (2 ^ k),
        (∏ m : Fin 6, chi k r (f m) i) =
          chi k r (f 0) i * chi k r (f 1) i * chi k r (f 2) i *
          chi k r (f 3) i * chi k r (f 4) i * chi k r (f 5) i := by
      intro i; exact Fin.prod_univ_six _
    simp_rw [hchi6]
    rw [sum_chi_prod_six k r hrk]
    split_ifs <;> ring
  rw [hswap]
  let mkP : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → (Fin 6 → Fin r) → Prop :=
    fun a b d e g h f => f a = f b ∧ f d = f e ∧ f g = f h
  have hpair_le : ∀ f : Fin 6 → Fin r,
      (if IsPair6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) then ∏ m : Fin 6, c (f m) else 0) ≤
        ((if mkP 0 1 2 3 4 5 f then ∏ m : Fin 6, c (f m) else 0) +
         (if mkP 0 1 2 4 3 5 f then ∏ m : Fin 6, c (f m) else 0) +
         (if mkP 0 1 2 5 3 4 f then ∏ m : Fin 6, c (f m) else 0)) +
        ((if mkP 0 2 1 3 4 5 f then ∏ m : Fin 6, c (f m) else 0) +
         (if mkP 0 2 1 4 3 5 f then ∏ m : Fin 6, c (f m) else 0) +
         (if mkP 0 2 1 5 3 4 f then ∏ m : Fin 6, c (f m) else 0)) +
        ((if mkP 0 3 1 2 4 5 f then ∏ m : Fin 6, c (f m) else 0) +
         (if mkP 0 3 1 4 2 5 f then ∏ m : Fin 6, c (f m) else 0) +
         (if mkP 0 3 1 5 2 4 f then ∏ m : Fin 6, c (f m) else 0)) +
        ((if mkP 0 4 1 2 3 5 f then ∏ m : Fin 6, c (f m) else 0) +
         (if mkP 0 4 1 3 2 5 f then ∏ m : Fin 6, c (f m) else 0) +
         (if mkP 0 4 1 5 2 3 f then ∏ m : Fin 6, c (f m) else 0)) +
        ((if mkP 0 5 1 2 3 4 f then ∏ m : Fin 6, c (f m) else 0) +
         (if mkP 0 5 1 3 2 4 f then ∏ m : Fin 6, c (f m) else 0) +
         (if mkP 0 5 1 4 2 3 f then ∏ m : Fin 6, c (f m) else 0)) := by
    intro f
    let v := ∏ m : Fin 6, c (f m)
    have hv_eq : v = c (f 0) * c (f 1) * c (f 2) * c (f 3) * c (f 4) * c (f 5) :=
      Fin.prod_univ_six _
    have hnn : ∀ P : Prop, [Decidable P] →
        (P → IsPair6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)) → 0 ≤ if P then v else 0 := by
      intro P _ hP; split_ifs with h
      · rw [hv_eq]; exact prod_pair6_nonneg c (hP h)
      · exact le_rfl
    have n1 := hnn (mkP 0 1 2 3 4 5 f) (fun ⟨a, b, d⟩ => Or.inl ⟨a, Or.inl ⟨b, d⟩⟩)
    have n2 := hnn (mkP 0 1 2 4 3 5 f) (fun ⟨a, b, d⟩ => Or.inl ⟨a, Or.inr (Or.inl ⟨b, d⟩)⟩)
    have n3 := hnn (mkP 0 1 2 5 3 4 f) (fun ⟨a, b, d⟩ => Or.inl ⟨a, Or.inr (Or.inr ⟨b, d⟩)⟩)
    have n4 := hnn (mkP 0 2 1 3 4 5 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inl ⟨a, Or.inl ⟨b, d⟩⟩))
    have n5 := hnn (mkP 0 2 1 4 3 5 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inl ⟨a, Or.inr (Or.inl ⟨b, d⟩)⟩))
    have n6 := hnn (mkP 0 2 1 5 3 4 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inl ⟨a, Or.inr (Or.inr ⟨b, d⟩)⟩))
    have n7 := hnn (mkP 0 3 1 2 4 5 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inr (Or.inl ⟨a, Or.inl ⟨b, d⟩⟩)))
    have n8 := hnn (mkP 0 3 1 4 2 5 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inr (Or.inl ⟨a, Or.inr (Or.inl ⟨b, d⟩)⟩)))
    have n9 := hnn (mkP 0 3 1 5 2 4 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inr (Or.inl ⟨a, Or.inr (Or.inr ⟨b, d⟩)⟩)))
    have n10 := hnn (mkP 0 4 1 2 3 5 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inr (Or.inr (Or.inl ⟨a, Or.inl ⟨b, d⟩⟩))))
    have n11 := hnn (mkP 0 4 1 3 2 5 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inr (Or.inr (Or.inl ⟨a, Or.inr (Or.inl ⟨b, d⟩)⟩))))
    have n12 := hnn (mkP 0 4 1 5 2 3 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inr (Or.inr (Or.inl ⟨a, Or.inr (Or.inr ⟨b, d⟩)⟩))))
    have n13 := hnn (mkP 0 5 1 2 3 4 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inr (Or.inr (Or.inr ⟨a, Or.inl ⟨b, d⟩⟩))))
    have n14 := hnn (mkP 0 5 1 3 2 4 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inr (Or.inr (Or.inr ⟨a, Or.inr (Or.inl ⟨b, d⟩)⟩))))
    have n15 := hnn (mkP 0 5 1 4 2 3 f) (fun ⟨a, b, d⟩ => Or.inr (Or.inr (Or.inr (Or.inr ⟨a, Or.inr (Or.inr ⟨b, d⟩)⟩))))
    change (if IsPair6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) then v else 0) ≤ _
    by_cases hp : IsPair6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5)
    · rw [if_pos hp]
      rcases hp with ⟨h1, (⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩)⟩ |
                     ⟨h1, (⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩)⟩ |
                     ⟨h1, (⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩)⟩ |
                     ⟨h1, (⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩)⟩ |
                     ⟨h1, (⟨h2, h3⟩ | ⟨h2, h3⟩ | ⟨h2, h3⟩)⟩
      · have e : (if mkP 0 1 2 3 4 5 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 1 2 4 3 5 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 1 2 5 3 4 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 2 1 3 4 5 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 2 1 4 3 5 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 2 1 5 3 4 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 3 1 2 4 5 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 3 1 4 2 5 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 3 1 5 2 4 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 4 1 2 3 5 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 4 1 3 2 5 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 4 1 5 2 3 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 5 1 2 3 4 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 5 1 3 2 4 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
      · have e : (if mkP 0 5 1 4 2 3 f then v else 0) = v := if_pos ⟨h1, h2, h3⟩; linarith
    · rw [if_neg hp]; linarith
  have hmk : ∀ (a b d e g h : Fin 6) (fn : Fin 6 → Fin 6),
      fn 0 = a → fn 1 = b → fn 2 = d → fn 3 = e → fn 4 = g → fn 5 = h →
      Function.Injective fn →
      (∑ f : Fin 6 → Fin r, if mkP a b d e g h f then ∏ m : Fin 6, c (f m) else 0) =
        (∑ t : Fin r, (c t) ^ 2) ^ 3 := by
    rintro a b d e g h fn rfl rfl rfl rfl rfl rfl hinj
    exact sum_six_match_eq c (Equiv.ofBijective fn (Finite.injective_iff_bijective.mp hinj))
  have h15sum :
      ∑ f : Fin 6 → Fin r,
        (if IsPair6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) then ∏ m : Fin 6, c (f m) else 0) ≤
      15 * (∑ t : Fin r, (c t) ^ 2) ^ 3 := by
    have hle := Finset.sum_le_sum (s := Finset.univ) fun f _ => hpair_le f
    simp only [Finset.sum_add_distrib] at hle
    have s1 := hmk 0 1 2 3 4 5 ![0, 1, 2, 3, 4, 5] rfl rfl rfl rfl rfl rfl (by decide)
    have s2 := hmk 0 1 2 4 3 5 ![0, 1, 2, 4, 3, 5] rfl rfl rfl rfl rfl rfl (by decide)
    have s3 := hmk 0 1 2 5 3 4 ![0, 1, 2, 5, 3, 4] rfl rfl rfl rfl rfl rfl (by decide)
    have s4 := hmk 0 2 1 3 4 5 ![0, 2, 1, 3, 4, 5] rfl rfl rfl rfl rfl rfl (by decide)
    have s5 := hmk 0 2 1 4 3 5 ![0, 2, 1, 4, 3, 5] rfl rfl rfl rfl rfl rfl (by decide)
    have s6 := hmk 0 2 1 5 3 4 ![0, 2, 1, 5, 3, 4] rfl rfl rfl rfl rfl rfl (by decide)
    have s7 := hmk 0 3 1 2 4 5 ![0, 3, 1, 2, 4, 5] rfl rfl rfl rfl rfl rfl (by decide)
    have s8 := hmk 0 3 1 4 2 5 ![0, 3, 1, 4, 2, 5] rfl rfl rfl rfl rfl rfl (by decide)
    have s9 := hmk 0 3 1 5 2 4 ![0, 3, 1, 5, 2, 4] rfl rfl rfl rfl rfl rfl (by decide)
    have s10 := hmk 0 4 1 2 3 5 ![0, 4, 1, 2, 3, 5] rfl rfl rfl rfl rfl rfl (by decide)
    have s11 := hmk 0 4 1 3 2 5 ![0, 4, 1, 3, 2, 5] rfl rfl rfl rfl rfl rfl (by decide)
    have s12 := hmk 0 4 1 5 2 3 ![0, 4, 1, 5, 2, 3] rfl rfl rfl rfl rfl rfl (by decide)
    have s13 := hmk 0 5 1 2 3 4 ![0, 5, 1, 2, 3, 4] rfl rfl rfl rfl rfl rfl (by decide)
    have s14 := hmk 0 5 1 3 2 4 ![0, 5, 1, 3, 2, 4] rfl rfl rfl rfl rfl rfl (by decide)
    have s15 := hmk 0 5 1 4 2 3 ![0, 5, 1, 4, 2, 3] rfl rfl rfl rfl rfl rfl (by decide)
    linarith
  calc (2 ^ k : ℤ) * ∑ f : Fin 6 → Fin r,
        (if IsPair6 (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) then ∏ m : Fin 6, c (f m) else 0)
      ≤ (2 ^ k : ℤ) * (15 * (∑ t : Fin r, (c t) ^ 2) ^ 3) :=
        mul_le_mul_of_nonneg_left h15sum (by positivity)
    _ = 15 * (2 ^ k : ℤ) * (∑ t : Fin r, (c t) ^ 2) ^ 3 := by ring

lemma level_one_bucket (k a : ℕ) (ha : 6 ≤ a) (hrk : 2 ^ a ≤ k)
    (A : Finset (Fin (2 ^ k))) (hA : 2 ^ a * A.card ≤ 2 ^ k) (σ : Fin (2 ^ k) → Bool) :
    16 * ∑ t : Fin (2 ^ a), (∑ i ∈ A, signBool (σ i) * chi k (2 ^ a) t i) ^ 2 ≤
      3 * (2 ^ k : ℤ) * (A.card : ℤ) := by
  let r := 2 ^ a
  let N : ℤ := 2 ^ k
  let c : Fin r → ℤ := fun t => ∑ i ∈ A, signBool (σ i) * chi k r t i
  let S : ℤ := ∑ t : Fin r, (c t) ^ 2
  change 16 * S ≤ 3 * N * (A.card : ℤ)
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg (fun t _ => sq_nonneg (c t))
  by_cases hS0 : S = 0
  · rw [hS0, mul_zero]; positivity
  have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS0)
  let F : Fin (2 ^ k) → ℤ := fun i => ∑ t : Fin r, c t * chi k r t i
  have hS_eq : S = ∑ i ∈ A, signBool (σ i) * F i := by
    simp only [S, F, sq]
    calc ∑ t : Fin r, c t * c t
        = ∑ t : Fin r, c t * ∑ i ∈ A, signBool (σ i) * chi k r t i := rfl
      _ = ∑ t : Fin r, ∑ i ∈ A, c t * (signBool (σ i) * chi k r t i) := by
          apply Finset.sum_congr rfl; intro t _; rw [Finset.mul_sum]
      _ = ∑ i ∈ A, ∑ t : Fin r, c t * (signBool (σ i) * chi k r t i) := Finset.sum_comm
      _ = ∑ i ∈ A, signBool (σ i) * ∑ t : Fin r, c t * chi k r t i := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro t _; ring
  have h6 : S ^ 6 ≤ (A.card : ℤ) ^ 5 * ∑ i ∈ A, (F i) ^ 6 := by
    have h1 := sum_pow_six_le A (fun i => signBool (σ i) * F i)
    rw [← hS_eq] at h1
    refine h1.trans_eq ?_
    congr 1
    apply Finset.sum_congr rfl; intro i _
    have hs : (signBool (σ i)) ^ 6 = 1 := by
      have : (signBool (σ i)) ^ 6 = ((signBool (σ i)) ^ 2) ^ 3 := by ring
      rw [this, signBool_sq]; ring
    rw [mul_pow, hs, one_mul]
  have hsub : ∑ i ∈ A, (F i) ^ 6 ≤ ∑ i : Fin (2 ^ k), (F i) ^ 6 := by
    apply Finset.sum_le_univ_sum_of_nonneg
    intro i; exact Even.pow_nonneg (by decide : Even 6) (F i)
  have hmom : ∑ i : Fin (2 ^ k), (F i) ^ 6 ≤ 15 * N * S ^ 3 :=
    sixth_moment_bound k r hrk c
  have hS6 : S ^ 6 ≤ 15 * N * (A.card : ℤ) ^ 5 * S ^ 3 := by
    have hA5 : (0 : ℤ) ≤ (A.card : ℤ) ^ 5 := by positivity
    calc S ^ 6 ≤ (A.card : ℤ) ^ 5 * ∑ i ∈ A, (F i) ^ 6 := h6
      _ ≤ (A.card : ℤ) ^ 5 * (15 * N * S ^ 3) :=
          mul_le_mul_of_nonneg_left (hsub.trans hmom) hA5
      _ = 15 * N * (A.card : ℤ) ^ 5 * S ^ 3 := by ring
  have hS3 : S ^ 3 ≤ 15 * N * (A.card : ℤ) ^ 5 := by
    have hS3_pos : 0 < S ^ 3 := pow_pos hS_pos 3
    have : S ^ 3 * S ^ 3 ≤ (15 * N * (A.card : ℤ) ^ 5) * S ^ 3 := by
      calc S ^ 3 * S ^ 3 = S ^ 6 := by ring
        _ ≤ 15 * N * (A.card : ℤ) ^ 5 * S ^ 3 := hS6
    exact le_of_mul_le_mul_right this hS3_pos
  have hr64 : 64 ≤ r := by
    show 2 ^ 6 ≤ 2 ^ a
    exact Nat.pow_le_pow_right (by omega) ha
  have h64A : 64 * (A.card : ℤ) ≤ N := by
    have h1 : 64 * A.card ≤ 2 ^ k := (Nat.mul_le_mul_right A.card hr64).trans hA
    change 64 * (A.card : ℤ) ≤ (2 ^ k : ℤ)
    exact_mod_cast h1
  have h4096 : 4096 * (A.card : ℤ) ^ 2 ≤ N ^ 2 := by
    have hA_nn : (0 : ℤ) ≤ A.card := by positivity
    nlinarith
  have hcube : (16 * S) ^ 3 ≤ (3 * N * (A.card : ℤ)) ^ 3 := by
    have hA3 : (0 : ℤ) ≤ (A.card : ℤ) ^ 3 := by positivity
    have hN : (0 : ℤ) ≤ N := by positivity
    have h1 : 15 * N * (4096 * (A.card : ℤ) ^ 2) * (A.card : ℤ) ^ 3 ≤
        15 * N * N ^ 2 * (A.card : ℤ) ^ 3 := by
      have hfac : 0 ≤ 15 * N * (A.card : ℤ) ^ 3 := by positivity
      calc 15 * N * (4096 * (A.card : ℤ) ^ 2) * (A.card : ℤ) ^ 3
          = (15 * N * (A.card : ℤ) ^ 3) * (4096 * (A.card : ℤ) ^ 2) := by ring
        _ ≤ (15 * N * (A.card : ℤ) ^ 3) * N ^ 2 := mul_le_mul_of_nonneg_left h4096 hfac
        _ = 15 * N * N ^ 2 * (A.card : ℤ) ^ 3 := by ring
    have h2 : 15 * N * N ^ 2 * (A.card : ℤ) ^ 3 ≤ 27 * N * N ^ 2 * (A.card : ℤ) ^ 3 := by
      have hnn : 0 ≤ N * N ^ 2 * (A.card : ℤ) ^ 3 := by positivity
      linarith
    calc (16 * S) ^ 3 = 4096 * S ^ 3 := by ring
      _ ≤ 4096 * (15 * N * (A.card : ℤ) ^ 5) := by linarith
      _ = 15 * N * (4096 * (A.card : ℤ) ^ 2) * (A.card : ℤ) ^ 3 := by ring
      _ ≤ 15 * N * N ^ 2 * (A.card : ℤ) ^ 3 := h1
      _ ≤ 27 * N * N ^ 2 * (A.card : ℤ) ^ 3 := h2
      _ = (3 * N * (A.card : ℤ)) ^ 3 := by ring
  by_contra hgt
  push_neg at hgt
  have hgt3 : (3 * N * (A.card : ℤ)) ^ 3 < (16 * S) ^ 3 := by
    have h1 : 0 ≤ 3 * N * (A.card : ℤ) := by positivity
    have hdiff : 0 < 16 * S - 3 * N * (A.card : ℤ) := by linarith
    have hquad : 0 < (16 * S) ^ 2 + (16 * S) * (3 * N * (A.card : ℤ)) + (3 * N * (A.card : ℤ)) ^ 2 := by
      nlinarith
    have hfac : (16 * S) ^ 3 - (3 * N * (A.card : ℤ)) ^ 3 =
        (16 * S - 3 * N * (A.card : ℤ)) *
          ((16 * S) ^ 2 + (16 * S) * (3 * N * (A.card : ℤ)) + (3 * N * (A.card : ℤ)) ^ 2) := by ring
    have hpos := mul_pos hdiff hquad
    linarith
  omega

end LevelOne


section ConflictBound

lemma conflict_lower_bound (k a : ℕ) (ha : 6 ≤ a) (hrk : 2 ^ a ≤ k)
    (π : Equiv.Perm (Fin (2 ^ k))) (U : Finset (Fin (2 ^ k))) (c : Fin (2 ^ k) → Bool) :
    16 * (U.card : ℤ) ^ 2 - 3 * (2 ^ k : ℤ) * (U.card : ℤ) ≤
      64 * (((U ×ˢ U).filter (fun z => z.1 < z.2 ∧
        xor (z.1.val.testBit ((π z.2).val % 2 ^ a)) (z.2.val.testBit ((π z.1).val % 2 ^ a)) ≠
          xor (c z.1) (c z.2))).card : ℤ) := by
  classical
  let N := 2 ^ k
  let r := 2 ^ a
  let addr : Fin N → Fin r := fun i => ⟨(π i).val % r, Nat.mod_lt _ (Nat.two_pow_pos a)⟩
  let U_s : Fin r → Finset (Fin N) := fun s => U.filter (fun i => addr i = s)
  have hU_card : U.card = ∑ s : Fin r, (U_s s).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := addr) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  have hUs_le : ∀ s : Fin r, r * (U_s s).card ≤ N := by
    intro s
    have h2k : N = r * 2 ^ (k - a) := by
      show 2 ^ k = 2 ^ a * 2 ^ (k - a)
      rw [← pow_add]; congr 1
      have ha2 : a < 2 ^ a := Nat.lt_two_pow_self
      omega
    have hle : (U_s s).card ≤ 2 ^ (k - a) := by
      rw [← Finset.card_range (2 ^ (k - a))]
      apply Finset.card_le_card_of_injOn (fun i => (π i).val / r)
      · intro i _
        refine Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)
        apply Nat.div_lt_of_lt_mul
        rw [← h2k]
        exact (π i).isLt
      · intro i hi j hj heq
        have hi' := (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2
        have hj' := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        have hmod : (π i).val % r = (π j).val % r := by
          have := congrArg Fin.val (hi'.trans hj'.symm)
          exact this
        have hval : (π i).val = (π j).val := by
          dsimp only at heq
          calc (π i).val = r * ((π i).val / r) + (π i).val % r := (Nat.div_add_mod _ _).symm
            _ = r * ((π j).val / r) + (π j).val % r := by rw [heq, hmod]
            _ = (π j).val := Nat.div_add_mod _ _
        exact π.injective (Fin.ext hval)
    calc r * (U_s s).card ≤ r * 2 ^ (k - a) := Nat.mul_le_mul_left r hle
      _ = N := h2k.symm
  let X : Fin r → Fin r → ℤ := fun s t => ∑ i ∈ U_s s, signBool (c i) * chi k r t i
  have hA_eq :
      ∑ i ∈ U, ∑ j ∈ U,
        signBool (xor (xor (i.val.testBit (addr j).val) (j.val.testBit (addr i).val))
                      (xor (c i) (c j))) =
      ∑ s : Fin r, ∑ t : Fin r, X s t * X t s := by
    have hterm : ∀ i j : Fin N,
        signBool (xor (xor (i.val.testBit (addr j).val) (j.val.testBit (addr i).val))
                      (xor (c i) (c j))) =
        (signBool (c i) * chi k r (addr j) i) * (signBool (c j) * chi k r (addr i) j) := by
      intro i j
      simp only [chi, signBool_xor]
      ring
    simp_rw [hterm]
    have hpart : ∀ (g : Fin N → ℤ), ∑ i ∈ U, g i = ∑ s : Fin r, ∑ i ∈ U_s s, g i := by
      intro g
      rw [← Finset.sum_fiberwise_of_maps_to (g := addr) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    rw [hpart]
    apply Finset.sum_congr rfl; intro s _
    calc ∑ i ∈ U_s s, ∑ j ∈ U, (signBool (c i) * chi k r (addr j) i) * (signBool (c j) * chi k r (addr i) j)
        = ∑ i ∈ U_s s, ∑ t : Fin r, ∑ j ∈ U_s t,
            (signBool (c i) * chi k r (addr j) i) * (signBool (c j) * chi k r (addr i) j) := by
          apply Finset.sum_congr rfl; intro i _; exact hpart _
      _ = ∑ t : Fin r, ∑ i ∈ U_s s, ∑ j ∈ U_s t,
            (signBool (c i) * chi k r t i) * (signBool (c j) * chi k r s j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro t _
          apply Finset.sum_congr rfl; intro i hi
          have his : addr i = s := (Finset.mem_filter.mp hi).2
          apply Finset.sum_congr rfl; intro j hj
          have hjt : addr j = t := (Finset.mem_filter.mp hj).2
          rw [his, hjt]
      _ = ∑ t : Fin r, X s t * X t s := by
          apply Finset.sum_congr rfl; intro t _
          simp only [X]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]
  have hcs_X : ∑ s : Fin r, ∑ t : Fin r, X s t * X t s ≤ ∑ s : Fin r, ∑ t : Fin r, (X s t) ^ 2 := by
    have hdiff : 0 ≤ ∑ s : Fin r, ∑ t : Fin r, (X s t - X t s) ^ 2 :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ => sq_nonneg _
    have hexp : ∑ s : Fin r, ∑ t : Fin r, (X s t - X t s) ^ 2 =
        2 * (∑ s : Fin r, ∑ t : Fin r, (X s t) ^ 2) - 2 * (∑ s : Fin r, ∑ t : Fin r, X s t * X t s) := by
      have hswap : ∑ s : Fin r, ∑ t : Fin r, (X t s) ^ 2 = ∑ s : Fin r, ∑ t : Fin r, (X s t) ^ 2 :=
        Finset.sum_comm
      have hsq : ∀ s t, (X s t - X t s) ^ 2 = (X s t) ^ 2 + (X t s) ^ 2 - 2 * (X s t * X t s) := by
        intros; ring
      simp_rw [hsq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hswap]
      ring
    linarith
  have hlevel : 16 * ∑ s : Fin r, ∑ t : Fin r, (X s t) ^ 2 ≤ 3 * (N : ℤ) * (U.card : ℤ) := by
    rw [Finset.mul_sum]
    have hle : ∑ s : Fin r, 16 * ∑ t : Fin r, (X s t) ^ 2 ≤
        ∑ s : Fin r, 3 * (N : ℤ) * ((U_s s).card : ℤ) := by
      apply Finset.sum_le_sum; intro s _
      exact level_one_bucket k a ha hrk (U_s s) (hUs_le s) c
    refine hle.trans_eq ?_
    rw [← Finset.mul_sum, hU_card, Nat.cast_sum]
  let badPred : Fin N × Fin N → Bool := fun z =>
    decide (xor (z.1.val.testBit (addr z.2).val) (z.2.val.testBit (addr z.1).val) ≠ xor (c z.1) (c z.2))
  let badAll := (U ×ˢ U).filter (fun z => badPred z = true)
  let badLt := (U ×ˢ U).filter (fun z => z.1 < z.2 ∧ badPred z = true)
  have hbadAll_eq : badAll.card = 2 * badLt.card := by
    let badGt := (U ×ˢ U).filter (fun z => z.2 < z.1 ∧ badPred z = true)
    have hgt : badGt.card = badLt.card := by
      apply Finset.card_bij (fun z _ => z.swap)
      · intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzU, hlt, hbp⟩
        rcases Finset.mem_product.mp hzU with ⟨h1, h2⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hlt, ?_⟩
        simp only [badPred, decide_eq_true_eq] at hbp ⊢
        intro heq; apply hbp
        rw [Bool.xor_comm (z.1.val.testBit _), Bool.xor_comm (c z.1)]
        exact heq
      · intro z1 _ z2 _ h; exact Prod.swap_injective h
      · intro z hz
        rcases Finset.mem_filter.mp hz with ⟨hzU, hlt, hbp⟩
        rcases Finset.mem_product.mp hzU with ⟨h1, h2⟩
        refine ⟨z.swap, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h2, h1⟩, hlt, ?_⟩, by simp⟩
        simp only [badPred, decide_eq_true_eq] at hbp ⊢
        intro heq; apply hbp
        rw [Bool.xor_comm (z.1.val.testBit _), Bool.xor_comm (c z.1)]
        exact heq
    have hunion : badLt ∪ badGt = badAll := by
      ext z
      simp only [badLt, badGt, badAll, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hU, _, hbp⟩ | ⟨hU, _, hbp⟩) <;> exact ⟨hU, hbp⟩
      · rintro ⟨hU, hbp⟩
        rcases lt_trichotomy z.1 z.2 with hlt | heq | hgt'
        · exact Or.inl ⟨hU, hlt, hbp⟩
        · exfalso
          simp only [badPred, heq, Bool.xor_self, ne_eq, not_true_eq_false, decide_false] at hbp
          exact Bool.false_ne_true hbp
        · exact Or.inr ⟨hU, hgt', hbp⟩
    have hdisj : Disjoint badLt badGt := by
      rw [Finset.disjoint_left]
      intro z h1 h2
      exact lt_asymm (Finset.mem_filter.mp h1).2.1 (Finset.mem_filter.mp h2).2.1
    rw [← hunion, Finset.card_union_of_disjoint hdisj, hgt]; omega
  have hsum_bad :
      ∑ i ∈ U, ∑ j ∈ U,
        signBool (xor (xor (i.val.testBit (addr j).val) (j.val.testBit (addr i).val))
                      (xor (c i) (c j))) =
      (U.card : ℤ) ^ 2 - 2 * (badAll.card : ℤ) := by
    have hprod :
        ∑ i ∈ U, ∑ j ∈ U,
          signBool (xor (xor (i.val.testBit (addr j).val) (j.val.testBit (addr i).val))
                        (xor (c i) (c j))) =
        ∑ z ∈ U ×ˢ U, (if badPred z = true then (-1 : ℤ) else 1) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      have hsb : ∀ b1 b2 : Bool,
          signBool (xor b1 b2) = if decide (b1 ≠ b2) = true then (-1 : ℤ) else 1 := by
        decide
      exact hsb _ _
    rw [hprod]
    have hrewrite : ∀ z : Fin N × Fin N,
        (if badPred z = true then (-1 : ℤ) else 1) = 1 - (if badPred z = true then (2 : ℤ) else 0) := by
      intro z; split_ifs <;> omega
    simp_rw [hrewrite, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_product, Nat.cast_mul, ← sq, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul]
    change (U.card : ℤ) ^ 2 - (badAll.card : ℤ) * 2 = (U.card : ℤ) ^ 2 - 2 * (badAll.card : ℤ)
    ring
  have hbadLt_eq : badLt =
      (U ×ˢ U).filter (fun z => z.1 < z.2 ∧
        xor (z.1.val.testBit ((π z.2).val % 2 ^ a)) (z.2.val.testBit ((π z.1).val % 2 ^ a)) ≠
          xor (c z.1) (c z.2)) := by
    ext z; simp [badLt, badPred, addr, r]
  rw [← hbadLt_eq]
  have h4 : (U.card : ℤ) ^ 2 - 4 * (badLt.card : ℤ) ≤ ∑ s : Fin r, ∑ t : Fin r, (X s t) ^ 2 := by
    have h1 : (U.card : ℤ) ^ 2 - 4 * (badLt.card : ℤ) = (U.card : ℤ) ^ 2 - 2 * (badAll.card : ℤ) := by
      rw [hbadAll_eq]; push_cast; ring
    rw [h1, ← hsum_bad, hA_eq]
    exact hcs_X
  change 16 * (U.card : ℤ) ^ 2 - 3 * (N : ℤ) * (U.card : ℤ) ≤ 64 * (badLt.card : ℤ)
  linarith

end ConflictBound

section UpperBound

open PEqualNP.CircuitLowerBounds

def runGates (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def fan2 (gs : List Gate) : Prop :=
  ∀ gate ∈ gs, gate.inputs.length ≤ 2

def count2 (gs : List Gate) : ℕ :=
  gs.countP (fun gate => gate.inputs.length == 2)

lemma runGates_nil (x : List Bool) : runGates [] x = x := rfl

lemma runGates_append (gs hs : List Gate) (x : List Bool) :
    runGates (gs ++ hs) x = runGates hs (runGates gs x) := by
  simp [runGates, List.foldl_append]

lemma runGates_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    runGates (gs ++ [g]) x =
      runGates gs x ++ [g.op.eval (g.inputs.map fun i => (runGates gs x).getD i false)] := by
  simp [runGates, List.foldl_append]

lemma runGates_length (gs : List Gate) (x : List Bool) :
    (runGates gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [runGates]
  | append_singleton gs g ih => rw [runGates_snoc]; simp [ih]; omega

lemma getD_append_lt (l : List Bool) (b : Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ [b]).getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_at (l : List Bool) (b : Bool) :
    (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma runGates_getD_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs.length) :
    (runGates (gs ++ hs) x).getD i false = (runGates gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, runGates_snoc, getD_append_lt]
    · exact ih
    · rw [runGates_length, List.length_append]; omega

lemma runGates_getD_init (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (runGates gs x).getD i false = x.getD i false := by
  have h := runGates_getD_prefix [] gs x i (by simpa using hi)
  simpa [runGates_nil] using h

lemma fan2_append {gs hs : List Gate} (hg : fan2 gs) (hh : fan2 hs) : fan2 (gs ++ hs) := by
  intro g hmem
  rcases List.mem_append.mp hmem with h | h
  · exact hg g h
  · exact hh g h

lemma count2_append (gs hs : List Gate) : count2 (gs ++ hs) = count2 gs + count2 hs := by
  simp [count2, List.countP_append]

def orList (base : ℕ) : List ℕ → List Gate × ℕ
  | [] => ([⟨GateOp.or, []⟩], base)
  | [w] => ([], w)
  | w :: w' :: ws =>
    let res := orList base (w' :: ws)
    (res.1 ++ [⟨GateOp.or, [w, res.2]⟩], base + res.1.length)

lemma orList_fan2 (base : ℕ) (ws : List ℕ) : fan2 (orList base ws).1 := by
  induction ws with
  | nil => intro g hg; simp [orList] at hg; subst hg; decide
  | cons w rest ih =>
    cases rest with
    | nil => intro g hg; simp [orList] at hg
    | cons w' ws' =>
      simp only [orList]
      apply fan2_append ih
      intro g hg; simp at hg; subst hg; simp

lemma orList_count2 (base : ℕ) (ws : List ℕ) : count2 (orList base ws).1 ≤ ws.length := by
  induction ws with
  | nil => simp [orList, count2]
  | cons w rest ih =>
    cases rest with
    | nil => simp [orList, count2]
    | cons w' ws' =>
      simp only [orList, count2_append]
      have h1 : count2 [⟨GateOp.or, [w, (orList base (w' :: ws')).2]⟩] = 1 := by simp [count2]
      rw [h1]; simp only [List.length_cons] at ih ⊢; omega

lemma orList_count2_sub (base : ℕ) (ws : List ℕ) : count2 (orList base ws).1 ≤ ws.length - 1 := by
  induction ws with
  | nil => simp [orList, count2]
  | cons w rest ih =>
    cases rest with
    | nil => simp [orList, count2]
    | cons w' ws' =>
      simp only [orList, count2_append]
      have h1 : count2 [⟨GateOp.or, [w, (orList base (w' :: ws')).2]⟩] = 1 := by simp [count2]
      rw [h1]; simp only [List.length_cons] at ih ⊢; omega

lemma orList_out_lt (base : ℕ) (ws : List ℕ) (hw : ∀ w ∈ ws, w < base) :
    (orList base ws).2 < base + (orList base ws).1.length := by
  induction ws with
  | nil => simp [orList]
  | cons w rest ih =>
    cases rest with
    | nil =>
      simp only [orList, List.length_nil, add_zero]
      exact hw w (by simp)
    | cons w' ws' =>
      simp only [orList, List.length_append, List.length_singleton]
      omega

lemma orList_eval (x : List Bool) (ws : List ℕ) (hw : ∀ w ∈ ws, w < x.length) :
    (runGates (orList x.length ws).1 x).getD (orList x.length ws).2 false =
      ws.any (fun w => x.getD w false) := by
  induction ws with
  | nil =>
    have h1 : runGates [⟨GateOp.or, []⟩] x = x ++ [false] := by
      simp [runGates, GateOp.eval]
    simp only [orList, h1, getD_append_at, List.any_nil]
  | cons w rest ih =>
    cases rest with
    | nil =>
      simp [orList, runGates]
    | cons w' ws' =>
      have hw' : ∀ u ∈ w' :: ws', u < x.length := fun u hu => hw u (List.mem_cons_of_mem w hu)
      have hih := ih hw'
      simp only [orList]
      rw [runGates_snoc]
      have hlen : (runGates (orList x.length (w' :: ws')).1 x).length =
          x.length + (orList x.length (w' :: ws')).1.length := runGates_length _ _
      rw [← hlen, getD_append_at]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        Bool.or_false, id_eq]
      rw [runGates_getD_init _ _ _ (hw w (by simp)), hih]
      simp [List.any_cons]

def orBank (base : ℕ) : List (List ℕ) → List Gate × List ℕ
  | [] => ([], [])
  | ws :: rest =>
    let r1 := orList base ws
    let r2 := orBank (base + r1.1.length) rest
    (r1.1 ++ r2.1, r1.2 :: r2.2)

lemma orBank_fan2 (base : ℕ) (groups : List (List ℕ)) : fan2 (orBank base groups).1 := by
  induction groups generalizing base with
  | nil => intro g hg; simp [orBank] at hg
  | cons ws rest ih =>
    simp only [orBank]
    exact fan2_append (orList_fan2 base ws) (ih _)

lemma orBank_count2 (base : ℕ) (groups : List (List ℕ)) :
    count2 (orBank base groups).1 ≤ (groups.map List.length).sum := by
  induction groups generalizing base with
  | nil => simp [orBank, count2]
  | cons ws rest ih =>
    simp only [orBank, count2_append, List.map_cons, List.sum_cons]
    have h1 := orList_count2 base ws
    have h2 := ih (base + (orList base ws).1.length)
    omega

lemma orBank_length (base : ℕ) (groups : List (List ℕ)) :
    (orBank base groups).2.length = groups.length := by
  induction groups generalizing base with
  | nil => rfl
  | cons ws rest ih => simp [orBank, ih]

lemma orBank_out_lt (base : ℕ) (groups : List (List ℕ))
    (hw : ∀ ws ∈ groups, ∀ w ∈ ws, w < base) :
    ∀ w ∈ (orBank base groups).2, w < base + (orBank base groups).1.length := by
  induction groups generalizing base with
  | nil => intro w hw'; simp [orBank] at hw'
  | cons ws rest ih =>
    intro w hw'
    simp only [orBank, List.mem_cons, List.length_append] at hw' ⊢
    rcases hw' with rfl | hrest
    · have h1 := orList_out_lt base ws (hw ws (by simp))
      omega
    · have h2 := ih (base + (orList base ws).1.length)
        (fun ws' hws' u hu => lt_of_lt_of_le (hw ws' (List.mem_cons_of_mem ws hws') u hu) (by omega))
        w hrest
      omega

lemma orBank_eval (x : List Bool) (groups : List (List ℕ))
    (hw : ∀ ws ∈ groups, ∀ w ∈ ws, w < x.length)
    (i : ℕ) (hi : i < groups.length) :
    (runGates (orBank x.length groups).1 x).getD ((orBank x.length groups).2.getD i 0) false =
      (groups.getD i []).any (fun w => x.getD w false) := by
  induction groups generalizing x i with
  | nil => simp at hi
  | cons ws rest ih =>
    simp only [orBank]
    cases i with
    | zero =>
      simp only [List.getD_cons_zero]
      have hlt := orList_out_lt x.length ws (hw ws (by simp))
      rw [runGates_getD_prefix _ _ _ _ hlt]
      exact orList_eval x ws (hw ws (by simp))
    | succ j =>
      simp only [List.length_cons] at hi
      simp only [List.getD_cons_succ]
      let x1 := runGates (orList x.length ws).1 x
      have hx1len : x1.length = x.length + (orList x.length ws).1.length := runGates_length _ _
      rw [runGates_append]
      change (runGates (orBank (x.length + (orList x.length ws).1.length) rest).1 x1).getD
          ((orBank (x.length + (orList x.length ws).1.length) rest).2.getD j 0) false =
        (rest.getD j []).any (fun w => x.getD w false)
      rw [← hx1len]
      have hw1 : ∀ ws' ∈ rest, ∀ w ∈ ws', w < x1.length := by
        intro ws' hws' w hwm
        have := hw ws' (List.mem_cons_of_mem ws hws') w hwm
        omega
      have hih := ih x1 hw1 j (by omega)
      rw [hih]
      have hmem : rest.getD j [] ∈ rest := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact List.getElem_mem _
      have hany : ∀ (l : List ℕ) (p q : ℕ → Bool), (∀ w ∈ l, p w = q w) → l.any p = l.any q := by
        intro l p q h
        induction l with
        | nil => rfl
        | cons a t ih => simp [h a (by simp), ih (fun w hw => h w (by simp [hw]))]
      apply hany
      intro w hwm
      exact runGates_getD_init _ _ _ (hw _ (List.mem_cons_of_mem ws hmem) w hwm)

def encodeRows : (s : ℕ) → (base : ℕ) → (Fin (2 ^ s) → ℕ) → List Gate × (Fin s → ℕ)
  | 0, _, _ => ([], fun i => Fin.elim0 i)
  | s + 1, base, ws =>
    let pairGates : List Gate :=
      List.ofFn (fun j : Fin (2 ^ s) =>
        ⟨GateOp.or,
          [ws ⟨2 * j.val, by have := j.isLt; rw [pow_succ']; omega⟩,
           ws ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ']; omega⟩]⟩)
    let oddList : List ℕ :=
      List.ofFn (fun j : Fin (2 ^ s) =>
        ws ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ']; omega⟩)
    let oddRes := orList (base + 2 ^ s) oddList
    let pairWires : Fin (2 ^ s) → ℕ := fun j => base + j.val
    let recRes := encodeRows s (base + 2 ^ s + oddRes.1.length) pairWires
    (pairGates ++ oddRes.1 ++ recRes.1,
     fun t => if h : t.val = 0 then oddRes.2 else recRes.2 ⟨t.val - 1, by omega⟩)

lemma runGates_ofFn_or2 (x : List Bool) (n : ℕ) (u v : Fin n → ℕ)
    (hu : ∀ j, u j < x.length) (hv : ∀ j, v j < x.length) (j : Fin n) :
    (runGates (List.ofFn (fun i : Fin n => ⟨GateOp.or, [u i, v i]⟩)) x).getD (x.length + j.val) false =
      (x.getD (u j) false || x.getD (v j) false) := by
  have hgen : ∀ (m : ℕ) (hm : m ≤ n),
      ∀ (j : Fin m),
        (runGates (List.ofFn (fun i : Fin m =>
            ⟨GateOp.or, [u ⟨i.val, lt_of_lt_of_le i.isLt hm⟩, v ⟨i.val, lt_of_lt_of_le i.isLt hm⟩]⟩)) x).getD
          (x.length + j.val) false =
        (x.getD (u ⟨j.val, lt_of_lt_of_le j.isLt hm⟩) false ||
         x.getD (v ⟨j.val, lt_of_lt_of_le j.isLt hm⟩) false) := by
    intro m
    induction m with
    | zero => intro _ j; exact Fin.elim0 j
    | succ m ih =>
      intro hm j
      rw [List.ofFn_succ', List.concat_eq_append, runGates_snoc]
      simp only [Fin.coe_castSucc, Fin.val_last]
      by_cases hj : j.val < m
      · have hlen : (runGates (List.ofFn (fun i : Fin m =>
            ⟨GateOp.or, [u ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩,
                         v ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩]⟩)) x).length = x.length + m := by
          rw [runGates_length, List.length_ofFn]
        rw [getD_append_lt _ _ _ (by rw [hlen]; omega)]
        exact ih (by omega) ⟨j.val, hj⟩
      · have hjm : j.val = m := by omega
        have hlen : (runGates (List.ofFn (fun i : Fin m =>
            ⟨GateOp.or, [u ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩,
                         v ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩]⟩)) x).length = x.length + m := by
          rw [runGates_length, List.length_ofFn]
        have hidx : x.length + j.val = (runGates (List.ofFn (fun i : Fin m =>
            ⟨GateOp.or, [u ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩,
                         v ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩]⟩)) x).length := by omega
        rw [hidx, getD_append_at]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
          Bool.or_false, id_eq]
        rw [runGates_getD_init _ _ _ (hu _), runGates_getD_init _ _ _ (hv _)]
        congr 1
        · congr 2; exact Fin.ext hjm.symm
        · congr 2; exact Fin.ext hjm.symm
  exact hgen n le_rfl j

lemma encodeRows_fan2 (s base : ℕ) (ws : Fin (2 ^ s) → ℕ) : fan2 (encodeRows s base ws).1 := by
  induction s generalizing base with
  | zero => intro g hg; simp [encodeRows] at hg
  | succ s ih =>
    simp only [encodeRows]
    apply fan2_append (fan2_append _ (orList_fan2 _ _)) (ih _ _)
    intro g hg
    rw [List.mem_ofFn] at hg
    obtain ⟨j, rfl⟩ := hg
    simp

lemma encodeRows_count2 (s base : ℕ) (ws : Fin (2 ^ s) → ℕ) :
    count2 (encodeRows s base ws).1 + 2 ≤ 2 * 2 ^ s := by
  induction s generalizing base with
  | zero => simp [encodeRows, count2]
  | succ s ih =>
    simp only [encodeRows, count2_append]
    have hpair : count2 (List.ofFn (fun j : Fin (2 ^ s) =>
        ⟨GateOp.or, [ws ⟨2 * j.val, by have := j.isLt; rw [pow_succ']; omega⟩,
                     ws ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ']; omega⟩]⟩)) = 2 ^ s := by
      unfold count2
      rw [List.countP_eq_length.mpr (by intro g hg; rw [List.mem_ofFn] at hg; obtain ⟨j, rfl⟩ := hg; simp),
        List.length_ofFn]
    have hodd := orList_count2_sub (base + 2 ^ s)
      (List.ofFn (fun j : Fin (2 ^ s) => ws ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ']; omega⟩))
    rw [List.length_ofFn] at hodd
    have hrec := ih (base + 2 ^ s + (orList (base + 2 ^ s)
      (List.ofFn (fun j : Fin (2 ^ s) => ws ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ']; omega⟩))).1.length)
      (fun j => base + j.val)
    have hpos : 1 ≤ 2 ^ s := Nat.two_pow_pos s
    have hpow : 2 ^ (s + 1) = 2 * 2 ^ s := pow_succ' 2 s
    omega

lemma encodeRows_out_lt (s base : ℕ) (ws : Fin (2 ^ s) → ℕ) (hw : ∀ u, ws u < base) :
    ∀ t : Fin s, (encodeRows s base ws).2 t < base + (encodeRows s base ws).1.length := by
  induction s generalizing base with
  | zero => intro t; exact Fin.elim0 t
  | succ s ih =>
    intro t
    simp only [encodeRows, List.length_append, List.length_ofFn]
    split_ifs with ht
    · have h1 := orList_out_lt (base + 2 ^ s)
        (List.ofFn (fun j : Fin (2 ^ s) => ws ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ']; omega⟩))
        (fun w hwm => by
          rw [List.mem_ofFn] at hwm
          obtain ⟨j, rfl⟩ := hwm
          exact lt_of_lt_of_le (hw _) (Nat.le_add_right base (2 ^ s)))
      omega
    · have h2 := ih (base + 2 ^ s + (orList (base + 2 ^ s)
        (List.ofFn (fun j : Fin (2 ^ s) => ws ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ']; omega⟩))).1.length)
        (fun j => base + j.val)
        (fun j => by have := j.isLt; omega)
        ⟨t.val - 1, by have := t.isLt; omega⟩
      omega

lemma encodeRows_eval (s : ℕ) (x : List Bool) (ws : Fin (2 ^ s) → ℕ)
    (hw : ∀ u, ws u < x.length) (u0 : Fin (2 ^ s))
    (hws : ∀ u : Fin (2 ^ s), x.getD (ws u) false = decide (u = u0)) :
    ∀ t : Fin s,
      (runGates (encodeRows s x.length ws).1 x).getD ((encodeRows s x.length ws).2 t) false =
        u0.val.testBit t.val := by
  induction s generalizing x with
  | zero => intro t; exact Fin.elim0 t
  | succ s ih =>
    intro t
    simp only [encodeRows]
    let pairGates : List Gate :=
      List.ofFn (fun j : Fin (2 ^ s) =>
        ⟨GateOp.or,
          [ws ⟨2 * j.val, by have := j.isLt; rw [pow_succ']; omega⟩,
           ws ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ']; omega⟩]⟩)
    let oddList : List ℕ :=
      List.ofFn (fun j : Fin (2 ^ s) =>
        ws ⟨2 * j.val + 1, by have := j.isLt; rw [pow_succ']; omega⟩)
    let oddRes := orList (x.length + 2 ^ s) oddList
    let pairWires : Fin (2 ^ s) → ℕ := fun j => x.length + j.val
    let recRes := encodeRows s (x.length + 2 ^ s + oddRes.1.length) pairWires
    let x1 := runGates pairGates x
    have hx1len : x1.length = x.length + 2 ^ s := by
      simp [x1, pairGates, runGates_length, List.length_ofFn]
    let x2 := runGates oddRes.1 x1
    have hx2len : x2.length = x.length + 2 ^ s + oddRes.1.length := by
      simp [x2, runGates_length, hx1len]
    have hpow : 2 ^ (s + 1) = 2 * 2 ^ s := pow_succ' 2 s
    have hu0_div : u0.val / 2 < 2 ^ s := by have := u0.isLt; omega
    have hx1_pair : ∀ j : Fin (2 ^ s), x1.getD (x.length + j.val) false =
        decide (j = ⟨u0.val / 2, hu0_div⟩) := by
      intro j
      have h := runGates_ofFn_or2 x (2 ^ s)
        (fun i => ws ⟨2 * i.val, by have := i.isLt; omega⟩)
        (fun i => ws ⟨2 * i.val + 1, by have := i.isLt; omega⟩)
        (fun i => hw _) (fun i => hw _) j
      change x1.getD (x.length + j.val) false = _
      rw [h, hws, hws]
      by_cases hdiv : j.val = u0.val / 2
      · have hmod : u0.val % 2 = 0 ∨ u0.val % 2 = 1 := Nat.mod_two_eq_zero_or_one u0.val
        have hfin : j = ⟨u0.val / 2, hu0_div⟩ := Fin.ext hdiv
        rw [decide_eq_true hfin]
        rcases hmod with hm | hm
        · have heq : (⟨2 * j.val, by have := j.isLt; omega⟩ : Fin (2 ^ (s + 1))) = u0 :=
            Fin.ext (by simp; omega)
          simp [heq]
        · have heq : (⟨2 * j.val + 1, by have := j.isLt; omega⟩ : Fin (2 ^ (s + 1))) = u0 :=
            Fin.ext (by simp; omega)
          simp [heq]
      · have hne1 : (⟨2 * j.val, by have := j.isLt; omega⟩ : Fin (2 ^ (s + 1))) ≠ u0 := by
          intro heq; apply hdiv; have := congrArg Fin.val heq; simp at this; omega
        have hne2 : (⟨2 * j.val + 1, by have := j.isLt; omega⟩ : Fin (2 ^ (s + 1))) ≠ u0 := by
          intro heq; apply hdiv; have := congrArg Fin.val heq; simp at this; omega
        have hne3 : j ≠ ⟨u0.val / 2, hu0_div⟩ := by
          intro heq; apply hdiv; exact congrArg Fin.val heq
        simp [hne1, hne2, hne3]
    split_ifs with ht
    · have hodd_lt : oddRes.2 < x.length + (pairGates ++ oddRes.1).length := by
        have h1 := orList_out_lt (x.length + 2 ^ s) oddList (fun w hwm => by
          rw [List.mem_ofFn] at hwm; obtain ⟨j, rfl⟩ := hwm; exact lt_of_lt_of_le (hw _) (by omega))
        simp only [oddRes, pairGates, List.length_append, List.length_ofFn] at h1 ⊢
        omega
      rw [runGates_getD_prefix (pairGates ++ oddRes.1) recRes.1 x oddRes.2 hodd_lt,
        runGates_append]
      change (runGates oddRes.1 x1).getD oddRes.2 false = u0.val.testBit t.val
      have hodd_eval : (runGates oddRes.1 x1).getD oddRes.2 false = oddList.any (fun w => x1.getD w false) := by
        have h := orList_eval x1 oddList (fun w hwm => by
          rw [List.mem_ofFn] at hwm; obtain ⟨j, rfl⟩ := hwm
          rw [hx1len]; exact lt_of_lt_of_le (hw _) (Nat.le_add_right x.length (2 ^ s)))
        simpa only [oddRes, hx1len] using h
      rw [hodd_eval, ht]
      have hbit0 : u0.val.testBit 0 = decide (u0.val % 2 = 1) := by
        simp [Nat.testBit_zero]
      rw [hbit0]
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨w, hwm, hwtrue⟩
        rw [List.mem_ofFn] at hwm
        obtain ⟨j, rfl⟩ := hwm
        rw [runGates_getD_init _ _ _ (hw _), hws, decide_eq_true_eq] at hwtrue
        have := congrArg Fin.val hwtrue
        simp at this
        omega
      · intro hmod
        let j : Fin (2 ^ s) := ⟨u0.val / 2, hu0_div⟩
        refine ⟨ws ⟨2 * j.val + 1, by have := j.isLt; omega⟩, ?_, ?_⟩
        · rw [List.mem_ofFn]; exact ⟨j, rfl⟩
        · rw [runGates_getD_init _ _ _ (hw _), hws, decide_eq_true_eq]
          exact Fin.ext (by simp [j]; omega)
    · rw [runGates_append, runGates_append]
      change (runGates recRes.1 x2).getD (recRes.2 ⟨t.val - 1, by have := t.isLt; omega⟩) false = u0.val.testBit t.val
      have hrec_eval := ih x2 pairWires
        (fun j => by simp only [pairWires, hx2len]; have := j.isLt; omega)
        ⟨u0.val / 2, hu0_div⟩
        (fun j => by
          rw [runGates_getD_init _ _ _ (by simp only [pairWires, hx1len]; exact Nat.add_lt_add_left j.isLt _)]
          exact hx1_pair j)
        ⟨t.val - 1, by have := t.isLt; omega⟩
      simp only [recRes, hx2len] at hrec_eval ⊢
      rw [hrec_eval, Nat.testBit_div_two]
      congr 1
      omega

def rowTypeVal : ℕ → ℕ → Bool → ℕ
  | 0, _, _ => 0
  | r + 1, x, fx => rowTypeVal r x fx + if xor (x.testBit r) fx then 2 ^ r else 0

lemma rowTypeVal_lt (r x : ℕ) (fx : Bool) : rowTypeVal r x fx < 2 ^ r := by
  induction r with
  | zero => simp [rowTypeVal]
  | succ r ih =>
    simp only [rowTypeVal, pow_succ']
    split_ifs <;> omega

lemma rowTypeVal_testBit (r x : ℕ) (fx : Bool) (t : ℕ) (ht : t < r) :
    (rowTypeVal r x fx).testBit t = xor (x.testBit t) fx := by
  induction r with
  | zero => omega
  | succ r ih =>
    simp only [rowTypeVal]
    by_cases htr : t < r
    · have hdiv : 2 ^ r = 2 ^ t * 2 ^ (r - t) := by rw [← pow_add]; congr 1; omega
      have heven : 2 ∣ 2 ^ (r - t) := by
        have hpos : 1 ≤ r - t := by omega
        obtain ⟨q, hq⟩ : ∃ q, r - t = q + 1 := ⟨r - t - 1, by omega⟩
        rw [hq, pow_succ]
        exact dvd_mul_left 2 _
      have hsame : ∀ a : ℕ, (a + if xor (x.testBit r) fx then 2 ^ r else 0).testBit t = a.testBit t := by
        intro a
        split_ifs
        · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
          rw [hdiv, Nat.add_mul_div_left _ _ (Nat.two_pow_pos t)]
          obtain ⟨q, hq⟩ := heven
          rw [hq]
          simp [Nat.add_mod, Nat.mul_mod]
        · simp
      rw [hsame, ih htr]
    · have hteq : t = r := by omega
      subst hteq
      have hlt := rowTypeVal_lt t x fx
      rw [Nat.testBit_eq_decide_div_mod_eq]
      split_ifs with hbit
      · have h1 : (rowTypeVal t x fx + 2 ^ t) / 2 ^ t = 1 := by
          rw [Nat.add_div_right _ (Nat.two_pow_pos t), Nat.div_eq_of_lt hlt]
        rw [h1, hbit]; decide
      · have h0 : (rowTypeVal t x fx + 0) / 2 ^ t = 0 := by
          rw [add_zero, Nat.div_eq_of_lt hlt]
        rw [h0]
        cases h : xor (x.testBit t) fx <;> simp_all

def selectOne (base bitW colFW colTW : ℕ) : List Gate × ℕ :=
  ([⟨GateOp.not, [bitW]⟩,
    ⟨GateOp.and, [colFW, bitW]⟩,
    ⟨GateOp.and, [colTW, base]⟩,
    ⟨GateOp.or, [base + 1, base + 2]⟩],
   base + 3)

lemma selectOne_fan2 (base bitW colFW colTW : ℕ) :
    fan2 (selectOne base bitW colFW colTW).1 := by
  intro g hg
  simp only [selectOne, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

lemma selectOne_count2 (base bitW colFW colTW : ℕ) :
    count2 (selectOne base bitW colFW colTW).1 = 3 := by
  simp [selectOne, count2]

lemma selectOne_eval (x : List Bool) (bitW colFW colTW : ℕ)
    (hb : bitW < x.length) (hf : colFW < x.length) (ht : colTW < x.length) :
    (runGates (selectOne x.length bitW colFW colTW).1 x).getD (selectOne x.length bitW colFW colTW).2 false =
      ((x.getD colFW false && x.getD bitW false) || (x.getD colTW false && !(x.getD bitW false))) := by
  simp only [selectOne]
  let g0 : Gate := ⟨GateOp.not, [bitW]⟩
  let g1 : Gate := ⟨GateOp.and, [colFW, bitW]⟩
  let g2 : Gate := ⟨GateOp.and, [colTW, x.length]⟩
  let g3 : Gate := ⟨GateOp.or, [x.length + 1, x.length + 2]⟩
  have hlist : [g0, g1, g2, g3] = ((([] ++ [g0]) ++ [g1]) ++ [g2]) ++ [g3] := rfl
  rw [hlist]
  let x0 := runGates [g0] x
  let x1 := runGates ([g0] ++ [g1]) x
  let x2 := runGates (([g0] ++ [g1]) ++ [g2]) x
  have hx0_eq : x0 = x ++ [!(x.getD bitW false)] := by
    simp [x0, g0, runGates, GateOp.eval]
  have hx0_len : x0.length = x.length + 1 := by simp [hx0_eq]
  have hx0_at : x0.getD x.length false = !(x.getD bitW false) := by
    rw [hx0_eq, getD_append_at]
  have hx0_init : ∀ i < x.length, x0.getD i false = x.getD i false := by
    intro i hi; rw [hx0_eq, getD_append_lt _ _ _ hi]
  have hx1_eq : x1 = x0 ++ [x.getD colFW false && x.getD bitW false] := by
    simp only [x1, runGates_snoc, g1, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, Bool.and_true, id_eq]
    change x0 ++ [x0.getD colFW false && x0.getD bitW false] = _
    rw [hx0_init _ hf, hx0_init _ hb]
  have hx1_len : x1.length = x.length + 2 := by simp [hx1_eq, hx0_len]
  have hx1_at : x1.getD (x.length + 1) false = (x.getD colFW false && x.getD bitW false) := by
    rw [hx1_eq, ← hx0_len, getD_append_at]
  have hx1_lt : ∀ i < x.length + 1, x1.getD i false = x0.getD i false := by
    intro i hi; rw [hx1_eq, getD_append_lt _ _ _ (by omega)]
  have hx2_eq : x2 = x1 ++ [x.getD colTW false && !(x.getD bitW false)] := by
    simp only [x2, runGates_snoc, g2, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, Bool.and_true, id_eq]
    change x1 ++ [x1.getD colTW false && x1.getD x.length false] = _
    rw [hx1_lt _ (by omega), hx0_init _ ht, hx1_lt _ (by omega), hx0_at]
  have hx2_len : x2.length = x.length + 3 := by simp [hx2_eq, hx1_len]
  have hx2_at : x2.getD (x.length + 2) false = (x.getD colTW false && !(x.getD bitW false)) := by
    rw [hx2_eq, ← hx1_len, getD_append_at]
  have hx2_lt : ∀ i < x.length + 2, x2.getD i false = x1.getD i false := by
    intro i hi; rw [hx2_eq, getD_append_lt _ _ _ (by omega)]
  rw [runGates_snoc]
  change (x2 ++ [g3.op.eval (g3.inputs.map fun i => x2.getD i false)]).getD (x.length + 3) false = _
  rw [← hx2_len, getD_append_at]
  simp only [g3, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
    Bool.or_false, id_eq]
  rw [hx2_lt _ (by omega), hx1_at, hx2_at]

def selectBank (base : ℕ) : List (ℕ × ℕ × ℕ) → List Gate × List ℕ
  | [] => ([], [])
  | (b, cf, ct) :: rest =>
    let r1 := selectOne base b cf ct
    let r2 := selectBank (base + r1.1.length) rest
    (r1.1 ++ r2.1, r1.2 :: r2.2)

lemma selectBank_fan2 (base : ℕ) (ts : List (ℕ × ℕ × ℕ)) : fan2 (selectBank base ts).1 := by
  induction ts generalizing base with
  | nil => intro g hg; simp [selectBank] at hg
  | cons p rest ih =>
    rcases p with ⟨b, cf, ct⟩
    simp only [selectBank]
    exact fan2_append (selectOne_fan2 base b cf ct) (ih _)

lemma selectBank_count2 (base : ℕ) (ts : List (ℕ × ℕ × ℕ)) :
    count2 (selectBank base ts).1 = 3 * ts.length := by
  induction ts generalizing base with
  | nil => simp [selectBank, count2]
  | cons p rest ih =>
    rcases p with ⟨b, cf, ct⟩
    simp only [selectBank, count2_append, selectOne_count2, List.length_cons]
    have := ih (base + (selectOne base b cf ct).1.length)
    omega

lemma selectBank_length (base : ℕ) (ts : List (ℕ × ℕ × ℕ)) :
    (selectBank base ts).2.length = ts.length := by
  induction ts generalizing base with
  | nil => rfl
  | cons p rest ih => rcases p with ⟨b, cf, ct⟩; simp [selectBank, ih]

lemma selectBank_out_lt (base : ℕ) (ts : List (ℕ × ℕ × ℕ)) :
    ∀ w ∈ (selectBank base ts).2, w < base + (selectBank base ts).1.length := by
  induction ts generalizing base with
  | nil => intro w hw; simp [selectBank] at hw
  | cons p rest ih =>
    rcases p with ⟨b, cf, ct⟩
    intro w hw
    simp only [selectBank, List.mem_cons, List.length_append] at hw ⊢
    rcases hw with rfl | hrest
    · simp only [selectOne, List.length_cons, List.length_nil]; omega
    · have := ih (base + (selectOne base b cf ct).1.length) w hrest
      omega

lemma selectBank_eval (x : List Bool) (ts : List (ℕ × ℕ × ℕ))
    (hw : ∀ p ∈ ts, p.1 < x.length ∧ p.2.1 < x.length ∧ p.2.2 < x.length)
    (i : ℕ) (hi : i < ts.length) :
    (runGates (selectBank x.length ts).1 x).getD ((selectBank x.length ts).2.getD i 0) false =
      let p := ts.getD i (0, 0, 0)
      ((x.getD p.2.1 false && x.getD p.1 false) || (x.getD p.2.2 false && !(x.getD p.1 false))) := by
  induction ts generalizing x i with
  | nil => simp at hi
  | cons p rest ih =>
    rcases p with ⟨b, cf, ct⟩
    simp only [selectBank]
    cases i with
    | zero =>
      simp only [List.getD_cons_zero]
      have hlt : (selectOne x.length b cf ct).2 < x.length + (selectOne x.length b cf ct).1.length := by
        simp [selectOne]
      rw [runGates_getD_prefix _ _ _ _ hlt]
      have hp := hw (b, cf, ct) (by simp)
      exact selectOne_eval x b cf ct hp.1 hp.2.1 hp.2.2
    | succ j =>
      simp only [List.length_cons] at hi
      simp only [List.getD_cons_succ]
      let x1 := runGates (selectOne x.length b cf ct).1 x
      have hx1len : x1.length = x.length + (selectOne x.length b cf ct).1.length := runGates_length _ _
      rw [runGates_append]
      change (runGates (selectBank (x.length + (selectOne x.length b cf ct).1.length) rest).1 x1).getD
          ((selectBank (x.length + (selectOne x.length b cf ct).1.length) rest).2.getD j 0) false = _
      rw [← hx1len]
      have hw1 : ∀ q ∈ rest, q.1 < x1.length ∧ q.2.1 < x1.length ∧ q.2.2 < x1.length := by
        intro q hq
        have := hw q (List.mem_cons_of_mem _ hq)
        omega
      have hih := ih x1 hw1 j (by omega)
      rw [hih]
      have hmem : rest.getD j (0, 0, 0) ∈ rest := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact List.getElem_mem _
      have hq := hw _ (List.mem_cons_of_mem _ hmem)
      dsimp only
      rw [runGates_getD_init _ _ _ hq.1, runGates_getD_init _ _ _ hq.2.1,
        runGates_getD_init _ _ _ hq.2.2]

lemma partition_sum_length {α : Type*} (l : List α) (m : ℕ) (key : α → Fin m) :
    ((List.ofFn (fun u : Fin m => l.filter (fun a => key a == u))).map List.length).sum = l.length := by
  induction l with
  | nil =>
    simp only [List.filter_nil, List.map_ofFn, Function.comp_def, List.length_nil]
    have : ∀ n, (List.ofFn (fun _ : Fin n => (0 : ℕ))).sum = 0 := by
      intro n; induction n with | zero => rfl | succ n ih => rw [List.ofFn_succ, List.sum_cons, ih]
    exact this m
  | cons a rest ih =>
    simp only [List.filter_cons, List.length_cons]
    rw [← ih]
    have hsplit : ∀ (f g : Fin m → ℕ),
        (∀ u, f u = g u + if key a == u then 1 else 0) →
        (List.ofFn f).sum = (List.ofFn g).sum + 1 := by
      intro f g hfg
      have h1 : (List.ofFn f).sum = ∑ u : Fin m, f u := List.sum_ofFn
      have h2 : (List.ofFn g).sum = ∑ u : Fin m, g u := List.sum_ofFn
      rw [h1, h2]
      simp_rw [hfg, Finset.sum_add_distrib]
      congr 1
      have h3 : (∑ u : Fin m, if key a == u then (1 : ℕ) else 0) =
          ∑ u : Fin m, if u = key a then (1 : ℕ) else 0 := by
        apply Finset.sum_congr rfl; intro u _
        by_cases h : u = key a
        · subst h; simp
        · simp [h, beq_false_of_ne (Ne.symm h)]
      rw [h3, Finset.sum_ite_eq']
      simp
    simp only [List.map_ofFn, Function.comp_def]
    apply hsplit
    intro u
    by_cases h : (key a == u) = true <;> simp [h]

lemma oneEach_length {n : ℕ} (x y : Fin n) :
    (PEqualNP.Represents.oneEach x y).length = 2 * n := by
  simp [PEqualNP.Represents.oneEach]; omega

lemma oneEach_getD_left {n : ℕ} (x y : Fin n) (i : ℕ) (hi : i < n) :
    (PEqualNP.Represents.oneEach x y).getD i false = decide (i = x.val) := by
  simp only [PEqualNP.Represents.oneEach, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [hi])]
  rw [List.getElem?_ofFn]
  simp only [hi, ↓reduceDIte, Option.getD_some]
  exact decide_eq_decide.mpr Fin.ext_iff

lemma oneEach_getD_right {n : ℕ} (x y : Fin n) (j : ℕ) (hj : j < n) :
    (PEqualNP.Represents.oneEach x y).getD (n + j) false = decide (j = y.val) := by
  simp only [PEqualNP.Represents.oneEach, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem?_ofFn, hj, ↓reduceDIte,
    Option.getD_some]
  exact decide_eq_decide.mpr Fin.ext_iff

lemma upper_bound_exact (k a : ℕ) (ha : 6 ≤ a) (hk : 2 * 2 ^ a ≤ k)
    (f g : Fin (2 ^ k) → Bool) :
    ∃ C : Circuit,
      fan2 C.gates ∧
      16 * count2 C.gates ≤ 33 * 2 ^ k ∧
      ∀ x y : Fin (2 ^ k),
        C.eval (PEqualNP.Represents.oneEach x y) =
          xor (x.val.testBit (y.val % 2 ^ a)) (xor (f x) (g y)) := by
  let N := 2 ^ k
  let r := 2 ^ a
  have hr_pos : 0 < r := Nat.two_pow_pos a
  have hr64 : 64 ≤ r := by show 2 ^ 6 ≤ 2 ^ a; exact Nat.pow_le_pow_right (by omega) ha
  let rowGroups : List (List ℕ) :=
    List.ofFn (fun u : Fin (2 ^ r) =>
      ((List.finRange N).filter (fun x => rowTypeVal r x.val (f x) == u.val)).map (fun x => x.val))
  let rowBank := orBank (2 * N) rowGroups
  let colGroups : List (List ℕ) :=
    List.ofFn (fun idx : Fin (2 * r) =>
      ((List.finRange N).filter (fun y => (2 * (y.val % r) + if g y then 1 else 0) == idx.val)).map
        (fun y => N + y.val))
  let colBank := orBank (2 * N + rowBank.1.length) colGroups
  let base2 := 2 * N + rowBank.1.length + colBank.1.length
  let rowWires : Fin (2 ^ r) → ℕ := fun u => rowBank.2.getD u.val 0
  let encRes := encodeRows r base2 rowWires
  let base3 := base2 + encRes.1.length
  let selInputs : List (ℕ × ℕ × ℕ) :=
    List.ofFn (fun t : Fin r =>
      (encRes.2 t, colBank.2.getD (2 * t.val) 0, colBank.2.getD (2 * t.val + 1) 0))
  let selBank := selectBank base3 selInputs
  let base4 := base3 + selBank.1.length
  let finalOr := orList base4 selBank.2
  let allGates := rowBank.1 ++ colBank.1 ++ encRes.1 ++ selBank.1 ++ finalOr.1
  refine ⟨⟨allGates, finalOr.2⟩, ?_, ?_, ?_⟩
  · exact fan2_append (fan2_append (fan2_append (fan2_append
      (orBank_fan2 _ _) (orBank_fan2 _ _)) (encodeRows_fan2 _ _ _))
      (selectBank_fan2 _ _)) (orList_fan2 _ _)
  · simp only [allGates, count2_append]
    have hrc : count2 rowBank.1 ≤ N := by
      refine (orBank_count2 _ _).trans ?_
      have hpart := partition_sum_length (List.finRange N) (2 ^ r)
        (fun x => ⟨rowTypeVal r x.val (f x), rowTypeVal_lt r x.val (f x)⟩)
      have hmap : (rowGroups.map List.length) =
          (List.ofFn (fun u : Fin (2 ^ r) =>
            (List.finRange N).filter (fun x =>
              (⟨rowTypeVal r x.val (f x), rowTypeVal_lt r x.val (f x)⟩ : Fin (2 ^ r)) == u))).map List.length := by
        simp only [rowGroups, List.map_ofFn, Function.comp_def, List.length_map]
        rfl
      rw [hmap, hpart, List.length_finRange]
    have hcc : count2 colBank.1 ≤ N := by
      refine (orBank_count2 _ _).trans ?_
      have hcol_lt : ∀ y : Fin N, 2 * (y.val % r) + (if g y then 1 else 0) < 2 * r := by
        intro y; have := Nat.mod_lt y.val hr_pos; split_ifs <;> omega
      have hpart := partition_sum_length (List.finRange N) (2 * r)
        (fun y => ⟨2 * (y.val % r) + if g y then 1 else 0, hcol_lt y⟩)
      have hmap : (colGroups.map List.length) =
          (List.ofFn (fun idx : Fin (2 * r) =>
            (List.finRange N).filter (fun y =>
              (⟨2 * (y.val % r) + if g y then 1 else 0, hcol_lt y⟩ : Fin (2 * r)) == idx))).map List.length := by
        simp only [colGroups, List.map_ofFn, Function.comp_def, List.length_map]
        rfl
      rw [hmap, hpart, List.length_finRange]
    have henc : count2 encRes.1 + 2 ≤ 2 * 2 ^ r := encodeRows_count2 r base2 rowWires
    have hsel : count2 selBank.1 = 3 * r := by
      rw [selectBank_count2]; simp [selInputs]
    have hfin : count2 finalOr.1 ≤ r := by
      refine (orList_count2 _ _).trans ?_
      rw [selectBank_length]; simp [selInputs]
    have h64r : 64 * r ≤ 2 ^ r := by
      have h1 : r < 2 ^ (r - 6) := by
        have hlt : r - 6 < 2 ^ (r - 6) := Nat.lt_two_pow_self
        have hle : 2 ^ 6 ≤ 2 ^ (r - 6) := Nat.pow_le_pow_right (by omega) (by omega)
        have h2 : r ≤ 2 * (r - 6) := by omega
        have hpow : 2 ^ (r - 6) = 2 ^ 6 * 2 ^ (r - 12) := by rw [← pow_add]; congr 1; omega
        have h3 : r - 12 < 2 ^ (r - 12) := Nat.lt_two_pow_self
        have h4 : 1 ≤ 2 ^ (r - 12) := Nat.two_pow_pos _
        omega
      have h2 : 2 ^ r = 64 * 2 ^ (r - 6) := by
        show 2 ^ r = 2 ^ 6 * 2 ^ (r - 6)
        rw [← pow_add]; congr 1; omega
      omega
    have h2r_le_N : 2 ^ (r + 6) ≤ N := by
      show 2 ^ (r + 6) ≤ 2 ^ k
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hpow6 : 2 ^ (r + 6) = 64 * 2 ^ r := by
      rw [pow_add]; ring
    omega
  · intro x y
    change (runGates allGates (PEqualNP.Represents.oneEach x y)).getD finalOr.2 false = _
    let inp := PEqualNP.Represents.oneEach x y
    have hinp_len : inp.length = 2 * N := oneEach_length x y
    have hrow_in : ∀ ws ∈ rowGroups, ∀ w ∈ ws, w < 2 * N := by
      intro ws hws w hw
      rw [List.mem_ofFn] at hws; obtain ⟨u, rfl⟩ := hws
      rw [List.mem_map] at hw; obtain ⟨x', _, rfl⟩ := hw
      have := x'.isLt; omega
    have hcol_in : ∀ ws ∈ colGroups, ∀ w ∈ ws, w < 2 * N + rowBank.1.length := by
      intro ws hws w hw
      rw [List.mem_ofFn] at hws; obtain ⟨idx, rfl⟩ := hws
      rw [List.mem_map] at hw; obtain ⟨y', _, rfl⟩ := hw
      have := y'.isLt; omega
    let x1 := runGates rowBank.1 inp
    have hx1_len : x1.length = 2 * N + rowBank.1.length := by rw [runGates_length, hinp_len]
    let x2 := runGates colBank.1 x1
    have hx2_len : x2.length = base2 := by rw [runGates_length, hx1_len]
    let x3 := runGates encRes.1 x2
    have hx3_len : x3.length = base3 := by rw [runGates_length, hx2_len]
    let x4 := runGates selBank.1 x3
    have hx4_len : x4.length = base4 := by rw [runGates_length, hx3_len]
    have hrowW_lt : ∀ u : Fin (2 ^ r), rowWires u < 2 * N + rowBank.1.length := by
      intro u
      have hlen : rowBank.2.length = 2 ^ r := by rw [orBank_length]; simp [rowGroups]
      have hmem : rowWires u ∈ rowBank.2 := by
        simp only [rowWires, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : u.val < rowBank.2.length),
          Option.getD_some]
        exact List.getElem_mem _
      exact orBank_out_lt (2 * N) rowGroups hrow_in _ hmem
    have hcolW_lt : ∀ idx : Fin (2 * r), colBank.2.getD idx.val 0 < base2 := by
      intro idx
      have hlen : colBank.2.length = 2 * r := by rw [orBank_length]; simp [colGroups]
      have hmem : colBank.2.getD idx.val 0 ∈ colBank.2 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : idx.val < colBank.2.length),
          Option.getD_some]
        exact List.getElem_mem _
      exact orBank_out_lt (2 * N + rowBank.1.length) colGroups hcol_in _ hmem
    have hx1_row : ∀ u : Fin (2 ^ r), x1.getD (rowWires u) false =
        decide (u = ⟨rowTypeVal r x.val (f x), rowTypeVal_lt r x.val (f x)⟩) := by
      intro u
      have hev := orBank_eval inp rowGroups (by simpa [hinp_len] using hrow_in) u.val (by simp [rowGroups])
      simp only [rowBank, hinp_len] at hev ⊢
      change (runGates (orBank (2 * N) rowGroups).1 inp).getD (rowWires u) false = _
      rw [hev]
      have hgrp : rowGroups.getD u.val [] =
          ((List.finRange N).filter (fun x' => rowTypeVal r x'.val (f x') == u.val)).map (fun x' => x'.val) := by
        simp [rowGroups, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      rw [hgrp, Bool.eq_iff_iff]
      simp only [List.any_map, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and,
        Function.comp_def, beq_iff_eq, decide_eq_true_eq, Fin.ext_iff]
      constructor
      · rintro ⟨x', hx'u, hbit⟩
        rw [oneEach_getD_left x y x'.val x'.isLt, decide_eq_true_eq] at hbit
        have hx'eq : x' = x := Fin.ext hbit
        subst hx'eq; exact hx'u.symm
      · intro heq
        refine ⟨x, heq.symm, ?_⟩
        rw [oneEach_getD_left x y x.val x.isLt]; simp
    have hx2_row : ∀ u : Fin (2 ^ r), x2.getD (rowWires u) false =
        decide (u = ⟨rowTypeVal r x.val (f x), rowTypeVal_lt r x.val (f x)⟩) := by
      intro u
      rw [runGates_getD_init _ _ _ (by rw [hx1_len]; exact hrowW_lt u)]
      exact hx1_row u
    have hx2_col : ∀ idx : Fin (2 * r), x2.getD (colBank.2.getD idx.val 0) false =
        decide (2 * (y.val % r) + (if g y then 1 else 0) = idx.val) := by
      intro idx
      have hev := orBank_eval x1 colGroups (by simpa [hx1_len] using hcol_in) idx.val (by simp [colGroups])
      simp only [colBank, hx1_len] at hev ⊢
      rw [hev]
      have hgrp : colGroups.getD idx.val [] =
          ((List.finRange N).filter (fun y' => (2 * (y'.val % r) + if g y' then 1 else 0) == idx.val)).map
            (fun y' => N + y'.val) := by
        simp [colGroups, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      rw [hgrp, Bool.eq_iff_iff]
      simp only [List.any_map, List.any_eq_true, List.mem_filter, List.mem_finRange, true_and,
        Function.comp_def, beq_iff_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨y', hy'idx, hbit⟩
        rw [runGates_getD_init _ _ _ (by rw [hinp_len]; have := y'.isLt; omega),
          oneEach_getD_right x y y'.val y'.isLt, decide_eq_true_eq] at hbit
        have hy'eq : y' = y := Fin.ext hbit
        subst hy'eq; exact hy'idx
      · intro heq
        refine ⟨y, heq, ?_⟩
        rw [runGates_getD_init _ _ _ (by rw [hinp_len]; have := y.isLt; omega),
          oneEach_getD_right x y y.val y.isLt]; simp
    have hx3_bit : ∀ t : Fin r, x3.getD (encRes.2 t) false = xor (x.val.testBit t.val) (f x) := by
      intro t
      have hev := encodeRows_eval r x2 rowWires (fun u => by rw [hx2_len]; exact lt_of_lt_of_le (hrowW_lt u) (by omega))
        ⟨rowTypeVal r x.val (f x), rowTypeVal_lt r x.val (f x)⟩ hx2_row t
      simp only [encRes, hx2_len] at hev ⊢
      rw [hev, rowTypeVal_testBit r x.val (f x) t.val t.isLt]
    have hx3_col : ∀ idx : Fin (2 * r), x3.getD (colBank.2.getD idx.val 0) false =
        decide (2 * (y.val % r) + (if g y then 1 else 0) = idx.val) := by
      intro idx
      rw [runGates_getD_init _ _ _ (by rw [hx2_len]; exact hcolW_lt idx)]
      exact hx2_col idx
    have hsel_in : ∀ p ∈ selInputs, p.1 < x3.length ∧ p.2.1 < x3.length ∧ p.2.2 < x3.length := by
      intro p hp
      rw [List.mem_ofFn] at hp; obtain ⟨t, rfl⟩ := hp
      rw [hx3_len]
      refine ⟨encodeRows_out_lt r base2 rowWires (fun u => lt_of_lt_of_le (hrowW_lt u) (by omega)) t,
        lt_of_lt_of_le (hcolW_lt ⟨2 * t.val, by have := t.isLt; omega⟩) (by omega),
        lt_of_lt_of_le (hcolW_lt ⟨2 * t.val + 1, by have := t.isLt; omega⟩) (by omega)⟩
    have hx4_sel : ∀ t : Fin r, x4.getD (selBank.2.getD t.val 0) false =
        (decide (y.val % r = t.val) && xor (xor (x.val.testBit t.val) (f x)) (g y)) := by
      intro t
      have hev := selectBank_eval x3 selInputs hsel_in t.val (by simp [selInputs])
      simp only [selBank, hx3_len] at hev ⊢
      rw [hev]
      have hp : selInputs.getD t.val (0, 0, 0) =
          (encRes.2 t, colBank.2.getD (2 * t.val) 0, colBank.2.getD (2 * t.val + 1) 0) := by
        simp [selInputs, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      rw [hp]
      dsimp only
      rw [hx3_bit t,
        hx3_col ⟨2 * t.val, by have := t.isLt; omega⟩,
        hx3_col ⟨2 * t.val + 1, by have := t.isLt; omega⟩]
      by_cases hmod : y.val % r = t.val
      · rw [hmod, decide_eq_true rfl, Bool.true_and]
        cases g y <;> cases xor (x.val.testBit t.val) (f x) <;> simp
      · rw [decide_eq_false hmod, Bool.false_and]
        have h1 : ¬ (2 * (y.val % r) + (if g y then 1 else 0) = 2 * t.val) := by
          cases g y <;> simp <;> omega
        have h2 : ¬ (2 * (y.val % r) + (if g y then 1 else 0) = 2 * t.val + 1) := by
          cases g y <;> simp <;> omega
        simp [h1, h2]
    have hfinal : (runGates allGates inp).getD finalOr.2 false =
        selBank.2.any (fun w => x4.getD w false) := by
      simp only [allGates, runGates_append]
      change (runGates finalOr.1 x4).getD finalOr.2 false = _
      have hev := orList_eval x4 selBank.2 (fun w hw => by
        rw [hx4_len]; exact selectBank_out_lt base3 selInputs w hw)
      simpa only [finalOr, hx4_len] using hev
    rw [hfinal, Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨w, hwm, hwtrue⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hwm
      have hir : i < r := by rw [selectBank_length] at hi; simpa [selInputs] using hi
      have hget : selBank.2[i] = selBank.2.getD i 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rw [hget, hx4_sel ⟨i, hir⟩, Bool.and_eq_true, decide_eq_true_eq] at hwtrue
      rcases hwtrue with ⟨hmod, hval⟩
      rw [← hmod] at hval
      have hxor : ∀ a b c : Bool, xor (xor a b) c = xor a (xor b c) := by decide
      rw [hxor] at hval
      exact hval
    · intro hval
      let t : Fin r := ⟨y.val % r, Nat.mod_lt y.val hr_pos⟩
      have hlen : t.val < selBank.2.length := by rw [selectBank_length]; simp [selInputs]
      refine ⟨selBank.2.getD t.val 0, ?_, ?_⟩
      · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
        exact List.getElem_mem _
      · rw [hx4_sel t, decide_eq_true rfl, Bool.true_and]
        have hxor : ∀ a b c : Bool, xor (xor a b) c = xor a (xor b c) := by decide
        rw [hxor]
        exact hval

end UpperBound


section FinalAssembly

lemma lower_bound (k a d : ℕ) (ha : 6 ≤ a) (hak : 2 * 2 ^ a ≤ k) (hd : 5 ≤ d) (hdk : 2 * d + 1 ≤ k)
    (f g : Fin (2 ^ k) → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (hb : 16 * (C.gates.countP (fun gate => gate.inputs.length == 2)) ≤ 33 * 2 ^ k) :
    let N := 2 ^ k
    let m := k - d
    let h := 2 ^ m
    let r := 2 ^ a
    let G := fun (x y : Fin N) => if x.val < h ∨ y.val < h then tagNat m d x.val y.val
      else x.val.testBit (y.val % r)
    let loss := (Finset.univ.filter (fun z : Fin N × Fin N =>
      C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠
        xor (G z.1 z.2) (xor (f z.1) (g z.2)))).card
    h * N < 1024 * loss := by
  intro N m h r G loss
  let T : Fin N → Fin N → Bool := fun x y => xor (G x y) (xor (f x) (g y))
  let H : Fin N → Fin N → Bool := fun x y => C.eval (PEqualNP.Represents.oneEach x y)
  let b := C.gates.countP (fun gate => gate.inputs.length == 2)
  have hr64 : 64 ≤ r := by show 2 ^ 6 ≤ 2 ^ a; exact Nat.pow_le_pow_right (by omega) ha
  have hk128 : 128 ≤ k := by omega
  have hm65 : 65 ≤ m := by omega
  have hN_ge2 : 2 ≤ N := by
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    simpa [N] using this
  have hh_div16 : h = 16 * 2 ^ (m - 4) := by
    show 2 ^ m = 2 ^ 4 * 2 ^ (m - 4)
    rw [← pow_add]; congr 1; omega
  have hN_div16 : N = 16 * 2 ^ (k - 4) := by
    show 2 ^ k = 2 ^ 4 * 2 ^ (k - 4)
    rw [← pow_add]; congr 1; omega
  have hN_div64 : N = 64 * 2 ^ (k - 6) := by
    show 2 ^ k = 2 ^ 6 * 2 ^ (k - 6)
    rw [← pow_add]; congr 1; omega
  have hN_mul_h : N = 2 ^ d * h := by
    show 2 ^ k = 2 ^ d * 2 ^ m
    rw [← pow_add]; congr 1; omega
  have h2d32 : 32 ≤ 2 ^ d := by
    show 2 ^ 5 ≤ 2 ^ d
    exact Nat.pow_le_pow_right (by omega) hd
  have h32h : 32 * h ≤ N := by
    rw [hN_mul_h]
    exact Nat.mul_le_mul_right h h2d32
  have hh_ge128 : 128 ≤ h := by
    have : 2 ^ 7 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    simpa [h] using this
  let v := h / 16
  have hv_pos : 0 < v := by omega
  have h16v : 16 * v = h := by omega
  have hrow_dist : ∀ i j : Fin N, i ≠ j →
      17 + 2 * (v - 1) ≤ (Finset.univ.filter (fun z : Fin N => T i z ≠ T j z)).card := by
    intro i j hij
    have htarget := tagNat_diff_card k d hdk (by omega) i.val j.val i.isLt j.isLt
      (fun heq => hij (Fin.ext heq)) (!(xor (f i) (f j)))
    have hcard_le :
        ((Finset.range h).filter (fun y => xor (tagNat m d i.val y) (tagNat m d j.val y) = !(xor (f i) (f j)))).card ≤
        (Finset.univ.filter (fun z : Fin N => T i z ≠ T j z)).card := by
      have hhN : h ≤ N := by omega
      apply Finset.card_le_card_of_injOn (fun y => ⟨y % N, Nat.mod_lt y (by omega)⟩)
      · intro y hy
        rcases Finset.mem_filter.mp (Finset.mem_coe.mp hy) with ⟨hyR, hyP⟩
        have hylt : y < h := Finset.mem_range.mp hyR
        have hyN : y < N := lt_of_lt_of_le hylt hhN
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        have hval : y % N = y := Nat.mod_eq_of_lt hyN
        have hylt' : y % N < h := by rw [hval]; exact hylt
        change T i ⟨y % N, Nat.mod_lt y (by omega)⟩ ≠ T j ⟨y % N, Nat.mod_lt y (by omega)⟩
        simp only [T, G]
        rw [if_pos (Or.inr hylt'), if_pos (Or.inr hylt')]
        have ht1 : tagNat m d i.val (y % N) = tagNat m d i.val y := by rw [hval]
        have ht2 : tagNat m d j.val (y % N) = tagNat m d j.val y := by rw [hval]
        rw [ht1, ht2]
        have hbool : ∀ a b c d e : Bool, xor a b = !(xor c d) → xor a (xor c e) ≠ xor b (xor d e) := by decide
        exact hbool _ _ _ _ _ hyP
      · intro y1 hy1 y2 hy2 heq
        have h1 : y1 < N := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hy1)).1) hhN
        have h2 : y2 < N := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hy2)).1) hhN
        have hv' := congrArg Fin.val heq
        dsimp only at hv'
        rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv'
        exact hv'
    have hthresh : 17 + 2 * (v - 1) ≤ h / 4 := by omega
    exact hthresh.trans (htarget.trans hcard_le)
  have hcol_dist : ∀ i j : Fin N, i ≠ j →
      17 + 2 * (v - 1) ≤ (Finset.univ.filter (fun z : Fin N => T z i ≠ T z j)).card := by
    intro i j hij
    have htarget := tagNat_diff_card k d hdk (by omega) i.val j.val i.isLt j.isLt
      (fun heq => hij (Fin.ext heq)) (!(xor (g i) (g j)))
    have hcard_le :
        ((Finset.range h).filter (fun y => xor (tagNat m d i.val y) (tagNat m d j.val y) = !(xor (g i) (g j)))).card ≤
        (Finset.univ.filter (fun z : Fin N => T z i ≠ T z j)).card := by
      have hhN : h ≤ N := by omega
      apply Finset.card_le_card_of_injOn (fun y => ⟨y % N, Nat.mod_lt y (by omega)⟩)
      · intro y hy
        rcases Finset.mem_filter.mp (Finset.mem_coe.mp hy) with ⟨hyR, hyP⟩
        have hylt : y < h := Finset.mem_range.mp hyR
        have hyN : y < N := lt_of_lt_of_le hylt hhN
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
        have hval : y % N = y := Nat.mod_eq_of_lt hyN
        have hylt' : y % N < h := by rw [hval]; exact hylt
        change T ⟨y % N, Nat.mod_lt y (by omega)⟩ i ≠ T ⟨y % N, Nat.mod_lt y (by omega)⟩ j
        simp only [T, G]
        rw [if_pos (Or.inl hylt'), if_pos (Or.inl hylt')]
        have ht1 : tagNat m d (y % N) i.val = tagNat m d y i.val := by rw [hval]
        have ht2 : tagNat m d (y % N) j.val = tagNat m d y j.val := by rw [hval]
        rw [ht1, ht2, tagNat_comm m d y i.val, tagNat_comm m d y j.val]
        have hbool : ∀ a b c d e : Bool, xor a b = !(xor c d) → xor a (xor e c) ≠ xor b (xor e d) := by decide
        exact hbool _ _ _ _ _ hyP
      · intro y1 hy1 y2 hy2 heq
        have h1 : y1 < N := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hy1)).1) hhN
        have h2 : y2 < N := lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hy2)).1) hhN
        have hv' := congrArg Fin.val heq
        dsimp only at hv'
        rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv'
        exact hv'
    have hthresh : 17 + 2 * (v - 1) ≤ h / 4 := by omega
    exact hthresh.trans (htarget.trans hcard_le)
  obtain ⟨π, S, piece, hS_def, _, _, hconf⟩ :=
    PEqualNP.Outside.L_meta_25812_aux.Deficit.deficit_bound N hN_ge2 T C hfan v hv_pos hrow_dist hcol_dist
  by_contra hle_loss
  have hloss_le : 1024 * loss ≤ h * N := by omega
  have hq_le : loss / v ≤ N / 64 := by
    rw [Nat.div_le_iff_le_mul_add_pred hv_pos]
    have h1 : 64 * loss ≤ v * N := by
      have : 16 * (64 * loss) ≤ 16 * (v * N) := by
        calc 16 * (64 * loss) = 1024 * loss := by ring
          _ ≤ h * N := hloss_le
          _ = 16 * (v * N) := by rw [← h16v]; ring
      omega
    have h2 : 64 * (N / 64) = N := by omega
    nlinarith
  let U := S.filter (fun i => h ≤ i.val ∧ h ≤ (π i).val)
  have hS_le_U : S.card ≤ U.card + 2 * h := by
    let B1 := (Finset.univ : Finset (Fin N)).filter (fun i => i.val < h)
    let B2 := (Finset.univ : Finset (Fin N)).filter (fun i => (π i).val < h)
    have hB1 : B1.card ≤ h := by
      rw [← Finset.card_range h]
      apply Finset.card_le_card_of_injOn (fun i : Fin N => i.val)
      · intro i hi; exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2)
      · intro i _ j _ h; exact Fin.ext h
    have hB2 : B2.card ≤ h := by
      rw [← Finset.card_range h]
      apply Finset.card_le_card_of_injOn (fun i : Fin N => (π i).val)
      · intro i hi; exact Finset.mem_coe.mpr (Finset.mem_range.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).2)
      · intro i _ j _ h; exact π.injective (Fin.ext h)
    have hsub : S ⊆ U ∪ (B1 ∪ B2) := by
      intro i hi
      by_cases h1 : i.val < h
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩))
      · by_cases h2 : (π i).val < h
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩))
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, by omega, by omega⟩)
    have hcard := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    omega
  have hU_sub : U ⊆ S := Finset.filter_subset _ _
  have hconf_U := hconf U hU_sub
  have herr_U : ((U ×ˢ U).filter (fun z => T z.1 (π z.2) ≠ H z.1 (π z.2))).card ≤ loss := by
    apply Finset.card_le_card_of_injOn (fun z : Fin N × Fin N => (z.1, π z.2))
    · intro z hz
      have hne := (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).2
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm hne⟩)
    · intro z1 _ z2 _ heq
      dsimp only at heq
      rcases Prod.mk.inj heq with ⟨h1, h2⟩
      exact Prod.ext h1 (π.injective h2)
  let c : Fin N → Bool := fun i => xor (f i) (g (π i))
  have hconf_eq :
      ((U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))).card =
      ((U ×ˢ U).filter (fun z => z.1 < z.2 ∧
        xor (z.1.val.testBit ((π z.2).val % r)) (z.2.val.testBit ((π z.1).val % r)) ≠
          xor (c z.1) (c z.2))).card := by
    congr 1
    apply Finset.filter_congr
    intro z hz
    rcases Finset.mem_product.mp hz with ⟨h1, h2⟩
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    have hG1 : G z.1 (π z.2) = z.1.val.testBit ((π z.2).val % r) := by
      simp only [G]; rw [if_neg]; omega
    have hG2 : G z.2 (π z.1) = z.2.val.testBit ((π z.1).val % r) := by
      simp only [G]; rw [if_neg]; omega
    simp only [T, hG1, hG2, c]
    have hiff : ∀ a1 a2 b1 b2 d1 d2 : Bool,
        (xor a1 (xor b1 d2) ≠ xor a2 (xor b2 d1)) ↔ (xor a1 a2 ≠ xor (xor b1 d1) (xor b2 d2)) := by
      decide
    rw [hiff]
  have hlb := conflict_lower_bound k a ha (by omega) π U c
  have hU_quad : (U.card : ℤ) ^ 2 ≤ (3 * (N / 16 : ℤ) + 4) * (U.card : ℤ) + 4 * (loss : ℤ) := by
    have hN16 : (N : ℤ) = 16 * (N / 16 : ℤ) := by omega
    have hconf_le : (((U ×ˢ U).filter (fun z => z.1 < z.2 ∧
        xor (z.1.val.testBit ((π z.2).val % r)) (z.2.val.testBit ((π z.1).val % r)) ≠
          xor (c z.1) (c z.2))).card : ℤ) ≤ (U.card : ℤ) + (loss : ℤ) := by
      rw [← hconf_eq]
      have h1 : ((U ×ˢ U).filter (fun z => z.1 < z.2 ∧ T z.1 (π z.2) ≠ T z.2 (π z.1))).card ≤ U.card + loss :=
        hconf_U.trans (Nat.add_le_add_left herr_U _)
      exact_mod_cast h1
    change 16 * (U.card : ℤ) ^ 2 - 3 * (N : ℤ) * (U.card : ℤ) ≤
      64 * (((U ×ˢ U).filter (fun z => z.1 < z.2 ∧
        xor (z.1.val.testBit ((π z.2).val % r)) (z.2.val.testBit ((π z.1).val % r)) ≠
          xor (c z.1) (c z.2))).card : ℤ) at hlb
    have hlb2 : 16 * (U.card : ℤ) ^ 2 - 48 * (N / 16 : ℤ) * (U.card : ℤ) ≤
      64 * (((U ×ˢ U).filter (fun z => z.1 < z.2 ∧
        xor (z.1.val.testBit ((π z.2).val % r)) (z.2.val.testBit ((π z.1).val % r)) ≠
          xor (c z.1) (c z.2))).card : ℤ) := by
      have hmul : 3 * (N : ℤ) * (U.card : ℤ) = 48 * (N / 16 : ℤ) * (U.card : ℤ) := by
        calc 3 * (N : ℤ) * (U.card : ℤ) = 3 * (16 * (N / 16 : ℤ)) * (U.card : ℤ) := by rw [← hN16]
          _ = 48 * (N / 16 : ℤ) * (U.card : ℤ) := by ring
      linarith
    linarith
  have hloss4 : 4 * (loss : ℤ) < ((N / 16 : ℤ)) ^ 2 := by
    have h1 : 1024 * (loss : ℤ) ≤ (h : ℤ) * (N : ℤ) := by exact_mod_cast hloss_le
    have h2 : 32 * (h : ℤ) ≤ (N : ℤ) := by exact_mod_cast h32h
    have hN16 : (N : ℤ) = 16 * (N / 16 : ℤ) := by omega
    have hN_pos : (0 : ℤ) < (N / 16 : ℤ) := by omega
    have hN_nn : (0 : ℤ) ≤ (N : ℤ) := by omega
    have h3 : 32 * (1024 * (loss : ℤ)) ≤ (N : ℤ) * (N : ℤ) :=
      calc 32 * (1024 * (loss : ℤ)) ≤ 32 * ((h : ℤ) * (N : ℤ)) := by linarith
        _ = (32 * (h : ℤ)) * (N : ℤ) := by ring
        _ ≤ (N : ℤ) * (N : ℤ) := mul_le_mul_of_nonneg_right h2 hN_nn
    have hsq : (N : ℤ) * (N : ℤ) = 256 * ((N / 16 : ℤ)) ^ 2 :=
      calc (N : ℤ) * (N : ℤ) = (16 * (N / 16 : ℤ)) * (16 * (N / 16 : ℤ)) := by rw [← hN16]
        _ = 256 * ((N / 16 : ℤ)) ^ 2 := by ring
    have hpos_sq : (0 : ℤ) < ((N / 16 : ℤ)) ^ 2 := sq_pos_of_pos hN_pos
    linarith
  have hU_le : U.card ≤ 4 * (N / 16) + 4 := by
    by_contra hgt
    have hgt' : 4 * (N / 16 : ℤ) + 5 ≤ (U.card : ℤ) := by omega
    have hN_pos : (0 : ℤ) < (N / 16 : ℤ) := by omega
    have hmul : ((N / 16 : ℤ)) ^ 2 ≤ (U.card : ℤ) * ((U.card : ℤ) - (3 * (N / 16 : ℤ) + 4)) := by
      have h1 : (N / 16 : ℤ) ≤ (U.card : ℤ) := by omega
      have h2 : (N / 16 : ℤ) ≤ (U.card : ℤ) - (3 * (N / 16 : ℤ) + 4) := by omega
      calc ((N / 16 : ℤ)) ^ 2 = (N / 16 : ℤ) * (N / 16 : ℤ) := by ring
        _ ≤ (U.card : ℤ) * ((U.card : ℤ) - (3 * (N / 16 : ℤ) + 4)) :=
          mul_le_mul h1 h2 (le_of_lt hN_pos) (by omega)
    have hquad' : (U.card : ℤ) * ((U.card : ℤ) - (3 * (N / 16 : ℤ) + 4)) ≤ 4 * (loss : ℤ) := by
      linarith
    linarith
  have hN16_le : N / 16 ≤ 54 := by
    have h1 : 32 * N ≤ 15 * b + 50 + 44 * (loss / v) + S.card := by
      simpa only [H, b] using hS_def
    have h2 : 15 * b ≤ 495 * (N / 16) := by
      have : 16 * b ≤ 33 * N := hb
      omega
    have h3 : 44 * (loss / v) ≤ 11 * (N / 16) := by omega
    have h4 : 2 * h ≤ N / 16 := by omega
    omega
  have hN16_gt : 54 < N / 16 := by
    have h1 : 2 ^ 6 ≤ 2 ^ (k - 4) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  omega

lemma upper_bound (k a d : ℕ) (ha : 6 ≤ a) (hak : 2 * 2 ^ a ≤ k) (hdk : 2 * d + 1 ≤ k)
    (f g : Fin (2 ^ k) → Bool) :
    let N := 2 ^ k
    let m := k - d
    let h := 2 ^ m
    let r := 2 ^ a
    let G := fun (x y : Fin N) => if x.val < h ∨ y.val < h then tagNat m d x.val y.val
      else x.val.testBit (y.val % r)
    let fits := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) ∧
        16 * (C.gates.countP (fun gate => gate.inputs.length == 2)) ≤ 33 * N
    let loss := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
      (Finset.univ.filter (fun z : Fin N × Fin N =>
        C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠
          xor (G z.1 z.2) (xor (f z.1) (g z.2)))).card
    ∃ C, fits C ∧ loss C + (N - h) ^ 2 ≤ N ^ 2 := by
  intro N m h r G fits loss
  obtain ⟨C, hfan, hb, heval⟩ := upper_bound_exact k a ha hak f g
  refine ⟨C, ⟨hfan, hb⟩, ?_⟩
  let good := (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => h ≤ z.1.val ∧ h ≤ z.2.val)
  let bad := (Finset.univ : Finset (Fin N × Fin N)).filter (fun z =>
    C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠ xor (G z.1 z.2) (xor (f z.1) (g z.2)))
  have hdisj : Disjoint bad good := by
    rw [Finset.disjoint_left]
    intro z hzb hzg
    have hne := (Finset.mem_filter.mp hzb).2
    have ⟨h1, h2⟩ := (Finset.mem_filter.mp hzg).2
    apply hne
    rw [heval z.1 z.2]
    have hG : G z.1 z.2 = z.1.val.testBit (z.2.val % r) := by
      simp only [G]; rw [if_neg]; omega
    rw [hG]
  have hgood_card : good.card = (N - h) ^ 2 := by
    have hhN : h ≤ N := Nat.pow_le_pow_right (by omega) (by omega)
    let S := (Finset.univ : Finset (Fin N)).filter (fun x => h ≤ x.val)
    have hS_card : S.card = N - h := by
      have hcompl : S.card + ((Finset.univ : Finset (Fin N)).filter (fun x => x.val < h)).card = N := by
        have h1 : S ∪ (Finset.univ.filter (fun x : Fin N => x.val < h)) = Finset.univ := by
          ext x; simp [S]; omega
        have h2 : Disjoint S (Finset.univ.filter (fun x : Fin N => x.val < h)) := by
          rw [Finset.disjoint_left]; intro x hx1 hx2
          have := (Finset.mem_filter.mp hx1).2
          have := (Finset.mem_filter.mp hx2).2
          omega
        have := Finset.card_union_of_disjoint h2
        rw [h1, Finset.card_univ, Fintype.card_fin] at this
        omega
      have hlt_card : ((Finset.univ : Finset (Fin N)).filter (fun x => x.val < h)).card = h := by
        calc ((Finset.univ : Finset (Fin N)).filter (fun x => x.val < h)).card
            = (Finset.range h).card := by
              apply Finset.card_bij (fun x _ => x.val)
              · intro x hx; exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
              · intro x1 _ x2 _ heq; exact Fin.ext heq
              · intro y hy
                have hylt := Finset.mem_range.mp hy
                exact ⟨⟨y, lt_of_lt_of_le hylt hhN⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hylt⟩, rfl⟩
          _ = h := Finset.card_range h
      omega
    have hprod : good = S ×ˢ S := by
      ext ⟨x, y⟩; simp [good, S]
    rw [hprod, Finset.card_product, hS_card, sq]
  have hunion : (bad ∪ good).card ≤ N ^ 2 := by
    calc (bad ∪ good).card ≤ (Finset.univ : Finset (Fin N × Fin N)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = N ^ 2 := by simp [sq]
  rw [Finset.card_union_of_disjoint hdisj, hgood_card] at hunion
  exact hunion

end FinalAssembly

end PEqualNP.Outside.L_meta_25812

theorem PEqualNP.Outside.L_meta_25812 :
∀ k a d : ℕ, (6 ≤ a ∧ 2*2^a ≤ k ∧ 5 ≤ d ∧ 2*d+1 ≤ k) →
  let N := 2^k
  let m := k-d
  let h := 2^m
  let low := fun (i j : Fin N) =>
    ((Finset.range m).filter (fun l => i.val.testBit l && j.val.testBit l)).card
  let cross := fun (i j : Fin N) => ((Finset.range d).filter (fun l =>
    i.val.testBit (m+l) && j.val.testBit 0 && j.val.testBit (l+1))).card
  let tag := fun (left right : Fin N) => (low left right + cross left right + cross right left)%2 == 1
  let r := 2^a
  let G := fun (x y : Fin N) => if x.val < h ∨ y.val < h then tag x y
    else x.val.testBit (y.val % r)
  ∀ f g : Fin N → Bool,
    let fits := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) ∧
        16*(C.gates.countP (fun gate => gate.inputs.length == 2)) ≤ 33*N
    let loss := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
      (Finset.univ.filter (fun z : Fin N × Fin N =>
        C.eval (PEqualNP.Represents.oneEach z.1 z.2) ≠
          xor (G z.1 z.2) (xor (f z.1) (g z.2)))).card
    (∀ C, fits C → h*N < 1024*loss C) ∧
      ∃ C, fits C ∧ loss C + (N-h)^2 ≤ N^2 := by
  intro k a d ⟨ha, hak, hd, hdk⟩ N m h low cross tag r G f g fits loss
  constructor
  · intro C hC
    exact PEqualNP.Outside.L_meta_25812.lower_bound k a d ha hak hd hdk f g C hC.1 hC.2
  · exact PEqualNP.Outside.L_meta_25812.upper_bound k a d ha hak hdk f g
