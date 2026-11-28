import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_985_aux

private abbrev F := ZMod 2

private def col {α : Type*} [DecidableEq α] (e : Finset α) : α → F :=
  fun i => if i ∈ e then 1 else 0

private noncomputable def W {α : Type*} [DecidableEq α] (S : Finset (Finset α)) : Submodule F (α → F) := by
  classical
  exact Submodule.span F (↑(S.image col) : Set (α → F))

private noncomputable def pair {α : Type*} (x y : α) : α → F := by
  classical
  exact fun j => (if j = x then 1 else 0) + (if j = y then 1 else 0)

private lemma double (a : F) : a + a = 0 := by
  rw [← two_mul]
  exact zero_mul _

private lemma pair_self {α : Type*} (x : α) : pair x x = 0 := by
  ext j
  exact double _

private lemma pair_comm {α : Type*} (x y : α) : pair x y = pair y x := by
  ext j
  exact add_comm _ _

private lemma pair_add {α : Type*} (x y z : α) : pair x y + pair y z = pair x z := by
  classical
  ext j
  simp only [Pi.add_apply, pair]
  let a : F := if j = x then 1 else 0
  let b : F := if j = y then 1 else 0
  let c : F := if j = z then 1 else 0
  change (a + b) + (b + c) = a + c
  calc
    _ = a + (b + b) + c := by ac_rfl
    _ = _ := by rw [double, add_zero]

private lemma pair_col {α : Type*} [DecidableEq α] {x y : α} (h : x ≠ y) :
    pair x y = col {x,y} := by
  classical
  ext j
  by_cases hx : j = x <;> by_cases hy : j = y <;> simp_all [pair, col]

private lemma col_mem {α : Type*} [DecidableEq α] {S : Finset (Finset α)} {e : Finset α} (he : e ∈ S) :
    col e ∈ W S := by
  classical
  apply Submodule.subset_span
  exact Finset.mem_image.mpr ⟨e, he, rfl⟩

private lemma rank_edges {α : Type*} [DecidableEq α] (S : Finset (Finset α)) :
    Module.finrank F (W S) ≤ S.card := by
  classical
  exact (finrank_span_finset_le_card (S.image col)).trans Finset.card_image_le

private lemma rank_colors {α β : Type*} [Nonempty α] [DecidableEq α] [DecidableEq β]
    (S : Finset (Finset α)) (U : Finset α) (f : α → β)
    (hE : ∀ e ∈ S, ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ e = {x,y} ∧ f x = f y)
    (hP : ∀ x ∈ U, ∀ y ∈ U, f x = f y → pair x y ∈ W S) :
    Module.finrank F (W S) + (U.image f).card = U.card := by
  classical
  let C := U.image f
  let r : β → α := fun c => if h : c ∈ C then Classical.choose (Finset.mem_image.mp h)
    else Classical.choice ‹Nonempty α›
  have hr {c} (hc : c ∈ C) : r c ∈ U ∧ f (r c) = c := by
    simpa only [r, dite_eq_left hc] using Classical.choose_spec (Finset.mem_image.mp hc)
  have hf {x} (hx : x ∈ U) : f x ∈ C := Finset.mem_image_of_mem f hx
  let B := C.image r
  have hBU : B ⊆ U := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    exact (hr hc).1
  have hBC : B.card = C.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb h
    rw [← (hr ha).2, ← (hr hb).2, h]
  let I := U \ B
  let v : I → α → F := fun i => pair i.val (r (f i.val))
  have hbase {x} (hx : x ∈ U) : pair x (r (f x)) ∈ Submodule.span F (Set.range v) := by
    by_cases h : x ∈ B
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
      rw [(hr hc).2, pair_self]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨x, Finset.mem_sdiff.mpr ⟨hx, h⟩⟩, rfl⟩
  have hs : Submodule.span F (Set.range v) = W S := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hi := (Finset.mem_sdiff.mp i.property).1
      exact hP i hi _ (hr (hf hi)).1 (hr (hf hi)).2.symm
    · apply Submodule.span_le.mpr
      intro a ha
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨x,hx,y,hy,hne,rfl,hxy⟩ := hE e he
      rw [← pair_col hne, ← pair_add x (r (f x)) y]
      exact Submodule.add_mem _ (hbase hx) (by rw [pair_comm, hxy]; exact hbase hy)
  have hli : LinearIndependent F v := by
    rw [linearIndependent_iff']
    intro s g hsum j hj
    have h := congrFun hsum j.val
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have hroot (i : I) : j.val ≠ r (f i.val) := by
      intro heq
      exact (Finset.mem_sdiff.mp j.property).2 (heq ▸ Finset.mem_image_of_mem r
        (hf (Finset.mem_sdiff.mp i.property).1))
    have hv (i : I) : v i j.val = if i = j then 1 else 0 := by
      by_cases hij : i = j
      · subst i
        simp [v, pair, hroot]
      · have hh : j.val ≠ i.val := fun e => hij (Subtype.ext e.symm)
        simp [v, pair, hroot, hh, hij]
    simpa [hv, Finset.sum_ite_eq', hj] using h
  rw [← hs, finrank_span_eq_card hli, Fintype.card_coe, ← hBC]
  exact Finset.card_sdiff_add_card_eq_card hBU


private noncomputable def parts {α : Type*} [DecidableEq α] (S : Finset (Finset α)) : Setoid α where
  r x y := pair x y ∈ W S
  iseqv := ⟨fun x => pair_self x ▸ Submodule.zero_mem _, fun h => pair_comm .. ▸ h,
    fun {x y z} hx hy => pair_add x y z ▸ Submodule.add_mem _ hx hy⟩

private lemma componentData {α : Type} [Nonempty α] [DecidableEq α]
    (S : Finset (Finset α)) (hS : ∀ e ∈ S, e.card = 2) :
    ∃ (β : Type) (inst : Fintype β) (a : β → Nat), letI := inst; (∀ i, 0 < a i) ∧
      Module.finrank F (W S) = ∑ i, a i ∧
      (S.biUnion id).card = ∑ i, (a i + 1) ∧
      S.card ≤ ∑ i, (a i + 1).choose 2 := by
  classical
  let U := S.biUnion id
  let f : α → Quotient (parts S) := Quotient.mk _
  let C := U.image f
  let B (c : Quotient (parts S)) := U.filter (fun x => f x = c)
  have hE : ∀ e ∈ S, ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ e = {x,y} ∧ f x = f y := by
    intro e he
    obtain ⟨x,y,hne,rfl⟩ := Finset.card_eq_two.mp (hS e he)
    exact ⟨x, Finset.mem_biUnion.mpr ⟨_, he, by simp⟩, y,
      Finset.mem_biUnion.mpr ⟨_, he, by simp⟩, hne, rfl,
      Quotient.sound (show pair x y ∈ W S by rw [pair_col hne]; exact col_mem he)⟩
  have hB (c : C) : 2 ≤ (B c.val).card := by
    obtain ⟨x,hx,hxc⟩ := Finset.mem_image.mp c.property
    obtain ⟨e,he,hxe⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨u,hu,v,hv,hn,rfl,huv⟩ := hE e he
    have huc : f u = c.val := by
      simp only [id, Finset.mem_insert, Finset.mem_singleton] at hxe
      rcases hxe with rfl | rfl
      · exact hxc
      · exact huv.trans hxc
    have hh : ({u,v} : Finset α) ⊆ B c.val := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hu, huc⟩
      · exact Finset.mem_filter.mpr ⟨hv, huv.symm.trans huc⟩
    simpa [hn] using Finset.card_le_card hh
  let a (c : C) := (B c.val).card - 1
  have ha (c : C) : a c + 1 = (B c.val).card := by
    have := hB c
    dsimp [a]
    omega
  have hV : U.card = ∑ c : C, (a c + 1) := by
    simp_rw [ha]
    rw [Finset.sum_coe_sort (f := fun c => (B c).card)]
    exact Finset.card_eq_sum_card_image f U
  have hR := rank_colors S U f hE (fun _ _ _ _ he => Quotient.exact he)
  have hC : (∑ _c : C, (1 : Nat)) = C.card := by simp
  change Module.finrank F (W S) + C.card = U.card at hR
  have hEdge : S ⊆ C.biUnion (fun c => (B c).powersetCard 2) := by
    intro e he
    obtain ⟨x,hx,y,hy,_,rfl,hxy⟩ := hE e he
    refine Finset.mem_biUnion.mpr ⟨f x, Finset.mem_image_of_mem f hx, ?_⟩
    refine Finset.mem_powersetCard.mpr ⟨?_, hS _ he⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hx, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hy, hxy.symm⟩
  refine ⟨C, inferInstance, a, fun c => ?_, ?_, hV, ?_⟩
  · have := ha c
    have := hB c
    omega
  · rw [Finset.sum_add_distrib, hC] at hV
    omega
  · simp_rw [ha]
    rw [Finset.sum_coe_sort (f := fun c => (B c).card.choose 2)]
    simpa only [Finset.card_powersetCard] using
      (Finset.card_le_card hEdge).trans Finset.card_biUnion_le
private theorem l985_arithmetic {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (ha : ∀ i, 0 < a i) {t δ E : ℕ}
    (ht : 3 ≤ t) (hδ : δ < t - 2)
    (hE : E ≤ ∑ i, (a i + 1).choose 2) (hRE : (∑ i, a i) ≤ E) :
    let R := ∑ i, a i
    let V := ∑ i, (a i + 1)
    (R ≤ t - 1 ∧ (t - 1).choose 2 ≤ E - R + δ) ↔
      (V = t ∧ t.choose 2 ≤ E + δ) := by
  classical
  intro R V
  change R ≤ E at hRE
  have hstep (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
    rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right, Nat.add_comm n]
  have hmerge (x y : ℕ) (hx : 0 < x) :
      x.choose 2 + (y + 1).choose 2 ≤ (x + y).choose 2 := by
    induction y with
    | zero => simp
    | succ y ih =>
      change x.choose 2 + (y + 1 + 1).choose 2 ≤ (x + y + 1).choose 2
      rw [hstep (y + 1), hstep (x + y)]
      omega
  -- With a nonempty tail, merging the head costs at least one unit in the argument of choose.
  have hbounds (b : ι → ℕ) (hb : ∀ i, 0 < b i) (s : Finset ι) :
      (∑ i ∈ s, (b i).choose 2) ≤ (∑ i ∈ s, b i).choose 2 ∧
        (2 ≤ s.card → (∑ i ∈ s, (b i).choose 2) ≤ ((∑ i ∈ s, b i) - 1).choose 2) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
      by_cases hs : s = ∅
      · subst s
        simp
      · obtain ⟨j, hj⟩ := Finset.nonempty_of_ne_empty hs
        let B := ∑ k ∈ s, b k
        have hjB : b j ≤ B := Finset.single_le_sum (fun k _ => Nat.zero_le (b k)) hj
        have hB : 1 ≤ B := by have := hb j; omega
        have hm := hmerge (b i) (B - 1) (hb i)
        rw [Nat.sub_add_cancel hB, show b i + (B - 1) = b i + B - 1 by omega] at hm
        have hstrong := (Nat.add_le_add_left ih.1 ((b i).choose 2)).trans hm
        exact ⟨hstrong.trans (Nat.choose_mono 2 (Nat.sub_le _ _)), fun _ => hstrong⟩
  have hcap : E ≤ (∑ i, (a i).choose 2) + R := by
    simpa only [hstep, Finset.sum_add_distrib] using hE
  have hV : V = R + Fintype.card ι := by
    simp [V, R, Finset.sum_add_distrib]
  have hmany (hv : 0 < V) (hc : Fintype.card ι ≠ 1) : 2 ≤ (Finset.univ : Finset ι).card := by
    have hnz : Fintype.card ι ≠ 0 := by
      intro hz
      have hs : (Finset.univ : Finset ι) = ∅ := Finset.card_eq_zero.mp (by simpa using hz)
      change 0 < ∑ i ∈ (Finset.univ : Finset ι), (a i + 1) at hv
      simp [hs] at hv
    simpa using (show 2 ≤ Fintype.card ι by omega)
  have htop : t.choose 2 = (t - 1).choose 2 + (t - 1) := by
    simpa only [show t - 1 + 1 = t by omega] using hstep (t - 1)
  have hgap (x : ℕ) (hx : x ≤ t - 2) : ¬ (t - 1).choose 2 ≤ x.choose 2 + δ := by
    have hm : x.choose 2 ≤ (t - 2).choose 2 := Nat.choose_mono 2 hx
    have he : (t - 1).choose 2 = (t - 2).choose 2 + (t - 2) := by
      simpa only [show t - 2 + 1 = t - 1 by omega] using hstep (t - 2)
    omega
  constructor
  · rintro ⟨hr, he⟩
    have hs : (t - 1).choose 2 ≤ (∑ i, (a i).choose 2) + δ := by omega
    have hb : (∑ i, (a i).choose 2) ≤ R.choose 2 := (hbounds a ha Finset.univ).1
    have hr' : R = t - 1 := by
      by_contra hne
      exact hgap R (by omega) (by omega)
    have hc : Fintype.card ι = 1 := by
      by_contra hne
      have hs' : (∑ i, (a i).choose 2) ≤ (R - 1).choose 2 :=
        (hbounds a ha Finset.univ).2 (hmany (by omega) hne)
      exact hgap (R - 1) (by omega) (by omega)
    exact ⟨by omega, by omega⟩
  · rintro ⟨hv, he⟩
    have hc : Fintype.card ι = 1 := by
      by_contra hne
      have hs : E ≤ (V - 1).choose 2 :=
        hE.trans ((hbounds (fun i => a i + 1) (by intro i; omega) Finset.univ).2
          (hmany (by omega) hne))
      rw [hv] at hs
      omega
    exact ⟨by omega, by omega⟩

private theorem sharpnessWitness (t : ℕ) (ht : 3 ≤ t) :
    ∃ (S : Finset (Finset (Fin (t + 1)))) (color : Fin (t + 1) → Bool),
      (∀ e ∈ S, e.card = 2) ∧
      S.card = (t - 1).choose 2 + 1 ∧
      S.biUnion id = Finset.univ ∧
      Function.Surjective color ∧
      (∀ e ∈ S, ∀ x ∈ e, ∀ y ∈ e, color x = color y) ∧
      (∀ x y, x ≠ y → color x = color y → ({x, y} : Finset (Fin (t + 1))) ∈ S) := by
  let emb : Fin (t - 1) ↪ Fin (t + 1) := Fin.castLEEmb (by omega)
  let A : Finset (Fin (t + 1)) := Finset.univ.map emb
  let u : Fin (t + 1) := ⟨t - 1, by omega⟩
  let v : Fin (t + 1) := ⟨t, by omega⟩
  let B : Finset (Fin (t + 1)) := {u, v}
  let S : Finset (Finset (Fin (t + 1))) := insert B (A.powersetCard 2)
  let color (x : Fin (t + 1)) : Bool := if x ∈ A then false else true
  have hAcard : A.card = t - 1 := by
    rw [show A = Finset.univ.map emb from rfl, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  have hA (x : Fin (t + 1)) : x ∈ A ↔ x.val < t - 1 := by
    change x ∈ Finset.univ.map emb ↔ _
    rw [Finset.mem_map]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.isLt
    · intro hx
      exact ⟨⟨x.val, hx⟩, Finset.mem_univ _, Fin.ext rfl⟩
  have hB (x : Fin (t + 1)) : x ∈ B ↔ x ∉ A := by
    rw [hA x]
    change x ∈ ({u, v} : Finset (Fin (t + 1))) ↔ _
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    change (x.val = t - 1 ∨ x.val = t) ↔ ¬ x.val < t - 1
    have hx := x.isLt
    omega
  have hu : u ∉ A := (hB u).1 (by simp [B])
  have huv : u ≠ v := by
    intro h
    have hval : t - 1 = t := congrArg Fin.val h
    omega
  have hBcard : B.card = 2 := Finset.card_pair_eq_two_iff.2 huv
  have hBnot : B ∉ A.powersetCard 2 := by
    intro h
    exact hu ((Finset.mem_powersetCard.1 h).1 (show u ∈ B by simp [B]))
  have hpair {x y : Fin (t + 1)} {D : Finset (Fin (t + 1))}
      (hx : x ∈ D) (hy : y ∈ D) : ({x, y} : Finset (Fin (t + 1))) ⊆ D := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hx hy
  refine ⟨S, color, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.1 he with rfl | he
    · exact hBcard
    · exact (Finset.mem_powersetCard.1 he).2
  · change (insert B (A.powersetCard 2)).card = _
    rw [Finset.card_insert_of_notMem hBnot, Finset.card_powersetCard, hAcard]
  · change (insert B (A.powersetCard 2)).biUnion id = _
    have hAtwo : 2 ≤ A.card := by rw [hAcard]; omega
    rw [Finset.biUnion_insert, Finset.powersetCard_biUnion (by decide : (2 : ℕ) ≠ 0) hAtwo]
    apply Finset.eq_univ_of_forall
    intro x
    change x ∈ B ∪ A
    by_cases hx : x ∈ A
    · exact Finset.mem_union_right _ hx
    · exact Finset.mem_union_left _ ((hB x).2 hx)
  · intro b
    cases b
    · let z : Fin (t + 1) := ⟨0, by omega⟩
      have hz : z ∈ A := (hA z).2 (by change 0 < t - 1; omega)
      exact ⟨z, by simp [color, hz]⟩
    · exact ⟨u, by simp [color, hu]⟩
  · intro e he x hx y hy
    rcases Finset.mem_insert.1 he with rfl | he
    · simp [color, (hB x).1 hx, (hB y).1 hy]
    · have heA := (Finset.mem_powersetCard.1 he).1
      simp [color, heA hx, heA hy]
  · intro x y hxy hcolor
    have hcard : ({x, y} : Finset (Fin (t + 1))).card = 2 :=
      Finset.card_pair_eq_two_iff.2 hxy
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A
    · exact Finset.mem_insert_of_mem (Finset.mem_powersetCard.2 ⟨hpair hx hy, hcard⟩)
    · simp [color, hx, hy] at hcolor
    · simp [color, hx, hy] at hcolor
    · have hEq : ({x, y} : Finset (Fin (t + 1))) = B :=
        Finset.eq_of_subset_of_card_le (hpair ((hB x).2 hx) ((hB y).2 hy)) (by
          rw [hBcard, hcard])
      exact Finset.mem_insert.2 (Or.inl hEq)

private lemma core (t : Nat) (ht : 3 ≤ t) :
  (∀ (n δ : Nat) (S : Finset (Finset (Fin n))), δ < t-2 → (∀ e ∈ S, e.card = 2) →
    ((Module.finrank F (W S) ≤ t-1 ∧ (t-1).choose 2 ≤ S.card - Module.finrank F (W S) + δ) ↔
      ((S.biUnion id).card = t ∧ t.choose 2 ≤ S.card + δ))) ∧
  ∃ S : Finset (Finset (Fin (t+1))), (∀ e ∈ S, e.card = 2) ∧
    Module.finrank F (W S) = t-1 ∧ S.card - Module.finrank F (W S) + (t-2) = (t-1).choose 2 ∧
    (S.biUnion id).card = t+1 := by
  classical
  constructor
  · intro n δ S hδ hS
    cases n with
    | zero =>
      have hEmpty : S = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro e he
        obtain ⟨x, _, _, _⟩ := Finset.card_eq_two.mp (hS e he)
        exact Fin.elim0 x
      subst S
      have hchoose : t-2 ≤ (t-1).choose 2 := by
        rw [show t-1 = (t-2)+1 by omega, Nat.choose_succ_succ', Nat.choose_one_right]
        omega
      simp only [Finset.card_empty, Nat.zero_sub, Nat.zero_add, Finset.biUnion_empty]
      omega
    | succ n =>
      obtain ⟨β, inst, a, ha, hR, hV, hE⟩ := componentData S hS
      let _ := inst
      rw [hR, hV]
      exact l985_arithmetic a ha ht hδ hE (hR ▸ rank_edges S)
  · obtain ⟨S, f, hS, hE, hU, hsurj, hcolor, hcomplete⟩ := sharpnessWitness t ht
    have hR := rank_colors S Finset.univ f (by
      intro e he
      obtain ⟨x,y,hne,rfl⟩ := Finset.card_eq_two.mp (hS e he)
      exact ⟨x, Finset.mem_univ _, y, Finset.mem_univ _, hne, rfl,
        hcolor _ he _ (by simp) _ (by simp)⟩) (by
      intro x _ y _ hxy
      by_cases h : x = y
      · subst y
        rw [pair_self]
        exact Submodule.zero_mem _
      · rw [pair_col h]
        exact col_mem (hcomplete x y h hxy))
    rw [Finset.image_univ_of_surjective hsurj] at hR
    simp only [Finset.card_univ, Fintype.card_bool, Fintype.card_fin] at hR
    have hRank : Module.finrank F (W S) = t-1 := by omega
    have hRE := rank_edges S
    refine ⟨S, hS, hRank, ?_, by simp [hU]⟩
    omega

end PEqualNP.Outside.L_lib_985_aux

theorem PEqualNP.Outside.L_lib_985 :
  let F := ZMod 2
  let rank := fun (n : Nat) (S : Finset (Finset (Fin n))) =>
    let col := fun (e : Finset (Fin n)) (i : Fin n) => if i ∈ e then (1 : F) else 0
    Module.finrank F (Submodule.span F ((S.image col : Finset (Fin n → F)) : Set (Fin n → F)))
  ∀ (t : Nat), 3 ≤ t →
    (∀ (n δ : Nat) (S : Finset (Finset (Fin n))), δ < t-2 → (∀ e ∈ S, e.card = 2) →
      ((rank n S ≤ t-1 ∧ (t-1).choose 2 ≤ S.card - rank n S + δ) ↔
        ((S.biUnion id).card = t ∧ t.choose 2 ≤ S.card + δ))) ∧
    ∃ S : Finset (Finset (Fin (t+1))), (∀ e ∈ S, e.card = 2) ∧
      rank (t+1) S = t-1 ∧ S.card - rank (t+1) S + (t-2) = (t-1).choose 2 ∧
      (S.biUnion id).card = t+1 := by
  intro F rank t ht
  have hc := PEqualNP.Outside.L_lib_985_aux.core t ht
  have hr (n : Nat) (S : Finset (Finset (Fin n))) :
      rank n S = Module.finrank F (PEqualNP.Outside.L_lib_985_aux.W S) := by
    apply congrArg (fun V : Submodule F (Fin n → F) => Module.finrank F V)
    unfold PEqualNP.Outside.L_lib_985_aux.W
    simp only [Finset.coe_image] <;> rfl
  simpa only [hr] using hc
