import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25796_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

lemma list_sum_count {α : Type*} [DecidableEq α] (l : List α) (S : Finset α)
    (hS : ∀ a ∈ l, a ∈ S) :
    ∑ a ∈ S, l.count a = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∈ S := hS x (by simp)
    have hxs : ∀ a ∈ xs, a ∈ S := fun a ha => hS a (by simp [ha])
    simp only [List.count_cons, List.length_cons, beq_iff_eq]
    have hsum : (∑ a ∈ S, (xs.count a + if x = a then 1 else 0)) =
        (∑ a ∈ S, xs.count a) + ∑ a ∈ S, (if x = a then 1 else 0) := Finset.sum_add_distrib
    rw [hsum, ih hxs]
    have h1 : (∑ a ∈ S, if x = a then 1 else 0) = 1 := by
      rw [Finset.sum_ite_eq]; simp [hx]
    omega

lemma list_sum_count_eq_countP {α : Type*} [DecidableEq α] (l : List α) (S : Finset α) :
    ∑ a ∈ S, l.count a = l.countP (fun a => decide (a ∈ S)) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, List.countP_cons, beq_iff_eq]
    rw [Finset.sum_add_distrib, ih]
    by_cases hx : x ∈ S
    · have h1 : (∑ a ∈ S, if x = a then 1 else 0) = 1 := by
        rw [Finset.sum_ite_eq]; simp [hx]
      simp [hx, h1]
    · have h1 : (∑ a ∈ S, if x = a then 1 else 0) = 0 := by
        rw [Finset.sum_ite_eq]; simp [hx]
      simp [hx, h1]

lemma readsIn_union {C : Circuit} {G₁ G₂ : Finset ℕ} (hdisj : Disjoint G₁ G₂) (w : ℕ) :
    readsIn C (G₁ ∪ G₂) w = readsIn C G₁ w + readsIn C G₂ w := by
  unfold readsIn
  exact Finset.sum_union hdisj

lemma readsIn_mono {C : Circuit} {G₁ G₂ : Finset ℕ} (hsub : G₁ ⊆ G₂) (w : ℕ) :
    readsIn C G₁ w ≤ readsIn C G₂ w := by
  unfold readsIn
  exact Finset.sum_le_sum_of_subset hsub

lemma readsIn_pos_iff {C : Circuit} {G : Finset ℕ} {w : ℕ} :
    0 < readsIn C G w ↔ ∃ k ∈ G, w ∈ (gateAt C k).inputs := by
  unfold readsIn
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  constructor
  · rintro ⟨k, hk, hpos⟩
    exact ⟨k, hk, List.count_pos_iff.mp hpos⟩
  · rintro ⟨k, hk, hmem⟩
    exact ⟨k, hk, List.count_pos_iff.mpr hmem⟩

lemma readsIn_zero_iff {C : Circuit} {G : Finset ℕ} {w : ℕ} :
    readsIn C G w = 0 ↔ ∀ k ∈ G, w ∉ (gateAt C k).inputs := by
  constructor
  · intro h0 k hk hmem
    have hpos : 0 < readsIn C G w := readsIn_pos_iff.mpr ⟨k, hk, hmem⟩
    omega
  · intro hall
    by_contra hne
    rcases readsIn_pos_iff.mp (Nat.pos_of_ne_zero hne) with ⟨k, hk, hmem⟩
    exact hall k hk hmem

lemma sum_readsIn_eq_sum_countP (C : Circuit) (G S : Finset ℕ) :
    ∑ w ∈ S, readsIn C G w = ∑ k ∈ G, (gateAt C k).inputs.countP (fun w => decide (w ∈ S)) := by
  unfold readsIn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact list_sum_count_eq_countP (gateAt C k).inputs S

lemma sum_readsIn_all {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (G : Finset ℕ)
    (hG : G ⊆ Finset.range C.size) :
    ∑ w ∈ Finset.range (n + C.size), readsIn C G w = ∑ k ∈ G, (gateAt C k).inputs.length := by
  unfold readsIn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply list_sum_count
  intro w hw
  have hk_lt : k < C.gates.length := Finset.mem_range.mp (hG hk)
  have hw_lt : w < n + k := hRB k hk_lt w hw
  exact Finset.mem_range.mpr (by change w < n + C.gates.length; omega)

def subWires (n : ℕ) (C : Circuit) (G W : Finset ℕ) (v : ℕ) : Finset ℕ :=
  if v ∈ W then
    if n ≤ v ∧ v - n ∈ G then
      insert v (((gateAt C (v - n)).inputs.toFinset.filter (· < v)).attach.biUnion
        (fun w => subWires n C G W w.1))
    else {v}
  else ∅
termination_by v
decreasing_by
  exact (Finset.mem_filter.mp w.2).2

lemma subWires_unfold (n : ℕ) (C : Circuit) (G W : Finset ℕ) (v : ℕ) :
    subWires n C G W v =
      if v ∈ W then
        if n ≤ v ∧ v - n ∈ G then
          insert v (((gateAt C (v - n)).inputs.toFinset.filter (· < v)).biUnion (fun w => subWires n C G W w))
        else {v}
      else ∅ := by
  conv_lhs => rw [subWires]
  split_ifs <;> try rfl
  congr 1; ext x; simp

lemma subWires_subset {n : ℕ} {C : Circuit} {G W : Finset ℕ} (v : ℕ) :
    subWires n C G W v ⊆ W ∧ ∀ x ∈ subWires n C G W v, x ≤ v := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    rw [subWires_unfold]
    by_cases hv : v ∈ W
    · simp only [hv, ite_true]
      by_cases hk : n ≤ v ∧ v - n ∈ G
      · simp only [hk.1, hk.2, and_self, ite_true]
        constructor
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hv
          · rcases Finset.mem_biUnion.mp hx' with ⟨w, hw, hxw⟩
            exact (ih w (Finset.mem_filter.mp hw).2).1 hxw
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact le_rfl
          · rcases Finset.mem_biUnion.mp hx' with ⟨w, hw, hxw⟩
            have hlt := (Finset.mem_filter.mp hw).2
            have hle := (ih w hlt).2 x hxw
            omega
      · simp only [hk, ite_false]
        exact ⟨Finset.singleton_subset_iff.mpr hv, fun x hx => by rw [Finset.mem_singleton.mp hx]⟩
    · simp only [hv, ite_false]
      exact ⟨Finset.empty_subset _, fun _ hx => by simp at hx⟩

lemma mem_subWires_self {n : ℕ} {C : Circuit} {G W : Finset ℕ} {v : ℕ} (hv : v ∈ W) :
    v ∈ subWires n C G W v := by
  rw [subWires_unfold]
  simp only [hv, ite_true]
  by_cases hk : n ≤ v ∧ v - n ∈ G
  · simp only [hk.1, hk.2, and_self, ite_true, Finset.mem_insert, true_or]
  · simp only [hk, ite_false, Finset.mem_singleton]

lemma subWires_eq_of_gate {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {G W : Finset ℕ}
    (hG : G ⊆ Finset.range C.size) {k : ℕ} (hk : k ∈ G) (hW : n + k ∈ W) :
    subWires n C G W (n + k) =
      insert (n + k) ((gateAt C k).inputs.toFinset.biUnion (fun w => subWires n C G W w)) := by
  rw [subWires_unfold]
  have h1 : n ≤ n + k := Nat.le_add_right n k
  simp only [hW, h1, Nat.add_sub_cancel_left, hk, and_self, ite_true]
  congr 1
  have hfilt : (gateAt C k).inputs.toFinset.filter (· < n + k) = (gateAt C k).inputs.toFinset := by
    apply Finset.filter_true_of_mem
    intro w hw
    exact hRB k (Finset.mem_range.mp (hG hk)) w (List.mem_toFinset.mp hw)
  rw [hfilt]

lemma subWires_eq_of_not_gate {n : ℕ} {C : Circuit} {G W : Finset ℕ} {v : ℕ}
    (hv : v ∈ W) (hng : ¬ (n ≤ v ∧ v - n ∈ G)) :
    subWires n C G W v = {v} := by
  rw [subWires_unfold]
  simp only [hv, hng, ite_true, ite_false]

lemma subWires_closed_down {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {G W : Finset ℕ}
    (hG : G ⊆ Finset.range C.size) {v : ℕ} :
    ∀ {k : ℕ}, k ∈ G → n + k ∈ subWires n C G W v →
      ∀ w ∈ (gateAt C k).inputs, w ∈ W → w ∈ subWires n C G W v := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro k hk hnk w hw hwW
    by_cases hv : v ∈ W
    · by_cases hkg : n ≤ v ∧ v - n ∈ G
      · have hv_eq : v = n + (v - n) := by omega
        have hsub : subWires n C G W v =
            insert v ((gateAt C (v - n)).inputs.toFinset.biUnion (fun u => subWires n C G W u)) := by
          conv_lhs => rw [hv_eq]
          rw [subWires_eq_of_gate hRB hG hkg.2 (hv_eq ▸ hv), ← hv_eq]
        rw [hsub] at hnk ⊢
        rcases Finset.mem_insert.mp hnk with heq | hmem
        · have hk_eq : k = v - n := by omega
          subst hk_eq
          refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨w, List.mem_toFinset.mpr hw, ?_⟩)
          exact mem_subWires_self hwW
        · rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, hnk_u⟩
          have hu_lt : u < v := by
            have h1 := hRB (v - n) (Finset.mem_range.mp (hG hkg.2)) u (List.mem_toFinset.mp hu)
            omega
          exact Finset.mem_insert_of_mem
            (Finset.mem_biUnion.mpr ⟨u, hu, ih u hu_lt hk hnk_u w hw hwW⟩)
      · rw [subWires_eq_of_not_gate hv hkg, Finset.mem_singleton] at hnk
        exfalso
        apply hkg
        rw [← hnk]
        exact ⟨Nat.le_add_right n k, by simpa using hk⟩
    · exfalso
      rw [subWires_unfold] at hnk
      simp [hv] at hnk

lemma mem_subWires_ne_has_parent {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {G W : Finset ℕ}
    (hG : G ⊆ Finset.range C.size) {v x : ℕ} (hx : x ∈ subWires n C G W v) (hne : x ≠ v) :
    ∃ k ∈ G, n + k ∈ subWires n C G W v ∧ x ∈ (gateAt C k).inputs := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    have hv : v ∈ W := by
      by_contra hnv
      rw [subWires_unfold] at hx
      simp [hnv] at hx
    by_cases hkg : n ≤ v ∧ v - n ∈ G
    · have hv_eq : v = n + (v - n) := by omega
      have hsub : subWires n C G W v =
          insert v ((gateAt C (v - n)).inputs.toFinset.biUnion (fun u => subWires n C G W u)) := by
        conv_lhs => rw [hv_eq]
        rw [subWires_eq_of_gate hRB hG hkg.2 (hv_eq ▸ hv), ← hv_eq]
      rw [hsub] at hx
      rcases Finset.mem_insert.mp hx with rfl | hmem
      · exact absurd rfl hne
      · rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, hxu⟩
        by_cases hxu_eq : x = u
        · subst hxu_eq
          refine ⟨v - n, hkg.2, ?_, List.mem_toFinset.mp hu⟩
          rw [← hv_eq]
          exact mem_subWires_self hv
        · have hu_lt : u < v := by
            have h1 := hRB (v - n) (Finset.mem_range.mp (hG hkg.2)) u (List.mem_toFinset.mp hu)
            omega
          rcases ih u hu_lt hxu hxu_eq with ⟨k, hk, hnk_u, hxk⟩
          refine ⟨k, hk, ?_, hxk⟩
          rw [hsub]
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, hnk_u⟩)
    · rw [subWires_eq_of_not_gate hv hkg, Finset.mem_singleton] at hx
      exact absurd hx hne

lemma subWires_disjoint {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {G W : Finset ℕ}
    (hG : G ⊆ Finset.range C.size)
    (hread1 : ∀ w ∈ W, readsIn C G w ≤ 1)
    {v₁ v₂ : ℕ} (h12 : v₁ ∉ subWires n C G W v₂) (h21 : v₂ ∉ subWires n C G W v₁) :
    Disjoint (subWires n C G W v₁) (subWires n C G W v₂) := by
  rw [Finset.disjoint_left]
  intro x₀ hx₁ hx₂
  set I := subWires n C G W v₁ ∩ subWires n C G W v₂
  have hIne : I.Nonempty := ⟨x₀, Finset.mem_inter.mpr ⟨hx₁, hx₂⟩⟩
  set x := I.max' hIne
  have hxI : x ∈ I := Finset.max'_mem I hIne
  rcases Finset.mem_inter.mp hxI with ⟨hxm1, hxm2⟩
  have hne1 : x ≠ v₁ := fun h => h12 (h ▸ hxm2)
  have hne2 : x ≠ v₂ := fun h => h21 (h ▸ hxm1)
  rcases mem_subWires_ne_has_parent hRB hG hxm1 hne1 with ⟨k₁, hk₁, hnk1, hxk1⟩
  rcases mem_subWires_ne_has_parent hRB hG hxm2 hne2 with ⟨k₂, hk₂, hnk2, hxk2⟩
  have hxW : x ∈ W := (subWires_subset v₁).1 hxm1
  have hr1 : readsIn C G x ≤ 1 := hread1 x hxW
  have hk_eq : k₁ = k₂ := by
    by_contra hkne
    have hsub : ({k₁, k₂} : Finset ℕ) ⊆ G := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption
    have hle : (gateAt C k₁).inputs.count x + (gateAt C k₂).inputs.count x ≤ readsIn C G x := by
      have h1 := readsIn_mono (C := C) hsub x
      rw [show readsIn C {k₁, k₂} x = (gateAt C k₁).inputs.count x + (gateAt C k₂).inputs.count x from by
        unfold readsIn; exact Finset.sum_pair hkne] at h1
      exact h1
    have c1 : 0 < (gateAt C k₁).inputs.count x := List.count_pos_iff.mpr hxk1
    have c2 : 0 < (gateAt C k₂).inputs.count x := List.count_pos_iff.mpr hxk2
    omega
  subst hk_eq
  have hnkI : n + k₁ ∈ I := Finset.mem_inter.mpr ⟨hnk1, hnk2⟩
  have hle_max : n + k₁ ≤ x := Finset.le_max' I (n + k₁) hnkI
  have hlt : x < n + k₁ := hRB k₁ (Finset.mem_range.mp (hG hk₁)) x hxk1
  omega

def extSlots (C : Circuit) (G W : Finset ℕ) : ℕ :=
  ∑ k ∈ G, (gateAt C k).inputs.countP (fun w => decide (w ∉ W))

structure CutTree (n : ℕ) (C : Circuit) (ordinaryGates once : Finset ℕ)
    (G S : Finset ℕ) (r : ℕ) : Prop where
  G_sub : G ⊆ ordinaryGates
  S_sub : S ⊆ once
  r_mem : r ∈ S ∪ G.image (fun k => n + k)
  r_reads : readsIn C G r = 0
  nonroot : ∀ w ∈ S ∪ G.image (fun k => n + k), w ≠ r →
    readsIn C G w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w

lemma subWires_mem_partition {n : ℕ} {C : Circuit} {G S W : Finset ℕ}
    (_hS : ∀ w ∈ S, w < n) (hW : W = S ∪ G.image (fun k => n + k)) (v : ℕ) :
    let Wv := subWires n C G W v
    let Gv := G.filter (fun k => n + k ∈ Wv)
    let Sv := S.filter (fun w => w ∈ Wv)
    Wv = Sv ∪ Gv.image (fun k => n + k) := by
  intro Wv Gv Sv
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image, Sv, Gv]
  constructor
  · intro hx
    have hxW : x ∈ W := (subWires_subset v).1 hx
    rw [hW] at hxW
    rcases Finset.mem_union.mp hxW with hxS | hxG
    · exact Or.inl ⟨hxS, hx⟩
    · rcases Finset.mem_image.mp hxG with ⟨k, hk, rfl⟩
      exact Or.inr ⟨k, ⟨hk, hx⟩, rfl⟩
  · rintro (⟨_, hx⟩ | ⟨k, ⟨_, hx⟩, rfl⟩)
    · exact hx
    · exact hx

lemma subWires_cutTree {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    (honce : ∀ w ∈ once, w < n)
    {G S : Finset ℕ} (hG : G ⊆ ordinaryGates) (hS : S ⊆ once)
    (hread_le : ∀ w ∈ S ∪ G.image (fun k => n + k), readsIn C G w ≤ 1)
    (hnonroot_all : ∀ w ∈ S ∪ G.image (fun k => n + k),
      readsIn C G w = 1 → readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)
    {v : ℕ} (hv : v ∈ S ∪ G.image (fun k => n + k)) :
    let W := S ∪ G.image (fun k => n + k)
    let Wv := subWires n C G W v
    let Gv := G.filter (fun k => n + k ∈ Wv)
    let Sv := S.filter (fun w => w ∈ Wv)
    CutTree n C ordinaryGates once Gv Sv v := by
  intro W Wv Gv Sv
  have hWv_eq : Wv = Sv ∪ Gv.image (fun k => n + k) :=
    subWires_mem_partition (fun w hw => honce w (hS hw)) rfl v
  have hGv_sub : Gv ⊆ G := Finset.filter_subset _ _
  have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hG hord
  refine ⟨Finset.Subset.trans hGv_sub hG, Finset.Subset.trans (Finset.filter_subset _ _) hS,
    ?_, ?_, ?_⟩
  · rw [← hWv_eq]; exact mem_subWires_self hv
  · rw [readsIn_zero_iff]
    intro k hk hmem
    have hnk_mem : n + k ∈ Wv := (Finset.mem_filter.mp hk).2
    have hle : n + k ≤ v := (subWires_subset v).2 (n + k) hnk_mem
    have hlt : v < n + k := hRB k (Finset.mem_range.mp (hG_range (hGv_sub hk))) v hmem
    omega
  · intro w hw hne
    rw [← hWv_eq] at hw
    rcases mem_subWires_ne_has_parent hRB hG_range hw hne with ⟨k, hk, hnk, hwk⟩
    have hpos : 0 < readsIn C Gv w := readsIn_pos_iff.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hnk⟩, hwk⟩
    have hle1 : readsIn C Gv w ≤ readsIn C G w := readsIn_mono hGv_sub w
    have hwW : w ∈ W := (subWires_subset v).1 hw
    have hr1 : readsIn C G w ≤ 1 := hread_le w hwW
    have hGv1 : readsIn C Gv w = 1 := by omega
    have hG1 : readsIn C G w = 1 := by omega
    have hnr := hnonroot_all w hwW hG1
    exact ⟨hGv1, hnr.1, hnr.2⟩

lemma cutTree_of_ext0 {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hbin : ∀ k ∈ ordinaryGates,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2)
    {G S : Finset ℕ} {r : ℕ} (hct : CutTree n C ordinaryGates once G S r)
    (he0 : extSlots C G (S ∪ G.image (fun k => n + k)) = 0) :
    let W := S ∪ G.image (fun k => n + k)
    G ⊆ ordinaryGates ∧ r ∈ W ∧ readsIn C G r = 0 ∧
    (∀ b ∈ (∅ : Finset ℕ), b ∉ W ∧ b < r ∧ readsIn C G b = 1) ∧
    (∀ j ∈ G, ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ W ∨ w ∈ (∅ : Finset ℕ)) ∧
    (∀ w ∈ W, w ≠ r → readsIn C G w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w) := by
  intro W
  change extSlots C G W = 0 at he0
  refine ⟨hct.G_sub, hct.r_mem, hct.r_reads, fun _ hb => by simp at hb, ?_, hct.nonroot⟩
  intro j hj
  have hbj := hbin j (hct.G_sub hj)
  refine ⟨hbj.1, hbj.2, fun w hw => Or.inl ?_⟩
  by_contra hnw
  have hpos : 0 < (gateAt C j).inputs.countP (fun u => decide (u ∉ W)) :=
    List.countP_pos_iff.mpr ⟨w, hw, by simp [hnw]⟩
  have hle : (gateAt C j).inputs.countP (fun u => decide (u ∉ W)) ≤ extSlots C G W :=
    Finset.single_le_sum (f := fun k => (gateAt C k).inputs.countP (fun u => decide (u ∉ W)))
      (fun _ _ => Nat.zero_le _) hj
  omega

lemma cutTree_of_ext1 {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    (hbin : ∀ k ∈ ordinaryGates,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2)
    (_honce : ∀ w ∈ once, w < n)
    {G S : Finset ℕ} {r : ℕ} (hct : CutTree n C ordinaryGates once G S r)
    (he1 : extSlots C G (S ∪ G.image (fun k => n + k)) = 1) :
    let W := S ∪ G.image (fun k => n + k)
    ∃ b : ℕ,
      G ⊆ ordinaryGates ∧ r ∈ W ∧ readsIn C G r = 0 ∧
      (∀ x ∈ ({b} : Finset ℕ), x ∉ W ∧ x < r ∧ readsIn C G x = 1) ∧
      (∀ j ∈ G, ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
        (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ W ∨ w ∈ ({b} : Finset ℕ)) ∧
      (∀ w ∈ W, w ≠ r → readsIn C G w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w) := by
  intro W
  change extSlots C G W = 1 at he1
  have hpos_sum : 0 < ∑ k ∈ G, (gateAt C k).inputs.countP (fun u => decide (u ∉ W)) := by
    change 0 < extSlots C G W; omega
  rcases Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp hpos_sum with ⟨k0, hk0, hk0_pos⟩
  rcases List.countP_pos_iff.mp hk0_pos with ⟨b, hb_in, hb_out⟩
  have hbW : b ∉ W := by simpa using hb_out
  have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hct.G_sub hord
  have hW_le_r : ∀ w ∈ W, w ≤ r := by
    have hlt_max : ∀ m, ∀ x ∈ W, m = n + C.size - x → x ≤ r := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ihm =>
        intro x hx hm
        by_cases hxr : x = r
        · omega
        · have hr1' := (hct.nonroot x hx hxr).1
          rcases readsIn_pos_iff.mp (by omega : 0 < readsIn C G x) with ⟨k', hk', hxk'⟩
          have hlt' : x < n + k' := hRB k' (Finset.mem_range.mp (hG_range hk')) x hxk'
          have hnk'_lt : n + k' < n + C.size := by
            have := Finset.mem_range.mp (hG_range hk'); omega
          have hnk'W : n + k' ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk')
          have hle' := ihm (n + C.size - (n + k')) (by omega) (n + k') hnk'W rfl
          omega
    intro w hw
    exact hlt_max (n + C.size - w) w hw rfl
  have hb_lt_r : b < r := by
    have h1 : b < n + k0 := hRB k0 (Finset.mem_range.mp (hG_range hk0)) b hb_in
    have h2 : n + k0 ≤ r := hW_le_r (n + k0) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk0))
    omega
  have hb_reads_le : readsIn C G b ≤ extSlots C G W := by
    unfold readsIn extSlots
    apply Finset.sum_le_sum
    intro k _
    have h1 : (gateAt C k).inputs.count b = (gateAt C k).inputs.countP (fun u => decide (u = b)) := by
      induction (gateAt C k).inputs with
      | nil => simp
      | cons a l ih =>
        simp only [List.count_cons, List.countP_cons, beq_iff_eq]
        by_cases h : a = b <;> simp [h, ih]
    rw [h1]
    apply List.countP_mono_left
    intro u _ hu
    have hub : u = b := by simpa using hu
    subst hub
    simpa using hbW
  have hb_reads_pos : 0 < readsIn C G b := readsIn_pos_iff.mpr ⟨k0, hk0, hb_in⟩
  have hb_reads : readsIn C G b = 1 := by omega
  have hall_out_eq_b : ∀ j ∈ G, ∀ w ∈ (gateAt C j).inputs, w ∉ W → w = b := by
    intro j hj w hw hnw
    by_contra hne
    have hle_sum : readsIn C G b + readsIn C G w ≤ extSlots C G W := by
      have hpair : ∑ u ∈ ({b, w} : Finset ℕ), readsIn C G u ≤ extSlots C G W := by
        rw [sum_readsIn_eq_sum_countP]
        unfold extSlots
        apply Finset.sum_le_sum
        intro k _
        apply List.countP_mono_left
        intro u _ hu
        have hu' : u = b ∨ u = w := by simpa using hu
        rcases hu' with rfl | rfl
        · simpa using hbW
        · simpa using hnw
      rw [Finset.sum_pair (Ne.symm hne)] at hpair
      exact hpair
    have hw_pos : 0 < readsIn C G w := readsIn_pos_iff.mpr ⟨j, hj, hw⟩
    omega
  refine ⟨b, hct.G_sub, hct.r_mem, hct.r_reads, ?_, ?_, hct.nonroot⟩
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact ⟨hbW, hb_lt_r, hb_reads⟩
  · intro j hj
    have hbj := hbin j (hct.G_sub hj)
    refine ⟨hbj.1, hbj.2, fun w hw => ?_⟩
    by_cases hwW : w ∈ W
    · exact Or.inl hwW
    · exact Or.inr (Finset.mem_singleton.mpr (hall_out_eq_b j hj w hw hwW))

lemma cutTree_W_eq_subWires_r {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    {G S : Finset ℕ} {r : ℕ} (hct : CutTree n C ordinaryGates once G S r) :
    subWires n C G (S ∪ G.image (fun k => n + k)) r = S ∪ G.image (fun k => n + k) := by
  set W := S ∪ G.image (fun k => n + k)
  have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hct.G_sub hord
  apply Finset.Subset.antisymm (subWires_subset r).1
  have hdown : ∀ (m : ℕ) (w : ℕ), w ∈ W → n + C.size - w = m → w ∈ subWires n C G W r := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro w hw hm
      by_cases hwr : w = r
      · subst hwr; exact mem_subWires_self hct.r_mem
      · have hr1 := (hct.nonroot w hw hwr).1
        rcases readsIn_pos_iff.mp (by omega : 0 < readsIn C G w) with ⟨k, hk, hwk⟩
        have hlt : w < n + k := hRB k (Finset.mem_range.mp (hG_range hk)) w hwk
        have hnk_lt : n + k < n + C.size := by
          have := Finset.mem_range.mp (hG_range hk); omega
        have hnkW : n + k ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
        have hnk_in : n + k ∈ subWires n C G W r := ih (n + C.size - (n + k)) (by omega) (n + k) hnkW rfl
        exact subWires_closed_down hRB hG_range hk hnk_in w hwk hw
  intro w hw
  exact hdown (n + C.size - w) w hw rfl

lemma cutTree_upper_split {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    (honce : ∀ w ∈ once, w < n)
    {G S : Finset ℕ} {r v : ℕ} (hct : CutTree n C ordinaryGates once G S r)
    (hv : v ∈ S ∪ G.image (fun k => n + k)) (hvr : v ≠ r) :
    let W := S ∪ G.image (fun k => n + k)
    let Wv := subWires n C G W v
    let Gv := G.filter (fun k => n + k ∈ Wv)
    let Sv := S.filter (fun w => w ∈ Wv)
    let G' := G \ Gv
    let S' := S \ Sv
    CutTree n C ordinaryGates once G' S' r ∧
    extSlots C G' (S' ∪ G'.image (fun k => n + k)) + extSlots C Gv Wv = extSlots C G W + 1 := by
  intro W Wv Gv Sv G' S'
  set W' := S' ∪ G'.image (fun k => n + k)
  have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hct.G_sub hord
  have hS_lt : ∀ w ∈ S, w < n := fun w hw => honce w (hct.S_sub hw)
  have hWv_eq : Wv = Sv ∪ Gv.image (fun k => n + k) := subWires_mem_partition hS_lt rfl v
  have hGv_sub : Gv ⊆ G := Finset.filter_subset _ _
  have hSv_sub : Sv ⊆ S := Finset.filter_subset _ _
  have hW'_eq : W' = W \ Wv := by
    ext x
    simp only [W', W, Finset.mem_union, Finset.mem_sdiff, Finset.mem_image, G', S', Gv, Sv,
      Finset.mem_filter]
    constructor
    · rintro (⟨hxS, hnx⟩ | ⟨k, ⟨hkG, hnk⟩, rfl⟩)
      · exact ⟨Or.inl hxS, fun hx => hnx ⟨hxS, hx⟩⟩
      · exact ⟨Or.inr ⟨k, hkG, rfl⟩, fun hx => hnk ⟨hkG, hx⟩⟩
    · rintro ⟨hxS | ⟨k, hkG, rfl⟩, hnx⟩
      · exact Or.inl ⟨hxS, fun h => hnx h.2⟩
      · exact Or.inr ⟨k, ⟨hkG, fun h => hnx h.2⟩, rfl⟩
  have hread_le : ∀ w ∈ W, readsIn C G w ≤ 1 := by
    intro w hw
    by_cases hwr : w = r
    · subst hwr; rw [hct.r_reads]; exact Nat.zero_le 1
    · rw [(hct.nonroot w hw hwr).1]
  have hsub_ct : CutTree n C ordinaryGates once Gv Sv v :=
    subWires_cutTree hRB hord honce hct.G_sub hct.S_sub hread_le
      (fun w hw hr1 => by
        have hne : w ≠ r := fun h => by subst h; rw [hct.r_reads] at hr1; omega
        have := hct.nonroot w hw hne
        exact ⟨this.2.1, this.2.2⟩) hv
  have hr_notin_Wv : r ∉ Wv := by
    intro hrWv
    have hle : r ≤ v := (subWires_subset v).2 r hrWv
    have hlt_v_r : v < r := by
      have hr1 := (hct.nonroot v hv hvr).1
      have hmax : ∀ (m : ℕ) (x : ℕ), x ∈ W → x ≠ r → n + C.size - x = m → x < r := by
        intro m
        induction m using Nat.strong_induction_on with
        | ind m ih =>
          intro x hx hxr hm
          have hx1 := (hct.nonroot x hx hxr).1
          rcases readsIn_pos_iff.mp (by omega : 0 < readsIn C G x) with ⟨k, hk, hxk⟩
          have hlt1 : x < n + k := hRB k (Finset.mem_range.mp (hG_range hk)) x hxk
          have hnk_lt : n + k < n + C.size := by
            have := Finset.mem_range.mp (hG_range hk); omega
          have hnkW : n + k ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
          by_cases hnkr : n + k = r
          · omega
          · have hlt2 := ih (n + C.size - (n + k)) (by omega) (n + k) hnkW hnkr rfl
            omega
      exact hmax (n + C.size - v) v hv hvr rfl
    omega
  have hdisjG : Disjoint G' Gv := Finset.sdiff_disjoint
  have hunionG : G' ∪ Gv = G := Finset.sdiff_union_of_subset hGv_sub
  have hGv_no_read_W' : ∀ w ∈ W', readsIn C Gv w = 0 := by
    intro w hw'
    rw [hW'_eq] at hw'
    rcases Finset.mem_sdiff.mp hw' with ⟨hwW, hnwv⟩
    rw [readsIn_zero_iff]
    intro k hk hwk
    rcases Finset.mem_filter.mp hk with ⟨hkG, hnkWv⟩
    exact hnwv (subWires_closed_down hRB hG_range hkG hnkWv w hwk hwW)
  have hct' : CutTree n C ordinaryGates once G' S' r := by
    refine ⟨Finset.Subset.trans Finset.sdiff_subset hct.G_sub,
      Finset.Subset.trans Finset.sdiff_subset hct.S_sub, ?_, ?_, ?_⟩
    · change r ∈ W'; rw [hW'_eq]; exact Finset.mem_sdiff.mpr ⟨hct.r_mem, hr_notin_Wv⟩
    · have hle : readsIn C G' r ≤ readsIn C G r :=
        readsIn_mono (C := C) (Finset.sdiff_subset (s := G) (t := Gv)) r
      rw [hct.r_reads] at hle; omega
    · intro w hw' hne
      change w ∈ W' at hw'
      have htot := readsIn_union (C := C) hdisjG w
      rw [hunionG] at htot
      have hwW : w ∈ W := (Finset.mem_sdiff.mp (hW'_eq ▸ hw')).1
      have hnr := hct.nonroot w hwW hne
      have h0 := hGv_no_read_W' w hw'
      exact ⟨by omega, hnr.2.1, hnr.2.2⟩
  refine ⟨hct', ?_⟩
  have hext_Gv : ∀ k ∈ Gv,
      (gateAt C k).inputs.countP (fun w => decide (w ∉ Wv)) =
      (gateAt C k).inputs.countP (fun w => decide (w ∉ W)) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkG, hnkWv⟩
    apply List.countP_congr
    intro w hw
    have hiff : w ∈ Wv ↔ w ∈ W :=
      ⟨fun h => (subWires_subset v).1 h, fun h => subWires_closed_down hRB hG_range hkG hnkWv w hw h⟩
    simp [hiff]
  have hG'_read_Wv : ∀ k ∈ G', ∀ w ∈ (gateAt C k).inputs, w ∈ Wv → w = v := by
    intro k hk w hw hwWv
    by_contra hne
    have hr_sub : readsIn C Gv w = 1 := (hsub_ct.nonroot w (hWv_eq ▸ hwWv) hne).1
    have hr_pos : 0 < readsIn C G' w := readsIn_pos_iff.mpr ⟨k, hk, hw⟩
    have htot := readsIn_union (C := C) hdisjG w
    rw [hunionG] at htot
    have hle1 : readsIn C G w ≤ 1 := hread_le w ((subWires_subset v).1 hwWv)
    omega
  have hext_G' : ∀ k ∈ G',
      (gateAt C k).inputs.countP (fun w => decide (w ∉ W')) =
      (gateAt C k).inputs.countP (fun w => decide (w ∉ W)) + (gateAt C k).inputs.count v := by
    intro k hk
    have hsplit : ∀ l : List ℕ, (∀ w ∈ l, w ∈ Wv → w = v) →
        l.countP (fun w => decide (w ∉ W')) =
        l.countP (fun w => decide (w ∉ W)) + l.count v := by
      intro l hl
      induction l with
      | nil => simp
      | cons a xs ih =>
        have hxs := ih (fun w hw => hl w (by simp [hw]))
        simp only [List.countP_cons, List.count_cons, beq_iff_eq]
        rw [hxs]
        by_cases haW : a ∈ W
        · by_cases haWv : a ∈ Wv
          · have hav : a = v := hl a (by simp) haWv
            have haW' : a ∉ W' := by rw [hW'_eq, Finset.mem_sdiff]; intro h; exact h.2 haWv
            have hd1 : decide (a ∉ W') = true := by simp [haW']
            have hd2 : decide (a ∉ W) = false := by simp [haW]
            rw [hd1, hd2]; simp [hav]; omega
          · have haW' : a ∈ W' := by rw [hW'_eq]; exact Finset.mem_sdiff.mpr ⟨haW, haWv⟩
            have hav : a ≠ v := fun h => haWv (h ▸ mem_subWires_self hv)
            have hd1 : decide (a ∉ W') = false := by simp [haW']
            have hd2 : decide (a ∉ W) = false := by simp [haW]
            rw [hd1, hd2]; simp [hav]
        · have haW' : a ∉ W' := by rw [hW'_eq, Finset.mem_sdiff]; intro h; exact haW h.1
          have hav : a ≠ v := fun h => haW (h ▸ hv)
          have hd1 : decide (a ∉ W') = true := by simp [haW']
          have hd2 : decide (a ∉ W) = true := by simp [haW]
          rw [hd1, hd2]; simp [hav]; omega
    exact hsplit (gateAt C k).inputs (hG'_read_Wv k hk)
  have hv_reads_G' : readsIn C G' v = 1 := by
    have htot := readsIn_union (C := C) hdisjG v
    rw [hunionG, hsub_ct.r_reads, add_zero] at htot
    rw [← htot]
    exact (hct.nonroot v hv hvr).1
  unfold extSlots
  rw [Finset.sum_congr rfl hext_G', Finset.sum_add_distrib, Finset.sum_congr rfl hext_Gv]
  have h1 : (∑ k ∈ G', (gateAt C k).inputs.count v) = 1 := hv_reads_G'
  rw [h1]
  have h2 : (∑ k ∈ G', (gateAt C k).inputs.countP (fun w => decide (w ∉ W))) +
      (∑ k ∈ Gv, (gateAt C k).inputs.countP (fun w => decide (w ∉ W))) =
      ∑ k ∈ G, (gateAt C k).inputs.countP (fun w => decide (w ∉ W)) := by
    rw [← Finset.sum_union hdisjG, hunionG]
  omega

lemma cutTree_node_children {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    (_hbin : ∀ k ∈ ordinaryGates,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2)
    (honce : ∀ w ∈ once, w < n)
    {G S : Finset ℕ} {r : ℕ} (hct : CutTree n C ordinaryGates once G S r)
    {k : ℕ} (hk : k ∈ G) (w₁ w₂ : ℕ) (hins : (gateAt C k).inputs = [w₁, w₂]) :
    let W := S ∪ G.image (fun j => n + j)
    let Wv := subWires n C G W (n + k)
    let Gv := G.filter (fun j => n + j ∈ Wv)
    let Sv := S.filter (fun w => w ∈ Wv)
    let W1 := subWires n C G W w₁
    let G1 := G.filter (fun j => n + j ∈ W1)
    let S1 := S.filter (fun w => w ∈ W1)
    let W2 := subWires n C G W w₂
    let G2 := G.filter (fun j => n + j ∈ W2)
    let S2 := S.filter (fun w => w ∈ W2)
    (Sv ⊆ S1 ∪ S2) ∧
    extSlots C Gv Wv =
      (if w₁ ∈ W then extSlots C G1 W1 else 1) + (if w₂ ∈ W then extSlots C G2 W2 else 1) := by
  intro W Wv Gv Sv W1 G1 S1 W2 G2 S2
  have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hct.G_sub hord
  have hS_lt : ∀ w ∈ S, w < n := fun w hw => honce w (hct.S_sub hw)
  have hnkW : n + k ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
  have hWv_eq : Wv = insert (n + k) (W1 ∪ W2) := by
    dsimp only [Wv]
    rw [subWires_eq_of_gate hRB hG_range hk hnkW, hins]
    ext x
    simp [W1, W2]
  have hread_le : ∀ w ∈ W, readsIn C G w ≤ 1 := by
    intro w hw
    by_cases hwr : w = r
    · subst hwr; rw [hct.r_reads]; exact Nat.zero_le 1
    · rw [(hct.nonroot w hw hwr).1]
  have hSv_sub : Sv ⊆ S1 ∪ S2 := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxS, hxWv⟩
    rw [hWv_eq] at hxWv
    rcases Finset.mem_insert.mp hxWv with rfl | hx12
    · have := hS_lt (n + k) hxS; omega
    · rcases Finset.mem_union.mp hx12 with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxS, h1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxS, h2⟩)
  refine ⟨hSv_sub, ?_⟩
  have hnk_notin1 : n + k ∉ W1 := by
    intro h
    have hle := (subWires_subset w₁).2 (n + k) h
    have hlt := hRB k (Finset.mem_range.mp (hG_range hk)) w₁ (by rw [hins]; simp)
    omega
  have hnk_notin2 : n + k ∉ W2 := by
    intro h
    have hle := (subWires_subset w₂).2 (n + k) h
    have hlt := hRB k (Finset.mem_range.mp (hG_range hk)) w₂ (by rw [hins]; simp)
    omega
  have hdisj12 : Disjoint W1 W2 := by
    by_cases h1 : w₁ ∈ W
    · by_cases h2 : w₂ ∈ W
      · have hne12 : w₁ ≠ w₂ := by
          intro heq
          subst heq
          have h2c : 2 ≤ readsIn C G w₁ := by
            have hle := Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count w₁)
              (fun _ _ => Nat.zero_le _) hk
            rw [hins] at hle
            simpa [readsIn] using hle
          have := hread_le w₁ h1
          omega
        have hn12 : w₁ ∉ W2 := by
          intro hmem
          rcases mem_subWires_ne_has_parent hRB hG_range hmem hne12 with ⟨k', hk', hnk', hwk'⟩
          have hkne : k' ≠ k := by
            intro heq; subst heq; exact hnk_notin2 hnk'
          have h2c : 2 ≤ readsIn C G w₁ := by
            have hsub : ({k, k'} : Finset ℕ) ⊆ G := by
              intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl <;> assumption
            have hle : (gateAt C k).inputs.count w₁ + (gateAt C k').inputs.count w₁ ≤ readsIn C G w₁ := by
              have h1 := readsIn_mono (C := C) hsub w₁
              rw [show readsIn C {k, k'} w₁ = (gateAt C k).inputs.count w₁ + (gateAt C k').inputs.count w₁ from by
                unfold readsIn; exact Finset.sum_pair hkne.symm] at h1
              exact h1
            have c1 : 0 < (gateAt C k).inputs.count w₁ := List.count_pos_iff.mpr (by rw [hins]; simp)
            have c2 : 0 < (gateAt C k').inputs.count w₁ := List.count_pos_iff.mpr hwk'
            omega
          have := hread_le w₁ h1
          omega
        have hn21 : w₂ ∉ W1 := by
          intro hmem
          rcases mem_subWires_ne_has_parent hRB hG_range hmem hne12.symm with ⟨k', hk', hnk', hwk'⟩
          have hkne : k' ≠ k := by
            intro heq; subst heq; exact hnk_notin1 hnk'
          have h2c : 2 ≤ readsIn C G w₂ := by
            have hsub : ({k, k'} : Finset ℕ) ⊆ G := by
              intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl <;> assumption
            have hle : (gateAt C k).inputs.count w₂ + (gateAt C k').inputs.count w₂ ≤ readsIn C G w₂ := by
              have h1 := readsIn_mono (C := C) hsub w₂
              rw [show readsIn C {k, k'} w₂ = (gateAt C k).inputs.count w₂ + (gateAt C k').inputs.count w₂ from by
                unfold readsIn; exact Finset.sum_pair hkne.symm] at h1
              exact h1
            have c1 : 0 < (gateAt C k).inputs.count w₂ := List.count_pos_iff.mpr (by rw [hins]; simp)
            have c2 : 0 < (gateAt C k').inputs.count w₂ := List.count_pos_iff.mpr hwk'
            omega
          have := hread_le w₂ h2
          omega
        exact subWires_disjoint hRB hG_range hread_le hn12 hn21
      · have hW2e : W2 = ∅ := by dsimp only [W2]; rw [subWires]; simp [h2]
        rw [hW2e]; exact Finset.disjoint_empty_right _
    · have hW1e : W1 = ∅ := by dsimp only [W1]; rw [subWires]; simp [h1]
      rw [hW1e]; exact Finset.disjoint_empty_left _
  have hGv_eq : Gv = insert k (G1 ∪ G2) := by
    ext j
    simp only [Gv, G1, G2, Finset.mem_filter, Finset.mem_insert, Finset.mem_union, hWv_eq]
    constructor
    · rintro ⟨hjG, hnj | h1 | h2⟩
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl ⟨hjG, h1⟩)
      · exact Or.inr (Or.inr ⟨hjG, h2⟩)
    · rintro (rfl | ⟨hjG, h1⟩ | ⟨hjG, h2⟩)
      · exact ⟨hk, Or.inl rfl⟩
      · exact ⟨hjG, Or.inr (Or.inl h1)⟩
      · exact ⟨hjG, Or.inr (Or.inr h2)⟩
  have hk_notin12 : k ∉ G1 ∪ G2 := by
    simp only [G1, G2, Finset.mem_union, Finset.mem_filter]
    rintro (⟨_, h1⟩ | ⟨_, h2⟩)
    · exact hnk_notin1 h1
    · exact hnk_notin2 h2
  have hdisjG12 : Disjoint G1 G2 := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    exact Finset.disjoint_left.mp hdisj12 (Finset.mem_filter.mp hj1).2 (Finset.mem_filter.mp hj2).2
  have hcongr1 : ∀ j ∈ G1,
      (gateAt C j).inputs.countP (fun w => decide (w ∉ Wv)) =
      (gateAt C j).inputs.countP (fun w => decide (w ∉ W1)) := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjG, hnjW1⟩
    apply List.countP_congr
    intro w hw
    have hiff : w ∈ Wv ↔ w ∈ W1 := by
      constructor
      · intro hwWv
        exact subWires_closed_down hRB hG_range hjG hnjW1 w hw ((subWires_subset (n + k)).1 hwWv)
      · intro hwW1
        rw [hWv_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hwW1)
    simp [hiff]
  have hcongr2 : ∀ j ∈ G2,
      (gateAt C j).inputs.countP (fun w => decide (w ∉ Wv)) =
      (gateAt C j).inputs.countP (fun w => decide (w ∉ W2)) := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjG, hnjW2⟩
    apply List.countP_congr
    intro w hw
    have hiff : w ∈ Wv ↔ w ∈ W2 := by
      constructor
      · intro hwWv
        exact subWires_closed_down hRB hG_range hjG hnjW2 w hw ((subWires_subset (n + k)).1 hwWv)
      · intro hwW2
        rw [hWv_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hwW2)
    simp [hiff]
  have hk_term : (gateAt C k).inputs.countP (fun w => decide (w ∉ Wv)) =
      (if w₁ ∈ W then 0 else 1) + (if w₂ ∈ W then 0 else 1) := by
    rw [hins]
    have h1 : w₁ ∈ Wv ↔ w₁ ∈ W :=
      ⟨fun h => (subWires_subset (n + k)).1 h,
       fun h => subWires_closed_down hRB hG_range hk (mem_subWires_self hnkW) w₁ (by rw [hins]; simp) h⟩
    have h2 : w₂ ∈ Wv ↔ w₂ ∈ W :=
      ⟨fun h => (subWires_subset (n + k)).1 h,
       fun h => subWires_closed_down hRB hG_range hk (mem_subWires_self hnkW) w₂ (by rw [hins]; simp) h⟩
    simp only [List.countP_cons, List.countP_nil, h1, h2]
    by_cases hw1 : w₁ ∈ W <;> by_cases hw2 : w₂ ∈ W <;> simp [hw1, hw2]
  have hG1_empty : w₁ ∉ W → extSlots C G1 W1 = 0 := by
    intro hnw1
    have hW1e : W1 = ∅ := by dsimp only [W1]; rw [subWires_unfold]; simp [hnw1]
    have hG1e : G1 = ∅ := by ext j; simp [G1, hW1e]
    simp [extSlots, hG1e]
  have hG2_empty : w₂ ∉ W → extSlots C G2 W2 = 0 := by
    intro hnw2
    have hW2e : W2 = ∅ := by dsimp only [W2]; rw [subWires_unfold]; simp [hnw2]
    have hG2e : G2 = ∅ := by ext j; simp [G2, hW2e]
    simp [extSlots, hG2e]
  have hmain : extSlots C Gv Wv =
      ((if w₁ ∈ W then 0 else 1) + (if w₂ ∈ W then 0 else 1)) + (extSlots C G1 W1 + extSlots C G2 W2) := by
    unfold extSlots
    rw [hGv_eq, Finset.sum_insert hk_notin12, Finset.sum_union hdisjG12,
        Finset.sum_congr rfl hcongr1, Finset.sum_congr rfl hcongr2, hk_term]
  rw [hmain]
  by_cases hw1 : w₁ ∈ W <;> by_cases hw2 : w₂ ∈ W
  · simp [hw1, hw2]
  · rw [hG2_empty hw2]; simp [hw1, hw2]; omega
  · rw [hG1_empty hw1]; simp [hw1, hw2]
  · rw [hG1_empty hw1, hG2_empty hw2]; simp [hw1, hw2]

lemma cutTree_leaf_bound {n p c : ℕ} {C : Circuit} {ordinaryGates once H : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    (hbin : ∀ k ∈ ordinaryGates,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2)
    (honce : ∀ w ∈ once, w < n)
    (hp_bd : ∀ S : Finset ℕ, S ⊆ once →
      (∃ (region : Finset ℕ) (root : ℕ),
        let wires := S ∪ region.image (fun k => n + k)
        let localReads := readsIn C region
        region ⊆ ordinaryGates ∧ root ∈ wires ∧ localReads root = 0 ∧
        (∀ b ∈ (∅ : Finset ℕ), b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
        (∀ j ∈ region, ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
          (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w ∈ (∅ : Finset ℕ)) ∧
        (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)) →
      (S \ H).card ≤ p)
    (hc_bd : ∀ (S : Finset ℕ) (b : ℕ), S ⊆ once →
      (∃ (region : Finset ℕ) (root : ℕ),
        let wires := S ∪ region.image (fun k => n + k)
        let localReads := readsIn C region
        region ⊆ ordinaryGates ∧ root ∈ wires ∧ localReads root = 0 ∧
        (∀ x ∈ ({b} : Finset ℕ), x ∉ wires ∧ x < root ∧ localReads x = 1) ∧
        (∀ j ∈ region, ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
          (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w ∈ ({b} : Finset ℕ)) ∧
        (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)) →
      (S \ H).card ≤ c)
    (e : ℕ) :
    ∀ (G S : Finset ℕ) (r : ℕ),
      CutTree n C ordinaryGates once G S r →
      extSlots C G (S ∪ G.image (fun k => n + k)) = e →
      (S \ H).card ≤ if e = 0 then p else c * (2 * e - 1) := by
  induction e using Nat.strong_induction_on with
  | ind e ih =>
    intro G S r hct he
    set W := S ∪ G.image (fun k => n + k)
    by_cases he0 : e = 0
    · subst he0
      simp only [ite_true]
      exact hp_bd S hct.S_sub ⟨G, r, cutTree_of_ext0 hbin hct he⟩
    · simp only [he0, ite_false]
      by_cases he1 : e = 1
      · subst he1
        rcases cutTree_of_ext1 hRB hord hbin honce hct he with ⟨b, hb⟩
        have hle := hc_bd S b hct.S_sub ⟨G, r, hb⟩
        simpa using hle
      · have he2 : 2 ≤ e := by omega
        have hread_le : ∀ w ∈ W, readsIn C G w ≤ 1 := by
          intro w hw
          by_cases hwr : w = r
          · subst hwr; rw [hct.r_reads]; exact Nat.zero_le 1
          · rw [(hct.nonroot w hw hwr).1]
        have hsub_ct : ∀ v ∈ W,
            CutTree n C ordinaryGates once
              (G.filter (fun j => n + j ∈ subWires n C G W v))
              (S.filter (fun w => w ∈ subWires n C G W v)) v :=
          fun v hv => subWires_cutTree hRB hord honce hct.G_sub hct.S_sub hread_le
            (fun w hw hr1 => by
              have hne : w ≠ r := fun h => by subst h; rw [hct.r_reads] at hr1; omega
              have := hct.nonroot w hw hne
              exact ⟨this.2.1, this.2.2⟩) hv
        set bad := G.filter (fun k => 2 ≤ extSlots C (G.filter (fun j => n + j ∈ subWires n C G W (n + k)))
          (subWires n C G W (n + k)))
        have hbad_ne : bad.Nonempty := by
          rcases Finset.mem_union.mp hct.r_mem with hrS | hrG
          · exfalso
            have hGe : G = ∅ := by
              have hsub_r := cutTree_W_eq_subWires_r hRB hord hct
              have hr_lt : r < n := honce r (hct.S_sub hrS)
              have hng : ¬ (n ≤ r ∧ r - n ∈ G) := fun h => by omega
              have hsing := subWires_eq_of_not_gate (C := C) hct.r_mem hng
              rw [hsing] at hsub_r
              ext k
              simp only [Finset.notMem_empty, iff_false]
              intro hk
              have hnk : n + k ∈ ({r} : Finset ℕ) := by
                rw [hsub_r]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
              rw [Finset.mem_singleton] at hnk
              omega
            rw [hGe] at he
            simp [extSlots] at he
            omega
          · rcases Finset.mem_image.mp hrG with ⟨kr, hkr, hkr_eq⟩
            refine ⟨kr, Finset.mem_filter.mpr ⟨hkr, ?_⟩⟩
            rw [hkr_eq, cutTree_W_eq_subWires_r hRB hord hct]
            have hGfilt : G.filter (fun j => n + j ∈ W) = G :=
              Finset.filter_true_of_mem (fun j hj => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
            rw [hGfilt, he]
            exact he2
        set k0 := bad.min' hbad_ne
        have hk0_bad : k0 ∈ bad := Finset.min'_mem bad hbad_ne
        rcases Finset.mem_filter.mp hk0_bad with ⟨hk0G, hk0_ge2⟩
        have hlen2 : (gateAt C k0).inputs.length = 2 := (hbin k0 (hct.G_sub hk0G)).2
        rcases List.length_eq_two.mp hlen2 with ⟨w₁, w₂, hins⟩
        have hchildren := cutTree_node_children hRB hord hbin honce hct hk0G w₁ w₂ hins
        set Wv := subWires n C G W (n + k0)
        set Gv := G.filter (fun j => n + j ∈ Wv)
        set Sv := S.filter (fun w => w ∈ Wv)
        set W1 := subWires n C G W w₁
        set G1 := G.filter (fun j => n + j ∈ W1)
        set S1 := S.filter (fun w => w ∈ W1)
        set W2 := subWires n C G W w₂
        set G2 := G.filter (fun j => n + j ∈ W2)
        set S2 := S.filter (fun w => w ∈ W2)
        have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hct.G_sub hord
        have he_child_le1 : ∀ w, w ∈ (gateAt C k0).inputs → w ∈ W →
            extSlots C (G.filter (fun j => n + j ∈ subWires n C G W w)) (subWires n C G W w) ≤ 1 := by
          intro w hw hwW
          rcases Finset.mem_union.mp hwW with hwS | hwG
          · have hw_lt : w < n := honce w (hct.S_sub hwS)
            have hng : ¬ (n ≤ w ∧ w - n ∈ G) := fun h => by omega
            have hsing := subWires_eq_of_not_gate (C := C) hwW hng
            have hGe : G.filter (fun j => n + j ∈ subWires n C G W w) = ∅ := by
              rw [hsing]; ext j; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
              intro h; omega
            rw [hGe]; simp [extSlots]
          · rcases Finset.mem_image.mp hwG with ⟨kw, hkw, rfl⟩
            have hlt : n + kw < n + k0 := hRB k0 (Finset.mem_range.mp (hG_range hk0G)) (n + kw) hw
            by_contra hge2
            have hkw_bad : kw ∈ bad := Finset.mem_filter.mpr ⟨hkw, by omega⟩
            have hmin : k0 ≤ kw := Finset.min'_le bad kw hkw_bad
            omega
        have he1_le : (if w₁ ∈ W then extSlots C G1 W1 else 1) ≤ 1 := by
          by_cases h1 : w₁ ∈ W
          · simp only [h1, ite_true]
            exact he_child_le1 w₁ (by rw [hins]; simp) h1
          · simp [h1]
        have he2_le : (if w₂ ∈ W then extSlots C G2 W2 else 1) ≤ 1 := by
          by_cases h2 : w₂ ∈ W
          · simp only [h2, ite_true]
            exact he_child_le1 w₂ (by rw [hins]; simp) h2
          · simp [h2]
        have hch2 : extSlots C Gv Wv =
            (if w₁ ∈ W then extSlots C G1 W1 else 1) + (if w₂ ∈ W then extSlots C G2 W2 else 1) :=
          hchildren.2
        have hkv2 : 2 ≤ extSlots C Gv Wv := hk0_ge2
        have hEv_eq2 : extSlots C Gv Wv = 2 := by omega
        have he1_eq1 : (if w₁ ∈ W then extSlots C G1 W1 else 1) = 1 := by omega
        have he2_eq1 : (if w₂ ∈ W then extSlots C G2 W2 else 1) = 1 := by omega
        have hS1_le : (S1 \ H).card ≤ c := by
          by_cases h1 : w₁ ∈ W
          · simp only [h1, ite_true] at he1_eq1
            have hW1_eq : W1 = S1 ∪ G1.image (fun j => n + j) :=
              subWires_mem_partition (fun w hw => honce w (hct.S_sub hw)) rfl w₁
            have hct1 := hsub_ct w₁ h1
            have hle := ih 1 (by omega) G1 S1 w₁ hct1 (by rw [← hW1_eq]; exact he1_eq1)
            simpa using hle
          · have hW1e : W1 = ∅ := by dsimp only [W1]; rw [subWires]; simp [h1]
            have hS1e : S1 = ∅ := by ext x; simp [S1, hW1e]
            simp [hS1e]
        have hS2_le : (S2 \ H).card ≤ c := by
          by_cases h2 : w₂ ∈ W
          · simp only [h2, ite_true] at he2_eq1
            have hW2_eq : W2 = S2 ∪ G2.image (fun j => n + j) :=
              subWires_mem_partition (fun w hw => honce w (hct.S_sub hw)) rfl w₂
            have hct2 := hsub_ct w₂ h2
            have hle := ih 1 (by omega) G2 S2 w₂ hct2 (by rw [← hW2_eq]; exact he2_eq1)
            simpa using hle
          · have hW2e : W2 = ∅ := by dsimp only [W2]; rw [subWires]; simp [h2]
            have hS2e : S2 = ∅ := by ext x; simp [S2, hW2e]
            simp [hS2e]
        have hSv_le : (Sv \ H).card ≤ 2 * c := by
          have hsub : Sv \ H ⊆ (S1 \ H) ∪ (S2 \ H) := by
            intro x hx
            rcases Finset.mem_sdiff.mp hx with ⟨hxSv, hxH⟩
            rcases Finset.mem_union.mp (hchildren.1 hxSv) with h1 | h2
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h1, hxH⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h2, hxH⟩)
          have hle := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
          omega
        by_cases hvr : n + k0 = r
        · have hWv_all : Wv = W := by dsimp only [Wv]; rw [hvr]; exact cutTree_W_eq_subWires_r hRB hord hct
          have hSv_all : Sv = S := by
            dsimp only [Sv]; rw [hWv_all]
            exact Finset.filter_true_of_mem (fun w hw => Finset.mem_union_left _ hw)
          rw [← hSv_all]
          have h3 : 2 * c ≤ c * (2 * e - 1) := by
            have : 2 ≤ 2 * e - 1 := by omega
            calc 2 * c = c * 2 := Nat.mul_comm 2 c
              _ ≤ c * (2 * e - 1) := Nat.mul_le_mul_left c this
          omega
        · have hnk0W : n + k0 ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk0G)
          have hup := cutTree_upper_split hRB hord honce hct hnk0W hvr
          set G' := G \ Gv
          set S' := S \ Sv
          have he' : extSlots C G' (S' ∪ G'.image (fun k => n + k)) = e - 1 := by
            have hup2 : extSlots C G' (S' ∪ G'.image (fun k => n + k)) + extSlots C Gv Wv = extSlots C G W + 1 :=
              hup.2
            have heW : extSlots C G W = e := he
            omega
          have hS'_le := ih (e - 1) (by omega) G' S' r hup.1 he'
          have hne0' : e - 1 ≠ 0 := by omega
          simp only [hne0', ite_false] at hS'_le
          have hS_split : S \ H ⊆ (S' \ H) ∪ (Sv \ H) := by
            intro x hx
            rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxH⟩
            by_cases hxSv : x ∈ Sv
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxSv, hxH⟩)
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxS, hxSv⟩, hxH⟩)
          have hle_sum := le_trans (Finset.card_le_card hS_split) (Finset.card_union_le _ _)
          have hmul_eq : c * (2 * (e - 1) - 1) + 2 * c = c * (2 * e - 1) := by
            have h1 : 2 * (e - 1) - 1 + 2 = 2 * e - 1 := by omega
            calc c * (2 * (e - 1) - 1) + 2 * c
                = c * (2 * (e - 1) - 1) + c * 2 := by rw [Nat.mul_comm 2 c]
              _ = c * (2 * (e - 1) - 1 + 2) := (Nat.mul_add c _ _).symm
              _ = c * (2 * e - 1) := by rw [h1]
          omega

end PEqualNP.Outside.L_meta_25796_aux

theorem PEqualNP.Outside.L_meta_25796 :
∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let gates := Finset.range C.size
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)) gates
  let special := ((Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)) ∪
    neg.image (fun k => n + k)
  let ordinaryGates := gates.filter (fun k => n + k ∉ special)
  let used := (Finset.range n).filter (fun w => 0 < reads w)
  let multiple := (Finset.range n).filter (fun w => 2 ≤ reads w)
  let once := (Finset.range n).filter (fun w => reads w = 1)
  let excess := C.size-neg.card+1-used.card
  let tree := fun (S E : Finset ℕ) => ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
    region ⊆ ordinaryGates ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w)
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  0 < C.size → C.output + 1 = n + C.size →
  (∀ j < C.size, j + 1 < C.size → 0 < reads (n + j)) →
  ∀ (p c : ℕ) (H : Finset ℕ), 0 < p → H ⊆ Finset.range n →
    (∀ w < n, reads w = 0 → w ∈ H) →
    (∀ S : Finset ℕ, S ⊆ once → tree S ∅ → (S \ H).card ≤ p) →
    (∀ (S : Finset ℕ) (b : ℕ), S ⊆ once → tree S {b} → (S \ H).card ≤ c) →
    n + (2*p-1)*multiple.card ≤
      (2*p+4*c)*excess + (p+2*c)*neg.card + p + H.card := by
  intro n C gates gate reads neg special ordinaryGates used multiple once excess tree
    hgates hRB hpos hout hnonout p c H hp hHsub hHunused hp_bd hc_bd
  classical
  have hgate_mem : ∀ k ∈ gates, gate k ∈ C.gates := by
    intro k hk
    have hklt : k < C.gates.length := Finset.mem_range.mp hk
    dsimp only [gate, PEqualNP.MetaComplexity.NestedCover.gateAt]
    rw [List.getD_eq_getElem _ _ hklt]
    exact List.getElem_mem hklt
  have hgate_len : ∀ k ∈ gates, (gate k).inputs.length = if k ∈ neg then 1 else 2 := by
    intro k hk
    have hgk := hgates (gate k) (hgate_mem k hk)
    by_cases hkn : k ∈ neg
    · simp only [hkn, ite_true]
      have hop : (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not := (Finset.mem_filter.mp hkn).2
      rcases hgk with ⟨hor | hor, _⟩ | ⟨_, hlen⟩
      · rw [hop] at hor; cases hor
      · rw [hop] at hor; cases hor
      · exact hlen
    · simp only [hkn, ite_false]
      have hne : (gate k).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := fun h =>
        hkn (Finset.mem_filter.mpr ⟨hk, h⟩)
      rcases hgk with ⟨_, hlen⟩ | ⟨hop, _⟩
      · exact hlen
      · exact absurd hop hne
  have hneg_sub : neg ⊆ gates := Finset.filter_subset _ _
  have hord_sub : ordinaryGates ⊆ gates := Finset.filter_subset _ _
  have hbin_ord : ∀ k ∈ ordinaryGates,
      ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate k).inputs.length = 2 := by
    intro k hk
    have hkg : k ∈ gates := hord_sub hk
    have hns : n + k ∉ special := (Finset.mem_filter.mp hk).2
    have hnn : k ∉ neg := fun h => hns (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
    have hgk := hgates (gate k) (hgate_mem k hkg)
    rcases hgk with h1 | ⟨hop, _⟩
    · exact h1
    · exact absurd (Finset.mem_filter.mpr ⟨hkg, hop⟩) hnn
  have htot_reads : ∑ w ∈ Finset.range (n + C.size), reads w = 2 * C.size - neg.card := by
    rw [PEqualNP.Outside.L_meta_25796_aux.sum_readsIn_all hRB gates (Finset.Subset.refl _)]
    have hsum : ∑ k ∈ gates, (gate k).inputs.length =
        ∑ k ∈ neg, 1 + ∑ k ∈ gates \ neg, 2 := by
      have hdisj : Disjoint neg (gates \ neg) := Finset.disjoint_sdiff
      have hu : neg ∪ (gates \ neg) = gates := Finset.union_sdiff_of_subset hneg_sub
      conv_lhs => rw [← hu, Finset.sum_union hdisj]
      congr 1
      · apply Finset.sum_congr rfl; intro k hk; rw [hgate_len k (hneg_sub hk)]; simp [hk]
      · apply Finset.sum_congr rfl; intro k hk
        rcases Finset.mem_sdiff.mp hk with ⟨hkg, hnn⟩
        rw [hgate_len k hkg]; simp [hnn]
    rw [hsum]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    have hcard_sdiff : (gates \ neg).card = C.size - neg.card := by
      rw [Finset.card_sdiff_of_subset hneg_sub, Finset.card_range]
    have hneg_le : neg.card ≤ C.size := by
      have := Finset.card_le_card hneg_sub; rwa [Finset.card_range] at this
    rw [hcard_sdiff]
    omega
  have hout_reads : reads (n + (C.size - 1)) = 0 := by
    rw [PEqualNP.Outside.L_meta_25796_aux.readsIn_zero_iff]
    intro k hk hmem
    have hlt := hRB k (Finset.mem_range.mp hk) (n + (C.size - 1)) hmem
    have hklt : k < C.size := Finset.mem_range.mp hk
    omega
  have hpos_wires : (Finset.range (n + C.size)).filter (fun w => 0 < reads w) =
      used ∪ (Finset.range (C.size - 1)).image (fun j => n + j) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image, used]
    constructor
    · rintro ⟨hw, hposw⟩
      by_cases hwn : w < n
      · exact Or.inl ⟨hwn, hposw⟩
      · right
        refine ⟨w - n, ?_, by omega⟩
        by_contra hge
        have heq : w = n + (C.size - 1) := by omega
        rw [heq, hout_reads] at hposw
        omega
    · rintro (⟨hwn, hposw⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨by omega, hposw⟩
      · exact ⟨by omega, hnonout j (by omega) (by omega)⟩
  have hpos_card : ((Finset.range (n + C.size)).filter (fun w => 0 < reads w)).card =
      used.card + (C.size - 1) := by
    rw [hpos_wires, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun _ _ h => by omega),
        Finset.card_range]
    rw [Finset.disjoint_left]
    intro w h1 h2
    have hwn : w < n := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    rcases Finset.mem_image.mp h2 with ⟨j, _, rfl⟩
    omega
  set R := ∑ w ∈ Finset.range (n + C.size), (reads w - 1)
  have hreads_decomp : ∑ w ∈ Finset.range (n + C.size), reads w =
      ((Finset.range (n + C.size)).filter (fun w => 0 < reads w)).card + R := by
    have hpt : ∀ w ∈ Finset.range (n + C.size),
        reads w = (if 0 < reads w then 1 else 0) + (reads w - 1) := by
      intro w _
      by_cases h : 0 < reads w <;> simp [h] <;> omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_boole, Nat.cast_id]
  have hneg_le : neg.card ≤ C.size := by
    have := Finset.card_le_card hneg_sub; rwa [Finset.card_range] at this
  have hR_eq : R = excess := by
    dsimp only [excess]
    rw [hpos_card] at hreads_decomp
    omega
  have hused_le : used.card ≤ C.size - neg.card + 1 := by
    rw [hpos_card] at hreads_decomp
    omega
  set specialGates := gates.filter (fun k => n + k ∈ special)
  set g := specialGates.card
  set u := multiple.card
  set t := neg.card
  set d := excess
  set e := ∑ k ∈ ordinaryGates, (gate k).inputs.countP (fun w => decide (w ∈ special))
  set x := ∑ k ∈ specialGates, (gate k).inputs.countP (fun w => decide (w ∉ special))
  have hneg_sub_sg : neg ⊆ specialGates := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨hneg_sub hk, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)⟩
  have hineqA : x + t ≤ 2 * g := by
    have hx_le : x ≤ ∑ k ∈ specialGates, (gate k).inputs.length := by
      dsimp only [x]
      apply Finset.sum_le_sum
      intro k _
      exact List.countP_le_length
    have hsum_sg : ∑ k ∈ specialGates, (gate k).inputs.length = 2 * g - t := by
      have hdisj : Disjoint neg (specialGates \ neg) := Finset.disjoint_sdiff
      have hu : neg ∪ (specialGates \ neg) = specialGates := Finset.union_sdiff_of_subset hneg_sub_sg
      conv_lhs => rw [← hu, Finset.sum_union hdisj]
      have s1 : ∑ k ∈ neg, (gate k).inputs.length = t := by
        have hpt : ∀ k ∈ neg, (gate k).inputs.length = 1 := fun k hk => by
          rw [hgate_len k (hneg_sub hk)]; simp [hk]
        rw [Finset.sum_congr rfl hpt]; simp [t]
      have s2 : ∑ k ∈ specialGates \ neg, (gate k).inputs.length = 2 * (g - t) := by
        have hpt : ∀ k ∈ specialGates \ neg, (gate k).inputs.length = 2 := fun k hk => by
          rcases Finset.mem_sdiff.mp hk with ⟨hks, hnn⟩
          rw [hgate_len k (Finset.mem_filter.mp hks).1]; simp [hnn]
        rw [Finset.sum_congr rfl hpt]
        simp only [Finset.sum_const, smul_eq_mul]
        rw [Finset.card_sdiff_of_subset hneg_sub_sg]
        ring
      have ht_le_g : t ≤ g := Finset.card_le_card hneg_sub_sg
      rw [s1, s2]
      omega
    have ht_le_g : t ≤ g := Finset.card_le_card hneg_sub_sg
    omega
  have hspec_sub : special ⊆ Finset.range (n + C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h1 | h2
    · exact (Finset.mem_filter.mp h1).1
    · rcases Finset.mem_image.mp h2 with ⟨k, hk, rfl⟩
      have := Finset.mem_range.mp (hneg_sub hk)
      exact Finset.mem_range.mpr (by omega)
  have hspec_card : special.card = u + g := by
    have hpart : special = multiple ∪ specialGates.image (fun k => n + k) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_image, multiple, specialGates, gates, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · intro hw
        have hwlt : w < n + C.size := Finset.mem_range.mp (hspec_sub hw)
        by_cases hwn : w < n
        · left
          refine ⟨hwn, ?_⟩
          rcases Finset.mem_union.mp hw with h1 | h2
          · exact (Finset.mem_filter.mp h1).2
          · rcases Finset.mem_image.mp h2 with ⟨k, _, heq⟩; omega
        · right
          exact ⟨w - n, ⟨by omega, by rwa [show n + (w - n) = w by omega]⟩, by omega⟩
      · rintro (⟨hwn, hr2⟩ | ⟨k, ⟨_, hsp⟩, rfl⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr2⟩)
        · exact hsp
    rw [hpart, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun _ _ h => by omega)]
    rw [Finset.disjoint_left]
    intro w h1 h2
    have hwn : w < n := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
    omega
  have hineqB : g + u ≤ d + t := by
    set shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
    have h1 : special.card ≤ shared.card + (neg.image (fun k => n + k)).card :=
      Finset.card_union_le _ _
    have h2 : (neg.image (fun k => n + k)).card ≤ t := Finset.card_image_le
    have h3 : shared.card ≤ R := by
      have hle1 : shared.card = ∑ _w ∈ shared, 1 := by simp
      rw [hle1]
      calc ∑ _w ∈ shared, 1
          ≤ ∑ w ∈ shared, (reads w - 1) := by
            apply Finset.sum_le_sum; intro w hw
            have := (Finset.mem_filter.mp hw).2; omega
        _ ≤ ∑ w ∈ Finset.range (n + C.size), (reads w - 1) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    rw [hspec_card] at h1
    omega
  have hineqC : e ≤ d + u + g := by
    have he_eq : e = ∑ w ∈ special, PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates w :=
      (PEqualNP.Outside.L_meta_25796_aux.sum_readsIn_eq_sum_countP C ordinaryGates special).symm
    have hle1 : e ≤ ∑ w ∈ special, reads w := by
      rw [he_eq]
      apply Finset.sum_le_sum
      intro w _
      exact PEqualNP.Outside.L_meta_25796_aux.readsIn_mono hord_sub w
    have hle2 : ∑ w ∈ special, reads w ≤ (∑ w ∈ special, (reads w - 1)) + special.card := by
      calc ∑ w ∈ special, reads w
          ≤ ∑ w ∈ special, ((reads w - 1) + 1) := by
            apply Finset.sum_le_sum; intro w _; omega
        _ = (∑ w ∈ special, (reads w - 1)) + ∑ _w ∈ special, 1 := Finset.sum_add_distrib
        _ = (∑ w ∈ special, (reads w - 1)) + special.card := by simp
    have hle3 : ∑ w ∈ special, (reads w - 1) ≤ R :=
      Finset.sum_le_sum_of_subset hspec_sub
    omega
  set OrdWires := once ∪ ordinaryGates.image (fun k => n + k)
  set Roots := OrdWires.filter (fun w => PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates w = 0)
  have hord_read_le : ∀ w ∈ OrdWires, reads w ≤ 1 := by
    intro w hw
    rcases Finset.mem_union.mp hw with h1 | h2
    · have := (Finset.mem_filter.mp h1).2; omega
    · rcases Finset.mem_image.mp h2 with ⟨k, hk, rfl⟩
      have hns : n + k ∉ special := (Finset.mem_filter.mp hk).2
      have hklt : k < C.size := Finset.mem_range.mp (hord_sub hk)
      by_contra hgt
      apply hns
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩)
  have hord_nonout_eq1 : ∀ w ∈ OrdWires, w ≠ C.output → reads w = 1 := by
    intro w hw hne
    rcases Finset.mem_union.mp hw with h1 | h2
    · exact (Finset.mem_filter.mp h1).2
    · rcases Finset.mem_image.mp h2 with ⟨k, hk, rfl⟩
      have hklt : k < C.size := Finset.mem_range.mp (hord_sub hk)
      have hposw : 0 < reads (n + k) := hnonout k hklt (by omega)
      have hle1 := hord_read_le (n + k) hw
      omega
  have hord_disj_spec : ∀ w ∈ OrdWires, w ∉ special := by
    intro w hw hsp
    rcases Finset.mem_union.mp hw with h1 | h2
    · have hwn : w < n := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
      have hr1 : reads w = 1 := (Finset.mem_filter.mp h1).2
      rcases Finset.mem_union.mp hsp with hsp1 | hsp2
      · have := (Finset.mem_filter.mp hsp1).2; omega
      · rcases Finset.mem_image.mp hsp2 with ⟨k, _, heq⟩; omega
    · rcases Finset.mem_image.mp h2 with ⟨k, hk, rfl⟩
      exact (Finset.mem_filter.mp hk).2 hsp
  have hdisj_ord_sg : Disjoint ordinaryGates specialGates := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  have hunion_ord_sg : ordinaryGates ∪ specialGates = gates := by
    ext k
    simp only [Finset.mem_union, ordinaryGates, specialGates, Finset.mem_filter]
    tauto
  have hRoots_le : Roots.card ≤ x + 1 := by
    have hsub : Roots \ {C.output} ⊆ OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w) := by
      intro w hw
      rcases Finset.mem_sdiff.mp hw with ⟨hwR, hne⟩
      rcases Finset.mem_filter.mp hwR with ⟨hwO, hr0⟩
      refine Finset.mem_filter.mpr ⟨hwO, ?_⟩
      have hr1 : reads w = 1 := hord_nonout_eq1 w hwO (by simpa using hne)
      have htot := PEqualNP.Outside.L_meta_25796_aux.readsIn_union (C := C) hdisj_ord_sg w
      rw [hunion_ord_sg] at htot
      change reads w = PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates w +
        PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w at htot
      omega
    have hcard1 : (Roots \ {C.output}).card ≤ x := by
      calc (Roots \ {C.output}).card
          ≤ (OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w)).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ w ∈ OrdWires, PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w := by
            have h1 : (OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w)).card =
                ∑ _w ∈ OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w), 1 := by simp
            rw [h1]
            calc ∑ _w ∈ OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w), 1
                ≤ ∑ w ∈ OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w),
                    PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w := by
                  apply Finset.sum_le_sum; intro w hw
                  exact (Finset.mem_filter.mp hw).2
              _ ≤ ∑ w ∈ OrdWires, PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w :=
                  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = ∑ k ∈ specialGates, (gate k).inputs.countP (fun w => decide (w ∈ OrdWires)) :=
            PEqualNP.Outside.L_meta_25796_aux.sum_readsIn_eq_sum_countP C specialGates OrdWires
        _ ≤ x := by
            dsimp only [x]
            apply Finset.sum_le_sum
            intro k _
            apply List.countP_mono_left
            intro w _ hw
            have hwO : w ∈ OrdWires := by simpa using hw
            simpa using hord_disj_spec w hwO
    have hcard2 : Roots.card ≤ (Roots \ {C.output}).card + 1 := by
      have := Finset.card_le_card (show Roots ⊆ (Roots \ {C.output}) ∪ {C.output} from
        fun w hw => by by_cases h : w = C.output <;> simp [hw, h])
      exact le_trans this (by simpa using Finset.card_union_le (Roots \ {C.output}) {C.output})
    omega
  have hord_reads_le1 : ∀ w ∈ OrdWires, PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates w ≤ 1 :=
    fun w hw => le_trans (PEqualNP.Outside.L_meta_25796_aux.readsIn_mono hord_sub w) (hord_read_le w hw)
  have hcover_ord : ∀ w ∈ OrdWires, ∃ r ∈ Roots, w ∈ PEqualNP.Outside.L_meta_25796_aux.subWires n C ordinaryGates OrdWires r := by
    have hdown : ∀ (m : ℕ) (w : ℕ), w ∈ OrdWires → n + C.size - w = m →
        ∃ r ∈ Roots, w ∈ PEqualNP.Outside.L_meta_25796_aux.subWires n C ordinaryGates OrdWires r := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro w hw hm
        by_cases hr0 : PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates w = 0
        · exact ⟨w, Finset.mem_filter.mpr ⟨hw, hr0⟩, PEqualNP.Outside.L_meta_25796_aux.mem_subWires_self hw⟩
        · rcases PEqualNP.Outside.L_meta_25796_aux.readsIn_pos_iff.mp (Nat.pos_of_ne_zero hr0) with ⟨k, hk, hwk⟩
          have hklt : k < C.size := Finset.mem_range.mp (hord_sub hk)
          have hlt : w < n + k := hRB k hklt w hwk
          have hnkO : n + k ∈ OrdWires := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
          rcases ih (n + C.size - (n + k)) (by omega) (n + k) hnkO rfl with ⟨r, hrR, hnk_in⟩
          exact ⟨r, hrR, PEqualNP.Outside.L_meta_25796_aux.subWires_closed_down hRB hord_sub hk hnk_in w hwk hw⟩
    intro w hw
    exact hdown (n + C.size - w) w hw rfl
  let Wr : ℕ → Finset ℕ := fun r => PEqualNP.Outside.L_meta_25796_aux.subWires n C ordinaryGates OrdWires r
  let Gr : ℕ → Finset ℕ := fun r => ordinaryGates.filter (fun k => n + k ∈ Wr r)
  let Sr : ℕ → Finset ℕ := fun r => once.filter (fun w => w ∈ Wr r)
  have hWr_disj : ∀ r₁ ∈ Roots, ∀ r₂ ∈ Roots, r₁ ≠ r₂ → Disjoint (Wr r₁) (Wr r₂) := by
    intro r₁ hr₁ r₂ hr₂ hne
    have hnot : ∀ a ∈ Roots, ∀ b ∈ Roots, a ≠ b → a ∉ Wr b := by
      intro a ha b _ hab haWb
      rcases PEqualNP.Outside.L_meta_25796_aux.mem_subWires_ne_has_parent hRB hord_sub haWb hab with
        ⟨k, hk, _, hak⟩
      have hposa : 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates a :=
        PEqualNP.Outside.L_meta_25796_aux.readsIn_pos_iff.mpr ⟨k, hk, hak⟩
      have h0a := (Finset.mem_filter.mp ha).2
      omega
    exact PEqualNP.Outside.L_meta_25796_aux.subWires_disjoint hRB hord_sub hord_reads_le1
      (hnot r₁ hr₁ r₂ hr₂ hne) (hnot r₂ hr₂ r₁ hr₁ hne.symm)
  have hGr_disj : Set.PairwiseDisjoint (Roots : Set ℕ) Gr := by
    intro r₁ hr₁ r₂ hr₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro k hk1 hk2
    exact Finset.disjoint_left.mp (hWr_disj r₁ hr₁ r₂ hr₂ hne)
      (Finset.mem_filter.mp hk1).2 (Finset.mem_filter.mp hk2).2
  have honce_lt : ∀ w ∈ once, w < n := fun w hw => Finset.mem_range.mp (Finset.mem_filter.mp hw).1
  have htree_bd : ∀ r ∈ Roots,
      (Sr r \ H).card ≤ p + 2 * c * PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r) := by
    intro r hrR
    have hrO : r ∈ OrdWires := (Finset.mem_filter.mp hrR).1
    have hct := PEqualNP.Outside.L_meta_25796_aux.subWires_cutTree hRB hord_sub honce_lt
      (Finset.Subset.refl _) (Finset.Subset.refl _) hord_reads_le1
      (fun w hw hr1 => by
        have hne : w ≠ C.output := by
          intro h; subst h
          have h0 : reads C.output = 0 := by rw [show C.output = n + (C.size - 1) by omega]; exact hout_reads
          have hle := PEqualNP.Outside.L_meta_25796_aux.readsIn_mono (C := C) hord_sub C.output
          change PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates C.output ≤ reads C.output at hle
          omega
        exact ⟨hord_nonout_eq1 w hw hne, hne.symm⟩) hrO
    have hWr_eq : Wr r = Sr r ∪ (Gr r).image (fun k => n + k) :=
      PEqualNP.Outside.L_meta_25796_aux.subWires_mem_partition honce_lt rfl r
    have hbd := PEqualNP.Outside.L_meta_25796_aux.cutTree_leaf_bound hRB hord_sub hbin_ord honce_lt
      hp_bd hc_bd (PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r))
      (Gr r) (Sr r) r hct (by rw [← hWr_eq])
    by_cases h0 : PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r) = 0
    · simp only [h0, ite_true] at hbd; omega
    · simp only [h0, ite_false] at hbd
      have h1 : c * (2 * PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r) - 1) ≤
          2 * c * PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r) := by
        calc c * (2 * PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r) - 1)
            ≤ c * (2 * PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r)) :=
              Nat.mul_le_mul_left c (Nat.sub_le _ _)
          _ = 2 * c * PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r) := by ring
      omega
  have hext_le_e : ∑ r ∈ Roots, PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r) ≤ e := by
    have hpt : ∀ r ∈ Roots, PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r) ≤
        ∑ k ∈ Gr r, (gate k).inputs.countP (fun w => decide (w ∈ special)) := by
      intro r _
      unfold PEqualNP.Outside.L_meta_25796_aux.extSlots
      apply Finset.sum_le_sum
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkO, hnkWr⟩
      apply List.countP_mono_left
      intro w hw hnw
      have hnw' : w ∉ Wr r := by simpa using hnw
      have hnwO : w ∉ OrdWires := fun h => hnw' (PEqualNP.Outside.L_meta_25796_aux.subWires_closed_down hRB hord_sub hkO hnkWr w hw h)
      have hwlt : w < n + C.size := by
        have hklt : k < C.size := Finset.mem_range.mp (hord_sub hkO)
        have := hRB k hklt w hw; omega
      have hposw : 0 < reads w := PEqualNP.Outside.L_meta_25796_aux.readsIn_pos_iff.mpr ⟨k, hord_sub hkO, hw⟩
      have hwsp : w ∈ special := by
        by_cases hwn : w < n
        · have hge2 : 2 ≤ reads w := by
            by_contra hlt2
            have hr1 : reads w = 1 := by omega
            exact hnwO (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwn, hr1⟩))
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwlt, hge2⟩)
        · by_contra hnsp
          have hkg : w - n ∈ gates := Finset.mem_range.mpr (by omega)
          have hkord : w - n ∈ ordinaryGates :=
            Finset.mem_filter.mpr ⟨hkg, by rwa [show n + (w - n) = w by omega]⟩
          exact hnwO (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w - n, hkord, by omega⟩))
      simpa using hwsp
    calc ∑ r ∈ Roots, PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r)
        ≤ ∑ r ∈ Roots, ∑ k ∈ Gr r, (gate k).inputs.countP (fun w => decide (w ∈ special)) :=
          Finset.sum_le_sum hpt
      _ = ∑ k ∈ Roots.biUnion Gr, (gate k).inputs.countP (fun w => decide (w ∈ special)) :=
          (Finset.sum_biUnion hGr_disj).symm
      _ ≤ e := Finset.sum_le_sum_of_subset (Finset.biUnion_subset.mpr (fun r _ => Finset.filter_subset _ _))
  have honceH_le : (once \ H).card ≤ p * (x + 1) + 2 * c * e := by
    have hsub : once \ H ⊆ Roots.biUnion (fun r => Sr r \ H) := by
      intro w hw
      rcases Finset.mem_sdiff.mp hw with ⟨hw1, hwH⟩
      rcases hcover_ord w (Finset.mem_union_left _ hw1) with ⟨r, hrR, hwWr⟩
      exact Finset.mem_biUnion.mpr ⟨r, hrR, Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hw1, hwWr⟩, hwH⟩⟩
    calc (once \ H).card
        ≤ (Roots.biUnion (fun r => Sr r \ H)).card := Finset.card_le_card hsub
      _ ≤ ∑ r ∈ Roots, (Sr r \ H).card := Finset.card_biUnion_le
      _ ≤ ∑ r ∈ Roots, (p + 2 * c * PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r)) :=
          Finset.sum_le_sum htree_bd
      _ = Roots.card * p + 2 * c * ∑ r ∈ Roots, PEqualNP.Outside.L_meta_25796_aux.extSlots C (Gr r) (Wr r) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum]
      _ ≤ (x + 1) * p + 2 * c * e := by
          have h1 := Nat.mul_le_mul_right p hRoots_le
          have h2 := Nat.mul_le_mul_left (2 * c) hext_le_e
          omega
      _ = p * (x + 1) + 2 * c * e := by ring
  have hn_le : n ≤ H.card + u + (once \ H).card := by
    have hsub : Finset.range n ⊆ H ∪ multiple ∪ (once \ H) := by
      intro w hw
      have hwn : w < n := Finset.mem_range.mp hw
      by_cases hwH : w ∈ H
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hwH)
      · by_cases hr0 : reads w = 0
        · exact absurd (hHunused w hwn hr0) hwH
        · by_cases hr1 : reads w = 1
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hw, hr1⟩, hwH⟩)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hw, by omega⟩))
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have h2 := Finset.card_union_le (H ∪ multiple) (once \ H)
    have h3 := Finset.card_union_le H multiple
    omega
  have hmain0 : n ≤ H.card + u + p * (x + 1) + 2 * c * e := by omega
  have hpx : p * x + p * t ≤ 2 * p * g := by
    calc p * x + p * t = p * (x + t) := (Nat.mul_add p x t).symm
      _ ≤ p * (2 * g) := Nat.mul_le_mul_left p hineqA
      _ = 2 * p * g := by ring
  have hce : 2 * c * e ≤ 2 * c * d + 2 * c * u + 2 * c * g := by
    calc 2 * c * e ≤ 2 * c * (d + u + g) := Nat.mul_le_mul_left (2 * c) hineqC
      _ = 2 * c * d + 2 * c * u + 2 * c * g := by ring
  have hgu : (2 * p + 2 * c) * g + (2 * p + 2 * c) * u ≤ (2 * p + 2 * c) * d + (2 * p + 2 * c) * t := by
    calc (2 * p + 2 * c) * g + (2 * p + 2 * c) * u
        = (2 * p + 2 * c) * (g + u) := (Nat.mul_add _ g u).symm
      _ ≤ (2 * p + 2 * c) * (d + t) := Nat.mul_le_mul_left _ hineqB
      _ = (2 * p + 2 * c) * d + (2 * p + 2 * c) * t := Nat.mul_add _ d t
  have hu_id : (2 * p - 1) * u + u = 2 * p * u := by
    have : 2 * p - 1 + 1 = 2 * p := by omega
    calc (2 * p - 1) * u + u = (2 * p - 1 + 1) * u := by ring
      _ = 2 * p * u := by rw [this]
  have hstep1 : n + (2 * p - 1) * u + p * t ≤
      H.card + p + 2 * c * d + (2 * p + 2 * c) * g + (2 * p + 2 * c) * u := by
    have hx1 : p * (x + 1) = p * x + p := by ring
    have hg1 : 2 * p * g + 2 * c * g = (2 * p + 2 * c) * g := by ring
    have hu1 : 2 * p * u + 2 * c * u = (2 * p + 2 * c) * u := by ring
    omega
  have hstep2 : (2 * p + 4 * c) * d = 2 * c * d + (2 * p + 2 * c) * d := by ring
  have hstep3 : (p + 2 * c) * t + p * t = (2 * p + 2 * c) * t := by ring
  omega
