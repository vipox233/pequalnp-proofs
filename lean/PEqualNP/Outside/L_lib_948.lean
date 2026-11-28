import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

namespace PEqualNP.Outside.L_lib_948

def Rows (n : Nat) := Finset (Finset (Fin n))

def cores {n : Nat} (H : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  ((H.product H).image (fun z => z.1 ∩ z.2)).filter (fun c => c.card = 2)

def ordinary {n : Nat} (H : Finset (Finset (Fin n))) : Finset (Fin n) :=
  Finset.univ \ (cores H).biUnion id

def base {n : Nat} (H : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  H.filter (fun R => R ⊆ ordinary H)

def outer {n : Nat} (H : Finset (Finset (Fin n))) (c : Finset (Fin n)) : Finset (Fin n) :=
  (H.filter (fun R => c ⊆ R)).biUnion id \ c

def step {n : Nat} (B : Finset (Finset (Fin n))) (V : Finset (Fin n)) : Finset (Fin n) :=
  V ∪ (B.filter (fun R => ¬ Disjoint R V)).biUnion id

def component {n : Nat} (H : Finset (Finset (Fin n))) (u : Fin n) : Finset (Fin n) :=
  (List.range n).foldl (fun V _ => step (base H) V) {u}

def parts {n : Nat} (H : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (ordinary H).image (component H)

def tests {n : Nat} (H : Finset (Finset (Fin n))) (C : Finset (Fin n)) : Nat :=
  ((base H).filter (fun R => R ⊆ C)).card

def trees {n : Nat} (H : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (parts H).filter (fun C => C.card = 2 * tests H C + 1)

def cycles {n : Nat} (H : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (parts H).filter (fun C => C.card = 2 * tests H C)

abbrev bad {n : Nat} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ C ∈ parts H, C.card < 2 * tests H C

def baseSize {n : Nat} (H : Finset (Finset (Fin n))) : Nat :=
  (base H).card + (cores H).card

def weight {n : Nat} (H : Finset (Finset (Fin n))) (edge : Finset (Finset (Fin n))) : Nat :=
  edge.prod Finset.card +
    2 * ((cores H).filter (fun c => (outer H c).image (component H) = edge)).card

def candidates {n : Nat} (H : Finset (Finset (Fin n))) :
    Finset (Finset (Finset (Finset (Fin n)))) :=
  ((trees H).powersetCard 2).powerset.filter (fun Q =>
    ∀ g ∈ Q, ∀ h ∈ Q, g ≠ h → Disjoint g h)

abbrev Valid {n : Nat} (H : Finset (Finset (Fin n))) (M : Finset (Finset (Fin n))) : Prop :=
  (∀ g ∈ M, g.card = 2) ∧
  (∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h) ∧
  (∀ R ∈ H, ∃ g ∈ M, g ⊆ R)

def rowsOf {n : Nat} (H : Finset (Finset (Fin n))) (c : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  H.filter (fun R => c ⊆ R)

def baseC {n : Nat} (H : Finset (Finset (Fin n))) (C : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (base H).filter (fun R => R ⊆ C)

lemma mem_cores_iff {n : Nat} {H : Finset (Finset (Fin n))} (hH3 : ∀ R ∈ H, R.card = 3)
    {c : Finset (Fin n)} :
    c ∈ cores H ↔ c.card = 2 ∧ ∃ R₁ ∈ H, ∃ R₂ ∈ H, R₁ ≠ R₂ ∧ R₁ ∩ R₂ = c := by
  simp only [cores, Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_image,
    Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨⟨R₁, R₂, ⟨h1, h2⟩, rfl⟩, hc⟩
    refine ⟨hc, R₁, h1, R₂, h2, ?_, rfl⟩
    intro heq
    subst heq
    rw [Finset.inter_self, hH3 R₁ h1] at hc
    omega
  · rintro ⟨hc, R₁, h1, R₂, h2, _, rfl⟩
    exact ⟨⟨R₁, R₂, ⟨h1, h2⟩, rfl⟩, hc⟩

lemma rowsOf_card_and_eq {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c : Finset (Fin n)} (hc : c ∈ cores H) :
    (rowsOf H c).card = 2 ∧ ∀ u ∈ c, H.filter (fun R => u ∈ R) = rowsOf H c := by
  rcases (mem_cores_iff hH3).mp hc with ⟨hcc, R₁, h1, R₂, h2, hne, hinter⟩
  have hsub1 : c ⊆ R₁ := hinter ▸ Finset.inter_subset_left
  have hsub2 : c ⊆ R₂ := hinter ▸ Finset.inter_subset_right
  have h1m : R₁ ∈ rowsOf H c := Finset.mem_filter.mpr ⟨h1, hsub1⟩
  have h2m : R₂ ∈ rowsOf H c := Finset.mem_filter.mpr ⟨h2, hsub2⟩
  have hge : 2 ≤ (rowsOf H c).card := by
    have hpair : ({R₁, R₂} : Finset _) ⊆ rowsOf H c := by
      intro R hR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl <;> assumption
    have hpc : ({R₁, R₂} : Finset _).card = 2 := Finset.card_pair hne
    exact hpc ▸ Finset.card_le_card hpair
  have hsub_u : ∀ u ∈ c, rowsOf H c ⊆ H.filter (fun R => u ∈ R) := by
    intro u hu R hR
    simp only [rowsOf, Finset.mem_filter] at hR ⊢
    exact ⟨hR.1, hR.2 hu⟩
  obtain ⟨u₀, hu₀⟩ : c.Nonempty := Finset.card_pos.mp (by omega)
  have hle : (rowsOf H c).card ≤ 2 :=
    (Finset.card_le_card (hsub_u u₀ hu₀)).trans (hdeg u₀)
  have hcard : (rowsOf H c).card = 2 := le_antisymm hle hge
  refine ⟨hcard, fun u hu => ?_⟩
  exact (Finset.eq_of_subset_of_card_le (hsub_u u hu) (by rw [hcard]; exact hdeg u)).symm

lemma cores_pairwise_disjoint {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c₁ c₂ : Finset (Fin n)} (h1 : c₁ ∈ cores H) (h2 : c₂ ∈ cores H) (hne : c₁ ≠ c₂) :
    Disjoint c₁ c₂ := by
  rw [Finset.disjoint_left]
  intro u hu1 hu2
  apply hne
  have eq1 := (rowsOf_card_and_eq hH3 hdeg h1).2 u hu1
  have eq2 := (rowsOf_card_and_eq hH3 hdeg h2).2 u hu2
  have hrows : rowsOf H c₁ = rowsOf H c₂ := eq1.symm.trans eq2
  have hc1 := ((mem_cores_iff hH3).mp h1).1
  have hc2 := ((mem_cores_iff hH3).mp h2).1
  rcases Finset.card_eq_two.mp (rowsOf_card_and_eq hH3 hdeg h1).1 with ⟨R₁, R₂, hRne, hReq⟩
  have hR1m : R₁ ∈ rowsOf H c₁ := by rw [hReq]; simp
  have hR2m : R₂ ∈ rowsOf H c₁ := by rw [hReq]; simp
  have hR1H : R₁ ∈ H := (Finset.mem_filter.mp hR1m).1
  have hR2H : R₂ ∈ H := (Finset.mem_filter.mp hR2m).1
  have h1sub : c₁ ⊆ R₁ ∩ R₂ :=
    Finset.subset_inter (Finset.mem_filter.mp hR1m).2 (Finset.mem_filter.mp hR2m).2
  have h2sub : c₂ ⊆ R₁ ∩ R₂ := by
    rw [hrows] at hR1m hR2m
    exact Finset.subset_inter (Finset.mem_filter.mp hR1m).2 (Finset.mem_filter.mp hR2m).2
  have hinter_le : (R₁ ∩ R₂).card ≤ 2 := by
    by_contra hgt
    have hge3 : 3 ≤ (R₁ ∩ R₂).card := by omega
    have heq1 : R₁ ∩ R₂ = R₁ :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [hH3 R₁ hR1H]; exact hge3)
    have heq2 : R₁ ∩ R₂ = R₂ :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [hH3 R₂ hR2H]; exact hge3)
    exact hRne (heq1.symm.trans heq2)
  have e1 : c₁ = R₁ ∩ R₂ := Finset.eq_of_subset_of_card_le h1sub (by rw [hc1]; exact hinter_le)
  have e2 : c₂ = R₁ ∩ R₂ := Finset.eq_of_subset_of_card_le h2sub (by rw [hc2]; exact hinter_le)
  exact e1.trans e2.symm

lemma core_unique_of_subset {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {R c₁ c₂ : Finset (Fin n)} (hR : R ∈ H)
    (h1 : c₁ ∈ cores H) (h2 : c₂ ∈ cores H) (hs1 : c₁ ⊆ R) (hs2 : c₂ ⊆ R) : c₁ = c₂ := by
  by_contra hne
  have hdisj := cores_pairwise_disjoint hH3 hdeg h1 h2 hne
  have hunion : (c₁ ∪ c₂).card ≤ R.card := Finset.card_le_card (Finset.union_subset hs1 hs2)
  rw [Finset.card_union_of_disjoint hdisj, ((mem_cores_iff hH3).mp h1).1,
      ((mem_cores_iff hH3).mp h2).1, hH3 R hR] at hunion
  omega

lemma mem_base_or_exists_core {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {R : Finset (Fin n)} (hR : R ∈ H) :
    R ∈ base H ∨ ∃ c ∈ cores H, c ⊆ R := by
  by_cases hsub : R ⊆ ordinary H
  · exact Or.inl (Finset.mem_filter.mpr ⟨hR, hsub⟩)
  · right
    rw [Finset.not_subset] at hsub
    rcases hsub with ⟨u, huR, huord⟩
    simp only [ordinary, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not,
      Finset.mem_biUnion, id_eq] at huord
    rcases huord with ⟨c, hc, huc⟩
    have hRmem : R ∈ rowsOf H c := by
      rw [← (rowsOf_card_and_eq hH3 hdeg hc).2 u huc]
      exact Finset.mem_filter.mpr ⟨hR, huR⟩
    exact ⟨c, hc, (Finset.mem_filter.mp hRmem).2⟩

lemma core_structure {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c : Finset (Fin n)} (hc : c ∈ cores H) :
    ∃ x y, x ≠ y ∧ x ∈ ordinary H ∧ y ∈ ordinary H ∧
      outer H c = {x, y} ∧ rowsOf H c = {insert x c, insert y c} := by
  have hcc := ((mem_cores_iff hH3).mp hc).1
  rcases Finset.card_eq_two.mp (rowsOf_card_and_eq hH3 hdeg hc).1 with ⟨R₁, R₂, hRne, hReq⟩
  have hR1m : R₁ ∈ rowsOf H c := by rw [hReq]; simp
  have hR2m : R₂ ∈ rowsOf H c := by rw [hReq]; simp
  have hR1H : R₁ ∈ H := (Finset.mem_filter.mp hR1m).1
  have hR2H : R₂ ∈ H := (Finset.mem_filter.mp hR2m).1
  have hc1 : c ⊆ R₁ := (Finset.mem_filter.mp hR1m).2
  have hc2 : c ⊆ R₂ := (Finset.mem_filter.mp hR2m).2
  have h1diff : (R₁ \ c).card = 1 := by
    rw [Finset.card_sdiff_of_subset hc1, hH3 R₁ hR1H, hcc]
  have h2diff : (R₂ \ c).card = 1 := by
    rw [Finset.card_sdiff_of_subset hc2, hH3 R₂ hR2H, hcc]
  rcases Finset.card_eq_one.mp h1diff with ⟨x, hx⟩
  rcases Finset.card_eq_one.mp h2diff with ⟨y, hy⟩
  have hxR1 : x ∈ R₁ ∧ x ∉ c := by
    have : x ∈ R₁ \ c := by rw [hx]; simp
    exact Finset.mem_sdiff.mp this
  have hyR2 : y ∈ R₂ ∧ y ∉ c := by
    have : y ∈ R₂ \ c := by rw [hy]; simp
    exact Finset.mem_sdiff.mp this
  have hR1eq : R₁ = insert x c := by
    ext u
    by_cases huc : u ∈ c
    · simp [huc, hc1 huc]
    · have : u ∈ R₁ \ c ↔ u = x := by rw [hx]; simp
      simp only [Finset.mem_sdiff, huc, not_false_eq_true, and_true] at this
      simp [this, huc]
  have hR2eq : R₂ = insert y c := by
    ext u
    by_cases huc : u ∈ c
    · simp [huc, hc2 huc]
    · have : u ∈ R₂ \ c ↔ u = y := by rw [hy]; simp
      simp only [Finset.mem_sdiff, huc, not_false_eq_true, and_true] at this
      simp [this, huc]
  have hxy : x ≠ y := by
    intro h
    apply hRne
    rw [hR1eq, hR2eq, h]
  have hord : ∀ z R, R ∈ H → c ⊆ R → z ∈ R → z ∉ c → z ∈ ordinary H := by
    intro z R hRH hcR hzR hzc
    simp only [ordinary, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion,
      id_eq, not_exists, not_and]
    intro c' hc' hzc'
    have hRm' : R ∈ rowsOf H c' := by
      rw [← (rowsOf_card_and_eq hH3 hdeg hc').2 z hzc']
      exact Finset.mem_filter.mpr ⟨hRH, hzR⟩
    have hc'eq := core_unique_of_subset hH3 hdeg hRH hc hc' hcR (Finset.mem_filter.mp hRm').2
    exact hzc (hc'eq ▸ hzc')
  refine ⟨x, y, hxy, hord x R₁ hR1H hc1 hxR1.1 hxR1.2, hord y R₂ hR2H hc2 hyR2.1 hyR2.2, ?_, ?_⟩
  · ext u
    simp only [outer, Finset.mem_sdiff, Finset.mem_biUnion, id_eq, Finset.mem_insert,
      Finset.mem_singleton]
    change (∃ R ∈ rowsOf H c, u ∈ R) ∧ u ∉ c ↔ u = x ∨ u = y
    rw [hReq, hR1eq, hR2eq]
    constructor
    · rintro ⟨⟨R, hR, huR⟩, huc⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl
      · simp only [Finset.mem_insert, huc, or_false] at huR; exact Or.inl huR
      · simp only [Finset.mem_insert, huc, or_false] at huR; exact Or.inr huR
    · rintro (h | h)
      · rw [h]; exact ⟨⟨insert x c, by simp, by simp⟩, hxR1.2⟩
      · rw [h]; exact ⟨⟨insert y c, by simp, by simp⟩, hyR2.2⟩
  · rw [hReq, hR1eq, hR2eq]

lemma outer_card_two {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c : Finset (Fin n)} (hc : c ∈ cores H) :
    (outer H c).card = 2 := by
  rcases core_structure hH3 hdeg hc with ⟨x, y, hxy, _, _, hout, _⟩
  rw [hout, Finset.card_pair hxy]

lemma outer_subset_ordinary {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c : Finset (Fin n)} (hc : c ∈ cores H) :
    outer H c ⊆ ordinary H := by
  rcases core_structure hH3 hdeg hc with ⟨x, y, _, hx, hy, hout, _⟩
  rw [hout]
  intro u hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl <;> assumption

lemma base_linear {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    {R₁ R₂ : Finset (Fin n)} (h1 : R₁ ∈ base H) (h2 : R₂ ∈ base H) (hne : R₁ ≠ R₂) :
    (R₁ ∩ R₂).card ≤ 1 := by
  by_contra hgt
  have h1H : R₁ ∈ H := (Finset.mem_filter.mp h1).1
  have h2H : R₂ ∈ H := (Finset.mem_filter.mp h2).1
  have h1ord : R₁ ⊆ ordinary H := (Finset.mem_filter.mp h1).2
  have hle2 : (R₁ ∩ R₂).card ≤ 2 := by
    by_contra hgt2
    have hge3 : 3 ≤ (R₁ ∩ R₂).card := by omega
    have e1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [hH3 R₁ h1H]; exact hge3)
    have e2 := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
      (by rw [hH3 R₂ h2H]; exact hge3)
    exact hne (e1.symm.trans e2)
  have hcard2 : (R₁ ∩ R₂).card = 2 := by omega
  have hcore : R₁ ∩ R₂ ∈ cores H := (mem_cores_iff hH3).mpr ⟨hcard2, R₁, h1H, R₂, h2H, hne, rfl⟩
  obtain ⟨u, hu⟩ : (R₁ ∩ R₂).Nonempty := Finset.card_pos.mp (by omega)
  have huord : u ∈ ordinary H := h1ord (Finset.mem_inter.mp hu).1
  simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
  exact huord.2 ⟨R₁ ∩ R₂, hcore, hu⟩

lemma foldl_range_eq_iterate {α : Type*} (f : α → α) (k : Nat) (x : α) :
    (List.range k).foldl (fun V _ => f V) x = f^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      Function.iterate_succ_apply']

lemma step_mono {n : Nat} (B : Finset (Finset (Fin n))) {V W : Finset (Fin n)} (h : V ⊆ W) :
    step B V ⊆ step B W := by
  intro u hu
  simp only [step, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, id_eq] at hu ⊢
  rcases hu with huV | ⟨R, ⟨hRB, hnd⟩, huR⟩
  · exact Or.inl (h huV)
  · refine Or.inr ⟨R, ⟨hRB, ?_⟩, huR⟩
    intro hd
    exact hnd (hd.mono_right h)

lemma subset_step {n : Nat} (B : Finset (Finset (Fin n))) (V : Finset (Fin n)) :
    V ⊆ step B V := Finset.subset_union_left

lemma step_iterate_mono {n : Nat} (B : Finset (Finset (Fin n))) (k : Nat)
    {V W : Finset (Fin n)} (h : V ⊆ W) :
    (step B)^[k] V ⊆ (step B)^[k] W := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact step_mono B ih

lemma subset_step_iterate {n : Nat} (B : Finset (Finset (Fin n))) (k : Nat) (V : Finset (Fin n)) :
    V ⊆ (step B)^[k] V := by
  induction k with
  | zero => exact Finset.Subset.rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (subset_step B _)

lemma step_iterate_fixed {n : Nat} (B : Finset (Finset (Fin n))) {V : Finset (Fin n)}
    (hfix : step B V = V) (k : Nat) : (step B)^[k] V = V := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]

lemma step_component_eq {n : Nat} (H : Finset (Finset (Fin n))) (u : Fin n) :
    step (base H) (component H u) = component H u := by
  unfold component
  rw [foldl_range_eq_iterate]
  set B := base H
  by_contra hne
  have hstrict : ∀ k ≤ n, ((step B)^[k] {u}).card ≥ k + 1 := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hne_k : step B ((step B)^[k] {u}) ≠ (step B)^[k] {u} := by
        intro heq
        apply hne
        have hadd : (step B)^[n] {u} = (step B)^[k] {u} := by
          have h1 : (step B)^[n] {u} = (step B)^[(n - k) + k] {u} := by
            rw [Nat.sub_add_cancel hk']
          rw [h1, Function.iterate_add_apply, step_iterate_fixed B heq]
        rw [hadd, heq]
      have hss : (step B)^[k] {u} ⊂ (step B)^[k + 1] {u} := by
        rw [Function.iterate_succ_apply']
        exact Finset.ssubset_iff_subset_ne.mpr ⟨subset_step B _, hne_k.symm⟩
      have hlt := Finset.card_lt_card hss
      have := ih hk'
      omega
  have hbig := hstrict n le_rfl
  have hle : ((step B)^[n] {u}).card ≤ n := by
    simpa [Fintype.card_fin] using Finset.card_le_univ ((step B)^[n] {u})
  omega

lemma step_iterate_symm {n : Nat} (B : Finset (Finset (Fin n))) (k : Nat) :
    ∀ u v : Fin n, v ∈ (step B)^[k] {u} → u ∈ (step B)^[k] {v} := by
  induction k with
  | zero =>
    intro u v h
    simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at h ⊢
    exact h.symm
  | succ k ih =>
    intro u v h
    rw [Function.iterate_succ_apply'] at h
    simp only [step, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, id_eq] at h
    rcases h with hv | ⟨R, ⟨hRB, hnd⟩, hvR⟩
    · rw [Function.iterate_succ_apply']
      exact subset_step B _ (ih u v hv)
    · rw [Finset.not_disjoint_iff] at hnd
      rcases hnd with ⟨w, hwR, hwk⟩
      have huw : u ∈ (step B)^[k] {w} := ih u w hwk
      have hwstep : w ∈ step B {v} := by
        simp only [step, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, id_eq]
        refine Or.inr ⟨R, ⟨hRB, ?_⟩, hwR⟩
        rw [Finset.not_disjoint_iff]
        exact ⟨v, hvR, Finset.mem_singleton_self v⟩
      rw [Function.iterate_succ_apply]
      exact step_iterate_mono B k (Finset.singleton_subset_iff.mpr hwstep) huw

lemma mem_component_self {n : Nat} (H : Finset (Finset (Fin n))) (u : Fin n) :
    u ∈ component H u := by
  unfold component
  rw [foldl_range_eq_iterate]
  exact subset_step_iterate (base H) n {u} (Finset.mem_singleton_self u)

lemma mem_component_symm {n : Nat} (H : Finset (Finset (Fin n))) {u v : Fin n}
    (h : v ∈ component H u) : u ∈ component H v := by
  unfold component at h ⊢
  rw [foldl_range_eq_iterate] at h ⊢
  exact step_iterate_symm (base H) n u v h

lemma component_subset_of_mem {n : Nat} (H : Finset (Finset (Fin n))) {u v : Fin n}
    (h : v ∈ component H u) : component H v ⊆ component H u := by
  have hfix := step_component_eq H u
  calc component H v
      = (step (base H))^[n] {v} := by unfold component; rw [foldl_range_eq_iterate]
    _ ⊆ (step (base H))^[n] (component H u) :=
        step_iterate_mono (base H) n (Finset.singleton_subset_iff.mpr h)
    _ = component H u := step_iterate_fixed (base H) hfix n

lemma component_eq_of_mem {n : Nat} (H : Finset (Finset (Fin n))) {u v : Fin n}
    (h : v ∈ component H u) : component H v = component H u :=
  Finset.Subset.antisymm (component_subset_of_mem H h)
    (component_subset_of_mem H (mem_component_symm H h))

lemma component_subset_ordinary {n : Nat} (H : Finset (Finset (Fin n))) {u : Fin n}
    (hu : u ∈ ordinary H) : component H u ⊆ ordinary H := by
  unfold component
  rw [foldl_range_eq_iterate]
  have hpres : ∀ V, V ⊆ ordinary H → step (base H) V ⊆ ordinary H := by
    intro V hV w hw
    simp only [step, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, id_eq] at hw
    rcases hw with hwV | ⟨R, ⟨hRB, _⟩, hwR⟩
    · exact hV hwV
    · exact (Finset.mem_filter.mp hRB).2 hwR
  have hiter : ∀ k, (step (base H))^[k] {u} ⊆ ordinary H := by
    intro k
    induction k with
    | zero => exact Finset.singleton_subset_iff.mpr hu
    | succ k ih => rw [Function.iterate_succ_apply']; exact hpres _ ih
  exact hiter n

lemma parts_pairwise_disjoint {n : Nat} (H : Finset (Finset (Fin n)))
    {C₁ C₂ : Finset (Fin n)} (h1 : C₁ ∈ parts H) (h2 : C₂ ∈ parts H) (hne : C₁ ≠ C₂) :
    Disjoint C₁ C₂ := by
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  apply hne
  rcases Finset.mem_image.mp h1 with ⟨u₁, _, rfl⟩
  rcases Finset.mem_image.mp h2 with ⟨u₂, _, rfl⟩
  exact (component_eq_of_mem H hw1).symm.trans (component_eq_of_mem H hw2)

lemma mem_parts_subset_ordinary {n : Nat} (H : Finset (Finset (Fin n)))
    {C : Finset (Fin n)} (hC : C ∈ parts H) : C ⊆ ordinary H := by
  rcases Finset.mem_image.mp hC with ⟨u, hu, rfl⟩
  exact component_subset_ordinary H hu

lemma mem_parts_nonempty {n : Nat} (H : Finset (Finset (Fin n)))
    {C : Finset (Fin n)} (hC : C ∈ parts H) : C.Nonempty := by
  rcases Finset.mem_image.mp hC with ⟨u, _, rfl⟩
  exact ⟨u, mem_component_self H u⟩

lemma eq_component_of_mem_part {n : Nat} (H : Finset (Finset (Fin n)))
    {C : Finset (Fin n)} (hC : C ∈ parts H) {v : Fin n} (hv : v ∈ C) :
    component H v = C := by
  rcases Finset.mem_image.mp hC with ⟨u, _, rfl⟩
  exact component_eq_of_mem H hv

lemma base_subset_component {n : Nat} (H : Finset (Finset (Fin n)))
    {R : Finset (Fin n)} (hR : R ∈ base H) {u : Fin n} (hu : u ∈ R) :
    R ⊆ component H u := by
  have h1 : R ⊆ step (base H) (component H u) := by
    intro w hw
    simp only [step, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, id_eq]
    refine Or.inr ⟨R, ⟨hR, ?_⟩, hw⟩
    rw [Finset.not_disjoint_iff]
    exact ⟨u, hu, mem_component_self H u⟩
  rwa [step_component_eq H u] at h1

lemma base_eq_biUnion_baseC {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3) :
    base H = (parts H).biUnion (baseC H) := by
  ext R
  simp only [Finset.mem_biUnion, baseC, Finset.mem_filter]
  constructor
  · intro hR
    have hRH : R ∈ H := (Finset.mem_filter.mp hR).1
    have hRord : R ⊆ ordinary H := (Finset.mem_filter.mp hR).2
    obtain ⟨u, hu⟩ : R.Nonempty := Finset.card_pos.mp (by rw [hH3 R hRH]; omega)
    refine ⟨component H u, Finset.mem_image.mpr ⟨u, hRord hu, rfl⟩, hR,
      base_subset_component H hR hu⟩
  · rintro ⟨_, _, hR, _⟩
    exact hR

lemma base_card_eq_sum_tests {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3) :
    (base H).card = (parts H).sum (tests H) := by
  rw [base_eq_biUnion_baseC hH3, Finset.card_biUnion]
  · rfl
  · intro C₁ h1 C₂ h2 hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro R hR1 hR2
    have hRH : R ∈ H := (Finset.mem_filter.mp (Finset.mem_filter.mp hR1).1).1
    obtain ⟨u, hu⟩ : R.Nonempty := Finset.card_pos.mp (by rw [hH3 R hRH]; omega)
    exact Finset.disjoint_left.mp (parts_pairwise_disjoint H h1 h2 hne)
      ((Finset.mem_filter.mp hR1).2 hu) ((Finset.mem_filter.mp hR2).2 hu)

def Connected {n : Nat} (C : Finset (Fin n)) (T : Finset (Finset (Fin n))) : Prop :=
  C.Nonempty ∧ ∀ S : Finset (Fin n), S.Nonempty → S ⊂ C →
    ∃ R ∈ T, ¬ Disjoint R S ∧ ¬ R ⊆ S

lemma component_connected {n : Nat} (H : Finset (Finset (Fin n)))
    {C : Finset (Fin n)} (hC : C ∈ parts H) :
    Connected C (baseC H C) := by
  refine ⟨mem_parts_nonempty H hC, fun S hSne hSss => ?_⟩
  obtain ⟨a, haS⟩ := hSne
  have haC : a ∈ C := hSss.1 haS
  have hCa : C = component H a := (eq_component_of_mem_part H hC haC).symm
  have hnot : ¬ (step (base H))^[n] {a} ⊆ S := by
    have heq : (step (base H))^[n] {a} = C := by
      rw [hCa]; unfold component; rw [foldl_range_eq_iterate]
    rw [heq]
    exact hSss.2
  have hex : ∃ k < n, (step (base H))^[k] {a} ⊆ S ∧ ¬ (step (base H))^[k + 1] {a} ⊆ S := by
    by_contra hall
    push_neg at hall
    have hind : ∀ k ≤ n, (step (base H))^[k] {a} ⊆ S := by
      intro k hk
      induction k with
      | zero => exact Finset.singleton_subset_iff.mpr haS
      | succ k ih => exact hall k (Nat.lt_of_succ_le hk) (ih (Nat.le_of_succ_le hk))
    exact hnot (hind n le_rfl)
  rcases hex with ⟨k, hk, hsubk, hnotk1⟩
  rw [Function.iterate_succ_apply'] at hnotk1
  rw [Finset.not_subset] at hnotk1
  rcases hnotk1 with ⟨w, hw1, hwS⟩
  simp only [step, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, id_eq] at hw1
  rcases hw1 with hwk | ⟨R, ⟨hRB, hnd⟩, hwR⟩
  · exact absurd (hsubk hwk) hwS
  · have hndS : ¬ Disjoint R S := fun hd => hnd (hd.mono_right hsubk)
    have hnotRS : ¬ R ⊆ S := fun hs => hwS (hs hwR)
    have hRC : R ⊆ C := by
      rw [Finset.not_disjoint_iff] at hndS
      rcases hndS with ⟨x, hxR, hxS⟩
      rw [← eq_component_of_mem_part H hC (hSss.1 hxS)]
      exact base_subset_component H hRB hxR
    exact ⟨R, Finset.mem_filter.mpr ⟨hRB, hRC⟩, hndS, hnotRS⟩

lemma card_le_two_mul_add_one {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))}
    (h3 : ∀ R ∈ T, R.card = 3) (hsub : ∀ R ∈ T, R ⊆ C) (hconn : Connected C T) :
    C.card ≤ 2 * T.card + 1 := by
  have haux : ∀ m : Nat, ∀ S : Finset (Fin n), S.Nonempty → S ⊆ C → (C \ S).card ≤ m →
      C.card - S.card ≤ 2 * (T.filter (fun R => ¬ R ⊆ S)).card := by
    intro m
    induction m with
    | zero =>
      intro S _ hSC h0
      have hSCeq : S = C := by
        have hce : (C \ S).card = 0 := Nat.eq_zero_of_le_zero h0
        rw [Finset.card_sdiff_of_subset hSC] at hce
        exact Finset.eq_of_subset_of_card_le hSC (by omega)
      rw [hSCeq, Nat.sub_self]
      exact Nat.zero_le _
    | succ m ih =>
      intro S hSne hSC hle
      by_cases hSCeq : S = C
      · rw [hSCeq, Nat.sub_self]; exact Nat.zero_le _
      · have hSss : S ⊂ C := Finset.ssubset_iff_subset_ne.mpr ⟨hSC, hSCeq⟩
        rcases hconn.2 S hSne hSss with ⟨R, hRT, hnd, hnotRS⟩
        set S' := S ∪ R
        have hS'C : S' ⊆ C := Finset.union_subset hSC (hsub R hRT)
        have hSS' : S ⊂ S' := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
          intro heq
          exact hnotRS (heq ▸ Finset.subset_union_right)
        have hcard_lt : S.card < S'.card := Finset.card_lt_card hSS'
        have hS'le : (C \ S').card ≤ m := by
          rw [Finset.card_sdiff_of_subset hS'C]
          rw [Finset.card_sdiff_of_subset hSC] at hle
          have := Finset.card_le_card hS'C
          have := Finset.card_le_card hSC
          omega
        have hstep := ih S' (hSne.mono Finset.subset_union_left) hS'C hS'le
        have hS'card : S'.card ≤ S.card + 2 := by
          have h1 : 1 ≤ (S ∩ R).card := by
            rw [Finset.not_disjoint_iff] at hnd
            rcases hnd with ⟨x, hxR, hxS⟩
            exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxS, hxR⟩⟩
          have hu := Finset.card_union_add_card_inter S R
          rw [h3 R hRT] at hu
          change S'.card + (S ∩ R).card = S.card + 3 at hu
          omega
        have hTdrop : (T.filter (fun R' => ¬ R' ⊆ S')).card + 1 ≤
            (T.filter (fun R' => ¬ R' ⊆ S)).card := by
          have hRm : R ∈ T.filter (fun R' => ¬ R' ⊆ S) := Finset.mem_filter.mpr ⟨hRT, hnotRS⟩
          have hRnm : R ∉ T.filter (fun R' => ¬ R' ⊆ S') := by
            simp [Finset.mem_filter, S']
          have hsubF : T.filter (fun R' => ¬ R' ⊆ S') ⊆
              (T.filter (fun R' => ¬ R' ⊆ S)).erase R := by
            intro R' hR'
            simp only [Finset.mem_filter, Finset.mem_erase] at hR' ⊢
            refine ⟨?_, hR'.1, fun hs => hR'.2 (hs.trans Finset.subset_union_left)⟩
            intro heq
            exact hR'.2 (heq ▸ Finset.subset_union_right)
          have hc1 := Finset.card_le_card hsubF
          rw [Finset.card_erase_of_mem hRm] at hc1
          have hpos : 1 ≤ (T.filter (fun R' => ¬ R' ⊆ S)).card := Finset.card_pos.mpr ⟨R, hRm⟩
          omega
        have hCS' := Finset.card_le_card hS'C
        omega
  obtain ⟨u, huC⟩ := hconn.1
  have h1 := haux C.card {u} ⟨u, Finset.mem_singleton_self u⟩
    (Finset.singleton_subset_iff.mpr huC) (Finset.card_le_card Finset.sdiff_subset)
  have hfilt : T.filter (fun R => ¬ R ⊆ {u}) = T := by
    ext R
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hRT hsub1
    have := Finset.card_le_card hsub1
    rw [h3 R hRT, Finset.card_singleton] at this
    omega
  rw [hfilt, Finset.card_singleton] at h1
  omega

lemma card_biUnion_pairs {n : Nat} {M : Finset (Finset (Fin n))}
    (h2 : ∀ g ∈ M, g.card = 2)
    (hdisj : ∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h) :
    (M.biUnion id).card = 2 * M.card := by
  rw [Finset.card_biUnion (t := id) (fun g hg h hh hne => hdisj g hg h hh hne)]
  simp only [id_eq]
  rw [Finset.sum_const_nat (fun g hg => h2 g hg), mul_comm]

lemma linear_witness_unique_R {n : Nat} {T : Finset (Finset (Fin n))}
    (hlin : ∀ R₁ ∈ T, ∀ R₂ ∈ T, R₁ ≠ R₂ → (R₁ ∩ R₂).card ≤ 1)
    {g R₁ R₂ : Finset (Fin n)} (hg2 : g.card = 2)
    (h1 : R₁ ∈ T) (h2 : R₂ ∈ T) (hs1 : g ⊆ R₁) (hs2 : g ⊆ R₂) : R₁ = R₂ := by
  by_contra hne
  have hle := hlin R₁ h1 R₂ h2 hne
  have hge := Finset.card_le_card (Finset.subset_inter hs1 hs2)
  omega

lemma witness_unique_g {n : Nat} {M : Finset (Finset (Fin n))}
    (h2 : ∀ g ∈ M, g.card = 2)
    (hdisj : ∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h)
    {R g₁ g₂ : Finset (Fin n)} (hR3 : R.card = 3)
    (h1 : g₁ ∈ M) (h2m : g₂ ∈ M) (hs1 : g₁ ⊆ R) (hs2 : g₂ ⊆ R) : g₁ = g₂ := by
  by_contra hne
  have hd := hdisj g₁ h1 g₂ h2m hne
  have hle := Finset.card_le_card (Finset.union_subset hs1 hs2)
  rw [Finset.card_union_of_disjoint hd, h2 g₁ h1, h2 g₂ h2m, hR3] at hle
  omega

lemma linear_filter_card_eq {n : Nat} {T M : Finset (Finset (Fin n))}
    (h3 : ∀ R ∈ T, R.card = 3)
    (hlin : ∀ R₁ ∈ T, ∀ R₂ ∈ T, R₁ ≠ R₂ → (R₁ ∩ R₂).card ≤ 1)
    (h2 : ∀ g ∈ M, g.card = 2)
    (hdisj : ∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h)
    (hcov : ∀ R ∈ T, ∃ g ∈ M, g ⊆ R) :
    (M.filter (fun g => ∃ R ∈ T, g ⊆ R)).card = T.card := by
  classical
  refine (Finset.card_nbij'
    (fun R => if h : R ∈ T then Classical.choose (hcov R h) else ∅)
    (fun g => if h : ∃ R ∈ T, g ⊆ R then Classical.choose h else ∅)
    ?_ ?_ ?_ ?_).symm
  · intro R hR
    simp only [Finset.mem_coe] at hR ⊢
    simp only [hR, ↓reduceDIte, Finset.mem_filter]
    have hspec := Classical.choose_spec (hcov R hR)
    exact ⟨hspec.1, R, hR, hspec.2⟩
  · intro g hg
    simp only [Finset.mem_coe] at hg ⊢
    have hex : ∃ R ∈ T, g ⊆ R := (Finset.mem_filter.mp hg).2
    simp only [hex, ↓reduceDIte]
    exact (Classical.choose_spec hex).1
  · intro R hR
    simp only [Finset.mem_coe] at hR
    simp only [hR, ↓reduceDIte]
    have hspec := Classical.choose_spec (hcov R hR)
    have hex : ∃ R' ∈ T, Classical.choose (hcov R hR) ⊆ R' := ⟨R, hR, hspec.2⟩
    simp only [hex, ↓reduceDIte]
    have hspec2 := Classical.choose_spec hex
    exact linear_witness_unique_R hlin (h2 _ hspec.1) hspec2.1 hR hspec2.2 hspec.2
  · intro g hg
    simp only [Finset.mem_coe] at hg
    rcases Finset.mem_filter.mp hg with ⟨hgM, hex⟩
    simp only [hex, ↓reduceDIte]
    have hspec := Classical.choose_spec hex
    simp only [hspec.1, ↓reduceDIte]
    have hspec2 := Classical.choose_spec (hcov _ hspec.1)
    exact witness_unique_g h2 hdisj (h3 _ hspec.1) hspec2.1 hgM hspec2.2 hspec.2

def LocalMatch {n : Nat} (C : Finset (Fin n)) (T : Finset (Finset (Fin n))) (r : Fin n) :
    Finset (Finset (Finset (Fin n))) :=
  Finset.univ.filter fun M =>
    (∀ g ∈ M, g.card = 2 ∧ g ⊆ C.erase r) ∧
    (∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h) ∧
    (∀ R ∈ T, ∃ g ∈ M, g ⊆ R)

def LocalMatchFull {n : Nat} (C : Finset (Fin n)) (T : Finset (Finset (Fin n))) :
    Finset (Finset (Finset (Fin n))) :=
  Finset.univ.filter fun M =>
    (∀ g ∈ M, g.card = 2 ∧ g ⊆ C) ∧
    (∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h) ∧
    (∀ R ∈ T, ∃ g ∈ M, g ⊆ R)

lemma localMatch_tight {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))} {r : Fin n}
    (h3 : ∀ R ∈ T, R.card = 3)
    (hlin : ∀ R₁ ∈ T, ∀ R₂ ∈ T, R₁ ≠ R₂ → (R₁ ∩ R₂).card ≤ 1)
    (hr : r ∈ C) (hcard : C.card = 2 * T.card + 1)
    {M : Finset (Finset (Fin n))} (hM : M ∈ LocalMatch C T r) :
    M.card = T.card ∧ M.biUnion id = C.erase r ∧ ∀ g ∈ M, ∃ R ∈ T, g ⊆ R := by
  simp only [LocalMatch, Finset.mem_filter, Finset.mem_univ, true_and] at hM
  rcases hM with ⟨h2sub, hdisj, hcov⟩
  have h2 : ∀ g ∈ M, g.card = 2 := fun g hg => (h2sub g hg).1
  have hfilt := linear_filter_card_eq h3 hlin h2 hdisj hcov
  have hTle : T.card ≤ M.card := hfilt ▸ Finset.card_le_card (Finset.filter_subset _ M)
  have hUsub : M.biUnion id ⊆ C.erase r := by
    intro u hu
    rcases Finset.mem_biUnion.mp hu with ⟨g, hgM, hug⟩
    exact (h2sub g hgM).2 hug
  have hUcard : (M.biUnion id).card = 2 * M.card := card_biUnion_pairs h2 hdisj
  have herase : (C.erase r).card = 2 * T.card := by rw [Finset.card_erase_of_mem hr, hcard]; omega
  have hMle : M.card ≤ T.card := by
    have := Finset.card_le_card hUsub
    rw [hUcard, herase] at this
    omega
  have hMeq : M.card = T.card := le_antisymm hMle hTle
  have hUeq : M.biUnion id = C.erase r :=
    Finset.eq_of_subset_of_card_le hUsub (by rw [hUcard, herase, hMeq])
  have hfeq : M.filter (fun g => ∃ R ∈ T, g ⊆ R) = M :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ M) (by rw [hfilt, hMeq])
  refine ⟨hMeq, hUeq, fun g hg => ?_⟩
  rw [← hfeq] at hg
  exact (Finset.mem_filter.mp hg).2

lemma localMatchFull_tight {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))}
    (h3 : ∀ R ∈ T, R.card = 3)
    (hlin : ∀ R₁ ∈ T, ∀ R₂ ∈ T, R₁ ≠ R₂ → (R₁ ∩ R₂).card ≤ 1)
    (hcard : C.card = 2 * T.card)
    {M : Finset (Finset (Fin n))} (hM : M ∈ LocalMatchFull C T) :
    M.card = T.card ∧ M.biUnion id = C ∧ ∀ g ∈ M, ∃ R ∈ T, g ⊆ R := by
  simp only [LocalMatchFull, Finset.mem_filter, Finset.mem_univ, true_and] at hM
  rcases hM with ⟨h2sub, hdisj, hcov⟩
  have h2 : ∀ g ∈ M, g.card = 2 := fun g hg => (h2sub g hg).1
  have hfilt := linear_filter_card_eq h3 hlin h2 hdisj hcov
  have hTle : T.card ≤ M.card := hfilt ▸ Finset.card_le_card (Finset.filter_subset _ M)
  have hUsub : M.biUnion id ⊆ C := by
    intro u hu
    rcases Finset.mem_biUnion.mp hu with ⟨g, hgM, hug⟩
    exact (h2sub g hgM).2 hug
  have hUcard : (M.biUnion id).card = 2 * M.card := card_biUnion_pairs h2 hdisj
  have hMle : M.card ≤ T.card := by
    have := Finset.card_le_card hUsub
    rw [hUcard, hcard] at this
    omega
  have hMeq : M.card = T.card := le_antisymm hMle hTle
  have hUeq : M.biUnion id = C :=
    Finset.eq_of_subset_of_card_le hUsub (by rw [hUcard, hcard, hMeq])
  have hfeq : M.filter (fun g => ∃ R ∈ T, g ⊆ R) = M :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ M) (by rw [hfilt, hMeq])
  refine ⟨hMeq, hUeq, fun g hg => ?_⟩
  rw [← hfeq] at hg
  exact (Finset.mem_filter.mp hg).2

def degT {n : Nat} (T : Finset (Finset (Fin n))) (u : Fin n) : Nat :=
  (T.filter (fun R => u ∈ R)).card

def V2 {n : Nat} (C : Finset (Fin n)) (T : Finset (Finset (Fin n))) : Finset (Fin n) :=
  C.filter (fun u => degT T u = 2)

def tdeg {n : Nat} (C : Finset (Fin n)) (T : Finset (Finset (Fin n))) (R : Finset (Fin n)) : Nat :=
  (R ∩ V2 C T).card

lemma degT_pos_of_nonempty {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))}
    (h3 : ∀ R ∈ T, R.card = 3) (hsub : ∀ R ∈ T, R ⊆ C) (hconn : Connected C T)
    (hTne : T.Nonempty) {u : Fin n} (hu : u ∈ C) :
    1 ≤ degT T u := by
  obtain ⟨R₀, hR₀⟩ := hTne
  have hCge3 : 3 ≤ C.card := (h3 R₀ hR₀) ▸ Finset.card_le_card (hsub R₀ hR₀)
  have hss : ({u} : Finset (Fin n)) ⊂ C := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr hu, ?_⟩
    intro heq
    rw [← heq, Finset.card_singleton] at hCge3
    omega
  rcases hconn.2 {u} ⟨u, Finset.mem_singleton_self u⟩ hss with ⟨R, hRT, hnd, _⟩
  rw [Finset.not_disjoint_iff] at hnd
  rcases hnd with ⟨w, hwR, hwu⟩
  rw [Finset.mem_singleton] at hwu
  subst hwu
  exact Finset.card_pos.mpr ⟨R, Finset.mem_filter.mpr ⟨hRT, hwR⟩⟩

lemma sum_degT_eq {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))}
    (h3 : ∀ R ∈ T, R.card = 3) (hsub : ∀ R ∈ T, R ⊆ C) :
    C.sum (degT T) = 3 * T.card := by
  have h1 : C.sum (degT T) = C.sum (fun u => T.sum (fun R => if u ∈ R then 1 else 0)) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [degT, Finset.card_filter]
  rw [h1, Finset.sum_comm]
  have h2 : T.sum (fun R => C.sum (fun u => if u ∈ R then 1 else 0)) = T.sum (fun R => R.card) := by
    refine Finset.sum_congr rfl fun R hRT => ?_
    rw [← Finset.card_filter]
    congr 1
    ext u
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun hu => hsub R hRT hu
  rw [h2, Finset.sum_const_nat (fun R hR => h3 R hR), mul_comm]

lemma card_V2_add_card_C {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))}
    (h3 : ∀ R ∈ T, R.card = 3) (hsub : ∀ R ∈ T, R ⊆ C)
    (hdeg : ∀ u, degT T u ≤ 2) (hconn : Connected C T) (hTne : T.Nonempty) :
    C.card + (V2 C T).card = 3 * T.card := by
  rw [← sum_degT_eq h3 hsub]
  have h1 : ∀ u ∈ C, degT T u = 1 + if degT T u = 2 then 1 else 0 := by
    intro u hu
    have hge := degT_pos_of_nonempty h3 hsub hconn hTne hu
    have hle := hdeg u
    split_ifs <;> omega
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl),
    mul_one, ← Finset.card_filter]
  rfl

lemma sum_tdeg_eq {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))}
    (hsub : ∀ R ∈ T, R ⊆ C) :
    T.sum (tdeg C T) = 2 * (V2 C T).card := by
  have h1 : T.sum (tdeg C T) = T.sum (fun R => (V2 C T).sum (fun u => if u ∈ R then 1 else 0)) := by
    refine Finset.sum_congr rfl fun R _ => ?_
    dsimp only [tdeg]
    rw [← Finset.card_filter]
    congr 1
    ext u
    simp only [Finset.mem_inter, Finset.mem_filter, and_comm]
  rw [h1, Finset.sum_comm]
  have h2 : (V2 C T).sum (fun u => T.sum (fun R => if u ∈ R then 1 else 0)) =
      (V2 C T).sum (fun _ => 2) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [← Finset.card_filter]
    exact (Finset.mem_filter.mp hu).2
  rw [h2, Finset.sum_const_nat (fun _ _ => rfl), mul_comm]

lemma tdeg_pos_of_card_gt_three {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))}
    (h3 : ∀ R ∈ T, R.card = 3) (hsub : ∀ R ∈ T, R ⊆ C)
    (hdeg : ∀ u, degT T u ≤ 2) (hconn : Connected C T)
    (hCgt : 3 < C.card) {R : Finset (Fin n)} (hRT : R ∈ T) :
    1 ≤ tdeg C T R := by
  have hRss : R ⊂ C := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub R hRT, ?_⟩
    intro heq
    rw [← heq] at hCgt
    have := h3 R hRT
    omega
  have hRne : R.Nonempty := Finset.card_pos.mp (by rw [h3 R hRT]; omega)
  rcases hconn.2 R hRne hRss with ⟨R', hR'T, hnd, hnot⟩
  have hne : R' ≠ R := fun heq => hnot (heq ▸ Finset.Subset.rfl)
  rw [Finset.not_disjoint_iff] at hnd
  rcases hnd with ⟨v, hvR', hvR⟩
  have hv2 : degT T v = 2 := by
    have hle := hdeg v
    have hge : 2 ≤ degT T v := by
      have hsubp : ({R, R'} : Finset _) ⊆ T.filter (fun X => v ∈ X) := by
        intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hRT, hvR⟩
        · exact Finset.mem_filter.mpr ⟨hR'T, hvR'⟩
      have := Finset.card_le_card hsubp
      rwa [Finset.card_pair hne.symm] at this
    omega
  exact Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨hvR, Finset.mem_filter.mpr ⟨hsub R hRT hvR, hv2⟩⟩⟩

lemma peel_leaf_props {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))}
    (h3 : ∀ R ∈ T, R.card = 3) (hsub : ∀ R ∈ T, R ⊆ C)
    (hdeg : ∀ u, degT T u ≤ 2) (hconn : Connected C T)
    {R : Finset (Fin n)} (hRT : R ∈ T) {v : Fin n} (hleaf : R ∩ V2 C T = {v}) :
    let C' := C \ (R.erase v)
    let T' := T.erase R
    v ∈ R ∧ v ∈ C' ∧ C'.card + 2 = C.card ∧ T'.card + 1 = T.card ∧
    (∀ w ∈ R.erase v, ∀ R' ∈ T', w ∉ R') ∧
    (∀ R' ∈ T', R' ⊆ C') ∧ Connected C' T' := by
  have hvmem : v ∈ R ∩ V2 C T := by rw [hleaf]; simp
  have hvR : v ∈ R := (Finset.mem_inter.mp hvmem).1
  have hvC : v ∈ C := hsub R hRT hvR
  have hvC' : v ∈ C \ (R.erase v) := Finset.mem_sdiff.mpr ⟨hvC, by simp⟩
  have herase_sub : R.erase v ⊆ C := (Finset.erase_subset v R).trans (hsub R hRT)
  have herase_card : (R.erase v).card = 2 := by rw [Finset.card_erase_of_mem hvR, h3 R hRT]
  have hC'card : (C \ (R.erase v)).card + 2 = C.card := by
    rw [Finset.card_sdiff_of_subset herase_sub, herase_card]
    have := Finset.card_le_card herase_sub
    rw [herase_card] at this
    omega
  have hT'card : (T.erase R).card + 1 = T.card := by
    rw [Finset.card_erase_of_mem hRT]
    have := Finset.card_pos.mpr ⟨R, hRT⟩
    omega
  have hnotin : ∀ w ∈ R.erase v, ∀ R' ∈ T.erase R, w ∉ R' := by
    intro w hw R' hR' hwR'
    rcases Finset.mem_erase.mp hw with ⟨hwv, hwR⟩
    rcases Finset.mem_erase.mp hR' with ⟨hR'ne, hR'T⟩
    have hw2 : degT T w = 2 := by
      have hle := hdeg w
      have hge : 2 ≤ degT T w := by
        have hp : ({R, R'} : Finset _) ⊆ T.filter (fun X => w ∈ X) := by
          intro X hX
          simp only [Finset.mem_insert, Finset.mem_singleton] at hX
          rcases hX with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hRT, hwR⟩
          · exact Finset.mem_filter.mpr ⟨hR'T, hwR'⟩
        have := Finset.card_le_card hp
        rwa [Finset.card_pair hR'ne.symm] at this
      omega
    have hwV2 : w ∈ R ∩ V2 C T :=
      Finset.mem_inter.mpr ⟨hwR, Finset.mem_filter.mpr ⟨hsub R hRT hwR, hw2⟩⟩
    rw [hleaf, Finset.mem_singleton] at hwV2
    exact hwv hwV2
  have hsub' : ∀ R' ∈ T.erase R, R' ⊆ C \ (R.erase v) := by
    intro R' hR' u huR'
    refine Finset.mem_sdiff.mpr ⟨hsub R' (Finset.mem_of_mem_erase hR') huR', fun hu => ?_⟩
    exact hnotin u hu R' hR' huR'
  have hconn' : Connected (C \ (R.erase v)) (T.erase R) := by
    refine ⟨⟨v, hvC'⟩, fun S hSne hSss => ?_⟩
    by_cases hvS : v ∈ S
    · set Sbig := S ∪ R
      have hSbigSub : Sbig ⊆ C :=
        Finset.union_subset (hSss.1.trans Finset.sdiff_subset) (hsub R hRT)
      have hSbigNe : Sbig ≠ C := by
        intro heq
        apply hSss.2
        intro x hxC'
        have hxbig : x ∈ Sbig := heq.symm ▸ (Finset.mem_sdiff.mp hxC').1
        rcases Finset.mem_union.mp hxbig with hxS | hxR
        · exact hxS
        · by_cases hxv : x = v
          · exact hxv ▸ hvS
          · exact absurd (Finset.mem_erase.mpr ⟨hxv, hxR⟩) (Finset.mem_sdiff.mp hxC').2
      have hSbigss : Sbig ⊂ C := Finset.ssubset_iff_subset_ne.mpr ⟨hSbigSub, hSbigNe⟩
      rcases hconn.2 Sbig (hSne.mono Finset.subset_union_left) hSbigss with ⟨R', hR'T, hnd, hnot⟩
      have hR'ne : R' ≠ R := fun heq => hnot (heq ▸ Finset.subset_union_right)
      have hR'm : R' ∈ T.erase R := Finset.mem_erase.mpr ⟨hR'ne, hR'T⟩
      refine ⟨R', hR'm, ?_, fun hs => hnot (hs.trans Finset.subset_union_left)⟩
      rw [Finset.not_disjoint_iff] at hnd ⊢
      rcases hnd with ⟨w, hwR', hwbig⟩
      rcases Finset.mem_union.mp hwbig with hwS | hwR
      · exact ⟨w, hwR', hwS⟩
      · by_cases hwv : w = v
        · exact ⟨v, hwv ▸ hwR', hvS⟩
        · exact absurd hwR' (hnotin w (Finset.mem_erase.mpr ⟨hwv, hwR⟩) R' hR'm)
    · have hSssC : S ⊂ C := lt_of_lt_of_le hSss Finset.sdiff_subset
      rcases hconn.2 S hSne hSssC with ⟨R', hR'T, hnd, hnot⟩
      have hR'ne : R' ≠ R := by
        intro heq
        subst heq
        rw [Finset.not_disjoint_iff] at hnd
        rcases hnd with ⟨w, hwR, hwS⟩
        have hwC' := hSss.1 hwS
        by_cases hwv : w = v
        · exact hvS (hwv ▸ hwS)
        · exact (Finset.mem_sdiff.mp hwC').2 (Finset.mem_erase.mpr ⟨hwv, hwR⟩)
      exact ⟨R', Finset.mem_erase.mpr ⟨hR'ne, hR'T⟩, hnd, hnot⟩
  exact ⟨hvR, hvC', hC'card, hT'card, hnotin, hsub', hconn'⟩

lemma localMatch_peel_leaf {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))} {r : Fin n}
    (h3 : ∀ R ∈ T, R.card = 3) (hsub : ∀ R ∈ T, R ⊆ C)
    (hdeg : ∀ u, degT T u ≤ 2)
    (hlin : ∀ R₁ ∈ T, ∀ R₂ ∈ T, R₁ ≠ R₂ → (R₁ ∩ R₂).card ≤ 1)
    (hconn : Connected C T)
    (hr : r ∈ C) (hcard : C.card = 2 * T.card + 1)
    {R : Finset (Fin n)} (hRT : R ∈ T) (hrR : r ∉ R)
    {v : Fin n} (hleaf : R ∩ V2 C T = {v}) :
    (LocalMatch C T r).card = (LocalMatch (C \ (R.erase v)) (T.erase R) r).card := by
  have hp := peel_leaf_props h3 hsub hdeg hconn hRT hleaf
  rcases hp with ⟨hvR, hvC', hC'card, hT'card, hnotin, hsub', hconn'⟩
  set g₀ := R.erase v
  have hg₀2 : g₀.card = 2 := by rw [Finset.card_erase_of_mem hvR, h3 R hRT]
  have hrC' : r ∈ C \ g₀ := Finset.mem_sdiff.mpr ⟨hr, fun h => hrR (Finset.mem_of_mem_erase h)⟩
  have hg₀sub : g₀ ⊆ C.erase r := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨fun h => hrR (h ▸ Finset.mem_of_mem_erase hw),
      hsub R hRT (Finset.mem_of_mem_erase hw)⟩
  have hforced : ∀ M ∈ LocalMatch C T r, g₀ ∈ M := by
    intro M hM
    rcases localMatch_tight h3 hlin hr hcard hM with ⟨_, hUeq, hall⟩
    have hMspec := (Finset.mem_filter.mp hM).2
    rcases hMspec.2.2 R hRT with ⟨gR, hgRM, hgRR⟩
    have hsubg : g₀ ⊆ gR := by
      intro w hwg₀
      have hwU : w ∈ M.biUnion id := by rw [hUeq]; exact hg₀sub hwg₀
      rcases Finset.mem_biUnion.mp hwU with ⟨g, hgM, hwg⟩
      rcases hall g hgM with ⟨R', hR'T, hgR'⟩
      have hR'eq : R' = R := by
        by_contra hne
        exact hnotin w hwg₀ R' (Finset.mem_erase.mpr ⟨hne, hR'T⟩) (hgR' hwg)
      rw [hR'eq] at hgR'
      have hgeq := witness_unique_g (fun x hx => (hMspec.1 x hx).1) hMspec.2.1 (h3 R hRT)
        hgM hgRM hgR' hgRR
      exact hgeq ▸ hwg
    have hg₀eq : g₀ = gR :=
      Finset.eq_of_subset_of_card_le hsubg (by rw [hg₀2, (hMspec.1 gR hgRM).1])
    exact hg₀eq ▸ hgRM
  refine Finset.card_nbij' (fun M => M.erase g₀) (fun M' => insert g₀ M') ?_ ?_ ?_ ?_
  · intro M hM
    simp only [Finset.mem_coe] at hM ⊢
    have hg₀M := hforced M hM
    have hMspec := (Finset.mem_filter.mp hM).2
    simp only [LocalMatch, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun g hg => ?_, fun g hg h hh hne => ?_, fun R' hR' => ?_⟩
    · rcases Finset.mem_erase.mp hg with ⟨hgne, hgM⟩
      refine ⟨(hMspec.1 g hgM).1, fun u hug => ?_⟩
      have hu1 := (hMspec.1 g hgM).2 hug
      rcases Finset.mem_erase.mp hu1 with ⟨hur, huC⟩
      have hdisj := hMspec.2.1 g hgM g₀ hg₀M hgne
      exact Finset.mem_erase.mpr ⟨hur, Finset.mem_sdiff.mpr ⟨huC, Finset.disjoint_left.mp hdisj hug⟩⟩
    · exact hMspec.2.1 g (Finset.mem_of_mem_erase hg) h (Finset.mem_of_mem_erase hh) hne
    · rcases hMspec.2.2 R' (Finset.mem_of_mem_erase hR') with ⟨g, hgM, hgR'⟩
      refine ⟨g, Finset.mem_erase.mpr ⟨?_, hgM⟩, hgR'⟩
      intro hgeq
      subst hgeq
      obtain ⟨w, hwg₀⟩ : g₀.Nonempty := Finset.card_pos.mp (by omega)
      exact hnotin w hwg₀ R' hR' (hgR' hwg₀)
  · intro M' hM'
    simp only [Finset.mem_coe] at hM' ⊢
    have hM'spec := (Finset.mem_filter.mp hM').2
    simp only [LocalMatch, Finset.mem_filter, Finset.mem_univ, true_and]
    have hdisj0 : ∀ g ∈ M', Disjoint g₀ g := by
      intro g hg
      rw [Finset.disjoint_left]
      intro w hwg₀ hwg
      have hw := (hM'spec.1 g hg).2 hwg
      exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hw)).2 hwg₀
    refine ⟨fun g hg => ?_, fun g hg h hh hne => ?_, fun R' hR' => ?_⟩
    · rcases Finset.mem_insert.mp hg with rfl | hgM'
      · exact ⟨hg₀2, hg₀sub⟩
      · refine ⟨(hM'spec.1 g hgM').1, fun u hug => ?_⟩
        rcases Finset.mem_erase.mp ((hM'spec.1 g hgM').2 hug) with ⟨hur, huC'⟩
        exact Finset.mem_erase.mpr ⟨hur, (Finset.mem_sdiff.mp huC').1⟩
    · rcases Finset.mem_insert.mp hg with rfl | hgM' <;>
      rcases Finset.mem_insert.mp hh with rfl | hhM'
      · exact absurd rfl hne
      · exact hdisj0 h hhM'
      · exact (hdisj0 g hgM').symm
      · exact hM'spec.2.1 g hgM' h hhM' hne
    · by_cases hR'eq : R' = R
      · rw [hR'eq]
        exact ⟨g₀, Finset.mem_insert_self g₀ M', Finset.erase_subset v R⟩
      · rcases hM'spec.2.2 R' (Finset.mem_erase.mpr ⟨hR'eq, hR'⟩) with ⟨g, hgM', hgR'⟩
        exact ⟨g, Finset.mem_insert_of_mem hgM', hgR'⟩
  · intro M hM
    exact Finset.insert_erase (hforced M hM)
  · intro M' hM'
    have hg₀nm : g₀ ∉ M' := by
      intro hg₀M'
      have hM'spec := (Finset.mem_filter.mp hM').2
      obtain ⟨w, hwg₀⟩ : g₀.Nonempty := Finset.card_pos.mp (by omega)
      have hw := (hM'spec.1 g₀ hg₀M').2 hwg₀
      exact (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hw)).2 hwg₀
    exact Finset.erase_insert hg₀nm

lemma localMatch_card_one {n : Nat} :
    ∀ m : Nat, ∀ C : Finset (Fin n), ∀ T : Finset (Finset (Fin n)), ∀ r : Fin n,
      T.card = m →
      (∀ R ∈ T, R.card = 3) → (∀ R ∈ T, R ⊆ C) →
      (∀ u, degT T u ≤ 2) →
      (∀ R₁ ∈ T, ∀ R₂ ∈ T, R₁ ≠ R₂ → (R₁ ∩ R₂).card ≤ 1) →
      Connected C T → r ∈ C → C.card = 2 * T.card + 1 →
      (LocalMatch C T r).card = 1 := by
  intro m
  induction m with
  | zero =>
    intro C T r hm _ _ _ _ _ hr hcard
    have hTe : T = ∅ := Finset.card_eq_zero.mp hm
    have hCe : C.erase r = ∅ := Finset.card_eq_zero.mp (by rw [Finset.card_erase_of_mem hr, hcard, hm])
    have heq : LocalMatch C T r = {∅} := by
      ext M
      simp only [LocalMatch, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        hTe, hCe, Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true]
      constructor
      · intro hM
        refine Finset.eq_empty_of_forall_notMem fun g hg => ?_
        have h1 := (hM.1 g hg).1
        have h2 := Finset.subset_empty.mp (hM.1 g hg).2
        rw [h2, Finset.card_empty] at h1
        omega
      · rintro rfl; simp
    rw [heq, Finset.card_singleton]
  | succ m ih =>
    intro C T r hm h3 hsub hdeg hlin hconn hr hcard
    by_cases hm0 : m = 0
    · subst hm0
      rcases Finset.card_eq_one.mp hm with ⟨R, hTeq⟩
      have hRT : R ∈ T := by rw [hTeq]; simp
      have hRC : R = C := Finset.eq_of_subset_of_card_le (hsub R hRT) (by rw [h3 R hRT, hcard, hm])
      have heq : LocalMatch C T r = {{C.erase r}} := by
        ext M
        simp only [LocalMatch, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨h2sub, hdisj, hcov⟩
          rcases hcov R hRT with ⟨g, hgM, hgR⟩
          have hg2 := (h2sub g hgM).1
          have hgsub := (h2sub g hgM).2
          have hgeq : g = C.erase r :=
            Finset.eq_of_subset_of_card_le hgsub (by rw [hg2, Finset.card_erase_of_mem hr, hcard, hm])
          have hMeq : M = {g} := by
            ext g'
            simp only [Finset.mem_singleton]
            constructor
            · intro hg'M
              by_contra hne
              have hd := hdisj g' hg'M g hgM hne
              have hle := Finset.card_le_card (Finset.union_subset (h2sub g' hg'M).2 hgsub)
              rw [Finset.card_union_of_disjoint hd, (h2sub g' hg'M).1, hg2,
                Finset.card_erase_of_mem hr, hcard, hm] at hle
              omega
            · rintro rfl; exact hgM
          rw [hMeq, hgeq]
        · rintro rfl
          refine ⟨fun g hg => ?_, fun g hg h hh hne => ?_, fun R' hR' => ?_⟩
          · rw [Finset.mem_singleton] at hg; subst hg
            exact ⟨by rw [Finset.card_erase_of_mem hr, hcard, hm], Finset.Subset.rfl⟩
          · rw [Finset.mem_singleton] at hg hh; exact absurd (hg.trans hh.symm) hne
          · rw [hTeq, Finset.mem_singleton] at hR'; subst hR'
            exact ⟨C.erase r, Finset.mem_singleton_self _, hRC ▸ Finset.erase_subset r C⟩
      rw [heq, Finset.card_singleton]
    · have hTge2 : 2 ≤ T.card := by omega
      have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
      have hCgt3 : 3 < C.card := by omega
      have hV2 : (V2 C T).card = T.card - 1 := by
        have := card_V2_add_card_C h3 hsub hdeg hconn hTne
        omega
      have hsum : T.sum (tdeg C T) = 2 * (T.card - 1) := by
        rw [sum_tdeg_eq hsub, hV2]
      set L := T.filter (fun R => tdeg C T R = 1)
      have hLge2 : 2 ≤ L.card := by
        have hlb : L.card + 2 * (T \ L).card ≤ T.sum (tdeg C T) := by
          have hsplit : T.sum (tdeg C T) = L.sum (tdeg C T) + (T \ L).sum (tdeg C T) := by
            rw [← Finset.sum_union Finset.disjoint_sdiff,
              Finset.union_sdiff_of_subset (Finset.filter_subset _ T)]
          rw [hsplit]
          have hLsum : L.sum (tdeg C T) = L.card := by
            rw [Finset.sum_const_nat (fun R hR => (Finset.mem_filter.mp hR).2), mul_one]
          have hRsum : 2 * (T \ L).card ≤ (T \ L).sum (tdeg C T) := by
            calc 2 * (T \ L).card = (T \ L).sum (fun _ => 2) := by
                  rw [Finset.sum_const_nat (fun _ _ => rfl), mul_comm]
              _ ≤ (T \ L).sum (tdeg C T) := by
                  refine Finset.sum_le_sum fun R hR => ?_
                  rcases Finset.mem_sdiff.mp hR with ⟨hRT, hRnL⟩
                  have hpos := tdeg_pos_of_card_gt_three h3 hsub hdeg hconn hCgt3 hRT
                  have hne1 : tdeg C T R ≠ 1 := fun h1 => hRnL (Finset.mem_filter.mpr ⟨hRT, h1⟩)
                  omega
          omega
        have hsd : (T \ L).card = T.card - L.card := Finset.card_sdiff_of_subset (Finset.filter_subset _ T)
        have hLle : L.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ T)
        omega
      by_cases hex : ∃ R ∈ L, r ∉ R
      · rcases hex with ⟨R, hRL, hrR⟩
        have hRT : R ∈ T := (Finset.mem_filter.mp hRL).1
        have h1 : (R ∩ V2 C T).card = 1 := (Finset.mem_filter.mp hRL).2
        rcases Finset.card_eq_one.mp h1 with ⟨v, hv⟩
        rw [localMatch_peel_leaf h3 hsub hdeg hlin hconn hr hcard hRT hrR hv]
        have hp := peel_leaf_props h3 hsub hdeg hconn hRT hv
        rcases hp with ⟨hvR, _, hC'card, hT'card, _, hsub', hconn'⟩
        refine ih (C \ (R.erase v)) (T.erase R) r (by omega)
          (fun R' hR' => h3 R' (Finset.mem_of_mem_erase hR'))
          hsub'
          (fun u => (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset R T))).trans (hdeg u))
          (fun R₁ h1 R₂ h2 => hlin R₁ (Finset.mem_of_mem_erase h1) R₂ (Finset.mem_of_mem_erase h2))
          hconn'
          (Finset.mem_sdiff.mpr ⟨hr, fun h => hrR (Finset.mem_of_mem_erase h)⟩)
          (by omega)
      · push_neg at hex
        have hLsub : L ⊆ T.filter (fun R => r ∈ R) := fun R hR =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hR).1, hex R hR⟩
        have hLle2 : L.card ≤ 2 := (Finset.card_le_card hLsub).trans (hdeg r)
        have hL2 : L.card = 2 := le_antisymm hLle2 hLge2
        rcases Finset.card_eq_two.mp hL2 with ⟨R₁, R₂, hRne, hLeq⟩
        have hR1L : R₁ ∈ L := by rw [hLeq]; simp
        have hR2L : R₂ ∈ L := by rw [hLeq]; simp
        have hR1T : R₁ ∈ T := (Finset.mem_filter.mp hR1L).1
        have hR2T : R₂ ∈ T := (Finset.mem_filter.mp hR2L).1
        have hr1 : r ∈ R₁ := hex R₁ hR1L
        have hr2 : r ∈ R₂ := hex R₂ hR2L
        have hrV2 : r ∈ V2 C T := by
          refine Finset.mem_filter.mpr ⟨hr, ?_⟩
          have hge : 2 ≤ degT T r := by
            dsimp only [degT]
            have := Finset.card_le_card hLsub
            omega
          exact le_antisymm (hdeg r) hge
        have hR1V2 : R₁ ∩ V2 C T = {r} := by
          refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
          · exact Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hr1, hrV2⟩)
          · rw [Finset.card_singleton]; exact le_of_eq (Finset.mem_filter.mp hR1L).2
        have hR2V2 : R₂ ∩ V2 C T = {r} := by
          refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
          · exact Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hr2, hrV2⟩)
          · rw [Finset.card_singleton]; exact le_of_eq (Finset.mem_filter.mp hR2L).2
        have hT2 : T.card = 2 := by
          by_contra hne2
          have hCge7 : 7 ≤ C.card := by omega
          have hUcard : (R₁ ∪ R₂).card ≤ 5 := by
            have := Finset.card_union_add_card_inter R₁ R₂
            have h1 : 1 ≤ (R₁ ∩ R₂).card := Finset.card_pos.mpr ⟨r, Finset.mem_inter.mpr ⟨hr1, hr2⟩⟩
            rw [h3 R₁ hR1T, h3 R₂ hR2T] at this
            omega
          have hUss : R₁ ∪ R₂ ⊂ C := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.union_subset (hsub R₁ hR1T) (hsub R₂ hR2T), ?_⟩
            intro heq; rw [heq] at hUcard; omega
          rcases hconn.2 (R₁ ∪ R₂) ⟨r, Finset.mem_union_left _ hr1⟩ hUss with ⟨R', hR'T, hnd, hnot⟩
          have hR'ne1 : R' ≠ R₁ := fun h => hnot (h ▸ Finset.subset_union_left)
          have hR'ne2 : R' ≠ R₂ := fun h => hnot (h ▸ Finset.subset_union_right)
          rw [Finset.not_disjoint_iff] at hnd
          rcases hnd with ⟨w, hwR', hwU⟩
          have hw2 : degT T w = 2 := by
            rcases Finset.mem_union.mp hwU with hw1 | hw2'
            · have hp : ({R₁, R'} : Finset _) ⊆ T.filter (fun X => w ∈ X) := by
                intro X hX; simp only [Finset.mem_insert, Finset.mem_singleton] at hX
                rcases hX with rfl | rfl
                · exact Finset.mem_filter.mpr ⟨hR1T, hw1⟩
                · exact Finset.mem_filter.mpr ⟨hR'T, hwR'⟩
              have hge : 2 ≤ degT T w := (Finset.card_pair hR'ne1.symm) ▸ Finset.card_le_card hp
              exact le_antisymm (hdeg w) hge
            · have hp : ({R₂, R'} : Finset _) ⊆ T.filter (fun X => w ∈ X) := by
                intro X hX; simp only [Finset.mem_insert, Finset.mem_singleton] at hX
                rcases hX with rfl | rfl
                · exact Finset.mem_filter.mpr ⟨hR2T, hw2'⟩
                · exact Finset.mem_filter.mpr ⟨hR'T, hwR'⟩
              have hge : 2 ≤ degT T w := (Finset.card_pair hR'ne2.symm) ▸ Finset.card_le_card hp
              exact le_antisymm (hdeg w) hge
          have hwr : w = r := by
            rcases Finset.mem_union.mp hwU with hw1 | hw2'
            · have : w ∈ R₁ ∩ V2 C T := Finset.mem_inter.mpr ⟨hw1, Finset.mem_filter.mpr ⟨hsub R₁ hR1T hw1, hw2⟩⟩
              rwa [hR1V2, Finset.mem_singleton] at this
            · have : w ∈ R₂ ∩ V2 C T := Finset.mem_inter.mpr ⟨hw2', Finset.mem_filter.mpr ⟨hsub R₂ hR2T hw2', hw2⟩⟩
              rwa [hR2V2, Finset.mem_singleton] at this
          subst hwr
          have h3sub : ({R₁, R₂, R'} : Finset _) ⊆ T.filter (fun X => w ∈ X) := by
            intro X hX; simp only [Finset.mem_insert, Finset.mem_singleton] at hX
            rcases hX with rfl | rfl | rfl
            · exact Finset.mem_filter.mpr ⟨hR1T, hr1⟩
            · exact Finset.mem_filter.mpr ⟨hR2T, hr2⟩
            · exact Finset.mem_filter.mpr ⟨hR'T, hwR'⟩
          have hc3 : ({R₁, R₂, R'} : Finset _).card = 3 := by
            rw [Finset.card_insert_of_notMem, Finset.card_pair hR'ne2.symm]
            simp [hRne, hR'ne1.symm]
          have := hc3 ▸ Finset.card_le_card h3sub
          have hdw := hdeg w
          dsimp only [degT] at hdw
          omega
        have hTeq : T = {R₁, R₂} :=
          (Finset.eq_of_subset_of_card_le (Finset.filter_subset _ T)
            (by rw [hL2, hT2])).symm.trans hLeq
        have hinter : R₁ ∩ R₂ = {r} := by
          have hle := hlin R₁ hR1T R₂ hR2T hRne
          refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
          · exact Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨hr1, hr2⟩)
          · rw [Finset.card_singleton]; exact hle
        have hg1card : (R₁.erase r).card = 2 := by rw [Finset.card_erase_of_mem hr1, h3 R₁ hR1T]
        have hg2card : (R₂.erase r).card = 2 := by rw [Finset.card_erase_of_mem hr2, h3 R₂ hR2T]
        have hdisj12 : Disjoint (R₁.erase r) (R₂.erase r) := by
          rw [Finset.disjoint_left]
          intro u hu1 hu2
          have huI : u ∈ R₁ ∩ R₂ := Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase hu1, Finset.mem_of_mem_erase hu2⟩
          rw [hinter, Finset.mem_singleton] at huI
          exact (Finset.mem_erase.mp hu1).1 huI
        have heq : LocalMatch C T r = {{R₁.erase r, R₂.erase r}} := by
          ext M
          simp only [LocalMatch, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hM
            have hMmem : M ∈ LocalMatch C T r := by
              simp only [LocalMatch, Finset.mem_filter, Finset.mem_univ, true_and]; exact hM
            rcases localMatch_tight h3 hlin hr hcard hMmem with ⟨hMcard, _, _⟩
            rcases hM.2.2 R₁ hR1T with ⟨g₁, hg1M, hg1R1⟩
            rcases hM.2.2 R₂ hR2T with ⟨g₂, hg2M, hg2R2⟩
            have hg1eq : g₁ = R₁.erase r := by
              refine Finset.eq_of_subset_of_card_le (fun u hu => Finset.mem_erase.mpr
                ⟨(Finset.mem_erase.mp ((hM.1 g₁ hg1M).2 hu)).1, hg1R1 hu⟩) ?_
              rw [hg1card, (hM.1 g₁ hg1M).1]
            have hg2eq : g₂ = R₂.erase r := by
              refine Finset.eq_of_subset_of_card_le (fun u hu => Finset.mem_erase.mpr
                ⟨(Finset.mem_erase.mp ((hM.1 g₂ hg2M).2 hu)).1, hg2R2 hu⟩) ?_
              rw [hg2card, (hM.1 g₂ hg2M).1]
            have hne12 : R₁.erase r ≠ R₂.erase r := by
              intro h
              obtain ⟨w, hw⟩ : (R₁.erase r).Nonempty := Finset.card_pos.mp (by omega)
              exact Finset.disjoint_left.mp hdisj12 hw (h ▸ hw)
            have hsubM : ({R₁.erase r, R₂.erase r} : Finset _) ⊆ M := by
              intro g hg; simp only [Finset.mem_insert, Finset.mem_singleton] at hg
              rcases hg with rfl | rfl
              · exact hg1eq ▸ hg1M
              · exact hg2eq ▸ hg2M
            exact (Finset.eq_of_subset_of_card_le hsubM (by rw [Finset.card_pair hne12, hMcard, hT2])).symm
          · rintro rfl
            refine ⟨fun g hg => ?_, fun g hg h hh hne => ?_, fun R' hR' => ?_⟩
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hg
              rcases hg with rfl | rfl
              · exact ⟨hg1card, Finset.erase_subset_erase r (hsub R₁ hR1T)⟩
              · exact ⟨hg2card, Finset.erase_subset_erase r (hsub R₂ hR2T)⟩
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hg hh
              rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
              · exact absurd rfl hne
              · exact hdisj12
              · exact hdisj12.symm
              · exact absurd rfl hne
            · rw [hTeq] at hR'; simp only [Finset.mem_insert, Finset.mem_singleton] at hR'
              rcases hR' with h | h
              · rw [h]; exact ⟨R₁.erase r, by simp, Finset.erase_subset r R₁⟩
              · rw [h]; exact ⟨R₂.erase r, by simp, Finset.erase_subset r R₂⟩
        rw [heq, Finset.card_singleton]

lemma localMatchFull_peel_leaf {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))}
    (h3 : ∀ R ∈ T, R.card = 3) (hsub : ∀ R ∈ T, R ⊆ C)
    (hdeg : ∀ u, degT T u ≤ 2)
    (hlin : ∀ R₁ ∈ T, ∀ R₂ ∈ T, R₁ ≠ R₂ → (R₁ ∩ R₂).card ≤ 1)
    (hconn : Connected C T)
    (hcard : C.card = 2 * T.card)
    {R : Finset (Fin n)} (hRT : R ∈ T)
    {v : Fin n} (hleaf : R ∩ V2 C T = {v}) :
    (LocalMatchFull C T).card = (LocalMatchFull (C \ (R.erase v)) (T.erase R)).card := by
  have hp := peel_leaf_props h3 hsub hdeg hconn hRT hleaf
  rcases hp with ⟨hvR, _, _, _, hnotin, _, _⟩
  set g₀ := R.erase v
  have hg₀2 : g₀.card = 2 := by rw [Finset.card_erase_of_mem hvR, h3 R hRT]
  have hg₀sub : g₀ ⊆ C := (Finset.erase_subset v R).trans (hsub R hRT)
  have hforced : ∀ M ∈ LocalMatchFull C T, g₀ ∈ M := by
    intro M hM
    rcases localMatchFull_tight h3 hlin hcard hM with ⟨_, hUeq, hall⟩
    have hMspec := (Finset.mem_filter.mp hM).2
    rcases hMspec.2.2 R hRT with ⟨gR, hgRM, hgRR⟩
    have hsubg : g₀ ⊆ gR := by
      intro w hwg₀
      have hwU : w ∈ M.biUnion id := by rw [hUeq]; exact hg₀sub hwg₀
      rcases Finset.mem_biUnion.mp hwU with ⟨g, hgM, hwg⟩
      rcases hall g hgM with ⟨R', hR'T, hgR'⟩
      have hR'eq : R' = R := by
        by_contra hne
        exact hnotin w hwg₀ R' (Finset.mem_erase.mpr ⟨hne, hR'T⟩) (hgR' hwg)
      rw [hR'eq] at hgR'
      have hgeq := witness_unique_g (fun x hx => (hMspec.1 x hx).1) hMspec.2.1 (h3 R hRT)
        hgM hgRM hgR' hgRR
      exact hgeq ▸ hwg
    have hg₀eq : g₀ = gR :=
      Finset.eq_of_subset_of_card_le hsubg (by rw [hg₀2, (hMspec.1 gR hgRM).1])
    exact hg₀eq ▸ hgRM
  refine Finset.card_nbij' (fun M => M.erase g₀) (fun M' => insert g₀ M') ?_ ?_ ?_ ?_
  · intro M hM
    simp only [Finset.mem_coe] at hM ⊢
    have hg₀M := hforced M hM
    have hMspec := (Finset.mem_filter.mp hM).2
    simp only [LocalMatchFull, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun g hg => ?_, fun g hg h hh hne => ?_, fun R' hR' => ?_⟩
    · rcases Finset.mem_erase.mp hg with ⟨hgne, hgM⟩
      have hdisj := hMspec.2.1 g hgM g₀ hg₀M hgne
      exact ⟨(hMspec.1 g hgM).1, fun u hug =>
        Finset.mem_sdiff.mpr ⟨(hMspec.1 g hgM).2 hug, Finset.disjoint_left.mp hdisj hug⟩⟩
    · exact hMspec.2.1 g (Finset.mem_of_mem_erase hg) h (Finset.mem_of_mem_erase hh) hne
    · rcases hMspec.2.2 R' (Finset.mem_of_mem_erase hR') with ⟨g, hgM, hgR'⟩
      refine ⟨g, Finset.mem_erase.mpr ⟨?_, hgM⟩, hgR'⟩
      intro hgeq
      subst hgeq
      obtain ⟨w, hwg₀⟩ : g₀.Nonempty := Finset.card_pos.mp (by omega)
      exact hnotin w hwg₀ R' hR' (hgR' hwg₀)
  · intro M' hM'
    simp only [Finset.mem_coe] at hM' ⊢
    have hM'spec := (Finset.mem_filter.mp hM').2
    simp only [LocalMatchFull, Finset.mem_filter, Finset.mem_univ, true_and]
    have hdisj0 : ∀ g ∈ M', Disjoint g₀ g := by
      intro g hg
      rw [Finset.disjoint_left]
      intro w hwg₀ hwg
      exact (Finset.mem_sdiff.mp ((hM'spec.1 g hg).2 hwg)).2 hwg₀
    refine ⟨fun g hg => ?_, fun g hg h hh hne => ?_, fun R' hR' => ?_⟩
    · rcases Finset.mem_insert.mp hg with rfl | hgM'
      · exact ⟨hg₀2, hg₀sub⟩
      · exact ⟨(hM'spec.1 g hgM').1, ((hM'spec.1 g hgM').2).trans Finset.sdiff_subset⟩
    · rcases Finset.mem_insert.mp hg with rfl | hgM' <;>
      rcases Finset.mem_insert.mp hh with rfl | hhM'
      · exact absurd rfl hne
      · exact hdisj0 h hhM'
      · exact (hdisj0 g hgM').symm
      · exact hM'spec.2.1 g hgM' h hhM' hne
    · by_cases hR'eq : R' = R
      · rw [hR'eq]
        exact ⟨g₀, Finset.mem_insert_self g₀ M', Finset.erase_subset v R⟩
      · rcases hM'spec.2.2 R' (Finset.mem_erase.mpr ⟨hR'eq, hR'⟩) with ⟨g, hgM', hgR'⟩
        exact ⟨g, Finset.mem_insert_of_mem hgM', hgR'⟩
  · intro M hM
    exact Finset.insert_erase (hforced M hM)
  · intro M' hM'
    have hg₀nm : g₀ ∉ M' := by
      intro hg₀M'
      have hM'spec := (Finset.mem_filter.mp hM').2
      obtain ⟨w, hwg₀⟩ : g₀.Nonempty := Finset.card_pos.mp (by omega)
      exact (Finset.mem_sdiff.mp ((hM'spec.1 g₀ hg₀M').2 hwg₀)).2 hwg₀
    exact Finset.erase_insert hg₀nm

lemma cycle_erase_connected {n : Nat} {C : Finset (Fin n)} {T : Finset (Finset (Fin n))}
    (h3 : ∀ R ∈ T, R.card = 3) (hsub : ∀ R ∈ T, R ⊆ C)
    (hdeg : ∀ u, degT T u ≤ 2) (hconn : Connected C T)
    (hall2 : ∀ R ∈ T, tdeg C T R = 2)
    {R₀ : Finset (Fin n)} (hR₀ : R₀ ∈ T) {a₀ v₁ v₂ : Fin n}
    (hR₀V2 : R₀ ∩ V2 C T = {v₁, v₂}) (hv12 : v₁ ≠ v₂)
    (ha₀ : R₀ \ V2 C T = {a₀}) :
    Connected (C.erase a₀) (T.erase R₀) := by
  have ha₀m : a₀ ∈ R₀ \ V2 C T := by rw [ha₀]; simp
  have ha₀R₀ : a₀ ∈ R₀ := (Finset.mem_sdiff.mp ha₀m).1
  have ha₀nV2 : a₀ ∉ V2 C T := (Finset.mem_sdiff.mp ha₀m).2
  have ha₀C : a₀ ∈ C := hsub R₀ hR₀ ha₀R₀
  have hv1m : v₁ ∈ R₀ ∩ V2 C T := by rw [hR₀V2]; simp
  have hv2m : v₂ ∈ R₀ ∩ V2 C T := by rw [hR₀V2]; simp
  have hv1R₀ : v₁ ∈ R₀ := (Finset.mem_inter.mp hv1m).1
  have hv2R₀ : v₂ ∈ R₀ := (Finset.mem_inter.mp hv2m).1
  have hv1V2 : v₁ ∈ V2 C T := (Finset.mem_inter.mp hv1m).2
  have hv2V2 : v₂ ∈ V2 C T := (Finset.mem_inter.mp hv2m).2
  have hv1a₀ : v₁ ≠ a₀ := fun h => ha₀nV2 (h ▸ hv1V2)
  have hv2a₀ : v₂ ≠ a₀ := fun h => ha₀nV2 (h ▸ hv2V2)
  have ha₀only : ∀ R' ∈ T.erase R₀, a₀ ∉ R' := by
    intro R' hR' ha₀R'
    rcases Finset.mem_erase.mp hR' with ⟨hne, hR'T⟩
    have hge : 2 ≤ degT T a₀ := by
      have hp : ({R₀, R'} : Finset _) ⊆ T.filter (fun X => a₀ ∈ X) := by
        intro X hX; simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        rcases hX with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hR₀, ha₀R₀⟩
        · exact Finset.mem_filter.mpr ⟨hR'T, ha₀R'⟩
      exact (Finset.card_pair hne.symm) ▸ Finset.card_le_card hp
    exact ha₀nV2 (Finset.mem_filter.mpr ⟨ha₀C, le_antisymm (hdeg a₀) hge⟩)
  have hR₀eq : R₀ = {a₀, v₁, v₂} := by
    ext u
    by_cases hu : u ∈ V2 C T
    · have : u ∈ R₀ ↔ u ∈ R₀ ∩ V2 C T := by simp [hu]
      rw [this, hR₀V2]
      have hua : u ≠ a₀ := fun h => ha₀nV2 (h ▸ hu)
      simp [hua]
    · have : u ∈ R₀ ↔ u ∈ R₀ \ V2 C T := by simp [hu]
      rw [this, ha₀]
      have hu1 : u ≠ v₁ := fun h => hu (h ▸ hv1V2)
      have hu2 : u ≠ v₂ := fun h => hu (h ▸ hv2V2)
      simp [hu1, hu2]
  refine ⟨⟨v₁, Finset.mem_erase.mpr ⟨hv1a₀, hsub R₀ hR₀ hv1R₀⟩⟩, fun S hSne hSss => ?_⟩
  by_contra hno
  push_neg at hno
  have hsplit : ∀ R' ∈ T.erase R₀, R' ⊆ S ∨ Disjoint R' S := by
    intro R' hR'
    by_cases hd : Disjoint R' S
    · exact Or.inr hd
    · exact Or.inl (hno R' hR' hd)
  have hnot_both_out : ¬ (v₁ ∉ S ∧ v₂ ∉ S) := by
    rintro ⟨h1, h2⟩
    have ha₀S : a₀ ∉ S := fun h => (Finset.mem_erase.mp (hSss.1 h)).1 rfl
    have hdR₀ : Disjoint R₀ S := by
      rw [hR₀eq, Finset.disjoint_left]
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl <;> assumption
    have hSssC : S ⊂ C := lt_of_lt_of_le hSss (Finset.erase_subset a₀ C)
    rcases hconn.2 S hSne hSssC with ⟨R, hRT, hnd, hnot⟩
    have hRne : R ≠ R₀ := fun h => hnd (h ▸ hdR₀)
    rcases hsplit R (Finset.mem_erase.mpr ⟨hRne, hRT⟩) with hs | hd
    · exact hnot hs
    · exact hnd hd
  have hnot_both_in : ¬ (v₁ ∈ S ∧ v₂ ∈ S) := by
    rintro ⟨h1, h2⟩
    set S' := insert a₀ S
    have hS'ss : S' ⊂ C := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.insert_subset ha₀C
        (hSss.1.trans (Finset.erase_subset a₀ C)), ?_⟩
      intro heq
      apply hSss.2
      intro x hx
      rcases Finset.mem_erase.mp hx with ⟨hxa, hxC⟩
      have hxS' : x ∈ S' := heq.symm ▸ hxC
      rcases Finset.mem_insert.mp hxS' with rfl | hxS
      · exact absurd rfl hxa
      · exact hxS
    rcases hconn.2 S' (hSne.mono (Finset.subset_insert a₀ S)) hS'ss with ⟨R, hRT, hnd, hnot⟩
    by_cases hReq : R = R₀
    · subst hReq
      apply hnot
      rw [hR₀eq]
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with h | h | h
      · rw [h]; exact Finset.mem_insert_self a₀ S
      · rw [h]; exact Finset.mem_insert_of_mem h1
      · rw [h]; exact Finset.mem_insert_of_mem h2
    · have hRm : R ∈ T.erase R₀ := Finset.mem_erase.mpr ⟨hReq, hRT⟩
      rcases hsplit R hRm with hs | hd
      · exact hnot (hs.trans (Finset.subset_insert a₀ S))
      · apply hnd
        rw [Finset.disjoint_right]
        intro u huS'
        rcases Finset.mem_insert.mp huS' with rfl | huS
        · exact ha₀only R hRm
        · exact Finset.disjoint_right.mp hd huS
  have hparity : ∀ w w', (w = v₁ ∧ w' = v₂ ∨ w = v₂ ∧ w' = v₁) → w ∈ S → w' ∉ S → False := by
    intro w w' hww hwS hw'nS
    have hwR₀ : w ∈ R₀ := by rcases hww with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hwV2 : w ∈ V2 C T := by rcases hww with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    have hw'V2 : w' ∈ V2 C T := by rcases hww with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
    set TS := (T.erase R₀).filter (fun R' => R' ⊆ S)
    have hLHS : TS.sum (tdeg C T) = 2 * TS.card := by
      rw [Finset.sum_const_nat (fun R' hR' => hall2 R' (Finset.mem_of_mem_erase (Finset.mem_filter.mp hR').1)),
        mul_comm]
    have hRHS1 : TS.sum (tdeg C T) = (S ∩ V2 C T).sum (fun u => (TS.filter (fun R' => u ∈ R')).card) := by
      have hA : TS.sum (tdeg C T) = TS.sum (fun R' => (S ∩ V2 C T).sum (fun u => if u ∈ R' then 1 else 0)) := by
        refine Finset.sum_congr rfl fun R' hR' => ?_
        dsimp only [tdeg]
        rw [← Finset.card_filter]
        congr 1
        ext u
        simp only [Finset.mem_inter, Finset.mem_filter]
        constructor
        · rintro ⟨huR', huV2⟩
          exact ⟨⟨(Finset.mem_filter.mp hR').2 huR', huV2⟩, huR'⟩
        · rintro ⟨⟨_, huV2⟩, huR'⟩
          exact ⟨huR', huV2⟩
      rw [hA, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.card_filter]
    have hdeg_TS : ∀ u ∈ S ∩ V2 C T, (TS.filter (fun R' => u ∈ R')).card = if u = w then 1 else 2 := by
      intro u hu
      rcases Finset.mem_inter.mp hu with ⟨huS, huV2⟩
      have hu2 : (T.filter (fun R' => u ∈ R')).card = 2 := (Finset.mem_filter.mp huV2).2
      have hfeq : TS.filter (fun R' => u ∈ R') = (T.filter (fun R' => u ∈ R')).erase R₀ := by
        ext R'
        simp only [TS, Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨⟨hne, hR'T⟩, _⟩, huR'⟩
          exact ⟨hne, hR'T, huR'⟩
        · rintro ⟨hne, hR'T, huR'⟩
          have hR'm : R' ∈ T.erase R₀ := Finset.mem_erase.mpr ⟨hne, hR'T⟩
          rcases hsplit R' hR'm with hs | hd
          · exact ⟨⟨⟨hne, hR'T⟩, hs⟩, huR'⟩
          · exact absurd huS (Finset.disjoint_left.mp hd huR')
      rw [hfeq]
      by_cases huw : u = w
      · subst huw
        rw [if_pos rfl, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hR₀, hwR₀⟩), hu2]
      · rw [if_neg huw]
        have huR₀ : u ∉ R₀ := by
          intro h
          have : u ∈ R₀ ∩ V2 C T := Finset.mem_inter.mpr ⟨h, huV2⟩
          rw [hR₀V2] at this
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases hww with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rcases this with rfl | rfl
            · exact huw rfl
            · exact hw'nS huS
          · rcases this with rfl | rfl
            · exact hw'nS huS
            · exact huw rfl
        rw [Finset.erase_eq_of_notMem (s := T.filter (fun R' => u ∈ R'))
          (fun h => huR₀ (Finset.mem_filter.mp h).2), hu2]
    rw [Finset.sum_congr rfl hdeg_TS] at hRHS1
    have hwmem : w ∈ S ∩ V2 C T := Finset.mem_inter.mpr ⟨hwS, hwV2⟩
    rw [← Finset.add_sum_erase _ _ hwmem, if_pos rfl] at hRHS1
    have hrest : ((S ∩ V2 C T).erase w).sum (fun u => if u = w then 1 else 2) =
        2 * ((S ∩ V2 C T).erase w).card := by
      rw [Finset.sum_const_nat (fun u hu => if_neg (Finset.mem_erase.mp hu).1), mul_comm]
    rw [hrest, hLHS] at hRHS1
    omega
  by_cases h1 : v₁ ∈ S
  · by_cases h2 : v₂ ∈ S
    · exact hnot_both_in ⟨h1, h2⟩
    · exact hparity v₁ v₂ (Or.inl ⟨rfl, rfl⟩) h1 h2
  · by_cases h2 : v₂ ∈ S
    · exact hparity v₂ v₁ (Or.inr ⟨rfl, rfl⟩) h2 h1
    · exact hnot_both_out ⟨h1, h2⟩

lemma localMatchFull_card_two {n : Nat} :
    ∀ m : Nat, ∀ C : Finset (Fin n), ∀ T : Finset (Finset (Fin n)),
      T.card = m →
      (∀ R ∈ T, R.card = 3) → (∀ R ∈ T, R ⊆ C) →
      (∀ u, degT T u ≤ 2) →
      (∀ R₁ ∈ T, ∀ R₂ ∈ T, R₁ ≠ R₂ → (R₁ ∩ R₂).card ≤ 1) →
      Connected C T → C.card = 2 * T.card →
      (LocalMatchFull C T).card = 2 := by
  intro m
  induction m with
  | zero =>
    intro C T hm _ _ _ _ hconn hcard
    have := Finset.card_pos.mpr hconn.1
    omega
  | succ m ih =>
    intro C T hm h3 hsub hdeg hlin hconn hcard
    have hTge3 : 3 ≤ T.card := by
      by_contra hlt
      by_cases h1 : T.card = 1
      · rcases Finset.card_eq_one.mp h1 with ⟨R, hTeq⟩
        have hRT : R ∈ T := by rw [hTeq]; simp
        have := Finset.card_le_card (hsub R hRT)
        rw [h3 R hRT] at this
        omega
      · have h2 : T.card = 2 := by omega
        rcases Finset.card_eq_two.mp h2 with ⟨R₁, R₂, hne, hTeq⟩
        have h1T : R₁ ∈ T := by rw [hTeq]; simp
        have h2T : R₂ ∈ T := by rw [hTeq]; simp
        have hu := Finset.card_union_add_card_inter R₁ R₂
        have hle := hlin R₁ h1T R₂ h2T hne
        have hsubU := Finset.card_le_card (Finset.union_subset (hsub R₁ h1T) (hsub R₂ h2T))
        rw [h3 R₁ h1T, h3 R₂ h2T] at hu
        omega
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    have hCgt3 : 3 < C.card := by omega
    have hV2 : (V2 C T).card = T.card := by
      have := card_V2_add_card_C h3 hsub hdeg hconn hTne
      omega
    have hsum : T.sum (tdeg C T) = 2 * T.card := by
      rw [sum_tdeg_eq hsub, hV2]
    by_cases hleaf : ∃ R ∈ T, tdeg C T R = 1
    · rcases hleaf with ⟨R, hRT, htd1⟩
      rcases Finset.card_eq_one.mp htd1 with ⟨v, hv⟩
      rw [localMatchFull_peel_leaf h3 hsub hdeg hlin hconn hcard hRT hv]
      have hp := peel_leaf_props h3 hsub hdeg hconn hRT hv
      rcases hp with ⟨_, _, hC'card, hT'card, _, hsub', hconn'⟩
      exact ih (C \ (R.erase v)) (T.erase R) (by omega)
        (fun R' hR' => h3 R' (Finset.mem_of_mem_erase hR'))
        hsub'
        (fun u => (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset R T))).trans (hdeg u))
        (fun R₁ h1 R₂ h2 => hlin R₁ (Finset.mem_of_mem_erase h1) R₂ (Finset.mem_of_mem_erase h2))
        hconn'
        (by omega)
    · push_neg at hleaf
      have hallge2 : ∀ R ∈ T, 2 ≤ tdeg C T R := by
        intro R hRT
        have hpos := tdeg_pos_of_card_gt_three h3 hsub hdeg hconn hCgt3 hRT
        have hne1 := hleaf R hRT
        omega
      have hall2 : ∀ R ∈ T, tdeg C T R = 2 := by
        intro R hRT
        by_contra hne2
        have hgt2 : 3 ≤ tdeg C T R := by have := hallge2 R hRT; omega
        have hsumge : 2 * T.card + 1 ≤ T.sum (tdeg C T) := by
          rw [← Finset.add_sum_erase _ _ hRT]
          have hrest : 2 * (T.erase R).card ≤ (T.erase R).sum (tdeg C T) := by
            calc 2 * (T.erase R).card = (T.erase R).sum (fun _ => 2) := by
                  rw [Finset.sum_const_nat (fun _ _ => rfl), mul_comm]
              _ ≤ (T.erase R).sum (tdeg C T) :=
                  Finset.sum_le_sum fun R' hR' => hallge2 R' (Finset.mem_of_mem_erase hR')
          rw [Finset.card_erase_of_mem hRT] at hrest
          change 2 * (T.card - 1) ≤ ∑ x ∈ T.erase R, tdeg C T x at hrest
          omega
        omega
      obtain ⟨R₀, hR₀⟩ := hTne
      have htd0 : (R₀ ∩ V2 C T).card = 2 := hall2 R₀ hR₀
      rcases Finset.card_eq_two.mp htd0 with ⟨v₁, v₂, hv12, hR₀V2⟩
      have hdiff1 : (R₀ \ V2 C T).card = 1 := by
        have h := Finset.card_sdiff_add_card_inter R₀ (V2 C T)
        rw [h3 R₀ hR₀, htd0] at h
        omega
      rcases Finset.card_eq_one.mp hdiff1 with ⟨a₀, ha₀⟩
      have hconn' := cycle_erase_connected h3 hsub hdeg hconn hall2 hR₀ hR₀V2 hv12 ha₀
      have ha₀m : a₀ ∈ R₀ \ V2 C T := by rw [ha₀]; simp
      have ha₀R₀ : a₀ ∈ R₀ := (Finset.mem_sdiff.mp ha₀m).1
      have ha₀nV2 : a₀ ∉ V2 C T := (Finset.mem_sdiff.mp ha₀m).2
      have ha₀C : a₀ ∈ C := hsub R₀ hR₀ ha₀R₀
      have hv1m : v₁ ∈ R₀ ∩ V2 C T := by rw [hR₀V2]; simp
      have hv2m : v₂ ∈ R₀ ∩ V2 C T := by rw [hR₀V2]; simp
      have hv1R₀ : v₁ ∈ R₀ := (Finset.mem_inter.mp hv1m).1
      have hv2R₀ : v₂ ∈ R₀ := (Finset.mem_inter.mp hv2m).1
      have hv1a₀ : v₁ ≠ a₀ := fun h => ha₀nV2 (h ▸ (Finset.mem_inter.mp hv1m).2)
      have hv2a₀ : v₂ ≠ a₀ := fun h => ha₀nV2 (h ▸ (Finset.mem_inter.mp hv2m).2)
      have ha₀only : ∀ R' ∈ T.erase R₀, a₀ ∉ R' := by
        intro R' hR' ha₀R'
        rcases Finset.mem_erase.mp hR' with ⟨hne, hR'T⟩
        have hge : 2 ≤ degT T a₀ := by
          have hp : ({R₀, R'} : Finset _) ⊆ T.filter (fun X => a₀ ∈ X) := by
            intro X hX; simp only [Finset.mem_insert, Finset.mem_singleton] at hX
            rcases hX with rfl | rfl
            · exact Finset.mem_filter.mpr ⟨hR₀, ha₀R₀⟩
            · exact Finset.mem_filter.mpr ⟨hR'T, ha₀R'⟩
          exact (Finset.card_pair hne.symm) ▸ Finset.card_le_card hp
        exact ha₀nV2 (Finset.mem_filter.mpr ⟨ha₀C, le_antisymm (hdeg a₀) hge⟩)
      have hsub' : ∀ R' ∈ T.erase R₀, R' ⊆ C.erase a₀ := fun R' hR' u hu =>
        Finset.mem_erase.mpr ⟨fun h => ha₀only R' hR' (h ▸ hu),
          hsub R' (Finset.mem_of_mem_erase hR') hu⟩
      have hR₀eq : R₀ = {a₀, v₁, v₂} := by
        ext u
        by_cases hu : u ∈ V2 C T
        · have : u ∈ R₀ ↔ u ∈ R₀ ∩ V2 C T := by simp [hu]
          rw [this, hR₀V2]
          have hua : u ≠ a₀ := fun h => ha₀nV2 (h ▸ hu)
          simp [hua]
        · have : u ∈ R₀ ↔ u ∈ R₀ \ V2 C T := by simp [hu]
          rw [this, ha₀]
          have hu1 : u ≠ v₁ := fun h => hu (h ▸ (Finset.mem_inter.mp hv1m).2)
          have hu2 : u ≠ v₂ := fun h => hu (h ▸ (Finset.mem_inter.mp hv2m).2)
          simp [hu1, hu2]
      set g₁ : Finset (Fin n) := {a₀, v₁}
      set g₂ : Finset (Fin n) := {a₀, v₂}
      set F₁ := (LocalMatchFull C T).filter (fun M => g₁ ∈ M)
      set F₂ := (LocalMatchFull C T).filter (fun M => g₂ ∈ M)
      have hFdisj : Disjoint F₁ F₂ := by
        rw [Finset.disjoint_left]
        intro M hM1 hM2
        have hMspec := (Finset.mem_filter.mp (Finset.mem_filter.mp hM1).1).2
        have hg1 : g₁ ∈ M := (Finset.mem_filter.mp hM1).2
        have hg2 : g₂ ∈ M := (Finset.mem_filter.mp hM2).2
        have hgne : g₁ ≠ g₂ := by
          intro h
          have : v₁ ∈ g₂ := h ▸ (by simp [g₁])
          simp [g₂, hv1a₀, hv12] at this
        have hd := hMspec.2.1 g₁ hg1 g₂ hg2 hgne
        exact Finset.disjoint_left.mp hd (by simp [g₁] : a₀ ∈ g₁) (by simp [g₂])
      have hFunion : LocalMatchFull C T = F₁ ∪ F₂ := by
        ext M
        simp only [F₁, F₂, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hM
          rcases localMatchFull_tight h3 hlin hcard hM with ⟨_, hUeq, hall⟩
          have hMspec := (Finset.mem_filter.mp hM).2
          have ha₀U : a₀ ∈ M.biUnion id := by rw [hUeq]; exact ha₀C
          rcases Finset.mem_biUnion.mp ha₀U with ⟨g, hgM, ha₀g⟩
          dsimp only [id_eq] at ha₀g
          rcases hall g hgM with ⟨R', hR'T, hgR'⟩
          have hR'eq : R' = R₀ := by
            by_contra hne
            exact ha₀only R' (Finset.mem_erase.mpr ⟨hne, hR'T⟩) (hgR' ha₀g)
          rw [hR'eq] at hgR'
          have hge1 : (g.erase a₀).card = 1 := by
            rw [Finset.card_erase_of_mem ha₀g, (hMspec.1 g hgM).1]
          rcases Finset.card_eq_one.mp hge1 with ⟨w, hw⟩
          have hwm : w ∈ g.erase a₀ := by rw [hw]; simp
          rcases Finset.mem_erase.mp hwm with ⟨hwa₀, hwg⟩
          have hgeq : g = {a₀, w} := by
            ext u
            by_cases hua : u = a₀
            · rw [hua]; simp [ha₀g]
            · have : u ∈ g.erase a₀ ↔ u = w := by rw [hw]; simp
              rw [Finset.mem_erase] at this
              have huiff : u ∈ g ↔ u = w := by tauto
              simp [Finset.mem_insert, Finset.mem_singleton, hua, huiff]
          have hwR₀ : w ∈ R₀ := hgR' hwg
          rw [hR₀eq] at hwR₀
          simp only [Finset.mem_insert, Finset.mem_singleton, hwa₀, false_or] at hwR₀
          rcases hwR₀ with hwv | hwv
          · rw [hwv] at hgeq; rw [hgeq] at hgM; exact Or.inl ⟨hM, hgM⟩
          · rw [hwv] at hgeq; rw [hgeq] at hgM; exact Or.inr ⟨hM, hgM⟩
        · rintro (⟨hM, _⟩ | ⟨hM, _⟩) <;> exact hM
      have hbij : ∀ w : Fin n, w ∈ R₀ → w ≠ a₀ →
          ((LocalMatchFull C T).filter (fun M => ({a₀, w} : Finset (Fin n)) ∈ M)).card =
          (LocalMatch (C.erase a₀) (T.erase R₀) w).card := by
        intro w hwR₀ hwa₀
        set gw : Finset (Fin n) := {a₀, w}
        have hgw2 : gw.card = 2 := Finset.card_pair hwa₀.symm
        have hgwsub : gw ⊆ C := by
          intro u hu; simp only [gw, Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact ha₀C
          · exact hsub R₀ hR₀ hwR₀
        refine Finset.card_nbij' (fun M => M.erase gw) (fun M' => insert gw M') ?_ ?_ ?_ ?_
        · intro M hM
          simp only [Finset.mem_coe] at hM ⊢
          rcases Finset.mem_filter.mp hM with ⟨hMF, hgwM⟩
          have hMspec := (Finset.mem_filter.mp hMF).2
          simp only [LocalMatch, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun g hg => ?_, fun g hg h hh hne => ?_, fun R' hR' => ?_⟩
          · rcases Finset.mem_erase.mp hg with ⟨hgne, hgM⟩
            have hd := hMspec.2.1 g hgM gw hgwM hgne
            refine ⟨(hMspec.1 g hgM).1, fun u hug => ?_⟩
            have hun : u ∉ gw := Finset.disjoint_left.mp hd hug
            simp only [gw, Finset.mem_insert, Finset.mem_singleton, not_or] at hun
            exact Finset.mem_erase.mpr ⟨hun.2, Finset.mem_erase.mpr ⟨hun.1, (hMspec.1 g hgM).2 hug⟩⟩
          · exact hMspec.2.1 g (Finset.mem_of_mem_erase hg) h (Finset.mem_of_mem_erase hh) hne
          · rcases hMspec.2.2 R' (Finset.mem_of_mem_erase hR') with ⟨g, hgM, hgR'⟩
            refine ⟨g, Finset.mem_erase.mpr ⟨?_, hgM⟩, hgR'⟩
            intro hgeq
            exact ha₀only R' hR' (hgR' (hgeq ▸ Finset.mem_insert_self a₀ {w}))
        · intro M' hM'
          simp only [Finset.mem_coe] at hM' ⊢
          have hM'spec := (Finset.mem_filter.mp hM').2
          simp only [Finset.mem_filter, LocalMatchFull, Finset.mem_univ, true_and]
          have hdisjw : ∀ g ∈ M', Disjoint gw g := by
            intro g hg
            rw [Finset.disjoint_left]
            intro u hugw hug
            have hu := (hM'spec.1 g hg).2 hug
            rcases Finset.mem_erase.mp hu with ⟨huw, hua⟩
            rcases Finset.mem_erase.mp hua with ⟨hua₀, _⟩
            simp only [gw, Finset.mem_insert, Finset.mem_singleton] at hugw
            rcases hugw with rfl | rfl
            · exact hua₀ rfl
            · exact huw rfl
          refine ⟨⟨fun g hg => ?_, fun g hg h hh hne => ?_, fun R' hR' => ?_⟩,
            Finset.mem_insert_self gw M'⟩
          · rcases Finset.mem_insert.mp hg with rfl | hgM'
            · exact ⟨hgw2, hgwsub⟩
            · exact ⟨(hM'spec.1 g hgM').1,
                ((hM'spec.1 g hgM').2).trans ((Finset.erase_subset w _).trans (Finset.erase_subset a₀ C))⟩
          · rcases Finset.mem_insert.mp hg with rfl | hgM' <;>
            rcases Finset.mem_insert.mp hh with rfl | hhM'
            · exact absurd rfl hne
            · exact hdisjw h hhM'
            · exact (hdisjw g hgM').symm
            · exact hM'spec.2.1 g hgM' h hhM' hne
          · by_cases hR'eq : R' = R₀
            · subst hR'eq
              refine ⟨gw, Finset.mem_insert_self gw M', fun u hu => ?_⟩
              simp only [gw, Finset.mem_insert, Finset.mem_singleton] at hu
              rcases hu with rfl | rfl <;> assumption
            · rcases hM'spec.2.2 R' (Finset.mem_erase.mpr ⟨hR'eq, hR'⟩) with ⟨g, hgM', hgR'⟩
              exact ⟨g, Finset.mem_insert_of_mem hgM', hgR'⟩
        · intro M hM
          exact Finset.insert_erase (Finset.mem_filter.mp hM).2
        · intro M' hM'
          have hnm : gw ∉ M' := by
            intro h
            have hM'spec := (Finset.mem_filter.mp hM').2
            have hu := (hM'spec.1 gw h).2 (Finset.mem_insert_self a₀ {w})
            exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hu)).1 rfl
          exact Finset.erase_insert hnm
      have hcard' : (C.erase a₀).card = 2 * (T.erase R₀).card + 1 := by
        rw [Finset.card_erase_of_mem ha₀C, Finset.card_erase_of_mem hR₀, hcard]
        omega
      have hc1 : (LocalMatch (C.erase a₀) (T.erase R₀) v₁).card = 1 :=
        localMatch_card_one (T.erase R₀).card (C.erase a₀) (T.erase R₀) v₁ rfl
          (fun R' hR' => h3 R' (Finset.mem_of_mem_erase hR'))
          hsub'
          (fun u => (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset R₀ T))).trans (hdeg u))
          (fun R₁ h1 R₂ h2 => hlin R₁ (Finset.mem_of_mem_erase h1) R₂ (Finset.mem_of_mem_erase h2))
          hconn'
          (Finset.mem_erase.mpr ⟨hv1a₀, hsub R₀ hR₀ hv1R₀⟩)
          hcard'
      have hc2 : (LocalMatch (C.erase a₀) (T.erase R₀) v₂).card = 1 :=
        localMatch_card_one (T.erase R₀).card (C.erase a₀) (T.erase R₀) v₂ rfl
          (fun R' hR' => h3 R' (Finset.mem_of_mem_erase hR'))
          hsub'
          (fun u => (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset R₀ T))).trans (hdeg u))
          (fun R₁ h1 R₂ h2 => hlin R₁ (Finset.mem_of_mem_erase h1) R₂ (Finset.mem_of_mem_erase h2))
          hconn'
          (Finset.mem_erase.mpr ⟨hv2a₀, hsub R₀ hR₀ hv2R₀⟩)
          hcard'
      rw [hFunion, Finset.card_union_of_disjoint hFdisj,
        hbij v₁ hv1R₀ hv1a₀, hbij v₂ hv2R₀ hv2a₀, hc1, hc2]

lemma card_pi_finset {α : Type} {β : α → Type} [DecidableEq α] [∀ a, DecidableEq (β a)]
    (s : Finset α) (t : ∀ a, Finset (β a)) :
    (s.pi t).card = s.prod (fun a => (t a).card) := by
  induction s using Finset.induction_on with
  | empty => simp [Finset.pi_empty]
  | insert a s ha ih =>
    rw [Finset.pi_insert ha, Finset.prod_insert ha, ← ih]
    rw [Finset.card_biUnion]
    · have hc : ∀ b ∈ t a, ((s.pi t).image (Finset.Pi.cons s a b)).card = (s.pi t).card :=
        fun b _ => Finset.card_image_of_injective _ (Finset.Pi.cons_injective ha)
      rw [Finset.sum_const_nat hc]
    · intro b₁ _ b₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro f hf1 hf2
      rcases Finset.mem_image.mp hf1 with ⟨g₁, _, rfl⟩
      rcases Finset.mem_image.mp hf2 with ⟨g₂, _, heq⟩
      have := congr_fun (congr_fun heq a) (Finset.mem_insert_self a s)
      simp only [Finset.Pi.cons_same] at this
      exact hne this.symm

def CoreMatchings {n : Nat} (H : Finset (Finset (Fin n))) (c : Finset (Fin n)) :
    Finset (Finset (Finset (Fin n))) :=
  Finset.univ.filter fun P =>
    P.card = 2 ∧
    (∀ g ∈ P, g.card = 2 ∧ (g ∩ c).card = 1 ∧ (g ∩ outer H c).card = 1) ∧
    (∀ g ∈ P, ∀ h ∈ P, g ≠ h → Disjoint g h)

def Mcore {n : Nat} (M : Finset (Finset (Fin n))) (c : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  M.filter (fun g => ¬ Disjoint g c)

lemma coreMatchings_explicit {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c : Finset (Fin n)} (hc : c ∈ cores H) :
    (CoreMatchings H c).card = 2 ∧
    ∀ P ∈ CoreMatchings H c,
      P.biUnion id = c ∪ outer H c ∧
      (∀ R ∈ rowsOf H c, ∃ g ∈ P, g ⊆ R) ∧
      (∀ g ∈ P, ¬ Disjoint g c ∧ g ⊆ c ∪ outer H c) := by
  have hcc : c.card = 2 := ((mem_cores_iff hH3).mp hc).1
  rcases Finset.card_eq_two.mp hcc with ⟨a, b, hab, hceq⟩
  rcases core_structure hH3 hdeg hc with ⟨x, y, hxy, hxord, hyord, hout, hrows⟩
  have hdisj_co : Disjoint c (outer H c) := Finset.disjoint_sdiff
  have hax : a ≠ x := fun h => Finset.disjoint_left.mp hdisj_co (by rw [hceq]; simp : a ∈ c) (by rw [hout, ← h]; simp)
  have hay : a ≠ y := fun h => Finset.disjoint_left.mp hdisj_co (by rw [hceq]; simp : a ∈ c) (by rw [hout, ← h]; simp)
  have hbx : b ≠ x := fun h => Finset.disjoint_left.mp hdisj_co (by rw [hceq]; simp : b ∈ c) (by rw [hout, ← h]; simp)
  have hby : b ≠ y := fun h => Finset.disjoint_left.mp hdisj_co (by rw [hceq]; simp : b ∈ c) (by rw [hout, ← h]; simp)
  set P₁ : Finset (Finset (Fin n)) := {{a, x}, {b, y}}
  set P₂ : Finset (Finset (Fin n)) := {{a, y}, {b, x}}
  have hP12ne : P₁ ≠ P₂ := by
    intro h
    have hm : ({a, x} : Finset (Fin n)) ∈ P₂ := h ▸ (by simp [P₁])
    simp only [P₂, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h1 | h2
    · have : x ∈ ({a, y} : Finset (Fin n)) := h1 ▸ (by simp)
      simp [hax.symm, hxy] at this
    · have : a ∈ ({b, x} : Finset (Fin n)) := h2 ▸ (by simp)
      simp [hab, hax] at this
  have hP1mem : P₁ ∈ CoreMatchings H c := by
    simp only [CoreMatchings, Finset.mem_filter, Finset.mem_univ, true_and]
    have hne : ({a, x} : Finset (Fin n)) ≠ {b, y} := by
      intro h; have : a ∈ ({b, y} : Finset (Fin n)) := h ▸ (by simp); simp [hab, hay] at this
    refine ⟨Finset.card_pair hne, fun g hg => ?_, fun g hg h hh hne' => ?_⟩
    · simp only [P₁, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · refine ⟨Finset.card_pair hax, ?_, ?_⟩
        · have : ({a, x} : Finset (Fin n)) ∩ c = {a} := by
            ext u; rw [hceq]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rfl
              · rcases h2 with h2 | h2
                · exact absurd h2.symm hax
                · exact absurd h2.symm hbx
            · rintro rfl; exact ⟨Or.inl rfl, Or.inl rfl⟩
          rw [this, Finset.card_singleton]
        · have : ({a, x} : Finset (Fin n)) ∩ outer H c = {x} := by
            ext u; rw [hout]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rcases h2 with h2 | h2
                · exact absurd h2 hax
                · exact absurd h2 hay
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, Or.inl rfl⟩
          rw [this, Finset.card_singleton]
      · refine ⟨Finset.card_pair hby, ?_, ?_⟩
        · have : ({b, y} : Finset (Fin n)) ∩ c = {b} := by
            ext u; rw [hceq]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rfl
              · rcases h2 with h2 | h2
                · exact absurd h2.symm hay
                · exact absurd h2.symm hby
            · rintro rfl; exact ⟨Or.inl rfl, Or.inr rfl⟩
          rw [this, Finset.card_singleton]
        · have : ({b, y} : Finset (Fin n)) ∩ outer H c = {y} := by
            ext u; rw [hout]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rcases h2 with h2 | h2
                · exact absurd h2 hbx
                · exact absurd h2 hby
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, Or.inr rfl⟩
          rw [this, Finset.card_singleton]
    · simp only [P₁, Finset.mem_insert, Finset.mem_singleton] at hg hh
      rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
      · exact absurd rfl hne'
      · rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
        rcases hu1 with rfl | rfl <;> rcases hu2 with h | h
        · exact hab h
        · exact hay h
        · exact hbx h.symm
        · exact hxy h
      · rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
        rcases hu1 with rfl | rfl <;> rcases hu2 with h | h
        · exact hab h.symm
        · exact hbx h
        · exact hay h.symm
        · exact hxy h.symm
      · exact absurd rfl hne'
  have hP2mem : P₂ ∈ CoreMatchings H c := by
    simp only [CoreMatchings, Finset.mem_filter, Finset.mem_univ, true_and]
    have hne : ({a, y} : Finset (Fin n)) ≠ {b, x} := by
      intro h; have : a ∈ ({b, x} : Finset (Fin n)) := h ▸ (by simp); simp [hab, hax] at this
    refine ⟨Finset.card_pair hne, fun g hg => ?_, fun g hg h hh hne' => ?_⟩
    · simp only [P₂, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · refine ⟨Finset.card_pair hay, ?_, ?_⟩
        · have : ({a, y} : Finset (Fin n)) ∩ c = {a} := by
            ext u; rw [hceq]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rfl
              · rcases h2 with h2 | h2
                · exact absurd h2.symm hay
                · exact absurd h2.symm hby
            · rintro rfl; exact ⟨Or.inl rfl, Or.inl rfl⟩
          rw [this, Finset.card_singleton]
        · have : ({a, y} : Finset (Fin n)) ∩ outer H c = {y} := by
            ext u; rw [hout]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rcases h2 with h2 | h2
                · exact absurd h2 hax
                · exact absurd h2 hay
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, Or.inr rfl⟩
          rw [this, Finset.card_singleton]
      · refine ⟨Finset.card_pair hbx, ?_, ?_⟩
        · have : ({b, x} : Finset (Fin n)) ∩ c = {b} := by
            ext u; rw [hceq]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rfl
              · rcases h2 with h2 | h2
                · exact absurd h2.symm hax
                · exact absurd h2.symm hbx
            · rintro rfl; exact ⟨Or.inl rfl, Or.inr rfl⟩
          rw [this, Finset.card_singleton]
        · have : ({b, x} : Finset (Fin n)) ∩ outer H c = {x} := by
            ext u; rw [hout]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, h2⟩
              · rcases h2 with h2 | h2
                · exact absurd h2 hbx
                · exact absurd h2 hby
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, Or.inl rfl⟩
          rw [this, Finset.card_singleton]
    · simp only [P₂, Finset.mem_insert, Finset.mem_singleton] at hg hh
      rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
      · exact absurd rfl hne'
      · rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
        rcases hu1 with rfl | rfl <;> rcases hu2 with h | h
        · exact hab h
        · exact hax h
        · exact hby h.symm
        · exact hxy h.symm
      · rw [Finset.disjoint_left]; intro u hu1 hu2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu1 hu2
        rcases hu1 with rfl | rfl <;> rcases hu2 with h | h
        · exact hab h.symm
        · exact hby h
        · exact hax h.symm
        · exact hxy h
      · exact absurd rfl hne'
  have hCM_eq : CoreMatchings H c = {P₁, P₂} := by
    ext P
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hP
      simp only [CoreMatchings, Finset.mem_filter, Finset.mem_univ, true_and] at hP
      rcases hP with ⟨hP2, hspec, hdisj⟩
      rcases Finset.card_eq_two.mp hP2 with ⟨g₁, g₂, hgne, hPeq⟩
      have hg1 : g₁ ∈ P := by rw [hPeq]; simp
      have hg2 : g₂ ∈ P := by rw [hPeq]; simp
      have hpair_form : ∀ g ∈ P, ∃ p ∈ c, ∃ q ∈ outer H c, g = {p, q} := by
        intro g hg
        rcases hspec g hg with ⟨hg2', hgc, hgo⟩
        rcases Finset.card_eq_one.mp hgc with ⟨p, hp⟩
        rcases Finset.card_eq_one.mp hgo with ⟨q, hq⟩
        have hpm : p ∈ g ∩ c := by rw [hp]; simp
        have hqm : q ∈ g ∩ outer H c := by rw [hq]; simp
        have hpq : p ≠ q := fun h => Finset.disjoint_left.mp hdisj_co
          (Finset.mem_inter.mp hpm).2 (h ▸ (Finset.mem_inter.mp hqm).2)
        have hsub : ({p, q} : Finset (Fin n)) ⊆ g := by
          intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact (Finset.mem_inter.mp hpm).1
          · exact (Finset.mem_inter.mp hqm).1
        refine ⟨p, (Finset.mem_inter.mp hpm).2, q, (Finset.mem_inter.mp hqm).2, ?_⟩
        exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hpq, hg2'])).symm
      rcases hpair_form g₁ hg1 with ⟨p₁, hp1c, q₁, hq1o, hg1eq⟩
      rcases hpair_form g₂ hg2 with ⟨p₂, hp2c, q₂, hq2o, hg2eq⟩
      have hd12 : Disjoint g₁ g₂ := hdisj g₁ hg1 g₂ hg2 hgne
      have hp12 : p₁ ≠ p₂ := fun h => Finset.disjoint_left.mp hd12
        (by rw [hg1eq]; simp : p₁ ∈ g₁) (by rw [hg2eq, ← h]; simp)
      have hq12 : q₁ ≠ q₂ := fun h => Finset.disjoint_left.mp hd12
        (by rw [hg1eq]; simp : q₁ ∈ g₁) (by rw [hg2eq, ← h]; simp)
      rw [hceq] at hp1c hp2c
      rw [hout] at hq1o hq2o
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp1c hp2c hq1o hq2o
      rcases hp1c with rfl | rfl <;> rcases hp2c with rfl | rfl
      · exact absurd rfl hp12
      · rcases hq1o with rfl | rfl <;> rcases hq2o with rfl | rfl
        · exact absurd rfl hq12
        · left; rw [hPeq, hg1eq, hg2eq]
        · right; rw [hPeq, hg1eq, hg2eq]
        · exact absurd rfl hq12
      · rcases hq1o with rfl | rfl <;> rcases hq2o with rfl | rfl
        · exact absurd rfl hq12
        · right; rw [hPeq, hg1eq, hg2eq, Finset.pair_comm]
        · left; rw [hPeq, hg1eq, hg2eq, Finset.pair_comm]
        · exact absurd rfl hq12
      · exact absurd rfl hp12
    · rintro (rfl | rfl)
      · exact hP1mem
      · exact hP2mem
  refine ⟨by rw [hCM_eq, Finset.card_pair hP12ne], fun P hP => ?_⟩
  rw [hCM_eq] at hP
  simp only [Finset.mem_insert, Finset.mem_singleton] at hP
  rcases hP with rfl | rfl
  · refine ⟨?_, ?_, ?_⟩
    · ext u; rw [hout, hceq]; simp [P₁, or_assoc, or_comm, or_left_comm]
    · intro R hR; rw [hrows] at hR; simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl
      · refine ⟨{a, x}, by simp [P₁], fun u hu => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h]; exact Finset.mem_insert_of_mem (by rw [hceq]; simp)
        · rw [h]; exact Finset.mem_insert_self x c
      · refine ⟨{b, y}, by simp [P₁], fun u hu => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h]; exact Finset.mem_insert_of_mem (by rw [hceq]; simp)
        · rw [h]; exact Finset.mem_insert_self y c
    · intro g hg; simp only [P₁, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · refine ⟨fun hd => Finset.disjoint_left.mp hd (by simp : a ∈ ({a, x} : Finset (Fin n))) (by rw [hceq]; simp), fun u hu => ?_⟩
        rw [hout, hceq]; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hu ⊢
        tauto
      · refine ⟨fun hd => Finset.disjoint_left.mp hd (by simp : b ∈ ({b, y} : Finset (Fin n))) (by rw [hceq]; simp), fun u hu => ?_⟩
        rw [hout, hceq]; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hu ⊢
        tauto
  · refine ⟨?_, ?_, ?_⟩
    · ext u; rw [hout, hceq]; simp [P₂, or_assoc, or_comm, or_left_comm]
    · intro R hR; rw [hrows] at hR; simp only [Finset.mem_insert, Finset.mem_singleton] at hR
      rcases hR with rfl | rfl
      · refine ⟨{b, x}, by simp [P₂], fun u hu => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h]; exact Finset.mem_insert_of_mem (by rw [hceq]; simp)
        · rw [h]; exact Finset.mem_insert_self x c
      · refine ⟨{a, y}, by simp [P₂], fun u hu => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h
        · rw [h]; exact Finset.mem_insert_of_mem (by rw [hceq]; simp)
        · rw [h]; exact Finset.mem_insert_self y c
    · intro g hg; simp only [P₂, Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · refine ⟨fun hd => Finset.disjoint_left.mp hd (by simp : a ∈ ({a, y} : Finset (Fin n))) (by rw [hceq]; simp), fun u hu => ?_⟩
        rw [hout, hceq]; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hu ⊢
        tauto
      · refine ⟨fun hd => Finset.disjoint_left.mp hd (by simp : b ∈ ({b, x} : Finset (Fin n))) (by rw [hceq]; simp), fun u hu => ?_⟩
        rw [hout, hceq]; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at hu ⊢
        tauto

lemma coreMatchings_disjoint {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {c₁ c₂ : Finset (Fin n)} (h1 : c₁ ∈ cores H) (h2 : c₂ ∈ cores H) (hne : c₁ ≠ c₂) :
    Disjoint (CoreMatchings H c₁) (CoreMatchings H c₂) := by
  rw [Finset.disjoint_left]
  intro P hP1 hP2
  have hu1 := ((coreMatchings_explicit hH3 hdeg h1).2 P hP1).1
  have hu2 := ((coreMatchings_explicit hH3 hdeg h2).2 P hP2).1
  have hcc1 : c₁.card = 2 := ((mem_cores_iff hH3).mp h1).1
  obtain ⟨u, hu⟩ : c₁.Nonempty := Finset.card_pos.mp (by omega)
  have huin : u ∈ c₂ ∪ outer H c₂ := by rw [← hu2, hu1]; exact Finset.mem_union_left _ hu
  rcases Finset.mem_union.mp huin with huc2 | huo2
  · exact Finset.disjoint_left.mp (cores_pairwise_disjoint hH3 hdeg h1 h2 hne) hu huc2
  · have huord := outer_subset_ordinary hH3 hdeg h2 huo2
    simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
    exact huord.2 ⟨c₁, h1, hu⟩

lemma mcore_behavior {n : Nat} {H M : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (h2 : ∀ g ∈ M, g.card = 2)
    (hdisj : ∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h)
    {c : Finset (Fin n)} (hc : c ∈ cores H)
    (hcov : ∀ R ∈ rowsOf H c, ∃ g ∈ M, g ⊆ R) :
    (c ∈ M ∧ Mcore M c = {c}) ∨ (c ∉ M ∧ Mcore M c ∈ CoreMatchings H c) := by
  by_cases hcM : c ∈ M
  · left
    refine ⟨hcM, ?_⟩
    ext g
    simp only [Mcore, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hgM, hnd⟩
      by_contra hne
      exact hnd (hdisj g hgM c hcM hne)
    · rintro h
      rw [h]
      have hcc := ((mem_cores_iff hH3).mp hc).1
      obtain ⟨u, hu⟩ : c.Nonempty := Finset.card_pos.mp (by omega)
      exact ⟨hcM, fun hd => Finset.disjoint_left.mp hd hu hu⟩
  · right
    refine ⟨hcM, ?_⟩
    have hcc := ((mem_cores_iff hH3).mp hc).1
    rcases core_structure hH3 hdeg hc with ⟨x, y, hxy, _, _, hout, hrows⟩
    have hdisj_co : Disjoint c (outer H c) := Finset.disjoint_sdiff
    have hxnc : x ∉ c := fun h => Finset.disjoint_left.mp hdisj_co h (by rw [hout]; simp)
    have hync : y ∉ c := fun h => Finset.disjoint_left.mp hdisj_co h (by rw [hout]; simp)
    have hR1m : insert x c ∈ rowsOf H c := by rw [hrows]; simp
    have hR2m : insert y c ∈ rowsOf H c := by rw [hrows]; simp
    rcases hcov _ hR1m with ⟨g₁, hg1M, hg1R1⟩
    rcases hcov _ hR2m with ⟨g₂, hg2M, hg2R2⟩
    have hg1c : g₁ ≠ c := fun h => hcM (h ▸ hg1M)
    have hg2c : g₂ ≠ c := fun h => hcM (h ▸ hg2M)
    have hxg1 : x ∈ g₁ := by
      by_contra hxn
      have hsub : g₁ ⊆ c := fun u hu => by
        rcases Finset.mem_insert.mp (hg1R1 hu) with rfl | huc
        · exact absurd hu hxn
        · exact huc
      exact hg1c (Finset.eq_of_subset_of_card_le hsub (by rw [h2 g₁ hg1M, hcc]))
    have hyg2 : y ∈ g₂ := by
      by_contra hyn
      have hsub : g₂ ⊆ c := fun u hu => by
        rcases Finset.mem_insert.mp (hg2R2 hu) with rfl | huc
        · exact absurd hu hyn
        · exact huc
      exact hg2c (Finset.eq_of_subset_of_card_le hsub (by rw [h2 g₂ hg2M, hcc]))
    have hg12ne : g₁ ≠ g₂ := by
      intro heq
      have hxR2 : x ∈ insert y c := hg2R2 (heq ▸ hxg1)
      rcases Finset.mem_insert.mp hxR2 with h | h
      · exact hxy h
      · exact hxnc h
    have hd12 : Disjoint g₁ g₂ := hdisj g₁ hg1M g₂ hg2M hg12ne
    have hg1_ic : (g₁ ∩ c).card = 1 := by
      have heq : g₁ ∩ c = g₁.erase x := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨hu1, huc⟩; exact ⟨fun h => hxnc (h ▸ huc), hu1⟩
        · rintro ⟨hux, hu1⟩
          rcases Finset.mem_insert.mp (hg1R1 hu1) with h | huc
          · exact absurd h hux
          · exact ⟨hu1, huc⟩
      rw [heq, Finset.card_erase_of_mem hxg1, h2 g₁ hg1M]
    have hg2_ic : (g₂ ∩ c).card = 1 := by
      have heq : g₂ ∩ c = g₂.erase y := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨hu2, huc⟩; exact ⟨fun h => hync (h ▸ huc), hu2⟩
        · rintro ⟨huy, hu2⟩
          rcases Finset.mem_insert.mp (hg2R2 hu2) with h | huc
          · exact absurd h huy
          · exact ⟨hu2, huc⟩
      rw [heq, Finset.card_erase_of_mem hyg2, h2 g₂ hg2M]
    have hg1_io : (g₁ ∩ outer H c).card = 1 := by
      have heq : g₁ ∩ outer H c = {x} := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_singleton, hout, Finset.mem_insert]
        constructor
        · rintro ⟨hu1, rfl | rfl⟩
          · rfl
          · rcases Finset.mem_insert.mp (hg1R1 hu1) with h | huc
            · exact absurd h.symm hxy
            · exact absurd huc hync
        · rintro rfl; exact ⟨hxg1, Or.inl rfl⟩
      rw [heq, Finset.card_singleton]
    have hg2_io : (g₂ ∩ outer H c).card = 1 := by
      have heq : g₂ ∩ outer H c = {y} := by
        ext u
        simp only [Finset.mem_inter, Finset.mem_singleton, hout, Finset.mem_insert]
        constructor
        · rintro ⟨hu2, rfl | rfl⟩
          · rcases Finset.mem_insert.mp (hg2R2 hu2) with h | huc
            · exact absurd h hxy
            · exact absurd huc hxnc
          · rfl
        · rintro rfl; exact ⟨hyg2, Or.inr rfl⟩
      rw [heq, Finset.card_singleton]
    have hc_sub : c ⊆ g₁ ∪ g₂ := by
      have hsub : (g₁ ∩ c) ∪ (g₂ ∩ c) ⊆ c :=
        Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
      have hdi : Disjoint (g₁ ∩ c) (g₂ ∩ c) :=
        hd12.mono Finset.inter_subset_left Finset.inter_subset_left
      have heq : (g₁ ∩ c) ∪ (g₂ ∩ c) = c :=
        Finset.eq_of_subset_of_card_le hsub
          (by rw [Finset.card_union_of_disjoint hdi, hg1_ic, hg2_ic, hcc])
      rw [← heq]
      exact Finset.union_subset (Finset.inter_subset_left.trans Finset.subset_union_left)
        (Finset.inter_subset_left.trans Finset.subset_union_right)
    have hMcore_eq : Mcore M c = {g₁, g₂} := by
      ext g
      simp only [Mcore, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hgM, hnd⟩
        rw [Finset.not_disjoint_iff] at hnd
        rcases hnd with ⟨u, hug, huc⟩
        rcases Finset.mem_union.mp (hc_sub huc) with hu1 | hu2
        · left; by_contra hne; exact Finset.disjoint_left.mp (hdisj g hgM g₁ hg1M hne) hug hu1
        · right; by_contra hne; exact Finset.disjoint_left.mp (hdisj g hgM g₂ hg2M hne) hug hu2
      · rintro (h | h)
        · rw [h]
          obtain ⟨u, hu⟩ : (g₁ ∩ c).Nonempty := Finset.card_pos.mp (by omega)
          exact ⟨hg1M, fun hd => Finset.disjoint_left.mp hd (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hu).2⟩
        · rw [h]
          obtain ⟨u, hu⟩ : (g₂ ∩ c).Nonempty := Finset.card_pos.mp (by omega)
          exact ⟨hg2M, fun hd => Finset.disjoint_left.mp hd (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hu).2⟩
    rw [hMcore_eq]
    simp only [CoreMatchings, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Finset.card_pair hg12ne, fun g hg => ?_, fun g hg h hh hne => ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with h | h
      · rw [h]; exact ⟨h2 g₁ hg1M, hg1_ic, hg1_io⟩
      · rw [h]; exact ⟨h2 g₂ hg2M, hg2_ic, hg2_io⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hg hh
      rcases hg with rfl | rfl <;> rcases hh with rfl | rfl
      · exact absurd rfl hne
      · exact hd12
      · exact hd12.symm
      · exact absurd rfl hne

def ValidAll {n : Nat} (H : Finset (Finset (Fin n))) (s : Nat) :
    Finset (Finset (Finset (Fin n))) :=
  Finset.univ.filter (fun M => Valid H M ∧ M.card = s)

lemma not_bad_and_baseSize_le_of_valid {n : Nat} {H M : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hM : Valid H M) :
    ¬ bad H ∧ baseSize H ≤ M.card := by
  rcases hM with ⟨h2, hdisj, hcov⟩
  constructor
  · rintro ⟨C, hC, hlt⟩
    set MC := M.filter (fun g => ∃ R ∈ baseC H C, g ⊆ R)
    have hMCcard : MC.card = tests H C :=
      linear_filter_card_eq (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
        (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
        h2 hdisj (fun R hR => hcov R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
    have hUsub : MC.biUnion id ⊆ C := by
      intro u hu
      rcases Finset.mem_biUnion.mp hu with ⟨g, hg, hug⟩
      rcases (Finset.mem_filter.mp hg).2 with ⟨R, hRC, hgR⟩
      exact (Finset.mem_filter.mp hRC).2 (hgR hug)
    have hUcard := card_biUnion_pairs (M := MC) (fun g hg => h2 g (Finset.mem_filter.mp hg).1)
      (fun g hg h hh hne => hdisj g (Finset.mem_filter.mp hg).1 h (Finset.mem_filter.mp hh).1 hne)
    have := Finset.card_le_card hUsub
    rw [hUcard, hMCcard] at this
    omega
  · set MB := M.filter (fun g => ∃ R ∈ base H, g ⊆ R)
    have hMBcard : MB.card = (base H).card :=
      linear_filter_card_eq (fun R hR => hH3 R (Finset.mem_filter.mp hR).1)
        (fun R₁ h1 R₂ h2' => base_linear hH3 h1 h2')
        h2 hdisj (fun R hR => hcov R (Finset.mem_filter.mp hR).1)
    have hmc_ge1 : ∀ c ∈ cores H, 1 ≤ (Mcore M c).card := by
      intro c hc
      have hbeh := mcore_behavior hH3 hdeg h2 hdisj hc
        (fun R hR => hcov R (Finset.mem_filter.mp hR).1)
      rcases hbeh with ⟨_, heq⟩ | ⟨_, hcm⟩
      · rw [heq, Finset.card_singleton]
      · have h2c := (Finset.mem_filter.mp hcm).2.1
        omega
    have hmc_disj_MB : ∀ c ∈ cores H, Disjoint (Mcore M c) MB := by
      intro c hc
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      rcases (Finset.mem_filter.mp hg2).2 with ⟨R, hRB, hgR⟩
      have hRord : R ⊆ ordinary H := (Finset.mem_filter.mp hRB).2
      apply (Finset.mem_filter.mp hg1).2
      rw [Finset.disjoint_left]
      intro u hug huc
      have huord := hRord (hgR hug)
      simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
      exact huord.2 ⟨c, hc, huc⟩
    have hmc_pair_disj : ∀ c₁ ∈ cores H, ∀ c₂ ∈ cores H, c₁ ≠ c₂ →
        Disjoint (Mcore M c₁) (Mcore M c₂) := by
      intro c₁ h1 c₂ h2' hne
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      have hbeh1 := mcore_behavior hH3 hdeg h2 hdisj h1
        (fun R hR => hcov R (Finset.mem_filter.mp hR).1)
      have hgsub1 : g ⊆ c₁ ∪ outer H c₁ := by
        rcases hbeh1 with ⟨_, heq⟩ | ⟨_, hcm⟩
        · rw [heq, Finset.mem_singleton] at hg1; rw [hg1]; exact Finset.subset_union_left
        · exact ((coreMatchings_explicit hH3 hdeg h1).2 _ hcm).2.2 g hg1 |>.2
      apply (Finset.mem_filter.mp hg2).2
      rw [Finset.disjoint_left]
      intro u hug huc2
      rcases Finset.mem_union.mp (hgsub1 hug) with huc1 | huo1
      · exact Finset.disjoint_left.mp (cores_pairwise_disjoint hH3 hdeg h1 h2' hne) huc1 huc2
      · have huord := outer_subset_ordinary hH3 hdeg h1 huo1
        simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
        exact huord.2 ⟨c₂, h2', huc2⟩
    have hsubM : MB ∪ (cores H).biUnion (Mcore M) ⊆ M := by
      refine Finset.union_subset (Finset.filter_subset _ M) ?_
      intro g hg
      rcases Finset.mem_biUnion.mp hg with ⟨c, _, hgc⟩
      exact (Finset.mem_filter.mp hgc).1
    have hdisjU : Disjoint MB ((cores H).biUnion (Mcore M)) := by
      rw [Finset.disjoint_right]
      intro g hg
      rcases Finset.mem_biUnion.mp hg with ⟨c, hc, hgc⟩
      exact Finset.disjoint_left.mp (hmc_disj_MB c hc) hgc
    have hle := Finset.card_le_card hsubM
    rw [Finset.card_union_of_disjoint hdisjU,
      Finset.card_biUnion (fun c₁ h1 c₂ h2' hne => hmc_pair_disj c₁ h1 c₂ h2' hne),
      hMBcard] at hle
    have hcsum : (cores H).card ≤ (cores H).sum (fun c => (Mcore M c).card) := by
      calc (cores H).card = (cores H).sum (fun _ => 1) := by
            rw [Finset.sum_const_nat (fun _ _ => rfl), mul_one]
        _ ≤ (cores H).sum (fun c => (Mcore M c).card) :=
            Finset.sum_le_sum hmc_ge1
    dsimp only [baseSize]
    omega

lemma parts_eq_trees_union_cycles {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3) (hnbad : ¬ bad H) :
    parts H = trees H ∪ cycles H ∧ Disjoint (trees H) (cycles H) := by
  constructor
  · ext C
    simp only [trees, cycles, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hC
      have hle : C.card ≤ 2 * tests H C + 1 :=
        card_le_two_mul_add_one
          (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
          (fun R hR => (Finset.mem_filter.mp hR).2)
          (component_connected H hC)
      have hge : 2 * tests H C ≤ C.card := by
        by_contra hlt
        exact hnbad ⟨C, hC, by omega⟩
      by_cases heq : C.card = 2 * tests H C + 1
      · exact Or.inl ⟨hC, heq⟩
      · exact Or.inr ⟨hC, by omega⟩
    · rintro (⟨hC, _⟩ | ⟨hC, _⟩) <;> exact hC
  · rw [Finset.disjoint_left]
    intro C h1 h2
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    omega

open Classical in
noncomputable def ValidNonCyc {n : Nat} (H : Finset (Finset (Fin n))) (k : Nat) :
    Finset (Finset (Finset (Fin n))) :=
  Finset.univ.filter fun N =>
    (∀ g ∈ N, g.card = 2 ∧ Disjoint g ((cycles H).biUnion id)) ∧
    (∀ g ∈ N, ∀ h ∈ N, g ≠ h → Disjoint g h) ∧
    (∀ R ∈ H, (∀ C ∈ cycles H, ¬ R ⊆ C) → ∃ g ∈ N, g ⊆ R) ∧
    N.card = k

lemma validAll_card_eq_pow_mul_noncyc {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hnbad : ¬ bad H) {s : Nat} (hs : baseSize H ≤ s) :
    (ValidAll H s).card =
      2 ^ (cycles H).card * (ValidNonCyc H (s - (cycles H).sum (tests H))).card := by
  have hcyc_le : (cycles H).sum (tests H) ≤ s := by
    have h1 := base_card_eq_sum_tests hH3
    have h2 : (cycles H).sum (tests H) ≤ (parts H).sum (tests H) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    dsimp only [baseSize] at hs
    omega
  set k := s - (cycles H).sum (tests H)
  set cycPi := (cycles H).pi (fun C => LocalMatchFull C (baseC H C))
  have hcycPi_card : cycPi.card = 2 ^ (cycles H).card := by
    rw [card_pi_finset]
    have h2 : ∀ C ∈ cycles H, (LocalMatchFull C (baseC H C)).card = 2 := by
      intro C hC
      have hCp : C ∈ parts H := (Finset.mem_filter.mp hC).1
      have hCcard : C.card = 2 * tests H C := (Finset.mem_filter.mp hC).2
      exact localMatchFull_card_two (tests H C) C (baseC H C) rfl
        (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
        (fun R hR => (Finset.mem_filter.mp hR).2)
        (fun u => (Finset.card_le_card (Finset.filter_subset_filter _
          ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)))).trans (hdeg u))
        (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
        (component_connected H hCp) hCcard
    rw [Finset.prod_congr rfl h2, Finset.prod_const]
  rw [← hcycPi_card, ← Finset.card_product]
  refine Finset.card_nbij'
    (fun M => (fun C _ => M.filter (fun g => g ⊆ C),
               M.filter (fun g => Disjoint g ((cycles H).biUnion id))))
    (fun p => ((cycles H).attach.biUnion (fun C => p.1 C.1 C.2)) ∪ p.2)
    ?_ ?_ ?_ ?_
  · intro M hM
    simp only [Finset.mem_coe, ValidAll, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
    rcases hM with ⟨⟨h2, hdisj, hcov⟩, hMcard⟩
    have hMC : ∀ C ∈ cycles H, M.filter (fun g => g ⊆ C) ∈ LocalMatchFull C (baseC H C) ∧
        (M.filter (fun g => g ⊆ C)).biUnion id = C ∧
        (M.filter (fun g => g ⊆ C)).card = tests H C := by
      intro C hC
      have hCp : C ∈ parts H := (Finset.mem_filter.mp hC).1
      have hCcard : C.card = 2 * tests H C := (Finset.mem_filter.mp hC).2
      have hmem : M.filter (fun g => g ⊆ C) ∈ LocalMatchFull C (baseC H C) := by
        simp only [LocalMatchFull, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun g hg => ⟨h2 g hg.1, hg.2⟩,
          fun g hg h hh hne => hdisj g hg.1 h hh.1 hne,
          fun R hR => ?_⟩
        rcases hcov R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1 with ⟨g, hgM, hgR⟩
        exact ⟨g, ⟨hgM, hgR.trans (Finset.mem_filter.mp hR).2⟩, hgR⟩
      rcases localMatchFull_tight
        (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
        (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
        hCcard hmem with ⟨hcard', hUeq, _⟩
      exact ⟨hmem, hUeq, hcard'⟩
    have hsplitM : ∀ g ∈ M, (∃ C ∈ cycles H, g ⊆ C) ∨ Disjoint g ((cycles H).biUnion id) := by
      intro g hgM
      by_cases hd : Disjoint g ((cycles H).biUnion id)
      · exact Or.inr hd
      · left
        rw [Finset.not_disjoint_iff] at hd
        rcases hd with ⟨u, hug, huU⟩
        rcases Finset.mem_biUnion.mp huU with ⟨C, hC, huC⟩
        dsimp only [id_eq] at huC
        have hUeq := (hMC C hC).2.1
        rw [← hUeq] at huC
        rcases Finset.mem_biUnion.mp huC with ⟨g', hg'f, hug'⟩
        dsimp only [id_eq] at hug'
        rcases Finset.mem_filter.mp hg'f with ⟨hg'M, hg'C⟩
        have hgeq : g = g' := by
          by_contra hne
          exact Finset.disjoint_left.mp (hdisj g hgM g' hg'M hne) hug hug'
        exact ⟨C, hC, hgeq ▸ hg'C⟩
    have hMdecomp : M = (cycles H).biUnion (fun C => M.filter (fun g => g ⊆ C)) ∪
        M.filter (fun g => Disjoint g ((cycles H).biUnion id)) := by
      ext g
      simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hgM
        rcases hsplitM g hgM with ⟨C, hC, hgC⟩ | hd
        · exact Or.inl ⟨C, hC, hgM, hgC⟩
        · exact Or.inr ⟨hgM, hd⟩
      · rintro (⟨_, _, hgM, _⟩ | ⟨hgM, _⟩) <;> exact hgM
    have hdisj_pieces : Disjoint ((cycles H).biUnion (fun C => M.filter (fun g => g ⊆ C)))
        (M.filter (fun g => Disjoint g ((cycles H).biUnion id))) := by
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      rcases Finset.mem_biUnion.mp hg1 with ⟨C, hC, hgf⟩
      rcases Finset.mem_filter.mp hgf with ⟨hgM, hgC⟩
      have hd := (Finset.mem_filter.mp hg2).2
      obtain ⟨u, hu⟩ : g.Nonempty := Finset.card_pos.mp (by rw [h2 g hgM]; omega)
      exact Finset.disjoint_left.mp hd hu (Finset.mem_biUnion.mpr ⟨C, hC, hgC hu⟩)
    have hdisj_cycs : ∀ C₁ ∈ cycles H, ∀ C₂ ∈ cycles H, C₁ ≠ C₂ →
        Disjoint (M.filter (fun g => g ⊆ C₁)) (M.filter (fun g => g ⊆ C₂)) := by
      intro C₁ h1 C₂ h2' hne
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      obtain ⟨u, hu⟩ : g.Nonempty := Finset.card_pos.mp (by rw [h2 g (Finset.mem_filter.mp hg1).1]; omega)
      exact Finset.disjoint_left.mp
        (parts_pairwise_disjoint H (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1 hne)
        ((Finset.mem_filter.mp hg1).2 hu) ((Finset.mem_filter.mp hg2).2 hu)
    have hNcard : (M.filter (fun g => Disjoint g ((cycles H).biUnion id))).card = k := by
      have h1 := congr_arg Finset.card hMdecomp
      rw [hMcard, Finset.card_union_of_disjoint hdisj_pieces,
        Finset.card_biUnion (fun C₁ h1 C₂ h2' hne => hdisj_cycs C₁ h1 C₂ h2' hne)] at h1
      have hsum : (cycles H).sum (fun C => (M.filter (fun g => g ⊆ C)).card) =
          (cycles H).sum (tests H) :=
        Finset.sum_congr rfl (fun C hC => (hMC C hC).2.2)
      rw [hsum] at h1
      omega
    rw [Finset.mem_product]
    refine ⟨Finset.mem_pi.mpr (fun C hC => (hMC C hC).1), ?_⟩
    simp only [ValidNonCyc, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun g hg => ⟨h2 g hg.1, hg.2⟩,
      fun g hg h hh hne => hdisj g hg.1 h hh.1 hne,
      fun R hRH hnotC => ?_, hNcard⟩
    rcases hcov R hRH with ⟨g, hgM, hgR⟩
    refine ⟨g, ⟨hgM, ?_⟩, hgR⟩
    rcases hsplitM g hgM with ⟨C, hC, hgC⟩ | hd
    · exfalso
      rcases mem_base_or_exists_core hH3 hdeg hRH with hRB | ⟨c, hc, hcR⟩
      · obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by rw [h2 g hgM]; omega)
        have huC : u ∈ C := hgC hug
        have hCp : C ∈ parts H := (Finset.mem_filter.mp hC).1
        have hRC : R ⊆ C := by
          rw [← eq_component_of_mem_part H hCp huC]
          exact base_subset_component H hRB (hgR hug)
        exact hnotC C hC hRC
      · have hcc := ((mem_cores_iff hH3).mp hc).1
        have hdisj_gc : Disjoint g c := by
          rw [Finset.disjoint_left]
          intro u hug huc
          have huord := mem_parts_subset_ordinary H (Finset.mem_filter.mp hC).1 (hgC hug)
          simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
          exact huord.2 ⟨c, hc, huc⟩
        have hle := Finset.card_le_card (Finset.union_subset hgR hcR)
        rw [Finset.card_union_of_disjoint hdisj_gc, h2 g hgM, hcc, hH3 R hRH] at hle
        omega
    · exact hd
  · intro p hp
    simp only [Finset.mem_coe] at hp ⊢
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hf : ∀ C (hC : C ∈ cycles H), p.1 C hC ∈ LocalMatchFull C (baseC H C) :=
      Finset.mem_pi.mp hp1
    simp only [ValidNonCyc, Finset.mem_filter, Finset.mem_univ, true_and] at hp2
    rcases hp2 with ⟨hN2, hNdisj, hNcov, hNcard⟩
    set U := (cycles H).attach.biUnion (fun C => p.1 C.1 C.2)
    have hfspec : ∀ C (hC : C ∈ cycles H),
        (∀ g ∈ p.1 C hC, g.card = 2 ∧ g ⊆ C) ∧
        (∀ g ∈ p.1 C hC, ∀ h ∈ p.1 C hC, g ≠ h → Disjoint g h) ∧
        (∀ R ∈ baseC H C, ∃ g ∈ p.1 C hC, g ⊆ R) ∧
        (p.1 C hC).card = tests H C := by
      intro C hC
      have hm := hf C hC
      have hspec := (Finset.mem_filter.mp hm).2
      have htight := localMatchFull_tight
        (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
        (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
        (Finset.mem_filter.mp hC).2 hm
      exact ⟨hspec.1, hspec.2.1, hspec.2.2, htight.1⟩
    have hdisj_UN : Disjoint U p.2 := by
      rw [Finset.disjoint_left]
      intro g hgU hgp2
      rcases Finset.mem_biUnion.mp hgU with ⟨⟨C, hC⟩, _, hgC⟩
      have hg2 := ((hfspec C hC).1 g hgC).1
      have hgsub := ((hfspec C hC).1 g hgC).2
      obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
      exact Finset.disjoint_left.mp (hN2 g hgp2).2 hug (Finset.mem_biUnion.mpr ⟨C, hC, hgsub hug⟩)
    have hdisj_att : ∀ C₁ ∈ (cycles H).attach, ∀ C₂ ∈ (cycles H).attach, C₁ ≠ C₂ →
        Disjoint (p.1 C₁.1 C₁.2) (p.1 C₂.1 C₂.2) := by
      intro ⟨C₁, h1⟩ _ ⟨C₂, h2'⟩ _ hne
      have hne' : C₁ ≠ C₂ := fun h => hne (Subtype.ext h)
      rw [Finset.disjoint_left]
      intro g hg1 hg2
      obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by rw [((hfspec C₁ h1).1 g hg1).1]; omega)
      exact Finset.disjoint_left.mp
        (parts_pairwise_disjoint H (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1 hne')
        (((hfspec C₁ h1).1 g hg1).2 hug) (((hfspec C₂ h2').1 g hg2).2 hug)
    have hUcard : U.card = (cycles H).sum (tests H) := by
      rw [Finset.card_biUnion (fun a ha b hb hne => hdisj_att a ha b hb hne)]
      have h1 : (cycles H).attach.sum (fun C => (p.1 C.1 C.2).card) =
          (cycles H).attach.sum (fun C => tests H C.1) :=
        Finset.sum_congr rfl (fun C _ => (hfspec C.1 C.2).2.2.2)
      rw [h1, Finset.sum_attach (cycles H) (tests H)]
    simp only [ValidAll, Valid, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨fun g hg => ?_, fun g hg h hh hne => ?_, fun R hRH => ?_⟩, ?_⟩
    · rcases Finset.mem_union.mp hg with hgU | hgp2
      · rcases Finset.mem_biUnion.mp hgU with ⟨⟨C, hC⟩, _, hgC⟩
        exact ((hfspec C hC).1 g hgC).1
      · exact (hN2 g hgp2).1
    · rcases Finset.mem_union.mp hg with hgU | hgp2 <;>
      rcases Finset.mem_union.mp hh with hhU | hhp2
      · rcases Finset.mem_biUnion.mp hgU with ⟨⟨C₁, h1⟩, _, hg1⟩
        rcases Finset.mem_biUnion.mp hhU with ⟨⟨C₂, h2'⟩, _, hh2⟩
        by_cases hCeq : C₁ = C₂
        · subst hCeq; exact (hfspec C₁ h1).2.1 g hg1 h hh2 hne
        · exact (parts_pairwise_disjoint H (Finset.mem_filter.mp h1).1
            (Finset.mem_filter.mp h2').1 hCeq).mono
            ((hfspec C₁ h1).1 g hg1).2 ((hfspec C₂ h2').1 h hh2).2
      · rcases Finset.mem_biUnion.mp hgU with ⟨⟨C, hC⟩, _, hgC⟩
        exact (hN2 h hhp2).2.symm.mono_left
          (((hfspec C hC).1 g hgC).2.trans (Finset.subset_biUnion_of_mem id hC))
      · rcases Finset.mem_biUnion.mp hhU with ⟨⟨C, hC⟩, _, hhC⟩
        exact (hN2 g hgp2).2.mono_right
          (((hfspec C hC).1 h hhC).2.trans (Finset.subset_biUnion_of_mem id hC))
      · exact hNdisj g hgp2 h hhp2 hne
    · by_cases hex : ∃ C ∈ cycles H, R ⊆ C
      · rcases hex with ⟨C, hC, hRC⟩
        have hRB : R ∈ base H := Finset.mem_filter.mpr
          ⟨hRH, hRC.trans (mem_parts_subset_ordinary H (Finset.mem_filter.mp hC).1)⟩
        rcases (hfspec C hC).2.2.1 R (Finset.mem_filter.mpr ⟨hRB, hRC⟩) with ⟨g, hgC, hgR⟩
        exact ⟨g, Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨⟨C, hC⟩, Finset.mem_attach _ _, hgC⟩), hgR⟩
      · push Not at hex
        rcases hNcov R hRH hex with ⟨g, hgp2, hgR⟩
        exact ⟨g, Finset.mem_union_right _ hgp2, hgR⟩
    · rw [Finset.card_union_of_disjoint hdisj_UN, hUcard, hNcard]
      omega
  · intro M hM
    simp only [Finset.mem_coe, ValidAll, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    rcases hM with ⟨⟨h2, hdisj, hcov⟩, _⟩
    ext g
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach, true_and,
      Subtype.exists, Finset.mem_filter]
    constructor
    · rintro (⟨_, _, hgM, _⟩ | ⟨hgM, _⟩) <;> exact hgM
    · intro hgM
      by_cases hd : Disjoint g ((cycles H).biUnion id)
      · exact Or.inr ⟨hgM, hd⟩
      · left
        rw [Finset.not_disjoint_iff] at hd
        rcases hd with ⟨u, hug, huU⟩
        rcases Finset.mem_biUnion.mp huU with ⟨C, hC, huC⟩
        dsimp only [id_eq] at huC
        have hmem : M.filter (fun g => g ⊆ C) ∈ LocalMatchFull C (baseC H C) := by
          simp only [LocalMatchFull, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun g' hg' => ⟨h2 g' hg'.1, hg'.2⟩,
            fun g' hg' h' hh' hne => hdisj g' hg'.1 h' hh'.1 hne,
            fun R hR => ?_⟩
          rcases hcov R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1 with ⟨g', hg'M, hg'R⟩
          exact ⟨g', ⟨hg'M, hg'R.trans (Finset.mem_filter.mp hR).2⟩, hg'R⟩
        have hUeq := (localMatchFull_tight
          (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
          (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
          (Finset.mem_filter.mp hC).2 hmem).2.1
        rw [← hUeq] at huC
        rcases Finset.mem_biUnion.mp huC with ⟨g', hg'f, hug'⟩
        dsimp only [id_eq] at hug'
        rcases Finset.mem_filter.mp hg'f with ⟨hg'M, hg'C⟩
        have hgeq : g = g' := by
          by_contra hne
          exact Finset.disjoint_left.mp (hdisj g hgM g' hg'M hne) hug hug'
        exact ⟨C, hC, hgM, hgeq ▸ hg'C⟩
  · intro p hp
    simp only [Finset.mem_coe] at hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hf := Finset.mem_pi.mp hp1
    simp only [ValidNonCyc, Finset.mem_filter, Finset.mem_univ, true_and] at hp2
    rcases hp2 with ⟨hN2, _, _, _⟩
    refine Prod.ext ?_ ?_
    · funext C hC
      ext g
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach,
        true_and, Subtype.exists]
      constructor
      · rintro ⟨(⟨C', hC', hgC'⟩ | hgp2), hgC⟩
        · have hg2 := ((Finset.mem_filter.mp (hf C' hC')).2.1 g hgC').1
          have hgsub := ((Finset.mem_filter.mp (hf C' hC')).2.1 g hgC').2
          obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
          have hCeq : C' = C := by
            by_contra hne
            exact Finset.disjoint_left.mp
              (parts_pairwise_disjoint H (Finset.mem_filter.mp hC').1 (Finset.mem_filter.mp hC).1 hne)
              (hgsub hug) (hgC hug)
          subst hCeq; exact hgC'
        · exfalso
          obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by rw [(hN2 g hgp2).1]; omega)
          exact Finset.disjoint_left.mp (hN2 g hgp2).2 hug (Finset.mem_biUnion.mpr ⟨C, hC, hgC hug⟩)
      · intro hgC
        exact ⟨Or.inl ⟨C, hC, hgC⟩, ((Finset.mem_filter.mp (hf C hC)).2.1 g hgC).2⟩
    · ext g
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach,
        true_and, Subtype.exists]
      constructor
      · rintro ⟨(⟨C, hC, hgC⟩ | hgp2), hd⟩
        · exfalso
          have hg2 := ((Finset.mem_filter.mp (hf C hC)).2.1 g hgC).1
          have hgsub := ((Finset.mem_filter.mp (hf C hC)).2.1 g hgC).2
          obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
          exact Finset.disjoint_left.mp hd hug (Finset.mem_biUnion.mpr ⟨C, hC, hgsub hug⟩)
        · exact hgp2
      · intro hgp2
        exact ⟨Or.inr hgp2, (hN2 g hgp2).2⟩

noncomputable def uniqueTreeMatch {n : Nat} (H : Finset (Finset (Fin n)))
    (C : Finset (Fin n)) (r : Fin n) : Finset (Finset (Fin n)) :=
  if h : (LocalMatch C (baseC H C) r).Nonempty then Classical.choose h else ∅

lemma uniqueTreeMatch_spec {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {C : Finset (Fin n)} (hC : C ∈ trees H) {r : Fin n} (hr : r ∈ C) :
    uniqueTreeMatch H C r ∈ LocalMatch C (baseC H C) r ∧
    ∀ M ∈ LocalMatch C (baseC H C) r, M = uniqueTreeMatch H C r := by
  have hCp : C ∈ parts H := (Finset.mem_filter.mp hC).1
  have hCcard : C.card = 2 * tests H C + 1 := (Finset.mem_filter.mp hC).2
  have h1 : (LocalMatch C (baseC H C) r).card = 1 :=
    localMatch_card_one (tests H C) C (baseC H C) r rfl
      (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
      (fun R hR => (Finset.mem_filter.mp hR).2)
      (fun u => (Finset.card_le_card (Finset.filter_subset_filter _
        ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)))).trans (hdeg u))
      (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
      (component_connected H hCp) hr hCcard
  have hne : (LocalMatch C (baseC H C) r).Nonempty := Finset.card_pos.mp (by omega)
  have hmem : uniqueTreeMatch H C r ∈ LocalMatch C (baseC H C) r := by
    unfold uniqueTreeMatch
    simp only [hne, ↓reduceDIte]
    exact Classical.choose_spec hne
  refine ⟨hmem, fun M hM => ?_⟩
  rcases Finset.card_eq_one.mp h1 with ⟨M₀, hM₀⟩
  have e1 : M = M₀ := by rw [hM₀, Finset.mem_singleton] at hM; exact hM
  have e2 : uniqueTreeMatch H C r = M₀ := by rw [hM₀, Finset.mem_singleton] at hmem; exact hmem
  exact e1.trans e2.symm

def Ncomp {n : Nat} (H N : Finset (Finset (Fin n))) (C : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  N.filter (fun g => ∃ R ∈ baseC H C, g ⊆ R)

noncomputable def rootOf {n : Nat} (H N : Finset (Finset (Fin n)))
    (C : Finset (Fin n)) (hC : C ∈ trees H) : Fin n :=
  if h : (C \ (Ncomp H N C).biUnion id).Nonempty then Classical.choose h
  else Classical.choose (mem_parts_nonempty H (Finset.mem_filter.mp hC).1)

lemma rootOf_spec {n : Nat} {H N : Finset (Finset (Fin n))} {k : Nat}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hN : N ∈ ValidNonCyc H k)
    {C : Finset (Fin n)} (hC : C ∈ trees H) :
    let r := rootOf H N C hC
    r ∈ C ∧
    C \ (Ncomp H N C).biUnion id = {r} ∧
    (Ncomp H N C).biUnion id = C.erase r ∧
    Ncomp H N C = uniqueTreeMatch H C r ∧
    (Ncomp H N C).card = tests H C := by
  have hN' := hN
  simp only [ValidNonCyc, Finset.mem_filter, Finset.mem_univ, true_and] at hN'
  rcases hN' with ⟨hN2, hNdisj, hNcov, _⟩
  have hCp : C ∈ parts H := (Finset.mem_filter.mp hC).1
  have hCcard : C.card = 2 * tests H C + 1 := (Finset.mem_filter.mp hC).2
  have hcovC : ∀ R ∈ baseC H C, ∃ g ∈ N, g ⊆ R := by
    intro R hR
    have hRB : R ∈ base H := (Finset.mem_filter.mp hR).1
    have hRH : R ∈ H := (Finset.mem_filter.mp hRB).1
    have hRC : R ⊆ C := (Finset.mem_filter.mp hR).2
    refine hNcov R hRH fun C' hC' hRC' => ?_
    obtain ⟨u, hu⟩ : R.Nonempty := Finset.card_pos.mp (by rw [hH3 R hRH]; omega)
    have hCeq : C = C' := by
      rw [← eq_component_of_mem_part H hCp (hRC hu),
        eq_component_of_mem_part H (Finset.mem_filter.mp hC').1 (hRC' hu)]
    have e2 := (Finset.mem_filter.mp hC').2
    rw [← hCeq] at e2
    omega
  have hcardNC : (Ncomp H N C).card = tests H C :=
    linear_filter_card_eq
      (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
      (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
      (fun g hg => (hN2 g hg).1) hNdisj hcovC
  have hUsub : (Ncomp H N C).biUnion id ⊆ C := by
    intro u hu
    rcases Finset.mem_biUnion.mp hu with ⟨g, hg, hug⟩
    rcases (Finset.mem_filter.mp hg).2 with ⟨R, hRC, hgR⟩
    exact (Finset.mem_filter.mp hRC).2 (hgR hug)
  have hUcard : ((Ncomp H N C).biUnion id).card = 2 * tests H C := by
    rw [card_biUnion_pairs (M := Ncomp H N C) (fun g hg => (hN2 g (Finset.mem_filter.mp hg).1).1)
      (fun g hg h hh hne => hNdisj g (Finset.mem_filter.mp hg).1 h (Finset.mem_filter.mp hh).1 hne),
      hcardNC]
  have hdiff1 : (C \ (Ncomp H N C).biUnion id).card = 1 := by
    rw [Finset.card_sdiff_of_subset hUsub, hCcard, hUcard]
    omega
  have hne : (C \ (Ncomp H N C).biUnion id).Nonempty := Finset.card_pos.mp (by omega)
  have hrdef : rootOf H N C hC = Classical.choose hne := by
    unfold rootOf
    simp only [hne, ↓reduceDIte]
  set r := rootOf H N C hC
  have hrmem : r ∈ C \ (Ncomp H N C).biUnion id := hrdef ▸ Classical.choose_spec hne
  have hrC : r ∈ C := (Finset.mem_sdiff.mp hrmem).1
  have hrnU : r ∉ (Ncomp H N C).biUnion id := (Finset.mem_sdiff.mp hrmem).2
  have hdiff_eq : C \ (Ncomp H N C).biUnion id = {r} :=
    (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hrmem)
      (by rw [hdiff1, Finset.card_singleton])).symm
  have hUeq : (Ncomp H N C).biUnion id = C.erase r := by
    ext u
    simp only [Finset.mem_erase]
    constructor
    · intro huU
      exact ⟨fun h => hrnU (h ▸ huU), hUsub huU⟩
    · rintro ⟨hur, huC⟩
      by_contra hunU
      have : u ∈ C \ (Ncomp H N C).biUnion id := Finset.mem_sdiff.mpr ⟨huC, hunU⟩
      rw [hdiff_eq, Finset.mem_singleton] at this
      exact hur this
  have hLM : Ncomp H N C ∈ LocalMatch C (baseC H C) r := by
    simp only [LocalMatch, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun g hg => ⟨(hN2 g (Finset.mem_filter.mp hg).1).1, fun u hug => ?_⟩,
      fun g hg h hh hne' => hNdisj g (Finset.mem_filter.mp hg).1 h (Finset.mem_filter.mp hh).1 hne',
      fun R hR => ?_⟩
    · rw [← hUeq]
      exact Finset.mem_biUnion.mpr ⟨g, hg, hug⟩
    · rcases hcovC R hR with ⟨g, hgN, hgR⟩
      exact ⟨g, Finset.mem_filter.mpr ⟨hgN, R, hR, hgR⟩, hgR⟩
  exact ⟨hrC, hdiff_eq, hUeq, (uniqueTreeMatch_spec hH3 hdeg hC hrC).2 _ hLM, hcardNC⟩

def activeCores {n : Nat} (H N : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (cores H).filter (fun c => c ∉ N)

def extraPairs {n : Nat} (H N : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  N.filter (fun g => g ⊆ ordinary H ∧ ¬ ∃ R ∈ base H, g ⊆ R)

def extractQ {n : Nat} (H N : Finset (Finset (Fin n))) : Finset (Finset (Finset (Fin n))) :=
  (activeCores H N).image (fun c => (outer H c).image (component H)) ∪
  (extraPairs H N).image (fun g => g.image (component H))

def OrdChoice {n : Nat} (H : Finset (Finset (Fin n))) (e : Finset (Finset (Fin n))) :
    Finset (Finset (Finset (Fin n))) :=
  (Finset.univ.filter fun g : Finset (Fin n) =>
    g.card = 2 ∧ g ⊆ e.biUnion id ∧ g.image (component H) = e).image singleton

def ActChoice {n : Nat} (H : Finset (Finset (Fin n))) (e : Finset (Finset (Fin n))) :
    Finset (Finset (Finset (Fin n))) :=
  ((cores H).filter (fun c => (outer H c).image (component H) = e)).biUnion (CoreMatchings H)

def EdgeChoice {n : Nat} (H : Finset (Finset (Fin n))) (e : Finset (Finset (Fin n))) :
    Finset (Finset (Finset (Fin n))) :=
  OrdChoice H e ∪ ActChoice H e

lemma ordChoice_card {n : Nat} {H : Finset (Finset (Fin n))}
    {e : Finset (Finset (Fin n))} (he : e ∈ (trees H).powersetCard 2) :
    (OrdChoice H e).card = e.prod Finset.card := by
  rcases Finset.mem_powersetCard.mp he with ⟨heT, he2⟩
  rcases Finset.card_eq_two.mp he2 with ⟨C₁, C₂, hne, heeq⟩
  have hC1 : C₁ ∈ trees H := heT (by rw [heeq]; simp)
  have hC2 : C₂ ∈ trees H := heT (by rw [heeq]; simp)
  have hC1p : C₁ ∈ parts H := (Finset.mem_filter.mp hC1).1
  have hC2p : C₂ ∈ parts H := (Finset.mem_filter.mp hC2).1
  have hdisj : Disjoint C₁ C₂ := parts_pairwise_disjoint H hC1p hC2p hne
  have hprod : e.prod Finset.card = C₁.card * C₂.card := by
    rw [heeq, Finset.prod_pair hne]
  rw [hprod, ← Finset.card_product]
  rw [OrdChoice, Finset.card_image_of_injective _ Finset.singleton_injective]
  let g2p : Finset (Fin n) → Fin n × Fin n := fun g =>
    if h : (g ∩ C₁).Nonempty ∧ (g ∩ C₂).Nonempty
    then (Classical.choose h.1, Classical.choose h.2)
    else (Classical.choose (mem_parts_nonempty H hC1p), Classical.choose (mem_parts_nonempty H hC2p))
  have hg2p : ∀ g, (h1 : (g ∩ C₁).Nonempty) → (h2 : (g ∩ C₂).Nonempty) →
      g2p g = (Classical.choose h1, Classical.choose h2) := by
    intro g h1 h2
    dsimp only [g2p]
    exact dite_cond_eq_true (eq_true ⟨h1, h2⟩)
  refine (Finset.card_nbij'
    (fun p : Fin n × Fin n => ({p.1, p.2} : Finset (Fin n)))
    g2p
    ?_ ?_ ?_ ?_).symm
  · intro p hp
    simp only [Finset.mem_coe] at hp ⊢
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hpne : p.1 ≠ p.2 := fun h => Finset.disjoint_left.mp hdisj hp1 (h ▸ hp2)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Finset.card_pair hpne, ?_, ?_⟩
    · intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact Finset.mem_biUnion.mpr ⟨C₁, by rw [heeq]; simp, hp1⟩
      · exact Finset.mem_biUnion.mpr ⟨C₂, by rw [heeq]; simp, hp2⟩
    · rw [Finset.image_insert, Finset.image_singleton,
        eq_component_of_mem_part H hC1p hp1, eq_component_of_mem_part H hC2p hp2, heeq]
  · intro g hg
    simp only [Finset.mem_coe] at hg ⊢
    rcases (Finset.mem_filter.mp hg).2 with ⟨hg2, hgsub, hgimg⟩
    have h1 : (g ∩ C₁).Nonempty := by
      have hm : C₁ ∈ g.image (component H) := by rw [hgimg, heeq]; simp
      rcases Finset.mem_image.mp hm with ⟨u, hug, huc⟩
      exact ⟨u, Finset.mem_inter.mpr ⟨hug, huc ▸ mem_component_self H u⟩⟩
    have h2 : (g ∩ C₂).Nonempty := by
      have hm : C₂ ∈ g.image (component H) := by rw [hgimg, heeq]; simp
      rcases Finset.mem_image.mp hm with ⟨u, hug, huc⟩
      exact ⟨u, Finset.mem_inter.mpr ⟨hug, huc ▸ mem_component_self H u⟩⟩
    rw [hg2p g h1 h2, Finset.mem_product]
    exact ⟨(Finset.mem_inter.mp (Classical.choose_spec h1)).2,
      (Finset.mem_inter.mp (Classical.choose_spec h2)).2⟩
  · intro p hp
    simp only [Finset.mem_coe] at hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have h1 : (({p.1, p.2} : Finset (Fin n)) ∩ C₁).Nonempty :=
      ⟨p.1, Finset.mem_inter.mpr ⟨by simp, hp1⟩⟩
    have h2 : (({p.1, p.2} : Finset (Fin n)) ∩ C₂).Nonempty :=
      ⟨p.2, Finset.mem_inter.mpr ⟨by simp, hp2⟩⟩
    rw [hg2p _ h1 h2]
    have hs1 := Classical.choose_spec h1
    have hs2 := Classical.choose_spec h2
    rcases Finset.mem_inter.mp hs1 with ⟨ha1, hb1⟩
    rcases Finset.mem_inter.mp hs2 with ⟨ha2, hb2⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha1 ha2
    have e1 : Classical.choose h1 = p.1 := by
      rcases ha1 with h | h
      · exact h
      · exact absurd (h ▸ hb1) (Finset.disjoint_right.mp hdisj hp2)
    have e2 : Classical.choose h2 = p.2 := by
      rcases ha2 with h | h
      · exact absurd (h ▸ hb2) (Finset.disjoint_left.mp hdisj hp1)
      · exact h
    exact Prod.ext e1 e2
  · intro g hg
    simp only [Finset.mem_coe] at hg
    rcases (Finset.mem_filter.mp hg).2 with ⟨hg2, _, hgimg⟩
    have h1 : (g ∩ C₁).Nonempty := by
      have hm : C₁ ∈ g.image (component H) := by rw [hgimg, heeq]; simp
      rcases Finset.mem_image.mp hm with ⟨u, hug, huc⟩
      exact ⟨u, Finset.mem_inter.mpr ⟨hug, huc ▸ mem_component_self H u⟩⟩
    have h2 : (g ∩ C₂).Nonempty := by
      have hm : C₂ ∈ g.image (component H) := by rw [hgimg, heeq]; simp
      rcases Finset.mem_image.mp hm with ⟨u, hug, huc⟩
      exact ⟨u, Finset.mem_inter.mpr ⟨hug, huc ▸ mem_component_self H u⟩⟩
    rw [hg2p g h1 h2]
    dsimp only
    have hs1 := Finset.mem_inter.mp (Classical.choose_spec h1)
    have hs2 := Finset.mem_inter.mp (Classical.choose_spec h2)
    have hne12 : Classical.choose h1 ≠ Classical.choose h2 :=
      fun h => Finset.disjoint_left.mp hdisj hs1.2 (h ▸ hs2.2)
    have hsub : ({Classical.choose h1, Classical.choose h2} : Finset (Fin n)) ⊆ g := by
      intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hs1.1
      · exact hs2.1
    exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hne12, hg2])

lemma edgeChoice_card {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {e : Finset (Finset (Fin n))} (he : e ∈ (trees H).powersetCard 2) :
    (EdgeChoice H e).card = weight H e := by
  have hdisj : Disjoint (OrdChoice H e) (ActChoice H e) := by
    rw [Finset.disjoint_left]
    intro P hP1 hP2
    rcases Finset.mem_image.mp hP1 with ⟨g, _, rfl⟩
    rcases Finset.mem_biUnion.mp hP2 with ⟨c, _, hPc⟩
    have h2 := (Finset.mem_filter.mp hPc).2.1
    rw [Finset.card_singleton] at h2
    omega
  have hAct : (ActChoice H e).card =
      2 * ((cores H).filter (fun c => (outer H c).image (component H) = e)).card := by
    rw [ActChoice, Finset.card_biUnion]
    · rw [Finset.sum_const_nat (fun c hc => (coreMatchings_explicit hH3 hdeg (Finset.mem_filter.mp hc).1).1),
        mul_comm]
    · intro c₁ h1 c₂ h2 hne
      exact coreMatchings_disjoint hH3 hdeg (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1 hne
  rw [EdgeChoice, Finset.card_union_of_disjoint hdisj, ordChoice_card he, hAct]
  rfl

lemma edgeChoice_unique_in_comp {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    {e : Finset (Finset (Fin n))} (he : e ∈ (trees H).powersetCard 2)
    {P : Finset (Finset (Fin n))} (hP : P ∈ EdgeChoice H e) :
    (∀ C ∈ e, (P.biUnion id ∩ C).card = 1) ∧
    (P.biUnion id ∩ ordinary H ⊆ e.biUnion id) ∧
    (∀ g ∈ P, g.card = 2 ∧ ¬ Disjoint g (e.biUnion id) ∧
      Disjoint g ((cycles H).biUnion id) ∧ ¬ ∃ R ∈ base H, g ⊆ R) ∧
    (∀ g ∈ P, ∀ h ∈ P, g ≠ h → Disjoint g h) := by
  rcases Finset.mem_powersetCard.mp he with ⟨heT, he2⟩
  have hpair_comp : ∀ S : Finset (Fin n), S.card = 2 → S ⊆ ordinary H → S.image (component H) = e →
      ∀ C ∈ e, (S ∩ C).card = 1 := by
    intro S hS2 hSord hSimg C hCe
    have hCp : C ∈ parts H := (Finset.mem_filter.mp (heT hCe)).1
    rcases Finset.card_eq_two.mp hS2 with ⟨u₁, u₂, hu12, hSeq⟩
    have himg_eq : ({component H u₁, component H u₂} : Finset _) = e := by
      rw [← hSimg, hSeq, Finset.image_insert, Finset.image_singleton]
    have hcomp_ne : component H u₁ ≠ component H u₂ := by
      intro h
      have : ({component H u₁, component H u₂} : Finset _).card = 1 := by rw [h]; simp
      rw [himg_eq, he2] at this
      omega
    have hCe' : C = component H u₁ ∨ C = component H u₂ := by
      rw [← himg_eq, Finset.mem_insert, Finset.mem_singleton] at hCe
      exact hCe
    rcases hCe' with rfl | rfl
    · have : S ∩ component H u₁ = {u₁} := by
        ext u; rw [hSeq]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, huC⟩
          · rfl
          · exact absurd (component_eq_of_mem H huC).symm hcomp_ne
        · rintro h; rw [h]; exact ⟨Or.inl rfl, mem_component_self H u₁⟩
      rw [this, Finset.card_singleton]
    · have : S ∩ component H u₂ = {u₂} := by
        ext u; rw [hSeq]; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, huC⟩
          · exact absurd (component_eq_of_mem H huC) hcomp_ne
          · rfl
        · rintro h; rw [h]; exact ⟨Or.inr rfl, mem_component_self H u₂⟩
      rw [this, Finset.card_singleton]
  have he_ord : e.biUnion id ⊆ ordinary H := by
    intro u hu
    rcases Finset.mem_biUnion.mp hu with ⟨C, hCe, huC⟩
    exact mem_parts_subset_ordinary H (Finset.mem_filter.mp (heT hCe)).1 huC
  have he_disj_cyc : Disjoint (e.biUnion id) ((cycles H).biUnion id) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    rcases Finset.mem_biUnion.mp hu1 with ⟨C₁, hC1, hu1'⟩
    rcases Finset.mem_biUnion.mp hu2 with ⟨C₂, hC2, hu2'⟩
    have h1T : C₁ ∈ trees H := heT hC1
    have hne : C₁ ≠ C₂ := by
      intro h; subst h
      have e1 := (Finset.mem_filter.mp h1T).2
      have e2 := (Finset.mem_filter.mp hC2).2
      omega
    exact Finset.disjoint_left.mp
      (parts_pairwise_disjoint H (Finset.mem_filter.mp h1T).1 (Finset.mem_filter.mp hC2).1 hne)
      hu1' hu2'
  rcases Finset.mem_union.mp hP with hOrd | hAct
  · rcases Finset.mem_image.mp hOrd with ⟨g, hg, rfl⟩
    rcases (Finset.mem_filter.mp hg).2 with ⟨hg2, hgsub, hgimg⟩
    have hU : ({g} : Finset _).biUnion id = g := by simp
    rw [hU]
    refine ⟨fun C hCe => hpair_comp g hg2 (hgsub.trans he_ord) hgimg C hCe,
      Finset.inter_subset_left.trans hgsub, fun g' hg' => ?_, fun g' hg' h' hh' hne => ?_⟩
    · rw [Finset.mem_singleton] at hg'
      rw [hg']
      refine ⟨hg2, ?_, he_disj_cyc.mono_left hgsub, ?_⟩
      · obtain ⟨u, hu⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
        exact fun hd => Finset.disjoint_left.mp hd hu (hgsub hu)
      · rintro ⟨R, hRB, hgR⟩
        obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
        have hRC : R ⊆ component H u := base_subset_component H hRB (hgR hug)
        have himg_sub : g.image (component H) ⊆ {component H u} := by
          intro C hC
          rcases Finset.mem_image.mp hC with ⟨v, hvg, rfl⟩
          rw [Finset.mem_singleton]
          exact component_eq_of_mem H (hRC (hgR hvg))
        have := Finset.card_le_card himg_sub
        rw [hgimg, he2, Finset.card_singleton] at this
        omega
    · rw [Finset.mem_singleton] at hg' hh'; exact absurd (hg'.trans hh'.symm) hne
  · rcases Finset.mem_biUnion.mp hAct with ⟨c, hcf, hPcm⟩
    rcases Finset.mem_filter.mp hcf with ⟨hc, hout_img⟩
    have hUeq := ((coreMatchings_explicit hH3 hdeg hc).2 P hPcm).1
    have hout_ord := outer_subset_ordinary hH3 hdeg hc
    have hout_sub_e : outer H c ⊆ e.biUnion id := by
      intro u hu
      exact Finset.mem_biUnion.mpr ⟨component H u, by rw [← hout_img]; exact Finset.mem_image_of_mem _ hu,
        mem_component_self H u⟩
    have hdisj_c_ord : Disjoint c (ordinary H) := by
      rw [Finset.disjoint_left]
      intro u huc huo
      simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
      exact huo.2 ⟨c, hc, huc⟩
    have hU_inter_ord : P.biUnion id ∩ ordinary H = outer H c := by
      rw [hUeq, Finset.union_inter_distrib_right,
        Finset.disjoint_iff_inter_eq_empty.mp hdisj_c_ord, Finset.empty_union,
        Finset.inter_eq_left.mpr hout_ord]
    have hPspec := (Finset.mem_filter.mp hPcm).2
    refine ⟨fun C hCe => ?_, by rw [hU_inter_ord]; exact hout_sub_e, fun g hg => ?_, hPspec.2.2⟩
    · have hCsub : C ⊆ ordinary H := mem_parts_subset_ordinary H (Finset.mem_filter.mp (heT hCe)).1
      have heqI : P.biUnion id ∩ C = outer H c ∩ C := by
        rw [← hU_inter_ord, Finset.inter_assoc, Finset.inter_eq_right.mpr hCsub]
      rw [heqI]
      exact hpair_comp (outer H c) (outer_card_two hH3 hdeg hc) hout_ord hout_img C hCe
    · rcases hPspec.2.1 g hg with ⟨hg2, hgc1, hgo1⟩
      have hgsub := ((coreMatchings_explicit hH3 hdeg hc).2 P hPcm).2.2 g hg |>.2
      refine ⟨hg2, ?_, ?_, ?_⟩
      · obtain ⟨u, hu⟩ : (g ∩ outer H c).Nonempty := Finset.card_pos.mp (by omega)
        rcases Finset.mem_inter.mp hu with ⟨hug, huo⟩
        exact fun hd => Finset.disjoint_left.mp hd hug (hout_sub_e huo)
      · rw [Finset.disjoint_left]
        intro u hug huCyc
        have huord : u ∈ ordinary H := by
          rcases Finset.mem_biUnion.mp huCyc with ⟨C, hC, huC⟩
          exact mem_parts_subset_ordinary H (Finset.mem_filter.mp hC).1 huC
        rcases Finset.mem_union.mp (hgsub hug) with huc | huo
        · exact Finset.disjoint_left.mp hdisj_c_ord huc huord
        · exact Finset.disjoint_left.mp he_disj_cyc (hout_sub_e huo) huCyc
      · rintro ⟨R, hRB, hgR⟩
        obtain ⟨u, hu⟩ : (g ∩ c).Nonempty := Finset.card_pos.mp (by omega)
        rcases Finset.mem_inter.mp hu with ⟨hug, huc⟩
        exact Finset.disjoint_left.mp hdisj_c_ord huc ((Finset.mem_filter.mp hRB).2 (hgR hug))

lemma validNonCyc_extractQ_mem {n : Nat} {H N : Finset (Finset (Fin n))} {s : Nat}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hnbad : ¬ bad H) (hs : baseSize H ≤ s)
    (hN : N ∈ ValidNonCyc H (s - (cycles H).sum (tests H))) :
    extractQ H N ∈ (candidates H).filter (fun Q => Q.card = s - baseSize H) ∧
    (∀ c ∈ activeCores H N, Mcore N c ∈ CoreMatchings H c) ∧
    (∀ g ∈ N, (∃ C ∈ trees H, g ∈ Ncomp H N C) ∨ (g ∈ cores H \ activeCores H N) ∨
      (∃ c ∈ activeCores H N, g ∈ Mcore N c) ∨ g ∈ extraPairs H N) := by
  have hN' := hN
  simp only [ValidNonCyc, Finset.mem_filter, Finset.mem_univ, true_and] at hN'
  rcases hN' with ⟨hN2, hNdisj, hNcov, hNcard⟩
  have hparts_split := parts_eq_trees_union_cycles hH3 hnbad
  have hNbase_eq : N.filter (fun g => ∃ R ∈ base H, g ⊆ R) = (trees H).biUnion (Ncomp H N) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_biUnion, Ncomp]
    constructor
    · rintro ⟨hgN, R, hRB, hgR⟩
      have hRmem : R ∈ (parts H).biUnion (baseC H) := by rw [← base_eq_biUnion_baseC hH3]; exact hRB
      rcases Finset.mem_biUnion.mp hRmem with ⟨C, hCp, hRC⟩
      rw [hparts_split.1] at hCp
      rcases Finset.mem_union.mp hCp with hCT | hCC
      · exact ⟨C, hCT, hgN, R, hRC, hgR⟩
      · exfalso
        obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by rw [(hN2 g hgN).1]; omega)
        exact Finset.disjoint_left.mp (hN2 g hgN).2 hug
          (Finset.mem_biUnion.mpr ⟨C, hCC, (Finset.mem_filter.mp hRC).2 (hgR hug)⟩)
    · rintro ⟨C, _, hgN, R, hRC, hgR⟩
      exact ⟨hgN, R, (Finset.mem_filter.mp hRC).1, hgR⟩
  have hroot_only : ∀ g ∈ N, (¬ ∃ R ∈ base H, g ⊆ R) → ∀ u ∈ g, u ∈ ordinary H →
      ∃ hC : component H u ∈ trees H, u = rootOf H N (component H u) hC := by
    intro g hgN hnotB u hug huord
    have hCp : component H u ∈ parts H := Finset.mem_image.mpr ⟨u, huord, rfl⟩
    rw [hparts_split.1] at hCp
    rcases Finset.mem_union.mp hCp with hCT | hCC
    · refine ⟨hCT, ?_⟩
      have hrs := rootOf_spec hH3 hdeg hN hCT
      have hun : u ∉ (Ncomp H N (component H u)).biUnion id := by
        intro huU
        rcases Finset.mem_biUnion.mp huU with ⟨g', hg'f, hug'⟩
        dsimp only [id_eq] at hug'
        rcases Finset.mem_filter.mp hg'f with ⟨hg'N, R, hRC, hg'R⟩
        have hgeq : g = g' := by
          by_contra hne
          exact Finset.disjoint_left.mp (hNdisj g hgN g' hg'N hne) hug hug'
        exact hnotB ⟨R, (Finset.mem_filter.mp hRC).1, hgeq ▸ hg'R⟩
      have hudiff : u ∈ component H u \ (Ncomp H N (component H u)).biUnion id :=
        Finset.mem_sdiff.mpr ⟨mem_component_self H u, hun⟩
      rw [hrs.2.1, Finset.mem_singleton] at hudiff
      exact hudiff
    · exfalso
      exact Finset.disjoint_left.mp (hN2 g hgN).2 hug
        (Finset.mem_biUnion.mpr ⟨component H u, hCC, mem_component_self H u⟩)
  have hcore_beh : ∀ c ∈ cores H,
      (c ∈ N ∧ Mcore N c = {c}) ∨ (c ∉ N ∧ Mcore N c ∈ CoreMatchings H c) := by
    intro c hc
    refine mcore_behavior hH3 hdeg (fun g hg => (hN2 g hg).1) hNdisj hc fun R hR => ?_
    have hRH : R ∈ H := (Finset.mem_filter.mp hR).1
    refine hNcov R hRH fun C hCC hRC => ?_
    have hcc := ((mem_cores_iff hH3).mp hc).1
    obtain ⟨u, huc⟩ : c.Nonempty := Finset.card_pos.mp (by omega)
    have huord := mem_parts_subset_ordinary H (Finset.mem_filter.mp hCC).1 (hRC ((Finset.mem_filter.mp hR).2 huc))
    simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
    exact huord.2 ⟨c, hc, huc⟩
  have hact_cm : ∀ c ∈ activeCores H N, Mcore N c ∈ CoreMatchings H c := by
    intro c hc
    rcases Finset.mem_filter.mp hc with ⟨hcH, hcnN⟩
    rcases hcore_beh c hcH with ⟨hcN, _⟩ | ⟨_, hcm⟩
    · exact absurd hcN hcnN
    · exact hcm
  have hact_root : ∀ c ∈ activeCores H N, ∀ u ∈ outer H c,
      ∃ g ∈ Mcore N c, u ∈ g ∧ ∃ hC : component H u ∈ trees H, u = rootOf H N (component H u) hC := by
    intro c hc u huo
    have hcH : c ∈ cores H := (Finset.mem_filter.mp hc).1
    have hcm := hact_cm c hc
    have hU := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).1
    have huU : u ∈ (Mcore N c).biUnion id := by rw [hU]; exact Finset.mem_union_right _ huo
    rcases Finset.mem_biUnion.mp huU with ⟨g, hgM, hug⟩
    dsimp only [id_eq] at hug
    have hgN : g ∈ N := (Finset.mem_filter.mp hgM).1
    have hnotB : ¬ ∃ R ∈ base H, g ⊆ R := by
      rintro ⟨R, hRB, hgR⟩
      have hnd := (Finset.mem_filter.mp hgM).2
      rw [Finset.not_disjoint_iff] at hnd
      rcases hnd with ⟨w, hwg, hwc⟩
      have hword := (Finset.mem_filter.mp hRB).2 (hgR hwg)
      simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hword
      exact hword.2 ⟨c, hcH, hwc⟩
    rcases hroot_only g hgN hnotB u hug (outer_subset_ordinary hH3 hdeg hcH huo) with ⟨hCT, hur⟩
    exact ⟨g, hgM, hug, hCT, hur⟩
  have hact_edge : ∀ c ∈ activeCores H N, (outer H c).image (component H) ∈ (trees H).powersetCard 2 := by
    intro c hc
    have hcH : c ∈ cores H := (Finset.mem_filter.mp hc).1
    rcases Finset.card_eq_two.mp (outer_card_two hH3 hdeg hcH) with ⟨x, y, hxy, hout⟩
    have hx : x ∈ outer H c := by rw [hout]; simp
    have hy : y ∈ outer H c := by rw [hout]; simp
    rcases hact_root c hc x hx with ⟨_, _, _, hCx, hxr⟩
    rcases hact_root c hc y hy with ⟨_, _, _, hCy, hyr⟩
    have hCne : component H x ≠ component H y := by
      intro heq
      apply hxy
      rw [hxr, hyr]
      congr 1
    rw [hout, Finset.image_insert, Finset.image_singleton, Finset.mem_powersetCard]
    refine ⟨fun C hC => ?_, Finset.card_pair hCne⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl <;> assumption
  have hextra_edge : ∀ g ∈ extraPairs H N, g.image (component H) ∈ (trees H).powersetCard 2 := by
    intro g hg
    rcases Finset.mem_filter.mp hg with ⟨hgN, hgord, hnotB⟩
    rcases Finset.card_eq_two.mp (hN2 g hgN).1 with ⟨x, y, hxy, hgeq⟩
    have hx : x ∈ g := by rw [hgeq]; simp
    have hy : y ∈ g := by rw [hgeq]; simp
    rcases hroot_only g hgN hnotB x hx (hgord hx) with ⟨hCx, hxr⟩
    rcases hroot_only g hgN hnotB y hy (hgord hy) with ⟨hCy, hyr⟩
    have hCne : component H x ≠ component H y := by
      intro heq
      apply hxy
      rw [hxr, hyr]
      congr 1
    rw [hgeq, Finset.image_insert, Finset.image_singleton, Finset.mem_powersetCard]
    refine ⟨fun C hC => ?_, Finset.card_pair hCne⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl <;> assumption
  have hact_extra_disj_C : ∀ c ∈ activeCores H N, ∀ g ∈ extraPairs H N,
      Disjoint ((outer H c).image (component H)) (g.image (component H)) := by
    intro c hc g hg
    rw [Finset.disjoint_left]
    intro C hC1 hC2
    rcases Finset.mem_image.mp hC1 with ⟨x, hxo, rfl⟩
    rcases Finset.mem_image.mp hC2 with ⟨y, hyg, hyeq⟩
    rcases hact_root c hc x hxo with ⟨g₁, hg1m, hxg1, hCx, hxr⟩
    rcases Finset.mem_filter.mp hg with ⟨hgN, hgord, hnotB⟩
    rcases hroot_only g hgN hnotB y hyg (hgord hyg) with ⟨hCy, hyr⟩
    have hxy : x = y := by rw [hxr, hyr]; congr 1; exact hyeq.symm
    have hg1N : g₁ ∈ N := (Finset.mem_filter.mp hg1m).1
    have hg1ne : g₁ ≠ g := by
      intro heq
      have hnd := (Finset.mem_filter.mp hg1m).2
      rw [Finset.not_disjoint_iff] at hnd
      rcases hnd with ⟨w, hwg1, hwc⟩
      have hword := hgord (heq ▸ hwg1)
      simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hword
      exact hword.2 ⟨c, (Finset.mem_filter.mp hc).1, hwc⟩
    exact Finset.disjoint_left.mp (hNdisj g₁ hg1N g hgN hg1ne) hxg1 (hxy ▸ hyg)
  have hact_disj_C : ∀ c₁ ∈ activeCores H N, ∀ c₂ ∈ activeCores H N, c₁ ≠ c₂ →
      Disjoint ((outer H c₁).image (component H)) ((outer H c₂).image (component H)) := by
    intro c₁ h1 c₂ h2 hne
    rw [Finset.disjoint_left]
    intro C hC1 hC2
    rcases Finset.mem_image.mp hC1 with ⟨x, hxo1, rfl⟩
    rcases Finset.mem_image.mp hC2 with ⟨y, hyo2, hyeq⟩
    rcases hact_root c₁ h1 x hxo1 with ⟨g₁, hg1m, hxg1, hCx, hxr⟩
    rcases hact_root c₂ h2 y hyo2 with ⟨g₂, hg2m, hyg2, hCy, hyr⟩
    have hxy : x = y := by rw [hxr, hyr]; congr 1; exact hyeq.symm
    have hg1N : g₁ ∈ N := (Finset.mem_filter.mp hg1m).1
    have hg2N : g₂ ∈ N := (Finset.mem_filter.mp hg2m).1
    have hg12ne : g₁ ≠ g₂ := by
      intro heq
      have hcm1 := hact_cm c₁ h1
      have hgsub1 := ((coreMatchings_explicit hH3 hdeg (Finset.mem_filter.mp h1).1).2 _ hcm1).2.2 g₁ hg1m |>.2
      have hnd2 := (Finset.mem_filter.mp hg2m).2
      rw [Finset.not_disjoint_iff] at hnd2
      rcases hnd2 with ⟨w, hwg2, hwc2⟩
      rcases Finset.mem_union.mp (hgsub1 (heq ▸ hwg2)) with hwc1 | hwo1
      · exact Finset.disjoint_left.mp
          (cores_pairwise_disjoint hH3 hdeg (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1 hne)
          hwc1 hwc2
      · have hword := outer_subset_ordinary hH3 hdeg (Finset.mem_filter.mp h1).1 hwo1
        simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hword
        exact hword.2 ⟨c₂, (Finset.mem_filter.mp h2).1, hwc2⟩
    exact Finset.disjoint_left.mp (hNdisj g₁ hg1N g₂ hg2N hg12ne) hxg1 (hxy ▸ hyg2)
  have hextra_disj_C : ∀ g₁ ∈ extraPairs H N, ∀ g₂ ∈ extraPairs H N, g₁ ≠ g₂ →
      Disjoint (g₁.image (component H)) (g₂.image (component H)) := by
    intro g₁ h1 g₂ h2 hne
    rw [Finset.disjoint_left]
    intro C hC1 hC2
    rcases Finset.mem_image.mp hC1 with ⟨x, hx1, rfl⟩
    rcases Finset.mem_image.mp hC2 with ⟨y, hy2, hyeq⟩
    rcases Finset.mem_filter.mp h1 with ⟨hg1N, hg1ord, hnot1⟩
    rcases Finset.mem_filter.mp h2 with ⟨hg2N, hg2ord, hnot2⟩
    rcases hroot_only g₁ hg1N hnot1 x hx1 (hg1ord hx1) with ⟨hCx, hxr⟩
    rcases hroot_only g₂ hg2N hnot2 y hy2 (hg2ord hy2) with ⟨hCy, hyr⟩
    have hxy : x = y := by rw [hxr, hyr]; congr 1; exact hyeq.symm
    exact Finset.disjoint_left.mp (hNdisj g₁ hg1N g₂ hg2N hne) hx1 (hxy ▸ hy2)
  have hQcand : extractQ H N ∈ candidates H := by
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun e he => ?_, fun e₁ he1 e₂ he2 hne => ?_⟩
    · rcases Finset.mem_union.mp he with h1 | h2
      · rcases Finset.mem_image.mp h1 with ⟨c, hc, rfl⟩; exact hact_edge c hc
      · rcases Finset.mem_image.mp h2 with ⟨g, hg, rfl⟩; exact hextra_edge g hg
    · rcases Finset.mem_union.mp he1 with h1 | h1 <;> rcases Finset.mem_union.mp he2 with h2 | h2
      · rcases Finset.mem_image.mp h1 with ⟨c₁, hc1, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨c₂, hc2, rfl⟩
        exact hact_disj_C c₁ hc1 c₂ hc2 (fun h => hne (congr_arg (fun c => (outer H c).image (component H)) h))
      · rcases Finset.mem_image.mp h1 with ⟨c₁, hc1, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨g₂, hg2, rfl⟩
        exact hact_extra_disj_C c₁ hc1 g₂ hg2
      · rcases Finset.mem_image.mp h1 with ⟨g₁, hg1, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨c₂, hc2, rfl⟩
        exact (hact_extra_disj_C c₂ hc2 g₁ hg1).symm
      · rcases Finset.mem_image.mp h1 with ⟨g₁, hg1, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨g₂, hg2, rfl⟩
        exact hextra_disj_C g₁ hg1 g₂ hg2 (fun h => hne (congr_arg (fun g => g.image (component H)) h))
  have hQcard : (extractQ H N).card = (activeCores H N).card + (extraPairs H N).card := by
    have hdisj_img : Disjoint ((activeCores H N).image (fun c => (outer H c).image (component H)))
        ((extraPairs H N).image (fun g => g.image (component H))) := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      rcases Finset.mem_image.mp he1 with ⟨c, hc, rfl⟩
      rcases Finset.mem_image.mp he2 with ⟨g, hg, heq⟩
      have h2 := (Finset.mem_powersetCard.mp (hact_edge c hc)).2
      obtain ⟨C, hC⟩ : ((outer H c).image (component H)).Nonempty := Finset.card_pos.mp (by omega)
      exact Finset.disjoint_left.mp (hact_extra_disj_C c hc g hg) hC (by rw [heq]; exact hC)
    have hinj1 : Set.InjOn (fun c => (outer H c).image (component H)) (activeCores H N : Set _) := by
      intro c₁ h1 c₂ h2 heq
      simp only [Finset.mem_coe] at h1 h2
      dsimp only at heq
      by_contra hne
      have h2c := (Finset.mem_powersetCard.mp (hact_edge c₁ h1)).2
      obtain ⟨C, hC⟩ : ((outer H c₁).image (component H)).Nonempty := Finset.card_pos.mp (by omega)
      exact Finset.disjoint_left.mp (hact_disj_C c₁ h1 c₂ h2 hne) hC (by rw [← heq]; exact hC)
    have hinj2 : Set.InjOn (fun g : Finset (Fin n) => g.image (component H)) (extraPairs H N : Set _) := by
      intro g₁ h1 g₂ h2 heq
      simp only [Finset.mem_coe] at h1 h2
      dsimp only at heq
      by_contra hne
      have h2c := (Finset.mem_powersetCard.mp (hextra_edge g₁ h1)).2
      obtain ⟨C, hC⟩ : (g₁.image (component H)).Nonempty := Finset.card_pos.mp (by omega)
      exact Finset.disjoint_left.mp (hextra_disj_C g₁ h1 g₂ h2 hne) hC (by rw [← heq]; exact hC)
    rw [extractQ, Finset.card_union_of_disjoint hdisj_img,
      Finset.card_image_of_injOn hinj1, Finset.card_image_of_injOn hinj2]
  have hpartN : ∀ g ∈ N, (∃ C ∈ trees H, g ∈ Ncomp H N C) ∨ (g ∈ cores H \ activeCores H N) ∨
      (∃ c ∈ activeCores H N, g ∈ Mcore N c) ∨ g ∈ extraPairs H N := by
    intro g hgN
    by_cases hB : ∃ R ∈ base H, g ⊆ R
    · left
      have hm : g ∈ (trees H).biUnion (Ncomp H N) := by
        rw [← hNbase_eq]; exact Finset.mem_filter.mpr ⟨hgN, hB⟩
      exact Finset.mem_biUnion.mp hm
    · by_cases hord : g ⊆ ordinary H
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨hgN, hord, hB⟩)))
      · rw [Finset.not_subset] at hord
        rcases hord with ⟨u, hug, huord⟩
        simp only [ordinary, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not,
          Finset.mem_biUnion, id_eq] at huord
        rcases huord with ⟨c, hc, huc⟩
        have hgmc : g ∈ Mcore N c := Finset.mem_filter.mpr ⟨hgN, fun hd => Finset.disjoint_left.mp hd hug huc⟩
        by_cases hcN : c ∈ N
        · rcases hcore_beh c hc with ⟨_, heq⟩ | ⟨hcn, _⟩
          · rw [heq, Finset.mem_singleton] at hgmc
            subst hgmc
            exact Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨hc, fun h => (Finset.mem_filter.mp h).2 hcN⟩))
          · exact absurd hcN hcn
        · exact Or.inr (Or.inr (Or.inl ⟨c, Finset.mem_filter.mpr ⟨hc, hcN⟩, hgmc⟩))
  have hN_eq_union : N = ((trees H).biUnion (Ncomp H N)) ∪ (cores H \ activeCores H N) ∪
      ((activeCores H N).biUnion (Mcore N)) ∪ extraPairs H N := by
    ext g
    simp only [Finset.mem_union, Finset.mem_biUnion]
    constructor
    · intro hgN
      rcases hpartN g hgN with h1 | h2 | h3 | h4
      · exact Or.inl (Or.inl (Or.inl h1))
      · exact Or.inl (Or.inl (Or.inr h2))
      · exact Or.inl (Or.inr h3)
      · exact Or.inr h4
    · rintro (((⟨C, _, h⟩ | h) | ⟨c, _, h⟩) | h)
      · exact (Finset.mem_filter.mp h).1
      · rcases Finset.mem_sdiff.mp h with ⟨hcH, hna⟩
        by_contra hcnN
        exact hna (Finset.mem_filter.mpr ⟨hcH, hcnN⟩)
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
  have hNcard_eq : N.card = (trees H).sum (tests H) + (cores H).card + (extractQ H N).card := by
    set S1 := (trees H).biUnion (Ncomp H N)
    set S2 := cores H \ activeCores H N
    set S3 := (activeCores H N).biUnion (Mcore N)
    set S4 := extraPairs H N
    have h12 : Disjoint S1 S2 := by
      rw [Finset.disjoint_left]; intro g h1 h2
      rcases Finset.mem_biUnion.mp h1 with ⟨C, _, hgC⟩
      rcases (Finset.mem_filter.mp hgC).2 with ⟨R, hRC, hgR⟩
      have hcH : g ∈ cores H := (Finset.mem_sdiff.mp h2).1
      have hcc := ((mem_cores_iff hH3).mp hcH).1
      obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
      have huord := (Finset.mem_filter.mp (Finset.mem_filter.mp hRC).1).2 (hgR hug)
      simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
      exact huord.2 ⟨g, hcH, hug⟩
    have h12_3 : Disjoint (S1 ∪ S2) S3 := by
      rw [Finset.disjoint_left]; intro g h12m h3
      rcases Finset.mem_biUnion.mp h3 with ⟨c, hc, hgmc⟩
      have hcH : c ∈ cores H := (Finset.mem_filter.mp hc).1
      rcases Finset.mem_union.mp h12m with h1 | h2
      · rcases Finset.mem_biUnion.mp h1 with ⟨C, _, hgC⟩
        rcases (Finset.mem_filter.mp hgC).2 with ⟨R, hRC, hgR⟩
        have hnd := (Finset.mem_filter.mp hgmc).2
        rw [Finset.not_disjoint_iff] at hnd
        rcases hnd with ⟨u, hug, huc⟩
        have huord := (Finset.mem_filter.mp (Finset.mem_filter.mp hRC).1).2 (hgR hug)
        simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
        exact huord.2 ⟨c, hcH, huc⟩
      · rcases Finset.mem_sdiff.mp h2 with ⟨hgH, hgna⟩
        have hne : g ≠ c := fun h => hgna (h ▸ hc)
        have hd := cores_pairwise_disjoint hH3 hdeg hgH hcH hne
        exact (Finset.mem_filter.mp hgmc).2 hd
    have h123_4 : Disjoint (S1 ∪ S2 ∪ S3) S4 := by
      rw [Finset.disjoint_left]; intro g h123 h4
      rcases Finset.mem_filter.mp h4 with ⟨_, hgord, hnotB⟩
      rcases Finset.mem_union.mp h123 with h12m | h3
      · rcases Finset.mem_union.mp h12m with h1 | h2
        · rcases Finset.mem_biUnion.mp h1 with ⟨C, _, hgC⟩
          rcases (Finset.mem_filter.mp hgC).2 with ⟨R, hRC, hgR⟩
          exact hnotB ⟨R, (Finset.mem_filter.mp hRC).1, hgR⟩
        · have hcH : g ∈ cores H := (Finset.mem_sdiff.mp h2).1
          have hcc := ((mem_cores_iff hH3).mp hcH).1
          obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
          have huord := hgord hug
          simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
          exact huord.2 ⟨g, hcH, hug⟩
      · rcases Finset.mem_biUnion.mp h3 with ⟨c, hc, hgmc⟩
        have hnd := (Finset.mem_filter.mp hgmc).2
        rw [Finset.not_disjoint_iff] at hnd
        rcases hnd with ⟨u, hug, huc⟩
        have huord := hgord hug
        simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
        exact huord.2 ⟨c, (Finset.mem_filter.mp hc).1, huc⟩
    have hS1card : S1.card = (trees H).sum (tests H) := by
      rw [Finset.card_biUnion]
      · exact Finset.sum_congr rfl (fun C hC => (rootOf_spec hH3 hdeg hN hC).2.2.2.2)
      · intro C₁ h1 C₂ h2 hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro g hg1 hg2
        obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by rw [(hN2 g (Finset.mem_filter.mp hg1).1).1]; omega)
        rcases (Finset.mem_filter.mp hg1).2 with ⟨R₁, hR1, hgR1⟩
        rcases (Finset.mem_filter.mp hg2).2 with ⟨R₂, hR2, hgR2⟩
        exact Finset.disjoint_left.mp
          (parts_pairwise_disjoint H (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1 hne)
          ((Finset.mem_filter.mp hR1).2 (hgR1 hug)) ((Finset.mem_filter.mp hR2).2 (hgR2 hug))
    have hS2card : S2.card = (cores H).card - (activeCores H N).card :=
      Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
    have hS3card : S3.card = 2 * (activeCores H N).card := by
      rw [Finset.card_biUnion]
      · rw [Finset.sum_const_nat (fun c hc => (Finset.mem_filter.mp (hact_cm c hc)).2.1), mul_comm]
      · intro c₁ h1 c₂ h2 hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro g hg1 hg2
        have hgsub1 := ((coreMatchings_explicit hH3 hdeg (Finset.mem_filter.mp h1).1).2 _
          (hact_cm c₁ h1)).2.2 g hg1 |>.2
        have hnd2 := (Finset.mem_filter.mp hg2).2
        rw [Finset.not_disjoint_iff] at hnd2
        rcases hnd2 with ⟨u, hug, huc2⟩
        rcases Finset.mem_union.mp (hgsub1 hug) with huc1 | huo1
        · exact Finset.disjoint_left.mp
            (cores_pairwise_disjoint hH3 hdeg (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1 hne)
            huc1 huc2
        · have huord := outer_subset_ordinary hH3 hdeg (Finset.mem_filter.mp h1).1 huo1
          simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huord
          exact huord.2 ⟨c₂, (Finset.mem_filter.mp h2).1, huc2⟩
    have hact_le : (activeCores H N).card ≤ (cores H).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have htot := congr_arg Finset.card hN_eq_union
    rw [Finset.card_union_of_disjoint h123_4, Finset.card_union_of_disjoint h12_3,
      Finset.card_union_of_disjoint h12, hS1card, hS2card, hS3card] at htot
    omega
  have hbase_split : (base H).card = (trees H).sum (tests H) + (cycles H).sum (tests H) := by
    rw [base_card_eq_sum_tests hH3, hparts_split.1, Finset.sum_union hparts_split.2]
  have hQcard_s : (extractQ H N).card = s - baseSize H := by
    dsimp only [baseSize] at hs ⊢
    omega
  exact ⟨Finset.mem_filter.mpr ⟨hQcand, hQcard_s⟩, hact_cm, hpartN⟩

lemma validNonCyc_fiber_card {n : Nat} {H : Finset (Finset (Fin n))} {s : Nat}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (hnbad : ¬ bad H) (hs : baseSize H ≤ s)
    {Q : Finset (Finset (Finset (Fin n)))}
    (hQ : Q ∈ (candidates H).filter (fun Q => Q.card = s - baseSize H)) :
    ((ValidNonCyc H (s - (cycles H).sum (tests H))).filter (fun N => extractQ H N = Q)).card =
      ((trees H \ Q.biUnion id).prod Finset.card) * Q.prod (weight H) := by
  classical
  rcases Finset.mem_filter.mp hQ with ⟨hQcand, hQcard⟩
  rcases Finset.mem_filter.mp hQcand with ⟨hQpow, hQdisj⟩
  have hQsub : Q ⊆ (trees H).powersetCard 2 := Finset.mem_powerset.mp hQpow
  have hparts_split := parts_eq_trees_union_cycles hH3 hnbad
  have hbase_split : (base H).card = (trees H).sum (tests H) + (cycles H).sum (tests H) := by
    rw [base_card_eq_sum_tests hH3, hparts_split.1, Finset.sum_union hparts_split.2]
  set k := s - (cycles H).sum (tests H)
  set freeTrees := trees H \ Q.biUnion id
  set Dom := (freeTrees.pi id) ×ˢ (Q.pi (EdgeChoice H))
  have hDom_card : Dom.card = (freeTrees.prod Finset.card) * Q.prod (weight H) := by
    rw [Finset.card_product, card_pi_finset, card_pi_finset]
    congr 1
    exact Finset.prod_congr rfl (fun e he => edgeChoice_card hH3 hdeg (hQsub he))
  rw [← hDom_card]
  let pickRoot : (∀ C ∈ freeTrees, Fin n) → (∀ e ∈ Q, Finset (Finset (Fin n))) →
      ∀ C ∈ trees H, Fin n :=
    fun rf dec C hCT =>
      if hf : C ∈ freeTrees then rf C hf
      else if hex : ∃ e ∈ Q, C ∈ e then
        let e := Classical.choose hex
        let he : e ∈ Q := (Classical.choose_spec hex).1
        if hne : ((dec e he).biUnion id ∩ C).Nonempty then Classical.choose hne
        else Classical.choose (mem_parts_nonempty H (Finset.mem_filter.mp hCT).1)
      else Classical.choose (mem_parts_nonempty H (Finset.mem_filter.mp hCT).1)
  let actOf : (∀ e ∈ Q, Finset (Finset (Fin n))) → Finset (Finset (Fin n)) :=
    fun dec => (cores H).filter (fun c => ∃ e, ∃ he : e ∈ Q, c ⊆ (dec e he).biUnion id)
  let recon : (∀ C ∈ freeTrees, Fin n) × (∀ e ∈ Q, Finset (Finset (Fin n))) →
      Finset (Finset (Fin n)) :=
    fun p =>
      ((trees H).attach.biUnion (fun C => uniqueTreeMatch H C.1 (pickRoot p.1 p.2 C.1 C.2))) ∪
      (cores H \ actOf p.2) ∪
      (Q.attach.biUnion (fun e => p.2 e.1 e.2))
  let decomp : Finset (Finset (Fin n)) →
      (∀ C ∈ freeTrees, Fin n) × (∀ e ∈ Q, Finset (Finset (Fin n))) :=
    fun N =>
      (fun C hCf => rootOf H N C (Finset.mem_sdiff.mp hCf).1,
       fun e _ => N.filter (fun g => ¬ Disjoint g (e.biUnion id) ∧ ¬ ∃ R ∈ base H, g ⊆ R))
  have hpick_mem : ∀ p ∈ Dom, ∀ C (hCT : C ∈ trees H),
      pickRoot p.1 p.2 C hCT ∈ C ∧
      (∀ hCf : C ∈ freeTrees, pickRoot p.1 p.2 C hCT = p.1 C hCf) ∧
      (∀ e (he : e ∈ Q), C ∈ e → (p.2 e he).biUnion id ∩ C = {pickRoot p.1 p.2 C hCT}) := by
    intro p hp C hCT
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hrf := Finset.mem_pi.mp hp1
    have hdec := Finset.mem_pi.mp hp2
    by_cases hCf : C ∈ freeTrees
    · have hnotQ : ∀ e ∈ Q, C ∉ e := by
        intro e he hCe
        exact (Finset.mem_sdiff.mp hCf).2 (Finset.mem_biUnion.mpr ⟨e, he, hCe⟩)
      have hpr : pickRoot p.1 p.2 C hCT = p.1 C hCf := by
        dsimp only [pickRoot]; simp only [hCf, ↓reduceDIte]
      refine ⟨hpr ▸ hrf C hCf, fun _ => hpr, fun e he hCe => absurd hCe (hnotQ e he)⟩
    · have hex : ∃ e ∈ Q, C ∈ e := by
        by_contra hno
        apply hCf
        refine Finset.mem_sdiff.mpr ⟨hCT, fun hU => hno ?_⟩
        exact Finset.mem_biUnion.mp hU
      set e₀ := Classical.choose hex
      have he₀ : e₀ ∈ Q := (Classical.choose_spec hex).1
      have hCe₀ : C ∈ e₀ := (Classical.choose_spec hex).2
      have hcard1 : ((p.2 e₀ he₀).biUnion id ∩ C).card = 1 :=
        (edgeChoice_unique_in_comp hH3 hdeg (hQsub he₀) (hdec e₀ he₀)).1 C hCe₀
      have hne : ((p.2 e₀ he₀).biUnion id ∩ C).Nonempty := Finset.card_pos.mp (by omega)
      have hpr : pickRoot p.1 p.2 C hCT = Classical.choose hne := by
        dsimp only [pickRoot]
        rw [dite_cond_eq_false (eq_false hCf), dite_cond_eq_true (eq_true hex)]
        exact dite_cond_eq_true (eq_true hne)
      have hspec := Classical.choose_spec hne
      have hsing : (p.2 e₀ he₀).biUnion id ∩ C = {pickRoot p.1 p.2 C hCT} := by
        rw [hpr]
        exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hspec)
          (by rw [hcard1, Finset.card_singleton])).symm
      refine ⟨hpr ▸ (Finset.mem_inter.mp hspec).2, fun h => absurd h hCf, fun e he hCe => ?_⟩
      have heeq : e = e₀ := by
        by_contra hne'
        exact Finset.disjoint_left.mp (hQdisj e he e₀ he₀ hne') hCe hCe₀
      subst heeq
      exact hsing
  have hdec_core : ∀ p ∈ Dom, ∀ c ∈ cores H,
      (c ∈ actOf p.2 ↔ ∃ e, ∃ he : e ∈ Q, (outer H c).image (component H) = e ∧
        p.2 e he ∈ CoreMatchings H c) := by
    intro p hp c hc
    have hdec := Finset.mem_pi.mp (Finset.mem_product.mp hp).2
    have hdisj_c_ord : Disjoint c (ordinary H) := by
      rw [Finset.disjoint_left]; intro u huc huo
      simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
      exact huo.2 ⟨c, hc, huc⟩
    have hcc := ((mem_cores_iff hH3).mp hc).1
    constructor
    · intro hca
      rcases (Finset.mem_filter.mp hca).2 with ⟨e, he, hcsub⟩
      rcases Finset.mem_union.mp (hdec e he) with hOrd | hAct
      · exfalso
        rcases Finset.mem_image.mp hOrd with ⟨g, hg, hpeq⟩
        obtain ⟨u, huc⟩ : c.Nonempty := Finset.card_pos.mp (by omega)
        have hug : u ∈ g := by
          have : u ∈ ({g} : Finset _).biUnion id := hpeq ▸ hcsub huc
          simpa using this
        have hgsub := (Finset.mem_filter.mp hg).2.2.1
        have huord : u ∈ ordinary H := by
          rcases Finset.mem_biUnion.mp (hgsub hug) with ⟨C, hCe, huC⟩
          exact mem_parts_subset_ordinary H
            (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub he)).1 hCe)).1 huC
        exact Finset.disjoint_left.mp hdisj_c_ord huc huord
      · rcases Finset.mem_biUnion.mp hAct with ⟨c', hc'f, hpcm⟩
        rcases Finset.mem_filter.mp hc'f with ⟨hc'H, hout'⟩
        have hUeq := ((coreMatchings_explicit hH3 hdeg hc'H).2 _ hpcm).1
        have hc_eq : c = c' := by
          by_contra hne
          obtain ⟨u, huc⟩ : c.Nonempty := Finset.card_pos.mp (by omega)
          have huin : u ∈ c' ∪ outer H c' := hUeq ▸ hcsub huc
          rcases Finset.mem_union.mp huin with huc' | huo'
          · exact Finset.disjoint_left.mp (cores_pairwise_disjoint hH3 hdeg hc hc'H hne) huc huc'
          · exact Finset.disjoint_left.mp hdisj_c_ord huc (outer_subset_ordinary hH3 hdeg hc'H huo')
        subst hc_eq
        exact ⟨e, he, hout', hpcm⟩
    · rintro ⟨e, he, _, hpcm⟩
      refine Finset.mem_filter.mpr ⟨hc, e, he, ?_⟩
      rw [((coreMatchings_explicit hH3 hdeg hc).2 _ hpcm).1]
      exact Finset.subset_union_left
  refine (Finset.card_nbij' recon decomp ?_ ?_ ?_ ?_).symm
  · intro p hp
    simp only [Finset.mem_coe] at hp ⊢
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hrf := Finset.mem_pi.mp hp1
    have hdec := Finset.mem_pi.mp hp2
    set S1 := (trees H).attach.biUnion (fun C => uniqueTreeMatch H C.1 (pickRoot p.1 p.2 C.1 C.2))
    set S2 := cores H \ actOf p.2
    set S3 := Q.attach.biUnion (fun e => p.2 e.1 e.2)
    have hU_S1 : ∀ C (hCT : C ∈ trees H),
        (uniqueTreeMatch H C (pickRoot p.1 p.2 C hCT)).biUnion id = C.erase (pickRoot p.1 p.2 C hCT) ∧
        (uniqueTreeMatch H C (pickRoot p.1 p.2 C hCT)).card = tests H C := by
      intro C hCT
      have hrC := (hpick_mem p hp C hCT).1
      have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT hrC).1
      have htight := localMatch_tight
        (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
        (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
        hrC (Finset.mem_filter.mp hCT).2 hLM
      exact ⟨htight.2.1, htight.1⟩
    have hS3_disj_S1_v : ∀ e (he : e ∈ Q), ∀ g ∈ p.2 e he, ∀ C (hCT : C ∈ trees H),
        Disjoint g (C.erase (pickRoot p.1 p.2 C hCT)) := by
      intro e he g hg C hCT
      have heprops := edgeChoice_unique_in_comp hH3 hdeg (hQsub he) (hdec e he)
      rw [Finset.disjoint_left]
      intro u hug huCe
      rcases Finset.mem_erase.mp huCe with ⟨hur, huC⟩
      have huord := mem_parts_subset_ordinary H (Finset.mem_filter.mp hCT).1 huC
      have huin : u ∈ (p.2 e he).biUnion id ∩ ordinary H :=
        Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨g, hg, hug⟩, huord⟩
      have hue : u ∈ e.biUnion id := heprops.2.1 huin
      rcases Finset.mem_biUnion.mp hue with ⟨C', hC'e, huC'⟩
      have hCeq : C = C' := by
        rw [← eq_component_of_mem_part H (Finset.mem_filter.mp hCT).1 huC,
          eq_component_of_mem_part H (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub he)).1 hC'e)).1 huC']
      subst hCeq
      have hsing := (hpick_mem p hp C hCT).2.2 e he hC'e
      have hum : u ∈ (p.2 e he).biUnion id ∩ C :=
        Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨g, hg, hug⟩, huC⟩
      rw [hsing, Finset.mem_singleton] at hum
      exact hur hum
    have hS3_v_disj : ∀ e₁ (h1 : e₁ ∈ Q), ∀ e₂ (h2 : e₂ ∈ Q), e₁ ≠ e₂ →
        Disjoint ((p.2 e₁ h1).biUnion id) ((p.2 e₂ h2).biUnion id) := by
      intro e₁ h1 e₂ h2 hne
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      by_cases huord : u ∈ ordinary H
      · have he1 := (edgeChoice_unique_in_comp hH3 hdeg (hQsub h1) (hdec e₁ h1)).2.1
          (Finset.mem_inter.mpr ⟨hu1, huord⟩)
        have he2 := (edgeChoice_unique_in_comp hH3 hdeg (hQsub h2) (hdec e₂ h2)).2.1
          (Finset.mem_inter.mpr ⟨hu2, huord⟩)
        rcases Finset.mem_biUnion.mp he1 with ⟨C₁, hC1, huC1⟩
        rcases Finset.mem_biUnion.mp he2 with ⟨C₂, hC2, huC2⟩
        have hCeq : C₁ = C₂ := by
          rw [← eq_component_of_mem_part H (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub h1)).1 hC1)).1 huC1,
            eq_component_of_mem_part H (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub h2)).1 hC2)).1 huC2]
        subst hCeq
        exact Finset.disjoint_left.mp (hQdisj e₁ h1 e₂ h2 hne) hC1 hC2
      · simp only [ordinary, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not,
          Finset.mem_biUnion, id_eq] at huord
        rcases huord with ⟨c, hc, huc⟩
        have hget : ∀ e (he : e ∈ Q), u ∈ (p.2 e he).biUnion id → (outer H c).image (component H) = e := by
          intro e he hue
          rcases Finset.mem_union.mp (hdec e he) with hOrd | hAct
          · exfalso
            rcases Finset.mem_image.mp hOrd with ⟨g, hg, hpeq⟩
            have hug : u ∈ g := by rw [← hpeq] at hue; simpa using hue
            have hgsub := (Finset.mem_filter.mp hg).2.2.1
            rcases Finset.mem_biUnion.mp (hgsub hug) with ⟨C, hCe, huC⟩
            have huo := mem_parts_subset_ordinary H
              (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub he)).1 hCe)).1 huC
            simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
            exact huo.2 ⟨c, hc, huc⟩
          · rcases Finset.mem_biUnion.mp hAct with ⟨c', hc'f, hpcm⟩
            rcases Finset.mem_filter.mp hc'f with ⟨hc'H, hout'⟩
            have hUeq := ((coreMatchings_explicit hH3 hdeg hc'H).2 _ hpcm).1
            rw [hUeq] at hue
            rcases Finset.mem_union.mp hue with huc' | huo'
            · have hceq : c = c' := by
                by_contra hne'
                exact Finset.disjoint_left.mp (cores_pairwise_disjoint hH3 hdeg hc hc'H hne') huc huc'
              exact hceq ▸ hout'
            · exfalso
              have huo := outer_subset_ordinary hH3 hdeg hc'H huo'
              simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
              exact huo.2 ⟨c, hc, huc⟩
        exact hne ((hget e₁ h1 hu1).symm.trans (hget e₂ h2 hu2))
    have hS2_disj_S3_v : ∀ c ∈ S2, ∀ e (he : e ∈ Q), Disjoint c ((p.2 e he).biUnion id) := by
      intro c hcS2 e he
      rcases Finset.mem_sdiff.mp hcS2 with ⟨hcH, hcna⟩
      rw [Finset.disjoint_left]
      intro u huc huU
      rcases Finset.mem_union.mp (hdec e he) with hOrd | hAct
      · rcases Finset.mem_image.mp hOrd with ⟨g, hg, hpeq⟩
        have hug : u ∈ g := by rw [← hpeq] at huU; simpa using huU
        rcases Finset.mem_biUnion.mp ((Finset.mem_filter.mp hg).2.2.1 hug) with ⟨C, hCe, huC⟩
        have huo := mem_parts_subset_ordinary H
          (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub he)).1 hCe)).1 huC
        simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
        exact huo.2 ⟨c, hcH, huc⟩
      · rcases Finset.mem_biUnion.mp hAct with ⟨c', hc'f, hpcm⟩
        rcases Finset.mem_filter.mp hc'f with ⟨hc'H, hout'⟩
        have hUeq := ((coreMatchings_explicit hH3 hdeg hc'H).2 _ hpcm).1
        rw [hUeq] at huU
        rcases Finset.mem_union.mp huU with huc' | huo'
        · have hceq : c = c' := by
            by_contra hne
            exact Finset.disjoint_left.mp (cores_pairwise_disjoint hH3 hdeg hcH hc'H hne) huc huc'
          subst hceq
          exact hcna ((hdec_core p hp c hcH).mpr ⟨e, he, hout', hpcm⟩)
        · have huo := outer_subset_ordinary hH3 hdeg hc'H huo'
          simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
          exact huo.2 ⟨c, hcH, huc⟩
    have hdisj_all : ∀ g ∈ recon p, ∀ h ∈ recon p, g ≠ h → Disjoint g h := by
      have hS1_mem : ∀ g ∈ S1, ∃ C, ∃ hCT : C ∈ trees H, g ∈ uniqueTreeMatch H C (pickRoot p.1 p.2 C hCT) := by
        intro g hg; rcases Finset.mem_biUnion.mp hg with ⟨⟨C, hCT⟩, _, hgC⟩; exact ⟨C, hCT, hgC⟩
      have hS3_mem : ∀ g ∈ S3, ∃ e, ∃ he : e ∈ Q, g ∈ p.2 e he := by
        intro g hg; rcases Finset.mem_biUnion.mp hg with ⟨⟨e, he⟩, _, hge⟩; exact ⟨e, he, hge⟩
      have hS1_disj_S2 : ∀ g ∈ S1, ∀ c ∈ S2, Disjoint g c := by
        intro g hg c hc
        rcases hS1_mem g hg with ⟨C, hCT, hgC⟩
        have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT (hpick_mem p hp C hCT).1).1
        have hgsub := ((Finset.mem_filter.mp hLM).2.1 g hgC).2.trans (Finset.erase_subset _ C)
        rw [Finset.disjoint_left]; intro u hug huc
        have huo := mem_parts_subset_ordinary H (Finset.mem_filter.mp hCT).1 (hgsub hug)
        simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
        exact huo.2 ⟨c, (Finset.mem_sdiff.mp hc).1, huc⟩
      have hS1_disj_S3 : ∀ g ∈ S1, ∀ h ∈ S3, Disjoint g h := by
        intro g hg h hh
        rcases hS1_mem g hg with ⟨C, hCT, hgC⟩
        rcases hS3_mem h hh with ⟨e, he, hhe⟩
        have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT (hpick_mem p hp C hCT).1).1
        exact (hS3_disj_S1_v e he h hhe C hCT).symm.mono_left ((Finset.mem_filter.mp hLM).2.1 g hgC).2
      have hS2_disj_S3 : ∀ c ∈ S2, ∀ h ∈ S3, Disjoint c h := by
        intro c hc h hh
        rcases hS3_mem h hh with ⟨e, he, hhe⟩
        exact (hS2_disj_S3_v c hc e he).mono_right (Finset.subset_biUnion_of_mem id hhe)
      intro g hg h hh hne
      rcases Finset.mem_union.mp hg with (hg12 | hg3) <;> rcases Finset.mem_union.mp hh with (hh12 | hh3)
      · rcases Finset.mem_union.mp hg12 with hg1 | hg2 <;> rcases Finset.mem_union.mp hh12 with hh1 | hh2
        · rcases hS1_mem g hg1 with ⟨C₁, h1, hgC1⟩
          rcases hS1_mem h hh1 with ⟨C₂, h2, hhC2⟩
          by_cases hCeq : C₁ = C₂
          · subst hCeq
            have hLM := (uniqueTreeMatch_spec hH3 hdeg h1 (hpick_mem p hp C₁ h1).1).1
            exact (Finset.mem_filter.mp hLM).2.2.1 g hgC1 h hhC2 hne
          · have hLM1 := (uniqueTreeMatch_spec hH3 hdeg h1 (hpick_mem p hp C₁ h1).1).1
            have hLM2 := (uniqueTreeMatch_spec hH3 hdeg h2 (hpick_mem p hp C₂ h2).1).1
            exact (parts_pairwise_disjoint H (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1 hCeq).mono
              (((Finset.mem_filter.mp hLM1).2.1 g hgC1).2.trans (Finset.erase_subset _ C₁))
              (((Finset.mem_filter.mp hLM2).2.1 h hhC2).2.trans (Finset.erase_subset _ C₂))
        · exact hS1_disj_S2 g hg1 h hh2
        · exact (hS1_disj_S2 h hh1 g hg2).symm
        · exact cores_pairwise_disjoint hH3 hdeg (Finset.mem_sdiff.mp hg2).1 (Finset.mem_sdiff.mp hh2).1 hne
      · rcases Finset.mem_union.mp hg12 with hg1 | hg2
        · exact hS1_disj_S3 g hg1 h hh3
        · exact hS2_disj_S3 g hg2 h hh3
      · rcases Finset.mem_union.mp hh12 with hh1 | hh2
        · exact (hS1_disj_S3 h hh1 g hg3).symm
        · exact (hS2_disj_S3 h hh2 g hg3).symm
      · rcases hS3_mem g hg3 with ⟨e₁, h1, hge1⟩
        rcases hS3_mem h hh3 with ⟨e₂, h2, hhe2⟩
        by_cases heeq : e₁ = e₂
        · subst heeq
          exact (edgeChoice_unique_in_comp hH3 hdeg (hQsub h1) (hdec e₁ h1)).2.2.2 g hge1 h hhe2 hne
        · exact (hS3_v_disj e₁ h1 e₂ h2 heeq).mono
            (Finset.subset_biUnion_of_mem id hge1) (Finset.subset_biUnion_of_mem id hhe2)
    have hcard_recon : (recon p).card = k := by
      have h2_all : ∀ g ∈ recon p, g.card = 2 := by
        intro g hg
        rcases Finset.mem_union.mp hg with (hg12 | hg3)
        · rcases Finset.mem_union.mp hg12 with hg1 | hg2
          · rcases Finset.mem_biUnion.mp hg1 with ⟨⟨C, hCT⟩, _, hgC⟩
            have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT (hpick_mem p hp C hCT).1).1
            exact ((Finset.mem_filter.mp hLM).2.1 g hgC).1
          · exact ((mem_cores_iff hH3).mp (Finset.mem_sdiff.mp hg2).1).1
        · rcases Finset.mem_biUnion.mp hg3 with ⟨⟨e, he⟩, _, hge⟩
          exact ((edgeChoice_unique_in_comp hH3 hdeg (hQsub he) (hdec e he)).2.2.1 g hge).1
      have h12 : Disjoint S1 S2 := by
        rw [Finset.disjoint_left]; intro g h1 h2
        have hg2 := h2_all g (Finset.mem_union_left _ (Finset.mem_union_left _ h1))
        obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
        rcases Finset.mem_biUnion.mp h1 with ⟨⟨C, hCT⟩, _, hgC⟩
        have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT (hpick_mem p hp C hCT).1).1
        have huo := mem_parts_subset_ordinary H (Finset.mem_filter.mp hCT).1
          (Finset.erase_subset _ C (((Finset.mem_filter.mp hLM).2.1 g hgC).2 hug))
        simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
        exact huo.2 ⟨g, (Finset.mem_sdiff.mp h2).1, hug⟩
      have h12_3 : Disjoint (S1 ∪ S2) S3 := by
        rw [Finset.disjoint_left]; intro g h12m h3
        have hg2 := h2_all g (Finset.mem_union_right _ h3)
        obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
        rcases Finset.mem_biUnion.mp h3 with ⟨⟨e, he⟩, _, hge⟩
        rcases Finset.mem_union.mp h12m with h1 | h2
        · rcases Finset.mem_biUnion.mp h1 with ⟨⟨C, hCT⟩, _, hgC⟩
          have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT (hpick_mem p hp C hCT).1).1
          exact Finset.disjoint_left.mp (hS3_disj_S1_v e he g hge C hCT) hug
            (((Finset.mem_filter.mp hLM).2.1 g hgC).2 hug)
        · exact Finset.disjoint_left.mp (hS2_disj_S3_v g h2 e he) hug
            (Finset.mem_biUnion.mpr ⟨g, hge, hug⟩)
      have hS1c : S1.card = (trees H).sum (tests H) := by
        rw [Finset.card_biUnion]
        · have h1 : (trees H).attach.sum (fun C => (uniqueTreeMatch H C.1 (pickRoot p.1 p.2 C.1 C.2)).card) =
              (trees H).attach.sum (fun C => tests H C.1) :=
            Finset.sum_congr rfl (fun C _ => (hU_S1 C.1 C.2).2)
          rw [h1, Finset.sum_attach (trees H) (tests H)]
        · intro ⟨C₁, h1⟩ _ ⟨C₂, h2⟩ _ hne
          dsimp only [Function.onFun]
          have hne' : C₁ ≠ C₂ := fun h => hne (Subtype.ext h)
          rw [Finset.disjoint_left]; intro g hg1 hg2
          have hLM1 := (uniqueTreeMatch_spec hH3 hdeg h1 (hpick_mem p hp C₁ h1).1).1
          have hLM2 := (uniqueTreeMatch_spec hH3 hdeg h2 (hpick_mem p hp C₂ h2).1).1
          obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by rw [((Finset.mem_filter.mp hLM1).2.1 g hg1).1]; omega)
          exact Finset.disjoint_left.mp
            (parts_pairwise_disjoint H (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2).1 hne')
            (Finset.erase_subset _ C₁ (((Finset.mem_filter.mp hLM1).2.1 g hg1).2 hug))
            (Finset.erase_subset _ C₂ (((Finset.mem_filter.mp hLM2).2.1 g hg2).2 hug))
      have hS2c : S2.card = (cores H).card - (actOf p.2).card :=
        Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
      have hS3c : S3.card = Q.card + (actOf p.2).card := by
        have hdisj3 : ∀ a ∈ Q.attach, ∀ b ∈ Q.attach, a ≠ b → Disjoint (p.2 a.1 a.2) (p.2 b.1 b.2) := by
          intro ⟨e₁, h1⟩ _ ⟨e₂, h2⟩ _ hne
          dsimp only [Function.onFun]
          have hne' : e₁ ≠ e₂ := fun h => hne (Subtype.ext h)
          rw [Finset.disjoint_left]; intro g hg1 hg2
          have hg2c := ((edgeChoice_unique_in_comp hH3 hdeg (hQsub h1) (hdec e₁ h1)).2.2.1 g hg1).1
          obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
          exact Finset.disjoint_left.mp (hS3_v_disj e₁ h1 e₂ h2 hne')
            (Finset.mem_biUnion.mpr ⟨g, hg1, hug⟩) (Finset.mem_biUnion.mpr ⟨g, hg2, hug⟩)
        rw [Finset.card_biUnion (fun a ha b hb hne => hdisj3 a ha b hb hne)]
        set Qact := Q.attach.filter (fun e => p.2 e.1 e.2 ∈ ActChoice H e.1)
        have hcard_e : ∀ e ∈ Q.attach, (p.2 e.1 e.2).card = 1 + if e ∈ Qact then 1 else 0 := by
          intro e _
          rcases Finset.mem_union.mp (hdec e.1 e.2) with hOrd | hAct
          · have hna : e ∉ Qact := by
              intro h; rcases Finset.mem_image.mp hOrd with ⟨g, _, hpeq⟩
              rcases Finset.mem_biUnion.mp (Finset.mem_filter.mp h).2 with ⟨c, _, hcm⟩
              have h2 := (Finset.mem_filter.mp hcm).2.1
              rw [← hpeq, Finset.card_singleton] at h2; omega
            rw [if_neg hna]
            rcases Finset.mem_image.mp hOrd with ⟨g, _, hpeq⟩
            rw [← hpeq, Finset.card_singleton]
          · have ha : e ∈ Qact := Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hAct⟩
            rw [if_pos ha]
            rcases Finset.mem_biUnion.mp hAct with ⟨c, _, hcm⟩
            exact (Finset.mem_filter.mp hcm).2.1
        rw [Finset.sum_congr rfl hcard_e, Finset.sum_add_distrib,
          Finset.sum_const_nat (fun _ _ => rfl), mul_one, Finset.card_attach,
          ← Finset.card_filter]
        have hQact_eq : (Q.attach.filter (fun e => e ∈ Qact)).card = (actOf p.2).card := by
          have hfeq : Q.attach.filter (fun e => e ∈ Qact) = Qact := by
            ext e; simp [Qact]
          rw [hfeq]
          by_cases hQne : Q.attach.Nonempty
          · let f1 : Finset (Fin n) → {x // x ∈ Q} := fun c =>
              if h : ∃ e : {x // x ∈ Q}, (outer H c).image (component H) = e.1
              then Classical.choose h else Classical.choose hQne
            let f2 : {x // x ∈ Q} → Finset (Fin n) := fun e =>
              if h : ∃ c ∈ cores H, p.2 e.1 e.2 ∈ CoreMatchings H c
              then Classical.choose h else ∅
            have hf1 : ∀ c, ∀ e : {x // x ∈ Q}, (outer H c).image (component H) = e.1 → f1 c = e := by
              intro c e hout
              have hex : ∃ e' : {x // x ∈ Q}, (outer H c).image (component H) = e'.1 := ⟨e, hout⟩
              dsimp only [f1]
              rw [dite_cond_eq_true (eq_true hex)]
              exact Subtype.ext ((Classical.choose_spec hex).symm.trans hout)
            have hf2 : ∀ e : {x // x ∈ Q}, ∀ c ∈ cores H, p.2 e.1 e.2 ∈ CoreMatchings H c → f2 e = c := by
              intro e c hcH hpcm
              have hex : ∃ c' ∈ cores H, p.2 e.1 e.2 ∈ CoreMatchings H c' := ⟨c, hcH, hpcm⟩
              dsimp only [f2]
              rw [dite_cond_eq_true (eq_true hex)]
              rcases Classical.choose_spec hex with ⟨hc'H, hpcm'⟩
              by_contra hne
              exact Finset.disjoint_left.mp (coreMatchings_disjoint hH3 hdeg hc'H hcH hne) hpcm' hpcm
            refine (Finset.card_nbij' f1 f2 ?_ ?_ ?_ ?_).symm
            · intro c hc
              simp only [Finset.mem_coe] at hc ⊢
              have hcH : c ∈ cores H := (Finset.mem_filter.mp hc).1
              rcases (hdec_core p hp c hcH).mp hc with ⟨e, he, hout, hpcm⟩
              rw [hf1 c ⟨e, he⟩ hout]
              exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,
                Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hcH, hout⟩, hpcm⟩⟩
            · intro e he
              simp only [Finset.mem_coe] at he ⊢
              rcases Finset.mem_biUnion.mp (Finset.mem_filter.mp he).2 with ⟨c, hcf, hpcm⟩
              rcases Finset.mem_filter.mp hcf with ⟨hcH, hout⟩
              rw [hf2 e c hcH hpcm]
              exact (hdec_core p hp c hcH).mpr ⟨e.1, e.2, hout, hpcm⟩
            · intro c hc
              simp only [Finset.mem_coe] at hc
              have hcH : c ∈ cores H := (Finset.mem_filter.mp hc).1
              rcases (hdec_core p hp c hcH).mp hc with ⟨e, he, hout, hpcm⟩
              rw [hf1 c ⟨e, he⟩ hout, hf2 ⟨e, he⟩ c hcH hpcm]
            · intro e he
              simp only [Finset.mem_coe] at he
              rcases Finset.mem_biUnion.mp (Finset.mem_filter.mp he).2 with ⟨c, hcf, hpcm⟩
              rcases Finset.mem_filter.mp hcf with ⟨hcH, hout⟩
              rw [hf2 e c hcH hpcm, hf1 c e hout]
          · have hQ1 : Qact = ∅ := Finset.eq_empty_of_forall_notMem (fun e he =>
              hQne ⟨e, (Finset.mem_filter.mp he).1⟩)
            have hQ2 : actOf p.2 = ∅ := Finset.eq_empty_of_forall_notMem (fun c hc => by
              rcases (Finset.mem_filter.mp hc).2 with ⟨e, he, _⟩
              exact hQne ⟨⟨e, he⟩, Finset.mem_attach _ _⟩)
            rw [hQ1, hQ2]; rfl
        rw [hQact_eq]
      have hact_le : (actOf p.2).card ≤ (cores H).card := Finset.card_le_card (Finset.filter_subset _ _)
      change (S1 ∪ S2 ∪ S3).card = k
      rw [Finset.card_union_of_disjoint h12_3, Finset.card_union_of_disjoint h12, hS1c, hS2c, hS3c, hQcard]
      dsimp only [baseSize, k] at hs ⊢
      omega
    have hrecon_VNC : recon p ∈ ValidNonCyc H k := by
      simp only [ValidNonCyc, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun g hg => ?_, hdisj_all, fun R hRH hnotC => ?_, hcard_recon⟩
      · rcases Finset.mem_union.mp hg with (hg12 | hg3)
        · rcases Finset.mem_union.mp hg12 with hg1 | hg2
          · rcases Finset.mem_biUnion.mp hg1 with ⟨⟨C, hCT⟩, _, hgC⟩
            have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT (hpick_mem p hp C hCT).1).1
            refine ⟨((Finset.mem_filter.mp hLM).2.1 g hgC).1, ?_⟩
            rw [Finset.disjoint_left]; intro u hug huCyc
            have huC := Finset.erase_subset _ C (((Finset.mem_filter.mp hLM).2.1 g hgC).2 hug)
            rcases Finset.mem_biUnion.mp huCyc with ⟨C', hC', huC'⟩
            have hne : C ≠ C' := by
              intro h; subst h; have e1 := (Finset.mem_filter.mp hCT).2
              have e2 := (Finset.mem_filter.mp hC').2; omega
            exact Finset.disjoint_left.mp
              (parts_pairwise_disjoint H (Finset.mem_filter.mp hCT).1 (Finset.mem_filter.mp hC').1 hne)
              huC huC'
          · have hcH := (Finset.mem_sdiff.mp hg2).1
            refine ⟨((mem_cores_iff hH3).mp hcH).1, ?_⟩
            rw [Finset.disjoint_left]; intro u huc huCyc
            rcases Finset.mem_biUnion.mp huCyc with ⟨C', hC', huC'⟩
            have huo := mem_parts_subset_ordinary H (Finset.mem_filter.mp hC').1 huC'
            simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
            exact huo.2 ⟨g, hcH, huc⟩
        · rcases Finset.mem_biUnion.mp hg3 with ⟨⟨e, he⟩, _, hge⟩
          have hep := (edgeChoice_unique_in_comp hH3 hdeg (hQsub he) (hdec e he)).2.2.1 g hge
          exact ⟨hep.1, hep.2.2.1⟩
      · rcases mem_base_or_exists_core hH3 hdeg hRH with hRB | ⟨c, hc, hcR⟩
        · have hRmem : R ∈ (parts H).biUnion (baseC H) := by rw [← base_eq_biUnion_baseC hH3]; exact hRB
          rcases Finset.mem_biUnion.mp hRmem with ⟨C, hCp, hRC⟩
          rw [hparts_split.1] at hCp
          rcases Finset.mem_union.mp hCp with hCT | hCC
          · have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT (hpick_mem p hp C hCT).1).1
            rcases (Finset.mem_filter.mp hLM).2.2.2 R hRC with ⟨g, hgC, hgR⟩
            exact ⟨g, Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_biUnion.mpr ⟨⟨C, hCT⟩, Finset.mem_attach _ _, hgC⟩)), hgR⟩
          · exact absurd (Finset.mem_filter.mp hRC).2 (hnotC C hCC)
        · by_cases hca : c ∈ actOf p.2
          · rcases (hdec_core p hp c hc).mp hca with ⟨e, he, _, hpcm⟩
            rcases ((coreMatchings_explicit hH3 hdeg hc).2 _ hpcm).2.1 R (Finset.mem_filter.mpr ⟨hRH, hcR⟩) with
              ⟨g, hge, hgR⟩
            exact ⟨g, Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨⟨e, he⟩, Finset.mem_attach _ _, hge⟩), hgR⟩
          · exact ⟨c, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hc, hca⟩)), hcR⟩
    refine Finset.mem_filter.mpr ⟨hrecon_VNC, ?_⟩
    have hact_eq : activeCores H (recon p) = actOf p.2 := by
      ext c
      simp only [activeCores, Finset.mem_filter]
      constructor
      · rintro ⟨hcH, hcn⟩
        by_contra hna
        exact hcn (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hcH, hna⟩)))
      · intro hca
        have hcH : c ∈ cores H := (Finset.mem_filter.mp hca).1
        refine ⟨hcH, fun hcM => ?_⟩
        rcases (hdec_core p hp c hcH).mp hca with ⟨e, he, _, hpcm⟩
        have hUeq := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hpcm).1
        have hcc := ((mem_cores_iff hH3).mp hcH).1
        obtain ⟨u, huc⟩ : c.Nonempty := Finset.card_pos.mp (by omega)
        have huU : u ∈ (p.2 e he).biUnion id := by rw [hUeq]; exact Finset.mem_union_left _ huc
        rcases Finset.mem_biUnion.mp huU with ⟨g, hge, hug⟩
        dsimp only [id_eq] at hug
        have hgM : g ∈ recon p := Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨⟨e, he⟩, Finset.mem_attach _ _, hge⟩)
        have hgne : g ≠ c := by
          intro h; rw [h] at hge
          have h1 := ((Finset.mem_filter.mp hpcm).2.2.1 c hge).2.1
          rw [Finset.inter_self, hcc] at h1; omega
        exact Finset.disjoint_left.mp (hdisj_all g hgM c hcM hgne) hug huc
    ext e
    simp only [extractQ, Finset.mem_union, Finset.mem_image, hact_eq]
    constructor
    · rintro (⟨c, hca, rfl⟩ | ⟨g, hgex, rfl⟩)
      · rcases (hdec_core p hp c (Finset.mem_filter.mp hca).1).mp hca with ⟨e', he', hout, _⟩
        exact hout ▸ he'
      · rcases Finset.mem_filter.mp hgex with ⟨hgM, hgord, hnotB⟩
        rcases Finset.mem_union.mp hgM with (hg12 | hg3)
        · exfalso
          rcases Finset.mem_union.mp hg12 with hg1 | hg2
          · rcases Finset.mem_biUnion.mp hg1 with ⟨⟨C, hCT⟩, _, hgC⟩
            have hrC := (hpick_mem p hp C hCT).1
            have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT hrC).1
            rcases (localMatch_tight
              (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
              (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
              hrC (Finset.mem_filter.mp hCT).2 hLM).2.2 g hgC with ⟨R, hRC, hgR⟩
            exact hnotB ⟨R, (Finset.mem_filter.mp hRC).1, hgR⟩
          · have hcH := (Finset.mem_sdiff.mp hg2).1
            have hcc := ((mem_cores_iff hH3).mp hcH).1
            obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
            have huo := hgord hug
            simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
            exact huo.2 ⟨g, hcH, hug⟩
        · rcases Finset.mem_biUnion.mp hg3 with ⟨⟨e', he'⟩, _, hge'⟩
          rcases Finset.mem_union.mp (hdec e' he') with hOrd | hAct
          · rcases Finset.mem_image.mp hOrd with ⟨g', hg'f, hpeq⟩
            rw [← hpeq, Finset.mem_singleton] at hge'
            rw [hge', (Finset.mem_filter.mp hg'f).2.2.2]
            exact he'
          · exfalso
            rcases Finset.mem_biUnion.mp hAct with ⟨c, hcf, hpcm⟩
            have hcH := (Finset.mem_filter.mp hcf).1
            have hgc1 := ((Finset.mem_filter.mp hpcm).2.2.1 g hge').2.1
            obtain ⟨u, hu⟩ : (g ∩ c).Nonempty := Finset.card_pos.mp (by omega)
            rcases Finset.mem_inter.mp hu with ⟨hug, huc⟩
            have huo := hgord hug
            simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
            exact huo.2 ⟨c, hcH, huc⟩
    · intro heQ
      rcases Finset.mem_union.mp (hdec e heQ) with hOrd | hAct
      · right
        rcases Finset.mem_image.mp hOrd with ⟨g, hgf, hpeq⟩
        have hge : g ∈ p.2 e heQ := by rw [← hpeq]; simp
        have hgM : g ∈ recon p := Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨⟨e, heQ⟩, Finset.mem_attach _ _, hge⟩)
        have hgspec := (Finset.mem_filter.mp hgf).2
        have hgord : g ⊆ ordinary H := fun u hu => by
          rcases Finset.mem_biUnion.mp (hgspec.2.1 hu) with ⟨C, hCe, huC⟩
          exact mem_parts_subset_ordinary H
            (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe)).1 huC
        have hnotB := ((edgeChoice_unique_in_comp hH3 hdeg (hQsub heQ) (hdec e heQ)).2.2.1 g hge).2.2.2
        exact ⟨g, Finset.mem_filter.mpr ⟨hgM, hgord, hnotB⟩, hgspec.2.2⟩
      · left
        rcases Finset.mem_biUnion.mp hAct with ⟨c, hcf, hpcm⟩
        rcases Finset.mem_filter.mp hcf with ⟨hcH, hout⟩
        exact ⟨c, (hdec_core p hp c hcH).mpr ⟨e, heQ, hout, hpcm⟩, hout⟩
  · intro N hN
    simp only [Finset.mem_coe] at hN ⊢
    rcases Finset.mem_filter.mp hN with ⟨hNV, hNQ⟩
    have hstr := validNonCyc_extractQ_mem hH3 hdeg hnbad hs hNV
    have hNV' := hNV
    simp only [ValidNonCyc, Finset.mem_filter, Finset.mem_univ, true_and] at hNV'
    rcases hNV' with ⟨hN2, hNdisj, _, _⟩
    rw [Finset.mem_product]
    refine ⟨Finset.mem_pi.mpr (fun C hCf => (rootOf_spec hH3 hdeg hNV (Finset.mem_sdiff.mp hCf).1).1),
      Finset.mem_pi.mpr (fun e heQ => ?_)⟩
    have he_ex : e ∈ extractQ H N := hNQ.symm ▸ heQ
    have hfilt_eq : ∀ g ∈ N, (¬ Disjoint g (e.biUnion id) ∧ ¬ ∃ R ∈ base H, g ⊆ R) →
        (∃ c ∈ activeCores H N, (outer H c).image (component H) = e ∧ g ∈ Mcore N c) ∨
        (g ∈ extraPairs H N ∧ g.image (component H) = e) := by
      intro g hgN ⟨hnd, hnotB⟩
      rcases hstr.2.2 g hgN with ⟨C, hCT, hgC⟩ | hgInact | ⟨c, hc, hgmc⟩ | hgEx
      · exfalso
        rcases (Finset.mem_filter.mp hgC).2 with ⟨R, hRC, hgR⟩
        exact hnotB ⟨R, (Finset.mem_filter.mp hRC).1, hgR⟩
      · exfalso
        rw [Finset.not_disjoint_iff] at hnd
        rcases hnd with ⟨u, hug, hue⟩
        rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
        have huo := mem_parts_subset_ordinary H
          (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe)).1 huC
        simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
        exact huo.2 ⟨g, (Finset.mem_sdiff.mp hgInact).1, hug⟩
      · left
        have he'Q : (outer H c).image (component H) ∈ Q := by
          rw [← hNQ]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)
        have heeq : (outer H c).image (component H) = e := by
          by_contra hne
          rw [Finset.not_disjoint_iff] at hnd
          rcases hnd with ⟨u, hug, hue⟩
          rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
          have hCT : C ∈ trees H := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
          have huo := mem_parts_subset_ordinary H (Finset.mem_filter.mp hCT).1 huC
          have hcH := (Finset.mem_filter.mp hc).1
          have hgsub := ((coreMatchings_explicit hH3 hdeg hcH).2 _ (hstr.2.1 c hc)).2.2 g hgmc |>.2
          rcases Finset.mem_union.mp (hgsub hug) with huc | huout
          · simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
            exact huo.2 ⟨c, hcH, huc⟩
          · have hCmem : C ∈ (outer H c).image (component H) := by
              rw [← eq_component_of_mem_part H (Finset.mem_filter.mp hCT).1 huC]
              exact Finset.mem_image_of_mem _ huout
            exact Finset.disjoint_left.mp (hQdisj _ he'Q e heQ hne) hCmem hCe
        exact ⟨c, hc, heeq, hgmc⟩
      · right
        have he'Q : g.image (component H) ∈ Q := by
          rw [← hNQ]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hgEx)
        have heeq : g.image (component H) = e := by
          by_contra hne
          rw [Finset.not_disjoint_iff] at hnd
          rcases hnd with ⟨u, hug, hue⟩
          rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
          have hCT : C ∈ trees H := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
          have hCmem : C ∈ g.image (component H) := by
            rw [← eq_component_of_mem_part H (Finset.mem_filter.mp hCT).1 huC]
            exact Finset.mem_image_of_mem _ hug
          exact Finset.disjoint_left.mp (hQdisj _ he'Q e heQ hne) hCmem hCe
        exact ⟨hgEx, heeq⟩
    rcases Finset.mem_union.mp he_ex with hA | hO
    · rcases Finset.mem_image.mp hA with ⟨c, hc, hout⟩
      have hcH := (Finset.mem_filter.mp hc).1
      have hcm := hstr.2.1 c hc
      have hEq : N.filter (fun g => ¬ Disjoint g (e.biUnion id) ∧ ¬ ∃ R ∈ base H, g ⊆ R) = Mcore N c := by
        ext g
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hgN, hnd, hnotB⟩
          rcases hfilt_eq g hgN ⟨hnd, hnotB⟩ with ⟨c', hc', hout', hgmc'⟩ | ⟨hgEx, hgimg⟩
          · have hceq : c' = c := by
              by_contra hne
              have hc'H := (Finset.mem_filter.mp hc').1
              have hU1 := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).1
              have hU2 := ((coreMatchings_explicit hH3 hdeg hc'H).2 _ (hstr.2.1 c' hc')).1
              have h2e := (Finset.mem_powersetCard.mp (hQsub heQ)).2
              obtain ⟨C, hCe⟩ : e.Nonempty := Finset.card_pos.mp (by omega)
              have hC1 : C ∈ (outer H c).image (component H) := hout.symm ▸ hCe
              have hC2 : C ∈ (outer H c').image (component H) := hout'.symm ▸ hCe
              rcases Finset.mem_image.mp hC1 with ⟨x, hxo, rfl⟩
              rcases Finset.mem_image.mp hC2 with ⟨y, hyo, hyeq⟩
              have hxU : x ∈ (Mcore N c).biUnion id := by rw [hU1]; exact Finset.mem_union_right _ hxo
              have hyU : y ∈ (Mcore N c').biUnion id := by rw [hU2]; exact Finset.mem_union_right _ hyo
              rcases Finset.mem_biUnion.mp hxU with ⟨g₁, hg1m, hxg1⟩
              rcases Finset.mem_biUnion.mp hyU with ⟨g₂, hg2m, hyg2⟩
              dsimp only [id_eq] at hxg1 hyg2
              have hCT : component H x ∈ trees H := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
              have hrs := rootOf_spec hH3 hdeg hNV hCT
              have hnot_in_nc : ∀ z g₀, g₀ ∈ N → (¬ ∃ R ∈ base H, g₀ ⊆ R) → z ∈ g₀ →
                  z ∈ component H x → z = rootOf H N (component H x) hCT := by
                intro z g₀ hg0N hnb0 hzg0 hzC
                have hzn : z ∉ (Ncomp H N (component H x)).biUnion id := by
                  intro hzU
                  rcases Finset.mem_biUnion.mp hzU with ⟨g', hg'f, hzg'⟩
                  dsimp only [id_eq] at hzg'
                  rcases Finset.mem_filter.mp hg'f with ⟨hg'N, R, hRC, hg'R⟩
                  have hgeq : g₀ = g' := by
                    by_contra hne'
                    exact Finset.disjoint_left.mp (hNdisj g₀ hg0N g' hg'N hne') hzg0 hzg'
                  exact hnb0 ⟨R, (Finset.mem_filter.mp hRC).1, hgeq ▸ hg'R⟩
                have := Finset.mem_sdiff.mpr ⟨hzC, hzn⟩
                rwa [hrs.2.1, Finset.mem_singleton] at this
              have hnb1 : ¬ ∃ R ∈ base H, g₁ ⊆ R := by
                rintro ⟨R, hRB, hgR⟩
                have hnd1 := (Finset.mem_filter.mp hg1m).2
                rw [Finset.not_disjoint_iff] at hnd1
                rcases hnd1 with ⟨w, hwg, hwc⟩
                have hwo := (Finset.mem_filter.mp hRB).2 (hgR hwg)
                simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
                exact hwo.2 ⟨c, hcH, hwc⟩
              have hnb2 : ¬ ∃ R ∈ base H, g₂ ⊆ R := by
                rintro ⟨R, hRB, hgR⟩
                have hnd2 := (Finset.mem_filter.mp hg2m).2
                rw [Finset.not_disjoint_iff] at hnd2
                rcases hnd2 with ⟨w, hwg, hwc⟩
                have hwo := (Finset.mem_filter.mp hRB).2 (hgR hwg)
                simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
                exact hwo.2 ⟨c', hc'H, hwc⟩
              have hxr := hnot_in_nc x g₁ (Finset.mem_filter.mp hg1m).1 hnb1 hxg1 (mem_component_self H x)
              have hyr := hnot_in_nc y g₂ (Finset.mem_filter.mp hg2m).1 hnb2 hyg2
                (hyeq ▸ mem_component_self H y)
              have hxy : x = y := hxr.trans hyr.symm
              have hg12 : g₁ = g₂ := by
                by_contra hne'
                exact Finset.disjoint_left.mp
                  (hNdisj g₁ (Finset.mem_filter.mp hg1m).1 g₂ (Finset.mem_filter.mp hg2m).1 hne')
                  hxg1 (hxy ▸ hyg2)
              have hsub1 := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).2.2 g₁ hg1m |>.2
              have hnd2 := (Finset.mem_filter.mp hg2m).2
              rw [Finset.not_disjoint_iff] at hnd2
              rcases hnd2 with ⟨w, hwg2, hwc'⟩
              rcases Finset.mem_union.mp (hsub1 (hg12 ▸ hwg2)) with hwc | hwo
              · exact Finset.disjoint_left.mp (cores_pairwise_disjoint hH3 hdeg hcH hc'H (Ne.symm hne)) hwc hwc'
              · have huo := outer_subset_ordinary hH3 hdeg hcH hwo
                simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
                exact huo.2 ⟨c', hc'H, hwc'⟩
            exact hceq ▸ hgmc'
          · exfalso
            have h2e := (Finset.mem_powersetCard.mp (hQsub heQ)).2
            obtain ⟨C, hCe⟩ : e.Nonempty := Finset.card_pos.mp (by omega)
            have hC1 : C ∈ (outer H c).image (component H) := hout.symm ▸ hCe
            have hC2 : C ∈ g.image (component H) := hgimg.symm ▸ hCe
            rcases Finset.mem_image.mp hC1 with ⟨x, hxo, rfl⟩
            rcases Finset.mem_image.mp hC2 with ⟨y, hyg, hyeq⟩
            have hU1 := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).1
            have hxU : x ∈ (Mcore N c).biUnion id := by rw [hU1]; exact Finset.mem_union_right _ hxo
            rcases Finset.mem_biUnion.mp hxU with ⟨g₁, hg1m, hxg1⟩
            dsimp only [id_eq] at hxg1
            have hCT : component H x ∈ trees H := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
            have hrs := rootOf_spec hH3 hdeg hNV hCT
            have hnb1 : ¬ ∃ R ∈ base H, g₁ ⊆ R := by
              rintro ⟨R, hRB, hgR⟩
              have hnd1 := (Finset.mem_filter.mp hg1m).2
              rw [Finset.not_disjoint_iff] at hnd1
              rcases hnd1 with ⟨w, hwg, hwc⟩
              have hwo := (Finset.mem_filter.mp hRB).2 (hgR hwg)
              simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
              exact hwo.2 ⟨c, hcH, hwc⟩
            have hnot_in_nc : ∀ z g₀, g₀ ∈ N → (¬ ∃ R ∈ base H, g₀ ⊆ R) → z ∈ g₀ →
                z ∈ component H x → z = rootOf H N (component H x) hCT := by
              intro z g₀ hg0N hnb0 hzg0 hzC
              have hzn : z ∉ (Ncomp H N (component H x)).biUnion id := by
                intro hzU
                rcases Finset.mem_biUnion.mp hzU with ⟨g', hg'f, hzg'⟩
                dsimp only [id_eq] at hzg'
                rcases Finset.mem_filter.mp hg'f with ⟨hg'N, R, hRC, hg'R⟩
                have hgeq : g₀ = g' := by
                  by_contra hne'
                  exact Finset.disjoint_left.mp (hNdisj g₀ hg0N g' hg'N hne') hzg0 hzg'
                exact hnb0 ⟨R, (Finset.mem_filter.mp hRC).1, hgeq ▸ hg'R⟩
              have := Finset.mem_sdiff.mpr ⟨hzC, hzn⟩
              rwa [hrs.2.1, Finset.mem_singleton] at this
            have hxr := hnot_in_nc x g₁ (Finset.mem_filter.mp hg1m).1 hnb1 hxg1 (mem_component_self H x)
            have hyr := hnot_in_nc y g hgN hnotB hyg (hyeq ▸ mem_component_self H y)
            have hxy : x = y := hxr.trans hyr.symm
            have hg1eq : g₁ = g := by
              by_contra hne'
              exact Finset.disjoint_left.mp (hNdisj g₁ (Finset.mem_filter.mp hg1m).1 g hgN hne')
                hxg1 (hxy ▸ hyg)
            have hnd1 := (Finset.mem_filter.mp hg1m).2
            rw [Finset.not_disjoint_iff] at hnd1
            rcases hnd1 with ⟨w, hwg1, hwc⟩
            have hwo := (Finset.mem_filter.mp hgEx).2.1 (hg1eq ▸ hwg1)
            simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
            exact hwo.2 ⟨c, hcH, hwc⟩
        · intro hgmc
          have hPmem : Mcore N c ∈ EdgeChoice H e :=
            Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hcH, hout⟩, hcm⟩)
          have hep := (edgeChoice_unique_in_comp hH3 hdeg (hQsub heQ) hPmem).2.2.1 g hgmc
          exact ⟨(Finset.mem_filter.mp hgmc).1, hep.2.1, hep.2.2.2⟩
      dsimp only [decomp]
      rw [hEq]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hcH, hout⟩, hcm⟩)
    · rcases Finset.mem_image.mp hO with ⟨g₀, hg0Ex, hg0img⟩
      rcases Finset.mem_filter.mp hg0Ex with ⟨hg0N, hg0ord, hnb0⟩
      have hEq : N.filter (fun g => ¬ Disjoint g (e.biUnion id) ∧ ¬ ∃ R ∈ base H, g ⊆ R) = {g₀} := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hgN, hnd, hnotB⟩
          rcases hfilt_eq g hgN ⟨hnd, hnotB⟩ with ⟨c, hc, hout, hgmc⟩ | ⟨hgEx, hgimg⟩
          · exfalso
            have hcH := (Finset.mem_filter.mp hc).1
            have hcm := hstr.2.1 c hc
            have h2e := (Finset.mem_powersetCard.mp (hQsub heQ)).2
            obtain ⟨C, hCe⟩ : e.Nonempty := Finset.card_pos.mp (by omega)
            have hC1 : C ∈ (outer H c).image (component H) := hout.symm ▸ hCe
            have hC2 : C ∈ g₀.image (component H) := hg0img.symm ▸ hCe
            rcases Finset.mem_image.mp hC1 with ⟨x, hxo, rfl⟩
            rcases Finset.mem_image.mp hC2 with ⟨y, hyg, hyeq⟩
            have hU1 := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).1
            have hxU : x ∈ (Mcore N c).biUnion id := by rw [hU1]; exact Finset.mem_union_right _ hxo
            rcases Finset.mem_biUnion.mp hxU with ⟨g₁, hg1m, hxg1⟩
            dsimp only [id_eq] at hxg1
            have hCT : component H x ∈ trees H := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
            have hrs := rootOf_spec hH3 hdeg hNV hCT
            have hnb1 : ¬ ∃ R ∈ base H, g₁ ⊆ R := by
              rintro ⟨R, hRB, hgR⟩
              have hnd1 := (Finset.mem_filter.mp hg1m).2
              rw [Finset.not_disjoint_iff] at hnd1
              rcases hnd1 with ⟨w, hwg, hwc⟩
              have hwo := (Finset.mem_filter.mp hRB).2 (hgR hwg)
              simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
              exact hwo.2 ⟨c, hcH, hwc⟩
            have hnot_in_nc : ∀ z g', g' ∈ N → (¬ ∃ R ∈ base H, g' ⊆ R) → z ∈ g' →
                z ∈ component H x → z = rootOf H N (component H x) hCT := by
              intro z g' hg'N hnb' hzg' hzC
              have hzn : z ∉ (Ncomp H N (component H x)).biUnion id := by
                intro hzU
                rcases Finset.mem_biUnion.mp hzU with ⟨g'', hg''f, hzg''⟩
                dsimp only [id_eq] at hzg''
                rcases Finset.mem_filter.mp hg''f with ⟨hg''N, R, hRC, hg''R⟩
                have hgeq : g' = g'' := by
                  by_contra hne'
                  exact Finset.disjoint_left.mp (hNdisj g' hg'N g'' hg''N hne') hzg' hzg''
                exact hnb' ⟨R, (Finset.mem_filter.mp hRC).1, hgeq ▸ hg''R⟩
              have := Finset.mem_sdiff.mpr ⟨hzC, hzn⟩
              rwa [hrs.2.1, Finset.mem_singleton] at this
            have hxr := hnot_in_nc x g₁ (Finset.mem_filter.mp hg1m).1 hnb1 hxg1 (mem_component_self H x)
            have hyr := hnot_in_nc y g₀ hg0N hnb0 hyg (hyeq ▸ mem_component_self H y)
            have hxy : x = y := hxr.trans hyr.symm
            have hg1eq : g₁ = g₀ := by
              by_contra hne'
              exact Finset.disjoint_left.mp (hNdisj g₁ (Finset.mem_filter.mp hg1m).1 g₀ hg0N hne')
                hxg1 (hxy ▸ hyg)
            have hnd1 := (Finset.mem_filter.mp hg1m).2
            rw [Finset.not_disjoint_iff] at hnd1
            rcases hnd1 with ⟨w, hwg1, hwc⟩
            have hwo := hg0ord (hg1eq ▸ hwg1)
            simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
            exact hwo.2 ⟨c, hcH, hwc⟩
          · by_contra hne
            have h2e := (Finset.mem_powersetCard.mp (hQsub heQ)).2
            obtain ⟨C, hCe⟩ : e.Nonempty := Finset.card_pos.mp (by omega)
            have hC1 : C ∈ g.image (component H) := hgimg.symm ▸ hCe
            have hC2 : C ∈ g₀.image (component H) := hg0img.symm ▸ hCe
            rcases Finset.mem_image.mp hC1 with ⟨x, hxg, rfl⟩
            rcases Finset.mem_image.mp hC2 with ⟨y, hyg, hyeq⟩
            have hCT : component H x ∈ trees H := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
            have hrs := rootOf_spec hH3 hdeg hNV hCT
            have hnot_in_nc : ∀ z g', g' ∈ N → (¬ ∃ R ∈ base H, g' ⊆ R) → z ∈ g' →
                z ∈ component H x → z = rootOf H N (component H x) hCT := by
              intro z g' hg'N hnb' hzg' hzC
              have hzn : z ∉ (Ncomp H N (component H x)).biUnion id := by
                intro hzU
                rcases Finset.mem_biUnion.mp hzU with ⟨g'', hg''f, hzg''⟩
                dsimp only [id_eq] at hzg''
                rcases Finset.mem_filter.mp hg''f with ⟨hg''N, R, hRC, hg''R⟩
                have hgeq : g' = g'' := by
                  by_contra hne'
                  exact Finset.disjoint_left.mp (hNdisj g' hg'N g'' hg''N hne') hzg' hzg''
                exact hnb' ⟨R, (Finset.mem_filter.mp hRC).1, hgeq ▸ hg''R⟩
              have := Finset.mem_sdiff.mpr ⟨hzC, hzn⟩
              rwa [hrs.2.1, Finset.mem_singleton] at this
            have hxr := hnot_in_nc x g hgN hnotB hxg (mem_component_self H x)
            have hyr := hnot_in_nc y g₀ hg0N hnb0 hyg (hyeq ▸ mem_component_self H y)
            have hxy : x = y := hxr.trans hyr.symm
            exact Finset.disjoint_left.mp (hNdisj g hgN g₀ hg0N hne) hxg (hxy ▸ hyg)
        · rintro h
          rw [h]
          have hg0sub : g₀ ⊆ e.biUnion id := fun u hu =>
            Finset.mem_biUnion.mpr ⟨component H u, hg0img ▸ Finset.mem_image_of_mem _ hu,
              mem_component_self H u⟩
          obtain ⟨u, hu⟩ : g₀.Nonempty := Finset.card_pos.mp (by rw [(hN2 g₀ hg0N).1]; omega)
          exact ⟨hg0N, fun hd => Finset.disjoint_left.mp hd hu (hg0sub hu), hnb0⟩
      dsimp only [decomp]
      rw [hEq]
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨g₀, ?_, rfl⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hN2 g₀ hg0N).1, ?_, hg0img⟩
      intro u hu
      exact Finset.mem_biUnion.mpr ⟨component H u, hg0img ▸ Finset.mem_image_of_mem _ hu,
        mem_component_self H u⟩
  · intro p hp
    simp only [Finset.mem_coe] at hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hdec := Finset.mem_pi.mp hp2
    have hNcomp_eq : ∀ C (hCT : C ∈ trees H),
        Ncomp H (recon p) C = uniqueTreeMatch H C (pickRoot p.1 p.2 C hCT) := by
      intro C hCT
      have hrC := (hpick_mem p hp C hCT).1
      have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT hrC).1
      ext g
      simp only [Ncomp, Finset.mem_filter]
      constructor
      · rintro ⟨hgM, R, hRC, hgR⟩
        rcases Finset.mem_union.mp hgM with (hg12 | hg3)
        · rcases Finset.mem_union.mp hg12 with hg1 | hg2
          · rcases Finset.mem_biUnion.mp hg1 with ⟨⟨C', hC'T⟩, _, hgC'⟩
            have hLM' := (uniqueTreeMatch_spec hH3 hdeg hC'T (hpick_mem p hp C' hC'T).1).1
            obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by rw [((Finset.mem_filter.mp hLM').2.1 g hgC').1]; omega)
            have huC : u ∈ C := (Finset.mem_filter.mp hRC).2 (hgR hug)
            have huC' : u ∈ C' := Finset.erase_subset _ C' (((Finset.mem_filter.mp hLM').2.1 g hgC').2 hug)
            have hCeq : C' = C := by
              by_contra hne
              exact Finset.disjoint_left.mp
                (parts_pairwise_disjoint H (Finset.mem_filter.mp hC'T).1 (Finset.mem_filter.mp hCT).1 hne)
                huC' huC
            subst hCeq; exact hgC'
          · exfalso
            have hcH := (Finset.mem_sdiff.mp hg2).1
            have hcc := ((mem_cores_iff hH3).mp hcH).1
            obtain ⟨u, hug⟩ : g.Nonempty := Finset.card_pos.mp (by omega)
            have huo := (Finset.mem_filter.mp (Finset.mem_filter.mp hRC).1).2 (hgR hug)
            simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
            exact huo.2 ⟨g, hcH, hug⟩
        · exfalso
          rcases Finset.mem_biUnion.mp hg3 with ⟨⟨e, he⟩, _, hge⟩
          exact ((edgeChoice_unique_in_comp hH3 hdeg (hQsub he) (hdec e he)).2.2.1 g hge).2.2.2
            ⟨R, (Finset.mem_filter.mp hRC).1, hgR⟩
      · intro hgU
        rcases (localMatch_tight
          (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
          (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
          hrC (Finset.mem_filter.mp hCT).2 hLM).2.2 g hgU with ⟨R, hRC, hgR⟩
        exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨⟨C, hCT⟩, Finset.mem_attach _ _, hgU⟩)), R, hRC, hgR⟩
    refine Prod.ext ?_ ?_
    · funext C hCf
      have hCT : C ∈ trees H := (Finset.mem_sdiff.mp hCf).1
      have hpr := (hpick_mem p hp C hCT).2.1 hCf
      have hrC := (hpick_mem p hp C hCT).1
      have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT hrC).1
      have hUeq := (localMatch_tight
        (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
        (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
        hrC (Finset.mem_filter.mp hCT).2 hLM).2.1
      have hdiff : C \ (Ncomp H (recon p) C).biUnion id = {p.1 C hCf} := by
        rw [hNcomp_eq C hCT, hUeq, hpr]
        ext u
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
        constructor
        · rintro ⟨huC, hnot⟩
          by_contra hne
          exact hnot ⟨hne, huC⟩
        · rintro rfl; exact ⟨hpr ▸ hrC, fun h => h.1 rfl⟩
      have hne : (C \ (Ncomp H (recon p) C).biUnion id).Nonempty := by rw [hdiff]; simp
      dsimp only [decomp, rootOf]
      rw [dite_cond_eq_true (eq_true hne)]
      have hcm : Classical.choose hne ∈ ({p.1 C hCf} : Finset _) := hdiff ▸ Classical.choose_spec hne
      exact Finset.mem_singleton.mp hcm
    · funext e heQ
      dsimp only [decomp]
      ext g
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hgM, hnd, hnotB⟩
        rcases Finset.mem_union.mp hgM with (hg12 | hg3)
        · exfalso
          rcases Finset.mem_union.mp hg12 with hg1 | hg2
          · rcases Finset.mem_biUnion.mp hg1 with ⟨⟨C, hCT⟩, _, hgC⟩
            have hrC := (hpick_mem p hp C hCT).1
            have hLM := (uniqueTreeMatch_spec hH3 hdeg hCT hrC).1
            rcases (localMatch_tight
              (fun R hR => hH3 R (Finset.mem_filter.mp (Finset.mem_filter.mp hR).1).1)
              (fun R₁ h1 R₂ h2' => base_linear hH3 (Finset.mem_filter.mp h1).1 (Finset.mem_filter.mp h2').1)
              hrC (Finset.mem_filter.mp hCT).2 hLM).2.2 g hgC with ⟨R, hRC, hgR⟩
            exact hnotB ⟨R, (Finset.mem_filter.mp hRC).1, hgR⟩
          · rw [Finset.not_disjoint_iff] at hnd
            rcases hnd with ⟨u, huc, hue⟩
            rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
            have huo := mem_parts_subset_ordinary H
              (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe)).1 huC
            simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
            exact huo.2 ⟨g, (Finset.mem_sdiff.mp hg2).1, huc⟩
        · rcases Finset.mem_biUnion.mp hg3 with ⟨⟨e', he'⟩, _, hge'⟩
          have heeq : e' = e := by
            by_contra hne
            rw [Finset.not_disjoint_iff] at hnd
            rcases hnd with ⟨u, hug, hue⟩
            rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
            have hCT := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
            have huo := mem_parts_subset_ordinary H (Finset.mem_filter.mp hCT).1 huC
            have hue' := (edgeChoice_unique_in_comp hH3 hdeg (hQsub he') (hdec e' he')).2.1
              (Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨g, hge', hug⟩, huo⟩)
            rcases Finset.mem_biUnion.mp hue' with ⟨C', hC'e', huC'⟩
            have hCeq : C = C' := by
              rw [← eq_component_of_mem_part H (Finset.mem_filter.mp hCT).1 huC,
                eq_component_of_mem_part H (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub he')).1 hC'e')).1 huC']
            subst hCeq
            exact Finset.disjoint_left.mp (hQdisj e' he' e heQ hne) hC'e' hCe
          subst heeq; exact hge'
      · intro hge
        have hep := (edgeChoice_unique_in_comp hH3 hdeg (hQsub heQ) (hdec e heQ)).2.2.1 g hge
        exact ⟨Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨⟨e, heQ⟩, Finset.mem_attach _ _, hge⟩), hep.2.1, hep.2.2.2⟩
  · intro N hN
    simp only [Finset.mem_coe] at hN
    rcases Finset.mem_filter.mp hN with ⟨hNV, hNQ⟩
    have hstr := validNonCyc_extractQ_mem hH3 hdeg hnbad hs hNV
    have hNV' := hNV
    simp only [ValidNonCyc, Finset.mem_filter, Finset.mem_univ, true_and] at hNV'
    rcases hNV' with ⟨hN2, hNdisj, _, _⟩
    have hdp : decomp N ∈ Dom := by
      rw [Finset.mem_product]
      refine ⟨Finset.mem_pi.mpr (fun C hCf => (rootOf_spec hH3 hdeg hNV (Finset.mem_sdiff.mp hCf).1).1),
        Finset.mem_pi.mpr (fun e heQ => ?_)⟩
      have he_ex : e ∈ extractQ H N := hNQ.symm ▸ heQ
      rcases Finset.mem_union.mp he_ex with hA | hO
      · rcases Finset.mem_image.mp hA with ⟨c, hc, hout⟩
        have hcH := (Finset.mem_filter.mp hc).1
        have hcm := hstr.2.1 c hc
        have hPmem : Mcore N c ∈ EdgeChoice H e :=
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hcH, hout⟩, hcm⟩)
        have hEq : (decomp N).2 e heQ = Mcore N c := by
          ext g; dsimp only [decomp]; simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hgN, hnd, hnotB⟩
            rcases hstr.2.2 g hgN with ⟨C, _, hgC⟩ | hgIn | ⟨c', hc', hgmc'⟩ | hgEx
            · rcases (Finset.mem_filter.mp hgC).2 with ⟨R, hRC, hgR⟩
              exact absurd ⟨R, (Finset.mem_filter.mp hRC).1, hgR⟩ hnotB
            · rw [Finset.not_disjoint_iff] at hnd
              rcases hnd with ⟨u, hug, hue⟩
              rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
              have huo := mem_parts_subset_ordinary H
                (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe)).1 huC
              simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
              exact absurd ⟨g, (Finset.mem_sdiff.mp hgIn).1, hug⟩ huo.2
            · have hc'H := (Finset.mem_filter.mp hc').1
              have he'Q : (outer H c').image (component H) ∈ Q := by
                rw [← hNQ]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc')
              have hout' : (outer H c').image (component H) = e := by
                by_contra hne
                rw [Finset.not_disjoint_iff] at hnd
                rcases hnd with ⟨u, hug, hue⟩
                rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
                have hCT := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
                have huo := mem_parts_subset_ordinary H (Finset.mem_filter.mp hCT).1 huC
                have hgsub := ((coreMatchings_explicit hH3 hdeg hc'H).2 _ (hstr.2.1 c' hc')).2.2 g hgmc' |>.2
                rcases Finset.mem_union.mp (hgsub hug) with huc' | huout
                · simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
                  exact huo.2 ⟨c', hc'H, huc'⟩
                · have hCmem : C ∈ (outer H c').image (component H) := by
                    rw [← eq_component_of_mem_part H (Finset.mem_filter.mp hCT).1 huC]
                    exact Finset.mem_image_of_mem _ huout
                  exact Finset.disjoint_left.mp (hQdisj _ he'Q e heQ hne) hCmem hCe
              have hceq : c' = c := by
                by_contra hne
                have h2e := (Finset.mem_powersetCard.mp (hQsub heQ)).2
                obtain ⟨C, hCe⟩ : e.Nonempty := Finset.card_pos.mp (by omega)
                rcases Finset.mem_image.mp (hout.symm ▸ hCe) with ⟨x, hxo, rfl⟩
                rcases Finset.mem_image.mp (hout'.symm ▸ hCe) with ⟨y, hyo, hyeq⟩
                have hU1 := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).1
                have hU2 := ((coreMatchings_explicit hH3 hdeg hc'H).2 _ (hstr.2.1 c' hc')).1
                rcases Finset.mem_biUnion.mp (by rw [hU1]; exact Finset.mem_union_right _ hxo) with ⟨g₁, hg1m, hxg1⟩
                rcases Finset.mem_biUnion.mp (by rw [hU2]; exact Finset.mem_union_right _ hyo) with ⟨g₂, hg2m, hyg2⟩
                dsimp only [id_eq] at hxg1 hyg2
                have hCT := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
                have hrs := rootOf_spec hH3 hdeg hNV hCT
                have hroot : ∀ z g₀ c₀, c₀ ∈ cores H → g₀ ∈ Mcore N c₀ → z ∈ g₀ → z ∈ component H x →
                    z = rootOf H N (component H x) hCT := by
                  intro z g₀ c₀ hc0 hg0m hzg0 hzC
                  have hzn : z ∉ (Ncomp H N (component H x)).biUnion id := by
                    intro hzU
                    rcases Finset.mem_biUnion.mp hzU with ⟨g', hg'f, hzg'⟩
                    dsimp only [id_eq] at hzg'
                    rcases Finset.mem_filter.mp hg'f with ⟨hg'N, R, hRC, hg'R⟩
                    have hgeq : g₀ = g' := by
                      by_contra hne'
                      exact Finset.disjoint_left.mp (hNdisj g₀ (Finset.mem_filter.mp hg0m).1 g' hg'N hne') hzg0 hzg'
                    have hnd0 := (Finset.mem_filter.mp hg0m).2
                    rw [Finset.not_disjoint_iff] at hnd0
                    rcases hnd0 with ⟨w, hwg0, hwc0⟩
                    have hwo := (Finset.mem_filter.mp (Finset.mem_filter.mp hRC).1).2 (hg'R (hgeq ▸ hwg0))
                    simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
                    exact hwo.2 ⟨c₀, hc0, hwc0⟩
                  have := Finset.mem_sdiff.mpr ⟨hzC, hzn⟩
                  rwa [hrs.2.1, Finset.mem_singleton] at this
                have hxy : x = y :=
                  (hroot x g₁ c hcH hg1m hxg1 (mem_component_self H x)).trans
                  (hroot y g₂ c' hc'H hg2m hyg2 (hyeq ▸ mem_component_self H y)).symm
                have hg12 : g₁ = g₂ := by
                  by_contra hne'
                  exact Finset.disjoint_left.mp
                    (hNdisj g₁ (Finset.mem_filter.mp hg1m).1 g₂ (Finset.mem_filter.mp hg2m).1 hne')
                    hxg1 (hxy ▸ hyg2)
                have hsub1 := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).2.2 g₁ hg1m |>.2
                have hnd2 := (Finset.mem_filter.mp hg2m).2
                rw [Finset.not_disjoint_iff] at hnd2
                rcases hnd2 with ⟨w, hwg2, hwc'⟩
                rcases Finset.mem_union.mp (hsub1 (hg12 ▸ hwg2)) with hwc | hwo
                · exact Finset.disjoint_left.mp (cores_pairwise_disjoint hH3 hdeg hcH hc'H (Ne.symm hne)) hwc hwc'
                · have huo := outer_subset_ordinary hH3 hdeg hcH hwo
                  simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
                  exact huo.2 ⟨c', hc'H, hwc'⟩
              exact hceq ▸ hgmc'
            · exfalso
              have he'Q : g.image (component H) ∈ Q := by
                rw [← hNQ]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hgEx)
              have hgimg : g.image (component H) = e := by
                by_contra hne
                rw [Finset.not_disjoint_iff] at hnd
                rcases hnd with ⟨u, hug, hue⟩
                rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
                have hCT := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
                have hCmem : C ∈ g.image (component H) := by
                  rw [← eq_component_of_mem_part H (Finset.mem_filter.mp hCT).1 huC]
                  exact Finset.mem_image_of_mem _ hug
                exact Finset.disjoint_left.mp (hQdisj _ he'Q e heQ hne) hCmem hCe
              have h2e := (Finset.mem_powersetCard.mp (hQsub heQ)).2
              obtain ⟨C, hCe⟩ : e.Nonempty := Finset.card_pos.mp (by omega)
              rcases Finset.mem_image.mp (hout.symm ▸ hCe) with ⟨x, hxo, rfl⟩
              rcases Finset.mem_image.mp (hgimg.symm ▸ hCe) with ⟨y, hyg, hyeq⟩
              have hU1 := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).1
              rcases Finset.mem_biUnion.mp (by rw [hU1]; exact Finset.mem_union_right _ hxo) with ⟨g₁, hg1m, hxg1⟩
              dsimp only [id_eq] at hxg1
              have hCT := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
              have hrs := rootOf_spec hH3 hdeg hNV hCT
              have hxr : x = rootOf H N (component H x) hCT := by
                have hzn : x ∉ (Ncomp H N (component H x)).biUnion id := by
                  intro hzU; rcases Finset.mem_biUnion.mp hzU with ⟨g', hg'f, hzg'⟩
                  dsimp only [id_eq] at hzg'
                  rcases Finset.mem_filter.mp hg'f with ⟨hg'N, R, hRC, hg'R⟩
                  have hgeq : g₁ = g' := by
                    by_contra hne'
                    exact Finset.disjoint_left.mp (hNdisj g₁ (Finset.mem_filter.mp hg1m).1 g' hg'N hne') hxg1 hzg'
                  have hnd1 := (Finset.mem_filter.mp hg1m).2
                  rw [Finset.not_disjoint_iff] at hnd1
                  rcases hnd1 with ⟨w, hwg1, hwc⟩
                  have hwo := (Finset.mem_filter.mp (Finset.mem_filter.mp hRC).1).2 (hg'R (hgeq ▸ hwg1))
                  simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
                  exact hwo.2 ⟨c, hcH, hwc⟩
                have := Finset.mem_sdiff.mpr ⟨mem_component_self H x, hzn⟩
                rwa [hrs.2.1, Finset.mem_singleton] at this
              have hyr : y = rootOf H N (component H x) hCT := by
                have hzn : y ∉ (Ncomp H N (component H x)).biUnion id := by
                  intro hzU; rcases Finset.mem_biUnion.mp hzU with ⟨g', hg'f, hzg'⟩
                  dsimp only [id_eq] at hzg'
                  rcases Finset.mem_filter.mp hg'f with ⟨hg'N, R, hRC, hg'R⟩
                  have hgeq : g = g' := by
                    by_contra hne'
                    exact Finset.disjoint_left.mp (hNdisj g hgN g' hg'N hne') hyg hzg'
                  exact hnotB ⟨R, (Finset.mem_filter.mp hRC).1, hgeq ▸ hg'R⟩
                have := Finset.mem_sdiff.mpr ⟨hyeq ▸ mem_component_self H y, hzn⟩
                rwa [hrs.2.1, Finset.mem_singleton] at this
              have hg1eq : g₁ = g := by
                by_contra hne'
                exact Finset.disjoint_left.mp (hNdisj g₁ (Finset.mem_filter.mp hg1m).1 g hgN hne')
                  hxg1 ((hxr.trans hyr.symm) ▸ hyg)
              have hnd1 := (Finset.mem_filter.mp hg1m).2
              rw [Finset.not_disjoint_iff] at hnd1
              rcases hnd1 with ⟨w, hwg1, hwc⟩
              have hwo := (Finset.mem_filter.mp hgEx).2.1 (hg1eq ▸ hwg1)
              simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
              exact hwo.2 ⟨c, hcH, hwc⟩
          · intro hgmc
            have hep := (edgeChoice_unique_in_comp hH3 hdeg (hQsub heQ) hPmem).2.2.1 g hgmc
            exact ⟨(Finset.mem_filter.mp hgmc).1, hep.2.1, hep.2.2.2⟩
        rw [hEq]; exact hPmem
      · rcases Finset.mem_image.mp hO with ⟨g₀, hg0Ex, hg0img⟩
        rcases Finset.mem_filter.mp hg0Ex with ⟨hg0N, hg0ord, hnb0⟩
        have hPmem : ({g₀} : Finset _) ∈ EdgeChoice H e := by
          refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨g₀, ?_, rfl⟩)
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hN2 g₀ hg0N).1, ?_, hg0img⟩
          intro u hu
          exact Finset.mem_biUnion.mpr ⟨component H u, hg0img ▸ Finset.mem_image_of_mem _ hu,
            mem_component_self H u⟩
        have hEq : (decomp N).2 e heQ = {g₀} := by
          ext g; dsimp only [decomp]; simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hgN, hnd, hnotB⟩
            rcases hstr.2.2 g hgN with ⟨C, _, hgC⟩ | hgIn | ⟨c, hc, hgmc⟩ | hgEx
            · rcases (Finset.mem_filter.mp hgC).2 with ⟨R, hRC, hgR⟩
              exact absurd ⟨R, (Finset.mem_filter.mp hRC).1, hgR⟩ hnotB
            · rw [Finset.not_disjoint_iff] at hnd
              rcases hnd with ⟨u, hug, hue⟩
              rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
              have huo := mem_parts_subset_ordinary H
                (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe)).1 huC
              simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
              exact absurd ⟨g, (Finset.mem_sdiff.mp hgIn).1, hug⟩ huo.2
            · exfalso
              have hcH := (Finset.mem_filter.mp hc).1
              have hcm := hstr.2.1 c hc
              have he'Q : (outer H c).image (component H) ∈ Q := by
                rw [← hNQ]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hc)
              have hout : (outer H c).image (component H) = e := by
                by_contra hne
                rw [Finset.not_disjoint_iff] at hnd
                rcases hnd with ⟨u, hug, hue⟩
                rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
                have hCT := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
                have huo := mem_parts_subset_ordinary H (Finset.mem_filter.mp hCT).1 huC
                have hgsub := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).2.2 g hgmc |>.2
                rcases Finset.mem_union.mp (hgsub hug) with huc | huout
                · simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at huo
                  exact huo.2 ⟨c, hcH, huc⟩
                · have hCmem : C ∈ (outer H c).image (component H) := by
                    rw [← eq_component_of_mem_part H (Finset.mem_filter.mp hCT).1 huC]
                    exact Finset.mem_image_of_mem _ huout
                  exact Finset.disjoint_left.mp (hQdisj _ he'Q e heQ hne) hCmem hCe
              have h2e := (Finset.mem_powersetCard.mp (hQsub heQ)).2
              obtain ⟨C, hCe⟩ : e.Nonempty := Finset.card_pos.mp (by omega)
              rcases Finset.mem_image.mp (hout.symm ▸ hCe) with ⟨x, hxo, rfl⟩
              rcases Finset.mem_image.mp (hg0img.symm ▸ hCe) with ⟨y, hyg, hyeq⟩
              have hU1 := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).1
              rcases Finset.mem_biUnion.mp (by rw [hU1]; exact Finset.mem_union_right _ hxo) with ⟨g₁, hg1m, hxg1⟩
              dsimp only [id_eq] at hxg1
              have hCT := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
              have hrs := rootOf_spec hH3 hdeg hNV hCT
              have hxr : x = rootOf H N (component H x) hCT := by
                have hzn : x ∉ (Ncomp H N (component H x)).biUnion id := by
                  intro hzU; rcases Finset.mem_biUnion.mp hzU with ⟨g', hg'f, hzg'⟩
                  dsimp only [id_eq] at hzg'
                  rcases Finset.mem_filter.mp hg'f with ⟨hg'N, R, hRC, hg'R⟩
                  have hgeq : g₁ = g' := by
                    by_contra hne'
                    exact Finset.disjoint_left.mp (hNdisj g₁ (Finset.mem_filter.mp hg1m).1 g' hg'N hne') hxg1 hzg'
                  have hnd1 := (Finset.mem_filter.mp hg1m).2
                  rw [Finset.not_disjoint_iff] at hnd1
                  rcases hnd1 with ⟨w, hwg1, hwc⟩
                  have hwo := (Finset.mem_filter.mp (Finset.mem_filter.mp hRC).1).2 (hg'R (hgeq ▸ hwg1))
                  simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
                  exact hwo.2 ⟨c, hcH, hwc⟩
                have := Finset.mem_sdiff.mpr ⟨mem_component_self H x, hzn⟩
                rwa [hrs.2.1, Finset.mem_singleton] at this
              have hyr : y = rootOf H N (component H x) hCT := by
                have hzn : y ∉ (Ncomp H N (component H x)).biUnion id := by
                  intro hzU; rcases Finset.mem_biUnion.mp hzU with ⟨g', hg'f, hzg'⟩
                  dsimp only [id_eq] at hzg'
                  rcases Finset.mem_filter.mp hg'f with ⟨hg'N, R, hRC, hg'R⟩
                  have hgeq : g₀ = g' := by
                    by_contra hne'
                    exact Finset.disjoint_left.mp (hNdisj g₀ hg0N g' hg'N hne') hyg hzg'
                  exact hnb0 ⟨R, (Finset.mem_filter.mp hRC).1, hgeq ▸ hg'R⟩
                have := Finset.mem_sdiff.mpr ⟨hyeq ▸ mem_component_self H y, hzn⟩
                rwa [hrs.2.1, Finset.mem_singleton] at this
              have hg1eq : g₁ = g₀ := by
                by_contra hne'
                exact Finset.disjoint_left.mp (hNdisj g₁ (Finset.mem_filter.mp hg1m).1 g₀ hg0N hne')
                  hxg1 ((hxr.trans hyr.symm) ▸ hyg)
              have hnd1 := (Finset.mem_filter.mp hg1m).2
              rw [Finset.not_disjoint_iff] at hnd1
              rcases hnd1 with ⟨w, hwg1, hwc⟩
              have hwo := hg0ord (hg1eq ▸ hwg1)
              simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
              exact hwo.2 ⟨c, hcH, hwc⟩
            · have he'Q : g.image (component H) ∈ Q := by
                rw [← hNQ]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hgEx)
              have hgimg : g.image (component H) = e := by
                by_contra hne
                rw [Finset.not_disjoint_iff] at hnd
                rcases hnd with ⟨u, hug, hue⟩
                rcases Finset.mem_biUnion.mp hue with ⟨C, hCe, huC⟩
                have hCT := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
                have hCmem : C ∈ g.image (component H) := by
                  rw [← eq_component_of_mem_part H (Finset.mem_filter.mp hCT).1 huC]
                  exact Finset.mem_image_of_mem _ hug
                exact Finset.disjoint_left.mp (hQdisj _ he'Q e heQ hne) hCmem hCe
              by_contra hne
              have h2e := (Finset.mem_powersetCard.mp (hQsub heQ)).2
              obtain ⟨C, hCe⟩ : e.Nonempty := Finset.card_pos.mp (by omega)
              rcases Finset.mem_image.mp (hgimg.symm ▸ hCe) with ⟨x, hxg, rfl⟩
              rcases Finset.mem_image.mp (hg0img.symm ▸ hCe) with ⟨y, hyg, hyeq⟩
              have hCT := (Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe
              have hrs := rootOf_spec hH3 hdeg hNV hCT
              have hnot_in_nc : ∀ z g', g' ∈ N → (¬ ∃ R ∈ base H, g' ⊆ R) → z ∈ g' →
                  z ∈ component H x → z = rootOf H N (component H x) hCT := by
                intro z g' hg'N hnb' hzg' hzC
                have hzn : z ∉ (Ncomp H N (component H x)).biUnion id := by
                  intro hzU; rcases Finset.mem_biUnion.mp hzU with ⟨g'', hg''f, hzg''⟩
                  dsimp only [id_eq] at hzg''
                  rcases Finset.mem_filter.mp hg''f with ⟨hg''N, R, hRC, hg''R⟩
                  have hgeq : g' = g'' := by
                    by_contra hne'
                    exact Finset.disjoint_left.mp (hNdisj g' hg'N g'' hg''N hne') hzg' hzg''
                  exact hnb' ⟨R, (Finset.mem_filter.mp hRC).1, hgeq ▸ hg''R⟩
                have := Finset.mem_sdiff.mpr ⟨hzC, hzn⟩
                rwa [hrs.2.1, Finset.mem_singleton] at this
              have hxy : x = y :=
                (hnot_in_nc x g hgN hnotB hxg (mem_component_self H x)).trans
                (hnot_in_nc y g₀ hg0N hnb0 hyg (hyeq ▸ mem_component_self H y)).symm
              exact Finset.disjoint_left.mp (hNdisj g hgN g₀ hg0N hne) hxg (hxy ▸ hyg)
          · rintro h
            rw [h]
            have hep := (edgeChoice_unique_in_comp hH3 hdeg (hQsub heQ) hPmem).2.2.1 g₀ (by simp)
            exact ⟨hg0N, hep.2.1, hep.2.2.2⟩
        rw [hEq]; exact hPmem
    have hroot_eq : ∀ C (hCT : C ∈ trees H), pickRoot (decomp N).1 (decomp N).2 C hCT = rootOf H N C hCT := by
      intro C hCT
      by_cases hCf : C ∈ freeTrees
      · exact (hpick_mem (decomp N) hdp C hCT).2.1 hCf
      · have hex : ∃ e ∈ Q, C ∈ e := by
          by_contra hno
          exact hCf (Finset.mem_sdiff.mpr ⟨hCT, fun hU => hno (Finset.mem_biUnion.mp hU)⟩)
        rcases hex with ⟨e, heQ, hCe⟩
        have hsing := (hpick_mem (decomp N) hdp C hCT).2.2 e heQ hCe
        have hmem : pickRoot (decomp N).1 (decomp N).2 C hCT ∈ ((decomp N).2 e heQ).biUnion id ∩ C := by
          rw [hsing]; simp
        rcases Finset.mem_inter.mp hmem with ⟨huU, huC⟩
        rcases Finset.mem_biUnion.mp huU with ⟨g, hgf, hug⟩
        dsimp only [id_eq] at hug
        rcases Finset.mem_filter.mp hgf with ⟨hgN, _, hnotB⟩
        have hrs := rootOf_spec hH3 hdeg hNV hCT
        have hun : pickRoot (decomp N).1 (decomp N).2 C hCT ∉ (Ncomp H N C).biUnion id := by
          intro huNC
          rcases Finset.mem_biUnion.mp huNC with ⟨g', hg'f, hug'⟩
          dsimp only [id_eq] at hug'
          rcases Finset.mem_filter.mp hg'f with ⟨hg'N, R, hRC, hg'R⟩
          have hgeq : g = g' := by
            by_contra hne'
            exact Finset.disjoint_left.mp (hNdisj g hgN g' hg'N hne') hug hug'
          exact hnotB ⟨R, (Finset.mem_filter.mp hRC).1, hgeq ▸ hg'R⟩
        have := Finset.mem_sdiff.mpr ⟨huC, hun⟩
        rwa [hrs.2.1, Finset.mem_singleton] at this
    have hact_eq : actOf (decomp N).2 = activeCores H N := by
      ext c
      simp only [actOf, activeCores, Finset.mem_filter]
      constructor
      · rintro ⟨hcH, e, heQ, hcsub⟩
        refine ⟨hcH, fun hcN => ?_⟩
        have hcc := ((mem_cores_iff hH3).mp hcH).1
        obtain ⟨u, huc⟩ : c.Nonempty := Finset.card_pos.mp (by omega)
        rcases Finset.mem_biUnion.mp (hcsub huc) with ⟨g, hgf, hug⟩
        dsimp only [id_eq] at hug
        rcases Finset.mem_filter.mp hgf with ⟨hgN, hnd, _⟩
        have hgeq : g = c := by
          by_contra hne
          exact Finset.disjoint_left.mp (hNdisj g hgN c hcN hne) hug huc
        rw [hgeq] at hnd
        rw [Finset.not_disjoint_iff] at hnd
        rcases hnd with ⟨w, hwc, hwe⟩
        rcases Finset.mem_biUnion.mp hwe with ⟨C, hCe, hwC⟩
        have hwo := mem_parts_subset_ordinary H
          (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp (hQsub heQ)).1 hCe)).1 hwC
        simp only [ordinary, Finset.mem_sdiff, Finset.mem_biUnion, id_eq] at hwo
        exact hwo.2 ⟨c, hcH, hwc⟩
      · rintro ⟨hcH, hcnN⟩
        have hcA : c ∈ activeCores H N := Finset.mem_filter.mpr ⟨hcH, hcnN⟩
        have heQ : (outer H c).image (component H) ∈ Q := by
          rw [← hNQ]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcA)
        have hcm := hstr.2.1 c hcA
        have hU := ((coreMatchings_explicit hH3 hdeg hcH).2 _ hcm).1
        refine ⟨hcH, (outer H c).image (component H), heQ, fun u huc => ?_⟩
        have huU : u ∈ (Mcore N c).biUnion id := by rw [hU]; exact Finset.mem_union_left _ huc
        rcases Finset.mem_biUnion.mp huU with ⟨g, hgmc, hug⟩
        dsimp only [id_eq] at hug
        have hPmem : Mcore N c ∈ EdgeChoice H ((outer H c).image (component H)) :=
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hcH, rfl⟩, hcm⟩)
        have hep := (edgeChoice_unique_in_comp hH3 hdeg (hQsub heQ) hPmem).2.2.1 g hgmc
        exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hgmc).1, hep.2.1, hep.2.2.2⟩, hug⟩
    ext g
    simp only [recon, Finset.mem_union, Finset.mem_biUnion, Finset.mem_attach, true_and,
      Subtype.exists, hact_eq]
    constructor
    · rintro (((⟨C, hCT, hgU⟩ | hgIn) | ⟨e, heQ, hgf⟩))
      · rw [hroot_eq C hCT, ← (rootOf_spec hH3 hdeg hNV hCT).2.2.2.1] at hgU
        exact (Finset.mem_filter.mp hgU).1
      · rcases Finset.mem_sdiff.mp hgIn with ⟨hcH, hna⟩
        by_contra hcnN
        exact hna (Finset.mem_filter.mpr ⟨hcH, hcnN⟩)
      · exact (Finset.mem_filter.mp hgf).1
    · intro hgN
      rcases hstr.2.2 g hgN with ⟨C, hCT, hgC⟩ | hgIn | ⟨c, hcA, hgmc⟩ | hgEx
      · left; left
        refine ⟨C, hCT, ?_⟩
        rw [hroot_eq C hCT, ← (rootOf_spec hH3 hdeg hNV hCT).2.2.2.1]
        exact hgC
      · exact Or.inl (Or.inr hgIn)
      · right
        have hcH := (Finset.mem_filter.mp hcA).1
        have heQ : (outer H c).image (component H) ∈ Q := by
          rw [← hNQ]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hcA)
        have hPmem : Mcore N c ∈ EdgeChoice H ((outer H c).image (component H)) :=
          Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨c, Finset.mem_filter.mpr ⟨hcH, rfl⟩, hstr.2.1 c hcA⟩)
        have hep := (edgeChoice_unique_in_comp hH3 hdeg (hQsub heQ) hPmem).2.2.1 g hgmc
        exact ⟨_, heQ, Finset.mem_filter.mpr ⟨hgN, hep.2.1, hep.2.2.2⟩⟩
      · right
        have heQ : g.image (component H) ∈ Q := by
          rw [← hNQ]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hgEx)
        rcases Finset.mem_filter.mp hgEx with ⟨_, _, hnotB⟩
        have hsub : g ⊆ (g.image (component H)).biUnion id := fun u hu =>
          Finset.mem_biUnion.mpr ⟨component H u, Finset.mem_image_of_mem _ hu, mem_component_self H u⟩
        obtain ⟨u, hu⟩ : g.Nonempty := Finset.card_pos.mp (by rw [(hN2 g hgN).1]; omega)
        exact ⟨_, heQ, Finset.mem_filter.mpr ⟨hgN, fun hd => Finset.disjoint_left.mp hd hu (hsub hu), hnotB⟩⟩

lemma main_thm {n : Nat} {H : Finset (Finset (Fin n))}
    (hH3 : ∀ R ∈ H, R.card = 3)
    (hdeg : ∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2)
    (s : Nat) :
    (ValidAll H s).card =
      if bad H ∨ s < baseSize H then 0
      else 2 ^ (cycles H).card *
        ((candidates H).filter (fun Q => Q.card = s - baseSize H)).sum (fun Q =>
          ((trees H \ Q.biUnion id).prod Finset.card) * Q.prod (weight H)) := by
  by_cases hbad_lt : bad H ∨ s < baseSize H
  · rw [if_pos hbad_lt, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro M hM
    simp only [ValidAll, Finset.mem_filter, Finset.mem_univ, true_and] at hM
    rcases hM with ⟨hV, hMs⟩
    have hnb := not_bad_and_baseSize_le_of_valid hH3 hdeg hV
    rcases hbad_lt with hb | hlt
    · exact hnb.1 hb
    · omega
  · rw [if_neg hbad_lt]
    have hnbad : ¬ bad H := fun h => hbad_lt (Or.inl h)
    have hs : baseSize H ≤ s := Nat.le_of_not_lt (fun h => hbad_lt (Or.inr h))
    rw [validAll_card_eq_pow_mul_noncyc hH3 hdeg hnbad hs]
    congr 1
    rw [Finset.card_eq_sum_card_fiberwise
      (f := extractQ H)
      (t := (candidates H).filter (fun Q => Q.card = s - baseSize H))
      (fun N hN => (validNonCyc_extractQ_mem hH3 hdeg hnbad hs hN).1)]
    exact Finset.sum_congr rfl (fun Q hQ => validNonCyc_fiber_card hH3 hdeg hnbad hs hQ)

end PEqualNP.Outside.L_lib_948

theorem PEqualNP.Outside.L_lib_948 :
∀ (n : Nat) (H : Finset (Finset (Fin n))), (∀ R ∈ H, R.card = 3) →
  (∀ u : Fin n, (H.filter (fun R => u ∈ R)).card ≤ 2) →
  let Rows := Finset (Finset (Fin n))
  let cores := ((H.product H).image (fun z => z.1 ∩ z.2)).filter (fun c => c.card = 2)
  let ordinary := Finset.univ \ cores.biUnion id
  let base := H.filter (fun R => R ⊆ ordinary)
  let outer := fun c : Finset (Fin n) => (H.filter (fun R => c ⊆ R)).biUnion id \ c
  let component := fun u : Fin n => (List.range n).foldl (fun V _ =>
    V ∪ (base.filter (fun R => ¬ Disjoint R V)).biUnion id) {u}
  let parts := ordinary.image component
  let tests := fun C : Finset (Fin n) => (base.filter (fun R => R ⊆ C)).card
  let trees := parts.filter (fun C => C.card = 2*tests C+1)
  let cycles := parts.filter (fun C => C.card = 2*tests C)
  let bad := ∃ C ∈ parts, C.card < 2*tests C
  let baseSize := base.card+cores.card
  let weight := fun edge : Rows => edge.prod Finset.card +
    2*(cores.filter (fun c => (outer c).image component = edge)).card
  let candidates := (trees.powersetCard 2).powerset.filter (fun Q =>
    ∀ g ∈ Q, ∀ h ∈ Q, g ≠ h → Disjoint g h)
  let hist := fun s : Nat => Nat.card {M : Rows // (∀ g ∈ M, g.card = 2) ∧
    (∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h) ∧
    (∀ R ∈ H, ∃ g ∈ M, g ⊆ R) ∧ M.card = s}
  ∀ s : Nat, hist s = if bad ∨ s < baseSize then 0 else
    2^cycles.card * (candidates.filter (fun Q => Q.card = s-baseSize)).sum (fun Q =>
      ((trees \ Q.biUnion id).prod Finset.card) * Q.prod weight) := by
  intro n H hH3 hdeg
  dsimp only
  intro s
  have hcard : Nat.card {M : Finset (Finset (Fin n)) // (∀ g ∈ M, g.card = 2) ∧
      (∀ g ∈ M, ∀ h ∈ M, g ≠ h → Disjoint g h) ∧
      (∀ R ∈ H, ∃ g ∈ M, g ⊆ R) ∧ M.card = s} =
      (PEqualNP.Outside.L_lib_948.ValidAll H s).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply congr_arg Finset.card
    ext M
    simp only [PEqualNP.Outside.L_lib_948.ValidAll, PEqualNP.Outside.L_lib_948.Valid,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩,
      fun ⟨⟨h1, h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
  rw [hcard]
  exact PEqualNP.Outside.L_lib_948.main_thm hH3 hdeg s
