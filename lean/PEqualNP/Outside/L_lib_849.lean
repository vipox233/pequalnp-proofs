import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_849

variable {n : ℕ} (G : SimpleGraph (Fin n))

def Adj' (S : Finset (Fin n)) (a b : Fin n) : Prop := G.Adj a b ∧ a ∈ S ∧ b ∈ S

abbrev Rel (S : Finset (Fin n)) := Relation.ReflTransGen (Adj' G S)

noncomputable def parts (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  S.attach.image (fun v =>
    (S.attach.filter (fun u => (G.induce (↑S : Set (Fin n))).Reachable v u)).image Subtype.val)

theorem reach_iff (S : Finset (Fin n)) (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S) :
    (G.induce (↑S : Set (Fin n))).Reachable ⟨a, ha⟩ ⟨b, hb⟩ ↔ Rel G S a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    have key : ∀ x y : (↑S : Set (Fin n)), Relation.ReflTransGen (G.induce (↑S : Set (Fin n))).Adj x y →
        Rel G S x.1 y.1 := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih =>
        refine ih.tail ⟨?_, ?_, ?_⟩
        · simpa using hbc
        · exact Subtype.prop _
        · exact Subtype.prop _
    exact key _ _ h
  · intro h
    have key : ∀ y, Rel G S a y → ∀ hy : y ∈ S,
        Relation.ReflTransGen (G.induce (↑S : Set (Fin n))).Adj ⟨a, ha⟩ ⟨y, hy⟩ := by
      intro y hy
      induction hy with
      | refl => intro _; exact Relation.ReflTransGen.refl
      | tail _ hbc ih =>
        intro hd
        obtain ⟨hadj, hb', _⟩ := hbc
        exact (ih hb').tail (by simpa using hadj)
    exact key b h hb

theorem rel_mem (S : Finset (Fin n)) (v u : Fin n) (hv : v ∈ S) (h : Rel G S v u) : u ∈ S := by
  induction h with
  | refl => exact hv
  | tail _ hbc _ => exact hbc.2.2

theorem rel_symm (S : Finset (Fin n)) (a b : Fin n) (h : Rel G S a b) : Rel G S b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ⟨hbc.1.symm, hbc.2.2, hbc.2.1⟩ ih

theorem rel_mono (S S' : Finset (Fin n)) (hS : S ⊆ S') (a b : Fin n) (h : Rel G S a b) :
    Rel G S' a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail ⟨hbc.1, hS hbc.2.1, hS hbc.2.2⟩

theorem mem_parts (S X : Finset (Fin n)) :
    X ∈ parts G S ↔ ∃ v ∈ S, ∀ u, u ∈ X ↔ Rel G S v u := by
  unfold parts
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨⟨v, hv⟩, -, rfl⟩
    refine ⟨v, hv, fun u => ?_⟩
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨w, hw⟩, ⟨-, hr⟩, rfl⟩
      exact (reach_iff G S v w hv hw).1 hr
    · intro hr
      exact ⟨⟨u, rel_mem G S v u hv hr⟩, ⟨Finset.mem_attach _ _, (reach_iff G S v u hv _).2 hr⟩, rfl⟩
  · rintro ⟨v, hv, hX⟩
    refine ⟨⟨v, hv⟩, Finset.mem_attach _ _, ?_⟩
    ext u
    rw [hX u]
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨w, hw⟩, ⟨-, hr⟩, rfl⟩
      exact (reach_iff G S v w hv hw).1 hr
    · intro hr
      exact ⟨⟨u, rel_mem G S v u hv hr⟩, ⟨Finset.mem_attach _ _, (reach_iff G S v u hv _).2 hr⟩, rfl⟩

theorem part_sub (S X : Finset (Fin n)) (hX : X ∈ parts G S) : X ⊆ S := by
  obtain ⟨v, hv, hX⟩ := (mem_parts G S X).1 hX
  intro u hu
  exact rel_mem G S v u hv ((hX u).1 hu)

theorem part_root (S X : Finset (Fin n)) (hX : X ∈ parts G S) (a : Fin n) (ha : a ∈ X) :
    ∀ u, u ∈ X ↔ Rel G S a u := by
  obtain ⟨v, _, hX⟩ := (mem_parts G S X).1 hX
  have hva := (hX a).1 ha
  intro u
  rw [hX u]
  constructor
  · intro h; exact (rel_symm G S _ _ hva).trans h
  · intro h; exact hva.trans h

theorem part_eq (S X Y : Finset (Fin n)) (hX : X ∈ parts G S) (hY : Y ∈ parts G S)
    (a : Fin n) (haX : a ∈ X) (haY : a ∈ Y) : X = Y := by
  ext u
  rw [part_root G S X hX a haX, part_root G S Y hY a haY]

theorem part_ne (S X : Finset (Fin n)) (hX : X ∈ parts G S) : X.Nonempty := by
  obtain ⟨v, _, hX⟩ := (mem_parts G S X).1 hX
  exact ⟨v, (hX v).2 Relation.ReflTransGen.refl⟩

theorem part_of (S : Finset (Fin n)) (v : Fin n) (hv : v ∈ S) : ∃ X ∈ parts G S, v ∈ X := by
  classical
  refine ⟨S.filter (fun u => Rel G S v u), (mem_parts G S _).2 ⟨v, hv, fun u => ?_⟩, ?_⟩
  · simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨rel_mem G S v u hv h, h⟩
  · simp only [Finset.mem_filter]
    exact ⟨hv, Relation.ReflTransGen.refl⟩

theorem part_closed (S X : Finset (Fin n)) (hX : X ∈ parts G S) (x y : Fin n) (hx : x ∈ X)
    (hy : y ∈ S) (hxy : G.Adj x y) : y ∈ X := by
  rw [part_root G S X hX x hx]
  exact Relation.ReflTransGen.single ⟨hxy, part_sub G S X hX hx, hy⟩

theorem parts_replace (S C T S' : Finset (Fin n)) (hC : C ∈ parts G S) (hT : T ⊆ C)
    (hS' : ∀ v, v ∈ S' ↔ (v ∈ S ∧ v ∉ C) ∨ v ∈ T) (X : Finset (Fin n)) :
    X ∈ parts G S' ↔ (X ∈ parts G S ∧ X ≠ C) ∨ X ∈ parts G T := by
  have hCS := part_sub G S C hC
  have sub' : S' ⊆ S := by
    intro v hv
    rcases (hS' v).1 hv with h | h
    · exact h.1
    · exact hCS (hT h)
  have subT : T ⊆ S' := fun v hv => (hS' v).2 (Or.inr hv)
  -- paths from outside C
  have outC : ∀ v, v ∈ S → v ∉ C → ∀ u, Rel G S v u → u ∉ C ∧ Rel G S' v u := by
    intro v hv hvC u hu
    induction hu with
    | refl => exact ⟨hvC, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨hadj, hb, hc⟩ := hbc
      have hcC : c ∉ C := by
        intro hcC
        exact h1 (part_closed G S C hC _ _ hcC hb hadj.symm)
      refine ⟨hcC, h2.tail ⟨hadj, (hS' _).2 (Or.inl ⟨hb, h1⟩), (hS' _).2 (Or.inl ⟨hc, hcC⟩)⟩⟩
  have inT : ∀ v, v ∈ T → ∀ u, Rel G S' v u → Rel G T v u := by
    intro v hv u hu
    have : ∀ u, Rel G S' v u → u ∈ T ∧ Rel G T v u := by
      intro u hu
      induction hu with
      | refl => exact ⟨hv, Relation.ReflTransGen.refl⟩
      | @tail b c _ hbc ih =>
        obtain ⟨h1, h2⟩ := ih
        obtain ⟨hadj, _, hc⟩ := hbc
        have hcT : c ∈ T := by
          rcases (hS' _).1 hc with h | h
          · exact absurd (part_closed G S C hC _ _ (hT h1) h.1 hadj) h.2
          · exact h
        exact ⟨hcT, h2.tail ⟨hadj, h1, hcT⟩⟩
    exact (this u hu).2
  constructor
  · intro hX
    obtain ⟨v, hv, hXv⟩ := (mem_parts G S' X).1 hX
    rcases (hS' v).1 hv with h | h
    · left
      refine ⟨(mem_parts G S X).2 ⟨v, h.1, fun u => ?_⟩, ?_⟩
      · rw [hXv u]
        exact ⟨rel_mono G S' S sub' v u, fun hr => (outC v h.1 h.2 u hr).2⟩
      · intro hXC
        apply h.2
        rw [← hXC]
        exact (hXv v).2 Relation.ReflTransGen.refl
    · right
      refine (mem_parts G T X).2 ⟨v, h, fun u => ?_⟩
      rw [hXv u]
      exact ⟨inT v h u, rel_mono G T S' subT v u⟩
  · rintro (⟨hX, hXC⟩ | hX)
    · obtain ⟨v, hv, hXv⟩ := (mem_parts G S X).1 hX
      have hvX : v ∈ X := (hXv v).2 Relation.ReflTransGen.refl
      have hvC : v ∉ C := fun hvC => hXC (part_eq G S X C hX hC v hvX hvC)
      refine (mem_parts G S' X).2 ⟨v, (hS' v).2 (Or.inl ⟨hv, hvC⟩), fun u => ?_⟩
      rw [hXv u]
      exact ⟨fun hr => (outC v hv hvC u hr).2, rel_mono G S' S sub' v u⟩
    · obtain ⟨v, hv, hXv⟩ := (mem_parts G T X).1 hX
      refine (mem_parts G S' X).2 ⟨v, subT hv, fun u => ?_⟩
      rw [hXv u]
      exact ⟨rel_mono G T S' subT v u, inT v hv u⟩

theorem sum_parts {M : Type*} [AddCommMonoid M] (f : Fin n → M) (T : Finset (Fin n)) :
    ∑ P ∈ parts G T, ∑ i ∈ P, f i = ∑ i ∈ T, f i := by
  classical
  have hU : (parts G T).biUnion id = T := by
    ext v
    simp only [Finset.mem_biUnion, id]
    constructor
    · rintro ⟨X, hX, hv⟩; exact part_sub G T X hX hv
    · intro hv; exact part_of G T v hv
  conv_rhs => rw [← hU]
  rw [Finset.sum_biUnion]
  · rfl
  · intro X hX Y hY hXY
    rw [Function.onFun, id, id, Finset.disjoint_left]
    intro a haX haY
    exact hXY (part_eq G T X Y hX hY a haX haY)

theorem parts_empty : parts G ∅ = ∅ := by
  ext X
  simp only [Finset.notMem_empty, iff_false]
  intro hX
  obtain ⟨v, hv, _⟩ := (mem_parts G ∅ X).1 hX
  simp at hv

end PEqualNP.Outside.L_lib_849

open PEqualNP.Outside.L_lib_849 in
theorem PEqualNP.Outside.L_lib_849 : ∀ (n m : ℕ) (G : SimpleGraph (Fin n)),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  ∀ h : Fin n → A,
    let parts := fun S : Finset (Fin n) =>
      S.attach.image (fun v =>
        (S.attach.filter (fun u => (G.induce (↑S : Set (Fin n))).Reachable v u)).image Subtype.val)
    let total := fun T : Finset (Fin n) => ∑ i ∈ T, h i
    let space := fun S => Submodule.span F (↑((parts S).image total) : Set A)
    let score := fun S => (parts S).card - Module.finrank F (space S)
    ∀ S : Finset (Fin n), (∀ T, score T ≤ score S) →
      (∀ T : Finset (Fin n), score T = score S → S.card ≤ T.card) →
      ∀ C ∈ parts S,
        total C ∈ Submodule.span F (↑(((parts S).erase C).image total) : Set A) ∧
        (∀ T : Finset (Fin n), T ⊆ C → T ≠ C → T.Nonempty → total T ∉ space S) ∧
        C.card ≤ (m - Module.finrank F (space S)) + 1 := by
  intro n m G F A h parts total space score S hmax hmin C hC
  have hP : ∀ T, parts T = PEqualNP.Outside.L_lib_849.parts G T := fun T => rfl
  have hC' : C ∈ PEqualNP.Outside.L_lib_849.parts G S := hC
  have hCS : C ⊆ S := part_sub G S C hC'
  have hCne : C.Nonempty := part_ne G S C hC'
  have htot : ∀ T : Finset (Fin n), ∑ P ∈ parts T, total P = total T := fun T => sum_parts G h T
  set W : Submodule F A := Submodule.span F (total '' (↑((parts S).erase C) : Set (Finset (Fin n)))) with hW
  have hWle : W ≤ space S := by
    apply Submodule.span_mono
    intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx ⊢
    obtain ⟨P, hP1, rfl⟩ := hx
    exact ⟨P, Finset.mem_of_mem_erase hP1, rfl⟩
  have hCsp : total C ∈ space S :=
    Submodule.subset_span (by simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨C, hC, rfl⟩)
  -- part one: no coloop
  have h1 : total C ∈ W := by
    by_contra hn
    have hmem : ∀ v, v ∈ S \ C ↔ (v ∈ S ∧ v ∉ C) ∨ v ∈ (∅ : Finset (Fin n)) := by
      intro v; simp [Finset.mem_sdiff]
    have hpp : parts (S \ C) = (parts S).erase C := by
      ext X
      rw [hP, hP, parts_replace G S C ∅ (S \ C) hC' (Finset.empty_subset _) hmem X, parts_empty,
        Finset.mem_erase]
      simp only [Finset.notMem_empty, or_false]
      exact and_comm
    have hlt : Module.finrank F W < Module.finrank F (space S) := by
      apply Submodule.finrank_lt_finrank_of_lt
      exact lt_of_le_of_ne hWle (fun he => hn (he ▸ hCsp))
    have e1 := hmax (S \ C)
    have e2 := hmin (S \ C)
    have hcard : ((parts S).erase C).card = (parts S).card - 1 := Finset.card_erase_of_mem hC
    have hpos : 1 ≤ (parts S).card := Finset.card_pos.2 ⟨C, hC⟩
    have hsl : (S \ C).card < S.card := Finset.card_lt_card (Finset.sdiff_ssubset hCS hCne)
    have hsW : space (S \ C) = W := by
      simp only [space]
      rw [hpp]
      simp only [Finset.coe_image]
      rfl
    have k1 : score (S \ C) = ((parts S).erase C).card - Module.finrank F W := by
      simp only [score]
      rw [hsW, hpp]
    have k2 : score S = (parts S).card - Module.finrank F (space S) := rfl
    rw [k1, k2] at e1 e2
    rw [hcard] at e1 e2
    have := e2 (by omega)
    omega
  -- part two: no proper part sums into the space
  have h2 : ∀ T : Finset (Fin n), T ⊆ C → T ≠ C → T.Nonempty → total T ∉ space S := by
    intro T hTC hTne hTn hTs
    have hSW : space S ≤ W := by
      apply Submodule.span_le.2
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨P, hP1, rfl⟩ := hx
      by_cases hPC : P = C
      · rw [hPC]; exact h1
      · exact Submodule.subset_span (by
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
          exact ⟨P, Finset.mem_erase.2 ⟨hPC, hP1⟩, rfl⟩)
    have hTW : total T ∈ W := hSW hTs
    set S' := (S \ C) ∪ T with hS'
    have hmem : ∀ v, v ∈ S' ↔ (v ∈ S ∧ v ∉ C) ∨ v ∈ T := by
      intro v; simp [hS', Finset.mem_sdiff]
    have hpp : parts S' = (parts S).erase C ∪ parts T := by
      ext X
      rw [hP, hP, hP, parts_replace G S C T S' hC' hTC hmem X, Finset.mem_union, Finset.mem_erase]
      rw [and_comm]
    have hdisj : Disjoint ((parts S).erase C) (parts T) := by
      rw [Finset.disjoint_left]
      intro X hX1 hX2
      obtain ⟨a, ha⟩ := part_ne G T X hX2
      have haC : a ∈ C := hTC (part_sub G T X hX2 ha)
      exact (Finset.mem_erase.1 hX1).1 (part_eq G S X C (Finset.mem_of_mem_erase hX1) hC' a ha haC)
    obtain ⟨t0, ht0⟩ := hTn
    obtain ⟨q0, hq0, -⟩ := part_of G T t0 ht0
    have hq0' : q0 ∈ parts T := hq0
    set U : Submodule F A := Submodule.span F (total '' (↑((parts T).erase q0) : Set (Finset (Fin n)))) with hU
    have hle : space S' ≤ W ⊔ U := by
      apply Submodule.span_le.2
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, hpp, Finset.mem_union] at hx
      obtain ⟨P, hP1, rfl⟩ := hx
      rcases hP1 with hP1 | hP1
      · exact Submodule.mem_sup_left (Submodule.subset_span (by
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨P, hP1, rfl⟩))
      · by_cases hPq : P = q0
        · have hs := Finset.add_sum_erase (parts T) total hq0'
          rw [htot T] at hs
          have : total P = total T - ∑ x ∈ (parts T).erase q0, total x := by
            rw [hPq, ← hs]; abel
          rw [this]
          refine Submodule.sub_mem _ (Submodule.mem_sup_left hTW) (Submodule.mem_sup_right ?_)
          refine Submodule.sum_mem _ (fun Q hQ => Submodule.subset_span ?_)
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
          exact ⟨Q, hQ, rfl⟩
        · exact Submodule.mem_sup_right (Submodule.subset_span (by
            simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
            exact ⟨P, Finset.mem_erase.2 ⟨hPq, hP1⟩, rfl⟩))
    have hrk1 : Module.finrank F (space S') ≤ Module.finrank F W + Module.finrank F U :=
      (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank W U)
    have hrk2 : Module.finrank F W ≤ Module.finrank F (space S) := Submodule.finrank_mono hWle
    have hrk3 : Module.finrank F U ≤ (parts T).card - 1 := by
      have := finrank_span_finset_le_card (R := F) (((parts T).erase q0).image total)
      have h4 := Finset.card_image_le (s := (parts T).erase q0) (f := total)
      have h5 := Finset.card_erase_of_mem hq0'
      unfold Set.finrank at this
      rw [hU, ← Finset.coe_image]
      omega
    have hcard : (parts S').card = ((parts S).card - 1) + (parts T).card := by
      rw [hpp, Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hC]
    have hpos : 1 ≤ (parts S).card := Finset.card_pos.2 ⟨C, hC⟩
    have htpos : 1 ≤ (parts T).card := Finset.card_pos.2 ⟨q0, hq0'⟩
    have hsub : S' ⊆ S := by
      intro v hv
      rcases (hmem v).1 hv with hv | hv
      · exact hv.1
      · exact hCS (hTC hv)
    have hsl : S'.card < S.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      obtain ⟨x, hxC, hxT⟩ := (Finset.ssubset_iff_of_subset hTC).1 (Finset.ssubset_iff_subset_ne.2 ⟨hTC, hTne⟩)
      refine ⟨x, hCS hxC, fun hx => ?_⟩
      rcases (hmem x).1 hx with hx | hx
      · exact hx.2 hxC
      · exact hxT hx
    have e1 := hmax S'
    have e2 := hmin S'
    simp only [score] at e1 e2
    rw [hcard] at e1 e2
    have := e2 (by omega)
    omega
  refine ⟨?_, h2, ?_⟩
  · simp only [Finset.coe_image]
    convert h1
  -- part three: the size bound
  obtain ⟨v0, hv0⟩ := hCne
  set D := space S with hD
  let b : ↥(C.erase v0) → A ⧸ D := fun x => D.mkQ (h x.1)
  have z2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hli : LinearIndependent F b := by
    rw [linearIndependent_iff']
    intro s g hsum i hi
    by_contra hgi
    classical
    let s1 := s.filter (fun j => g j ≠ 0)
    have hs1 : ∑ j ∈ s, g j • b j = ∑ j ∈ s1, b j := by
      rw [← Finset.sum_filter_of_ne (p := fun j => g j ≠ 0)]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [z2 (g j) (Finset.mem_filter.1 hj).2, one_smul]
      · intro j _ hj hg
        apply hj
        rw [hg, zero_smul]
    let T : Finset (Fin n) := s1.map (Function.Embedding.subtype _)
    have hT : total T ∈ D := by
      rw [← Submodule.Quotient.mk_eq_zero]
      have : (Submodule.Quotient.mk (total T) : A ⧸ D) = ∑ j ∈ s1, b j := by
        rw [show ∑ j ∈ s1, b j = D.mkQ (∑ j ∈ s1, h j.1) from (map_sum D.mkQ _ _).symm]
        simp only [T, total, Finset.sum_map, Function.Embedding.subtype_apply, Submodule.mkQ_apply]
      rw [this, ← hs1, hsum]
    apply h2 T _ _ _ hT
    · intro x hx
      simp only [T, Finset.mem_map, Function.Embedding.subtype_apply] at hx
      obtain ⟨j, -, rfl⟩ := hx
      exact Finset.mem_of_mem_erase j.2
    · intro hTC
      have : v0 ∈ T := hTC ▸ hv0
      simp only [T, Finset.mem_map, Function.Embedding.subtype_apply] at this
      obtain ⟨j, -, hj⟩ := this
      exact (Finset.mem_erase.1 (hj ▸ j.2)).1 rfl
    · exact ⟨i.1, Finset.mem_map.2 ⟨i, Finset.mem_filter.2 ⟨hi, hgi⟩, rfl⟩⟩
  have hc := hli.fintype_card_le_finrank
  have hq := Submodule.finrank_quotient_add_finrank D
  have hm : Module.finrank F A = m := Module.finrank_fin_fun F
  have hce : Fintype.card ↥(C.erase v0) = C.card - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem hv0]
  have hpos : 1 ≤ C.card := Finset.card_pos.2 ⟨v0, hv0⟩
  omega
