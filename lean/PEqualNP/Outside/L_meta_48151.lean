import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48151_aux

open SimpleGraph

noncomputable def rootPath {V : Type*} {T : SimpleGraph V} (h : T.IsTree) (r a : V) : T.Walk r a :=
  (h.existsUnique_path r a).choose

lemma rootPath_isPath {V : Type*} {T : SimpleGraph V} (h : T.IsTree) (r a : V) :
    (rootPath h r a).IsPath := (h.existsUnique_path r a).choose_spec.1
abbrev Below {V : Type*} {T : SimpleGraph V} (h : T.IsTree) (r a b : V) : Prop :=
  a ∈ (rootPath h r b).support

noncomputable def Depth {V : Type*} {T : SimpleGraph V} (h : T.IsTree) (r a : V) : Nat :=
  (rootPath h r a).length

section RootOrder
variable {V : Type*} [DecidableEq V] {T : SimpleGraph V} (h : T.IsTree) (r : V)

lemma rootPath_unique {a : V} (p : T.Walk r a) (hp : p.IsPath) : p = rootPath h r a :=
  (h.existsUnique_path r a).unique hp (rootPath_isPath h r a)

lemma below_prefix {a b : V} (hab : Below h r a b) :
    (rootPath h r a).support <+: (rootPath h r b).support := by
  have he := rootPath_unique h r ((rootPath h r b).takeUntil a hab)
    ((rootPath_isPath h r b).takeUntil hab)
  rw [← he]
  exact (rootPath h r b).support_takeUntil_prefix_support hab

lemma below_refl (a : V) : Below h r a a := (rootPath h r a).end_mem_support

lemma below_root (a : V) : Below h r r a := (rootPath h r a).start_mem_support

lemma below_trans {a b c : V} (hab : Below h r a b) (hbc : Below h r b c) : Below h r a c :=
  (below_prefix h r hbc).subset hab

lemma below_depth {a b : V} (hab : Below h r a b) : Depth h r a ≤ Depth h r b := by
  have H := (below_prefix h r hab).length_le
  simpa [Depth, Walk.length_support] using H

lemma below_eq_of_depth {a b : V} (hab : Below h r a b) (hd : Depth h r b ≤ Depth h r a) : a = b := by
  have hp := below_prefix h r hab
  have hl : (rootPath h r b).support.length ≤ (rootPath h r a).support.length := by
    simpa [Depth, Walk.length_support] using hd
  have he := hp.eq_of_length_le hl
  have e := congrArg List.getLast? he
  rw [List.getLast?_eq_some_getLast (by simp), List.getLast?_eq_some_getLast (by simp),
    Walk.getLast_support, Walk.getLast_support] at e
  exact Option.some.inj e

lemma below_compare {a b c : V} (ha : Below h r a c) (hb : Below h r b c) :
    Below h r a b ∨ Below h r b a := by
  have hp := below_prefix h r ha
  have hq := below_prefix h r hb
  rcases le_total (rootPath h r a).support.length (rootPath h r b).support.length with hd | hd
  · have H := (List.prefix_take_iff).2 ⟨hp, hd⟩
    rw [← List.prefix_iff_eq_take.mp hq] at H
    exact Or.inl (H.subset (below_refl h r a))
  · have H := (List.prefix_take_iff).2 ⟨hq, hd⟩
    rw [← List.prefix_iff_eq_take.mp hp] at H
    exact Or.inr (H.subset (below_refl h r b))

lemma below_of_adj {a b : V} (hab : T.Adj a b) : Below h r a b ∨ Below h r b a := by
  by_cases ha : Below h r a b
  · exact Or.inl ha
  · exact Or.inr (h.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      (rootPath_isPath h r a) (rootPath_isPath h r b) hab ha)

lemma walk_descends {F : Finset V} {a b c : V} (p : T.Walk b c)
    (hp : ∀ d ∈ p.support, d ∈ F)
    (hm : ∀ d ∈ F, Depth h r a ≤ Depth h r d)
    (hb : Below h r a b) : Below h r a c := by
  induction p with
  | nil => exact hb
  | @cons u v w huv q ih =>
    apply ih (fun d hd => hp d (by simp [hd]))
    rcases below_of_adj h r huv with hd | hd
    · exact below_trans h r hb hd
    · rcases below_compare h r hb hd with H | H
      · exact H
      · have e := below_eq_of_depth h r H (hm v (hp v (by simp)))
        simpa [e] using below_refl h r a

end RootOrder

def TreeConvex {V : Type*} {T : SimpleGraph V} (h : T.IsTree) (F : Finset V) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ (rootPath h a b).support, c ∈ F

section Convexity
variable {V : Type*} [DecidableEq V] {T : SimpleGraph V} (h : T.IsTree)

lemma convex_from_walks {F : Finset V}
    (hw : ∀ a ∈ F, ∀ b ∈ F, ∃ p : T.Walk a b, ∀ c ∈ p.support, c ∈ F) :
    TreeConvex h F := by
  intro a ha b hb c hc
  obtain ⟨p, hp⟩ := hw a ha b hb
  rw [← rootPath_unique h a p.toPath.val p.toPath.isPath] at hc
  exact hp c (p.support_toPath_subset_support hc)

lemma convex_connected {F : Finset V} (hc : (T.induce (↑F : Set V)).Connected) :
    TreeConvex h F := by
  apply convex_from_walks h
  intro a ha b hb
  obtain ⟨p⟩ := hc ⟨a, ha⟩ ⟨b, hb⟩
  refine ⟨p.map (SimpleGraph.Embedding.induce (↑F : Set V)).toHom, ?_⟩
  intro d hd
  have hd' : d ∈ p.support.map (SimpleGraph.Embedding.induce (↑F : Set V)).toHom :=
    Walk.support_map (SimpleGraph.Embedding.induce (↑F : Set V)).toHom p ▸ hd
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hd'
  exact u.property

lemma convex_union {F G : Finset V} (hF : TreeConvex h F) (hG : TreeConvex h G)
    (hi : (F ∩ G).Nonempty) : TreeConvex h (F ∪ G) := by
  obtain ⟨z, hz⟩ := hi
  have ⟨hzF, hzG⟩ := Finset.mem_inter.mp hz
  apply convex_from_walks h
  intro a ha b hb
  obtain ha | ha := Finset.mem_union.mp ha <;> obtain hb | hb := Finset.mem_union.mp hb
  · exact ⟨rootPath h a b, fun c hc => Finset.mem_union_left _ (hF a ha b hb c hc)⟩
  · refine ⟨(rootPath h a z).append (rootPath h z b), fun c hc => ?_⟩
    rcases (Walk.mem_support_append_iff ..).mp hc with hc | hc
    · exact Finset.mem_union_left _ (hF a ha z hzF c hc)
    · exact Finset.mem_union_right _ (hG z hzG b hb c hc)
  · refine ⟨(rootPath h a z).append (rootPath h z b), fun c hc => ?_⟩
    rcases (Walk.mem_support_append_iff ..).mp hc with hc | hc
    · exact Finset.mem_union_right _ (hG a ha z hzG c hc)
    · exact Finset.mem_union_left _ (hF z hzF b hb c hc)
  · exact ⟨rootPath h a b, fun c hc => Finset.mem_union_right _ (hG a ha b hb c hc)⟩

lemma convex_top (r : V) {F : Finset V} (hF : TreeConvex h F) (hn : F.Nonempty) :
    ∃ a ∈ F, ∀ b ∈ F, Below h r a b := by
  obtain ⟨a, ha, hm⟩ := Finset.exists_min_image F (Depth h r) hn
  exact ⟨a, ha, fun b hb =>
    walk_descends h r (rootPath h a b) (hF a ha b hb) hm (below_refl h r a)⟩

lemma convex_interval (r : V) {F : Finset V} (hF : TreeConvex h F)
    {a b c : V} (ha : a ∈ F) (hc : c ∈ F)
    (hab : Below h r a b) (hbc : Below h r b c) : b ∈ F := by
  classical
  have hac := below_trans h r hab hbc
  let p := rootPath h r c
  have he := rootPath_unique h a (p.dropUntil a hac) ((rootPath_isPath h r c).dropUntil hac)
  have hb : b ∈ (p.takeUntil a hac).support ∨ b ∈ (p.dropUntil a hac).support := by
    apply (Walk.mem_support_append_iff ..).mp
    rw [Walk.take_spec]
    exact hbc
  rcases hb with hb | hb
  · rw [rootPath_unique h r _ ((rootPath_isPath h r c).takeUntil hac)] at hb
    have e := below_eq_of_depth h r hab (below_depth h r hb)
    simpa [← e] using ha
  · exact hF a ha c hc b (he ▸ hb)

end Convexity

section Boundary
variable {V : Type*} [Fintype V] [DecidableEq V] {T : SimpleGraph V} (h : T.IsTree) (r : V)

def BoundaryRoot (v : V) (F : Finset V) (b : V) : Prop :=
  Below h r v b ∧ b ∉ F ∧
    ∀ a, Below h r v a → Below h r a b → a ∉ F → a = b

lemma boundary_exists {v w : V} {F : Finset V} (hw : Below h r v w) (hwF : w ∉ F) :
    ∃ b, BoundaryRoot h r v F b ∧ Below h r b w := by
  classical
  let A := Finset.univ.filter fun a => Below h r v a ∧ Below h r a w ∧ a ∉ F
  have hm : ∀ a, a ∈ A ↔ Below h r v a ∧ Below h r a w ∧ a ∉ F := by
    intro a
    simp [A]
  have hAw : A.Nonempty := ⟨w, (hm w).2 ⟨hw, below_refl h r w, hwF⟩⟩
  obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image A (Depth h r) hAw
  obtain ⟨hvb, hbw, hF⟩ := (hm b).1 hb
  refine ⟨b, ⟨hvb, hF, fun a hva hab haF => ?_⟩, hbw⟩
  exact below_eq_of_depth h r hab (hmin a ((hm a).2 ⟨hva, below_trans h r hab hbw, haF⟩))

lemma boundary_unique {v b c w : V} {F : Finset V}
    (hb : BoundaryRoot h r v F b) (hc : BoundaryRoot h r v F c)
    (hbw : Below h r b w) (hcw : Below h r c w) : b = c := by
  rcases below_compare h r hbw hcw with H | H
  · exact hc.2.2 b hb.1 H hb.2.1
  · exact (hb.2.2 c hc.1 H hc.2.1).symm

lemma boundary_avoids {v b w : V} {F : Finset V} (hv : v ∈ F) (hF : TreeConvex h F)
    (hb : BoundaryRoot h r v F b) (hbw : Below h r b w) : w ∉ F :=
  fun hw => hb.2.1 (convex_interval h r hF hv hw hb.1 hbw)

lemma boundary_depth {v b : V} {F : Finset V} (hv : v ∈ F) (hb : BoundaryRoot h r v F b) :
    Depth h r v < Depth h r b := by
  by_contra! hh
  exact hb.2.1 ((below_eq_of_depth h r hb.1 hh) ▸ hv)

lemma singleton_convex (v : V) : TreeConvex h ({v} : Finset V) := by
  intro a ha b hb c hc
  have ha' := Finset.mem_singleton.mp ha
  have hb' := Finset.mem_singleton.mp hb
  subst a
  subst b
  rw [← rootPath_unique h v .nil Walk.IsPath.nil] at hc
  simpa using hc

end Boundary

open SimpleGraph

section FinitePacking
variable {I V : Type*} [DecidableEq I] [DecidableEq V]

abbrev GoodPack (F : I → Finset V) (P : Finset I) : Prop :=
  (P : Set I).PairwiseDisjoint F

noncomputable def Opt (F : I → Finset V) (A : Finset I) : Nat :=
  letI := Classical.propDecidable
  (A.powerset.filter (GoodPack F)).sup Finset.card

lemma sub_goodPack {F : I → Finset V} {P Q : Finset I} (hs : P ⊆ Q) (h : GoodPack F Q) :
    GoodPack F P := fun _ ha _ hb hn => h (hs ha) (hs hb) hn

lemma card_le_opt {F : I → Finset V} {A P : Finset I} (hP : P ⊆ A) (hg : GoodPack F P) :
    P.card ≤ Opt F A := by
  classical
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hP, hg⟩)

lemma opt_attains (F : I → Finset V) (A : Finset I) :
    ∃ P ⊆ A, GoodPack F P ∧ P.card = Opt F A := by
  classical
  let B := A.powerset.filter (GoodPack F)
  have hB : B.Nonempty := ⟨∅, by simp [B, GoodPack]⟩
  obtain ⟨P, hP, he⟩ := Finset.exists_mem_eq_sup B hB Finset.card
  have hh : P ∈ A.powerset ∧ GoodPack F P := Finset.mem_filter.mp hP
  exact ⟨P, Finset.mem_powerset.mp hh.1, hh.2, he.symm⟩

lemma opt_le {F : I → Finset V} {A : Finset I} {k : Nat}
    (h : ∀ P ⊆ A, GoodPack F P → P.card ≤ k) : Opt F A ≤ k := by
  obtain ⟨P, hs, hg, he⟩ := opt_attains F A
  rw [← he]
  exact h P hs hg

lemma opt_mono {F : I → Finset V} {A B : Finset I} (h : A ⊆ B) : Opt F A ≤ Opt F B :=
  opt_le fun _ hs hg => card_le_opt (hs.trans h) hg

lemma good_insert {F : I → Finset V} {P : Finset I} {a : I} (h : GoodPack F P)
    (hd : ∀ b ∈ P, Disjoint (F a) (F b)) : GoodPack F (insert a P) := by
  intro i hi j hj hij
  change i ∈ insert a P at hi
  change j ∈ insert a P at hj
  rcases Finset.mem_insert.mp hi with hi | hi
  · subst i
    rcases Finset.mem_insert.mp hj with hj | hj
    · exact (hij hj.symm).elim
    · exact hd _ hj
  · rcases Finset.mem_insert.mp hj with hj | hj
    · subst j
      exact (hd _ hi).symm
    · exact h hi hj hij

lemma opt_partition {J : Type*} [DecidableEq J] (F : I → Finset V) (B : Finset J)
    (A : J → Finset I)
    (hsep : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → ∀ i ∈ A a, ∀ j ∈ A b,
      i ≠ j ∧ Disjoint (F i) (F j)) :
    Opt F (B.biUnion A) = ∑ j ∈ B, Opt F (A j) := by
  classical
  apply le_antisymm
  · apply opt_le
    intro P hs hp
    let Q := fun j => P ∩ A j
    have hdecomp : B.biUnion Q = P := by
      ext i
      constructor
      · intro hi
        obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
        exact (Finset.mem_inter.mp hij).1
      · intro hi
        obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp (hs hi)
        exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_inter.mpr ⟨hi, hij⟩⟩
    have hdis : (B : Set J).PairwiseDisjoint Q := by
      intro a ha b hb hab
      exact Finset.disjoint_left.mpr fun i hi hj =>
        (hsep a ha b hb hab i (Finset.mem_inter.mp hi).2 i (Finset.mem_inter.mp hj).2).1 rfl
    rw [← hdecomp, Finset.card_biUnion hdis]
    exact Finset.sum_le_sum fun j _ => card_le_opt
      (fun _ hi => (Finset.mem_inter.mp hi).2)
      (sub_goodPack (fun _ hi => (Finset.mem_inter.mp hi).1) hp)
  · choose Q hs hg hcard using fun j => opt_attains F (A j)
    have hsub : B.biUnion Q ⊆ B.biUnion A := by
      intro i hi
      obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_biUnion.mpr ⟨j, hj, hs j hij⟩
    have hgood : GoodPack F (B.biUnion Q) := by
      intro i hi j hj hne
      obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨b, hb, hjb⟩ := Finset.mem_biUnion.mp hj
      by_cases hab : a = b
      · subst b
        exact hg a hia hjb hne
      · exact (hsep a ha b hb hab i (hs a hia) j (hs b hjb)).2
    have hdis : (B : Set J).PairwiseDisjoint Q := by
      intro a ha b hb hab
      exact Finset.disjoint_left.mpr fun i hi hj => (hsep a ha b hb hab i (hs a hi) i (hs b hj)).1 rfl
    have hle := card_le_opt hsub hgood
    rw [Finset.card_biUnion hdis] at hle
    simpa only [hcard] using hle

end FinitePacking

section Transversal
variable {I V : Type*} [DecidableEq I] [DecidableEq V] {T : SimpleGraph V}
variable (h : T.IsTree) (r : V) (F : I → Finset V) (d : I → V)

lemma above_top_hits {a b : I} (hd : ∀ i, d i ∈ F i ∧ ∀ w ∈ F i, Below h r (d i) w)
    (hc : TreeConvex h (F b)) (hdepth : Depth h r (d b) ≤ Depth h r (d a))
    (hi : ¬ Disjoint (F a) (F b)) : d a ∈ F b := by
  classical
  obtain ⟨w, ha, hb⟩ := Finset.not_disjoint_iff.mp hi
  have hwa := (hd a).2 w ha
  have hwb := (hd b).2 w hb
  have hba : Below h r (d b) (d a) := by
    rcases below_compare h r hwb hwa with H | H
    · exact H
    · rw [below_eq_of_depth h r H hdepth]
      exact below_refl h r _
  exact convex_interval h r hc (hd b).1 hb hba hwa

lemma packing_transversal (hd : ∀ i, d i ∈ F i ∧ ∀ w ∈ F i, Below h r (d i) w)
    (hc : ∀ i, TreeConvex h (F i)) (A : Finset I) :
    ∃ H : Finset V, H.card ≤ Opt F A ∧ ∀ i ∈ A, ∃ w ∈ H, w ∈ F i := by
  classical
  obtain ⟨P, H, hP, hg, hHP, hhit⟩ : ∃ (P : Finset I) (H : Finset V),
      P ⊆ A ∧ GoodPack F P ∧ H.card ≤ P.card ∧ ∀ i ∈ A, ∃ w ∈ H, w ∈ F i := by
    refine Finset.strongInductionOn A ?_
    · intro A ih
      by_cases hn : A.Nonempty
      · obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image A (fun i => Depth h r (d i)) hn
        let B := A.filter fun i => d a ∉ F i
        have hs : B ⊆ A := Finset.filter_subset _ _
        have hnB : a ∉ B := fun H => (Finset.mem_filter.mp H).2 (hd a).1
        have hlt : B ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨hs, fun e => hnB (e ▸ ha)⟩
        obtain ⟨P, H, hP, hg, hHP, hhit⟩ := ih B hlt
        have hnP : a ∉ P := fun H => hnB (hP H)
        refine ⟨insert a P, insert (d a) H, Finset.insert_subset ha (hP.trans hs),
          good_insert hg ?_, ?_, ?_⟩
        · intro b hb
          by_contra hdis
          exact (Finset.mem_filter.mp (hP hb)).2
            (above_top_hits h r F d hd (hc b) (hmax b (hs (hP hb))) hdis)
        · rw [Finset.card_insert_of_notMem hnP]
          exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hHP)
        · intro b hb
          by_cases hh : d a ∈ F b
          · exact ⟨d a, Finset.mem_insert_self _ _, hh⟩
          · obtain ⟨w, hw, hf⟩ := hhit b (Finset.mem_filter.mpr ⟨hb, hh⟩)
            exact ⟨w, Finset.mem_insert_of_mem hw, hf⟩
      · have e : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
        subst A
        exact ⟨∅, ∅, by simp, by simp [GoodPack], by simp, by simp⟩
  exact ⟨H, hHP.trans (card_le_opt hP hg), hhit⟩

end Transversal

open SimpleGraph

section TreeRecurrence
variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
variable {T : SimpleGraph V} (h : T.IsTree) (r : V) (F : I → Finset V) (d : I → V)

noncomputable def branches (v : V) (C : Finset V) : Finset V :=
  letI := Classical.propDecidable
  Finset.univ.filter (BoundaryRoot h r v C)

noncomputable def active (A : Finset I) (v : V) : Finset I :=
  letI := Classical.propDecidable
  A.filter (fun i => Below h r v (d i))

noncomputable def avoiding (A : Finset I) (v : V) (C : Finset V) : Finset I :=
  (active h r d A v).filter fun i => Disjoint C (F i)

lemma mem_branches {v b : V} {C : Finset V} :
    b ∈ branches h r v C ↔ BoundaryRoot h r v C b := by
  classical
  simp [branches]

lemma mem_active {A : Finset I} {v : V} {i : I} :
    i ∈ active h r d A v ↔ i ∈ A ∧ Below h r v (d i) := by
  classical
  simp [active]

lemma mem_avoiding {A : Finset I} {v : V} {C : Finset V} {i : I} :
    i ∈ avoiding h r F d A v C ↔ i ∈ A ∧ Below h r v (d i) ∧ Disjoint C (F i) := by
  classical
  simp [avoiding, mem_active, and_assoc]

lemma branch_partition {A : Finset I} {v : V} {C : Finset V} (hv : v ∈ C) (hC : TreeConvex h C)
    (hd : ∀ i, d i ∈ F i ∧ ∀ w ∈ F i, Below h r (d i) w) :
    (branches h r v C).biUnion (active h r d A) = avoiding h r F d A v C := by
  ext i
  simp only [Finset.mem_biUnion, mem_active, mem_avoiding, mem_branches]
  constructor
  · rintro ⟨b, hb, hi, hbi⟩
    refine ⟨hi, below_trans h r hb.1 hbi, Finset.disjoint_left.mpr ?_⟩
    intro w hwC hwF
    exact boundary_avoids h r hv hC hb (below_trans h r hbi ((hd i).2 _ hwF)) hwC
  · rintro ⟨hi, hvd, hdis⟩
    have hn : d i ∉ C := fun H => Finset.disjoint_left.mp hdis H (hd i).1
    obtain ⟨b, hb, hbi⟩ := boundary_exists h r hvd hn
    exact ⟨b, hb, hi, hbi⟩

lemma branches_separate {A : Finset I} {v : V} {C : Finset V}
    (hd : ∀ i, d i ∈ F i ∧ ∀ w ∈ F i, Below h r (d i) w) :
    ∀ a ∈ branches h r v C, ∀ b ∈ branches h r v C, a ≠ b →
      ∀ i ∈ active h r d A a, ∀ j ∈ active h r d A b, i ≠ j ∧ Disjoint (F i) (F j) := by
  intro a ha b hb hab i hi j hj
  have hda := (mem_active h r d).mp hi |>.2
  have hdb := (mem_active h r d).mp hj |>.2
  have h₁ := (mem_branches h r).mp ha
  have h₂ := (mem_branches h r).mp hb
  refine ⟨fun e => hab (boundary_unique h r h₁ h₂ hda (e.symm ▸ hdb)), ?_⟩
  refine Finset.disjoint_left.mpr fun w hw hw' => hab ?_
  exact boundary_unique h r h₁ h₂ (below_trans h r hda ((hd i).2 _ hw))
    (below_trans h r hdb ((hd j).2 _ hw'))

lemma branch_sum {A : Finset I} {v : V} {C : Finset V} (hv : v ∈ C) (hC : TreeConvex h C)
    (hd : ∀ i, d i ∈ F i ∧ ∀ w ∈ F i, Below h r (d i) w) :
    Opt F (avoiding h r F d A v C) = ∑ b ∈ branches h r v C, Opt F (active h r d A b) := by
  rw [← branch_partition h r F d hv hC hd]
  exact opt_partition F _ _ (branches_separate h r F d hd)

noncomputable def rowChoices (v : V) : Finset I :=
  Finset.univ.filter fun i => d i = v

noncomputable def optionValue (A : Finset I) (v : V) (a : Option I) : Nat :=
  match a with
  | none => ∑ b ∈ branches h r v {v}, Opt F (active h r d A b)
  | some i => if i ∈ A then 1 + ∑ b ∈ branches h r v (F i), Opt F (active h r d A b) else 0

noncomputable def optionRows (v : V) : Finset (Option I) :=
  insert none ((rowChoices d v).image some)

lemma mem_optionRows_some {v : V} {i : I} : some i ∈ optionRows d v ↔ d i = v := by
  simp [optionRows, rowChoices]

lemma mem_optionRows_none (v : V) : none ∈ optionRows d v := Finset.mem_insert_self _ _

lemma opt_tree_step (A : Finset I) (v : V)
    (hd : ∀ i, d i ∈ F i ∧ ∀ w ∈ F i, Below h r (d i) w)
    (hc : ∀ i, TreeConvex h (F i)) :
    Opt F (active h r d A v) = (optionRows d v).sup (optionValue h r F d A v) := by
  classical
  apply le_antisymm
  · apply opt_le
    intro P hp hg
    by_cases hchoose : ∃ i ∈ P, d i = v
    · obtain ⟨i, hi, hdi⟩ := hchoose
      have hiA := (mem_active h r d).mp (hp hi) |>.1
      have hsub : P.erase i ⊆ avoiding h r F d A v (F i) := by
        intro j hj
        obtain ⟨hne, hjP⟩ := Finset.mem_erase.mp hj
        obtain ⟨hjA, hjd⟩ := (mem_active h r d).mp (hp hjP)
        exact (mem_avoiding h r F d).mpr ⟨hjA, hjd, hg hi hjP hne.symm⟩
      have hl := card_le_opt hsub (sub_goodPack (Finset.erase_subset _ _) hg)
      rw [branch_sum h r F d (hdi ▸ (hd i).1) (hc i) hd, Finset.card_erase_of_mem hi] at hl
      apply Finset.le_sup_of_le ((mem_optionRows_some d).mpr hdi)
      simp only [optionValue, hiA, if_true]
      have hp0 := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    · have hsub : P ⊆ avoiding h r F d A v {v} := by
        intro i hi
        obtain ⟨hiA, hvd⟩ := (mem_active h r d).mp (hp hi)
        refine (mem_avoiding h r F d).mpr ⟨hiA, hvd, Finset.disjoint_left.mpr ?_⟩
        intro w hw hwF
        have ew := Finset.mem_singleton.mp hw
        have e := below_eq_of_depth h r hvd (below_depth h r (ew ▸ (hd i).2 w hwF))
        exact hchoose ⟨i, hi, e.symm⟩
      have hl := card_le_opt hsub hg
      rw [branch_sum h r F d (Finset.mem_singleton_self v) (singleton_convex h v) hd] at hl
      exact Finset.le_sup_of_le (mem_optionRows_none d v) hl
  · apply Finset.sup_le
    intro a ha
    cases a with
    | none =>
      change (∑ b ∈ branches h r v {v}, Opt F (active h r d A b)) ≤ _
      rw [← branch_sum h r F d (Finset.mem_singleton_self v) (singleton_convex h v) hd]
      exact opt_mono fun _ hi => (Finset.mem_filter.mp hi).1
    | some i =>
      have hdi := (mem_optionRows_some d).mp ha
      by_cases hi : i ∈ A
      · simp only [optionValue, hi, if_true]
        rw [← branch_sum h r F d (hdi ▸ (hd i).1) (hc i) hd]
        obtain ⟨P, hp, hg, he⟩ := opt_attains F (avoiding h r F d A v (F i))
        have hnot : i ∉ P := by
          intro hh
          have H := (mem_avoiding h r F d).mp (hp hh) |>.2.2
          exact Finset.disjoint_left.mp H (hd i).1 (hd i).1
        have hia : i ∈ active h r d A v := (mem_active h r d).mpr ⟨hi, by rw [hdi]; exact below_refl h r v⟩
        have hl := card_le_opt (F := F) (Finset.insert_subset hia
          (fun j hj => (Finset.mem_filter.mp (hp hj)).1))
          (good_insert hg (fun j hj => (mem_avoiding h r F d).mp (hp hj) |>.2.2))
        simpa [Finset.card_insert_of_notMem hnot, he, Nat.add_comm] using hl
      · simp [optionValue, hi]

end TreeRecurrence

noncomputable def fitAlpha {V : Type*} (edge : V → V → Bool) (y : Finset V) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  (y.powerset.filter (fun z => ∀ a ∈ z, ∀ b ∈ z, edge a b = false)).sup Finset.card

private theorem fit_indep_filter_mem {V : Type*} {edge : V → V → Bool} {y z : Finset V} :
    z ∈ @Finset.filter (Finset V) (fun w => ∀ a ∈ w, ∀ b ∈ w, edge a b = false)
      (fun _ => Classical.propDecidable _) y.powerset ↔
    z ⊆ y ∧ (∀ a ∈ z, ∀ b ∈ z, edge a b = false) :=
  (@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) y.powerset z).trans
    (and_congr Finset.mem_powerset Iff.rfl)

def fitPack {V : Type*} (x : Finset V) (f : Finset V → V → Bool) : ℕ → Finset V → Prop :=
  Nat.rec (motive := fun _ => Finset V → Prop) (fun _ => True)
    (fun _ prev y => ∃ (u v : Finset V) (j : V), j ∈ x ∧ prev u ∧ u ⊆ v ∧ v ⊆ y ∧
      f u j = true ∧ f v j = false)

def fitAdmits {V : Type*} (edge : V → V → Bool) (x : Finset V) (e : ℕ) : Prop :=
  ∃ f : Finset V → V → Bool,
    (∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, edge i j = false) → f y j = true) ∧
    (∀ y, y ⊆ x → ∀ j ∈ y, f y j = false) ∧
    (∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true) ∧
    ∀ y l, y ⊆ x → fitPack x f l y → l ≤ fitAlpha edge y + e

def FitP3 {V : Type*} (edge : V → V → Bool) (p : Fin 3 → V) : Prop :=
  edge (p 0) (p 1) = true ∧ edge (p 1) (p 2) = true ∧
    edge (p 2) (p 0) = false ∧ p 2 ≠ p 0

def FitP3Free {V : Type*} (edge : V → V → Bool) (r : Finset V) : Prop :=
  ∀ p : Fin 3 → V, (∀ t, p t ∈ r) → ¬ FitP3 edge p

-- The next three lemmas adapt `lo_alpha`, `lo_step`, and `lo_chain` from
-- lean/PEqualNP/Outside/L_meta_48518.lean at 596fdbbc5fe5f46ed55b1dc21351d3d46d7db044.
-- The recursion is factored out as `fitPack` and the path predicate as `FitP3`.
private theorem fit_lo_alpha {V : Type*} [DecidableEq V]
    (edge : V → V → Bool) (U : Finset V) (a b : V) (n : ℕ)
    (hab : edge a b = true)
    (hU : ∀ z ⊆ U, (∀ j ∈ z, ∀ k ∈ z, edge j k = false) → z.card ≤ n) :
    ∀ z ⊆ insert a (insert b U), (∀ j ∈ z, ∀ k ∈ z, edge j k = false) → z.card ≤ n + 1 := by
  intro z hz hi
  by_cases ha : a ∈ z
  · have hb : b ∉ z := fun hb => by simp [hi a ha b hb] at hab
    have h1 : z.erase a ⊆ U := by
      intro k hk
      rw [Finset.mem_erase] at hk
      have := hz hk.2
      simp only [Finset.mem_insert] at this
      rcases this with h | h | h
      · exact absurd h hk.1
      · exact absurd (h ▸ hk.2) hb
      · exact h
    have := hU _ h1 (fun j hj k hk => hi j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk))
    have := Finset.pred_card_le_card_erase (s := z) (a := a)
    omega
  · have h1 : z.erase b ⊆ U := by
      intro k hk
      rw [Finset.mem_erase] at hk
      have := hz hk.2
      simp only [Finset.mem_insert] at this
      rcases this with h | h | h
      · exact absurd (h ▸ hk.2) ha
      · exact absurd h hk.1
      · exact h
    have := hU _ h1 (fun j hj k hk => hi j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk))
    have := Finset.pred_card_le_card_erase (s := z) (a := b)
    omega

private theorem fit_lo_step {V : Type*} [DecidableEq V] (edge : V → V → Bool) (x : Finset V)
    (f : Finset V → V → Bool)
    (h1 : ∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, edge i j = false) → f y j = true)
    (h2 : ∀ y, y ⊆ x → ∀ j ∈ y, f y j = false)
    (h3 : ∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true)
    (U : Finset V) (p : Fin 3 → V) (l : ℕ) (hU : U ⊆ x) (hx : ∀ t, p t ∈ x)
    (hn : ∀ t, p t ∉ U) (he : ∀ t, ∀ i ∈ U, edge i (p t) = false)
    (h20 : edge (p 2) (p 0) = false) (hne : p 2 ≠ p 0) (hp : fitPack x f l U) :
    ∃ s t : Fin 3, ((s = 1 ∧ t = 2) ∨ (s = 0 ∧ t = 1)) ∧
      fitPack x f (l + 2) (insert (p s) (insert (p t) U)) := by
  have hsub : ∀ s t : Fin 3, insert (p s) (insert (p t) U) ⊆ x := by
    intro s t k hk
    simp only [Finset.mem_insert] at hk
    rcases hk with h | h | h
    · exact h ▸ hx s
    · exact h ▸ hx t
    · exact hU h
  have hsub1 : ∀ t : Fin 3, insert (p t) U ⊆ x := fun t =>
    (Finset.subset_insert _ _).trans (hsub t t)
  have hf1 : ∀ t, f U (p t) = true := fun t => h1 U hU _ (hx t) ⟨hn t, he t⟩
  by_cases hc : f (insert (p 1) (insert (p 2) U)) (p 0) = false
  · refine ⟨1, 2, Or.inl ⟨rfl, rfl⟩, insert (p 2) U, _, p 0, hx 0,
      ⟨U, insert (p 2) U, p 2, hx 2, hp, Finset.subset_insert _ _, le_rfl, hf1 2,
        h2 _ (hsub1 2) _ (Finset.mem_insert_self _ _)⟩,
      Finset.subset_insert _ _, le_rfl, ?_, hc⟩
    refine h1 _ (hsub1 2) _ (hx 0) ⟨?_, ?_⟩
    · simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hne h.symm, hn 0⟩
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with h | h
      · exact h ▸ h20
      · exact he 0 i h
  · refine ⟨0, 1, Or.inr ⟨rfl, rfl⟩, insert (p 1) U, _, p 0, hx 0,
      ⟨U, insert (p 1) U, p 1, hx 1, hp, Finset.subset_insert _ _, le_rfl, hf1 1,
        h2 _ (hsub1 1) _ (Finset.mem_insert_self _ _)⟩,
      Finset.subset_insert _ _, le_rfl, ?_, h2 _ (hsub 0 1) _ (Finset.mem_insert_self _ _)⟩
    refine h3 _ (insert (p 1) (insert (p 2) U)) ?_ (hsub 1 2) _ (hx 0) (by simpa using hc)
    exact Finset.insert_subset_insert _ (Finset.subset_insert _ _)

private theorem fit_lo_chain {V ι : Type*} [DecidableEq V] (edge : V → V → Bool) (x : Finset V)
    (f : Finset V → V → Bool)
    (h1 : ∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, edge i j = false) → f y j = true)
    (h2 : ∀ y, y ⊆ x → ∀ j ∈ y, f y j = false)
    (h3 : ∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true)
    (pth : ι → Fin 3 → V)
    (L : List ι) : ∀ (U : Finset V) (l n : ℕ), U ⊆ x →
      (∀ q ∈ L, FitP3 edge (pth q)) → (∀ q ∈ L, ∀ t, pth q t ∈ x) →
      L.Pairwise (fun q r => ∀ s t, pth q s ≠ pth r t ∧ edge (pth q s) (pth r t) = false) →
      (∀ q ∈ L, ∀ t, pth q t ∉ U ∧ ∀ i ∈ U, edge i (pth q t) = false) →
      (∀ z ⊆ U, (∀ j ∈ z, ∀ k ∈ z, edge j k = false) → z.card ≤ n) →
      fitPack x f l U →
      ∃ Y ⊆ x, fitPack x f (l + 2 * L.length) Y ∧
        ∀ z ⊆ Y, (∀ j ∈ z, ∀ k ∈ z, edge j k = false) → z.card ≤ n + L.length := by
  induction L with
  | nil => intro U l n hU _ _ _ _ hn hp; exact ⟨U, hU, hp, hn⟩
  | cons q L ih =>
    intro U l n hU hin hx hpw hfr hn hp
    rw [List.pairwise_cons] at hpw
    obtain ⟨h01, h12, h20, hne⟩ := hin q List.mem_cons_self
    obtain ⟨s, t, hst, hp'⟩ := fit_lo_step edge x f h1 h2 h3 U (pth q) l hU
      (hx q List.mem_cons_self) (fun t => (hfr q List.mem_cons_self t).1)
      (fun t => (hfr q List.mem_cons_self t).2) h20 hne hp
    have hedge : edge (pth q s) (pth q t) = true := by
      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h12
      · exact h01
    have hsub : insert (pth q s) (insert (pth q t) U) ⊆ x := by
      intro k hk
      simp only [Finset.mem_insert] at hk
      rcases hk with h | h | h
      · exact h ▸ hx q List.mem_cons_self s
      · exact h ▸ hx q List.mem_cons_self t
      · exact hU h
    have hfr' : ∀ r ∈ L, ∀ t', pth r t' ∉ insert (pth q s) (insert (pth q t) U) ∧
        ∀ i ∈ insert (pth q s) (insert (pth q t) U), edge i (pth r t') = false := by
      intro r hr t'
      have hA := hpw.1 r hr
      have hB := hfr r (List.mem_cons_of_mem _ hr) t'
      refine ⟨?_, ?_⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => (hA s t').1 h.symm, fun h => (hA t t').1 h.symm, hB.1⟩
      · intro i hi
        simp only [Finset.mem_insert] at hi
        rcases hi with h | h | h
        · exact h ▸ (hA s t').2
        · exact h ▸ (hA t t').2
        · exact hB.2 i h
    obtain ⟨Y, hY, hpY, hnY⟩ := ih _ (l + 2) (n + 1) hsub
      (fun r hr => hin r (List.mem_cons_of_mem _ hr))
      (fun r hr => hx r (List.mem_cons_of_mem _ hr)) hpw.2 hfr'
      (fit_lo_alpha edge U _ _ n hedge hn) hp'
    refine ⟨Y, hY, ?_, ?_⟩
    · have : l + 2 * (q :: L).length = l + 2 + 2 * L.length := by
        simp only [List.length_cons]; ring
      rw [this]; exact hpY
    · intro z hz hi
      have := hnY z hz hi
      simp only [List.length_cons]; omega

/-- Mutually anticomplete induced paths each force one unit of excess over alpha. -/
theorem fit_lower {V ι : Type*} [DecidableEq V] (edge : V → V → Bool) (x : Finset V) {e : ℕ}
    (pth : ι → Fin 3 → V) (L : List ι)
    (hin : ∀ q ∈ L, FitP3 edge (pth q)) (hx : ∀ q ∈ L, ∀ t, pth q t ∈ x)
    (hpw : L.Pairwise (fun q r => ∀ s t, pth q s ≠ pth r t ∧ edge (pth q s) (pth r t) = false))
    (hadm : fitAdmits edge x e) : L.length ≤ e := by
  classical
  obtain ⟨f, h1, h2, h3, hb⟩ := hadm
  obtain ⟨Y, hY, hpack, hcard⟩ := fit_lo_chain edge x f h1 h2 h3 pth
    L ∅ 0 0 (Finset.empty_subset _) hin hx hpw
    (fun _ _ _ => ⟨Finset.notMem_empty _, fun _ hi => (Finset.notMem_empty _ hi).elim⟩)
    (fun z hz _ => by rw [Finset.subset_empty.1 hz]; simp) trivial
  have halpha : fitAlpha edge Y ≤ L.length := by
    unfold fitAlpha
    apply Finset.sup_le
    intro z hz
    have hz' := (fit_indep_filter_mem (edge := edge) (y := Y)).mp hz
    simpa only [Nat.zero_add] using hcard z hz'.1 hz'.2
  have hbound := hb Y _ hY hpack
  simp only [Nat.zero_add] at hbound
  omega

theorem fit_lower_finset {V ι : Type*} [DecidableEq V] (edge : V → V → Bool) (x : Finset V)
    {e : ℕ} (pth : ι → Fin 3 → V) (P : Finset ι)
    (hin : ∀ q ∈ P, FitP3 edge (pth q)) (hx : ∀ q ∈ P, ∀ t, pth q t ∈ x)
    (hsep : ∀ q ∈ P, ∀ r ∈ P, q ≠ r →
      ∀ s t, pth q s ≠ pth r t ∧ edge (pth q s) (pth r t) = false)
    (hadm : fitAdmits edge x e) : P.card ≤ e := by
  have hpw := (Finset.nodup_toList P).pairwise_of_forall_ne
    (fun q hq r hr hne => hsep q (Finset.mem_toList.mp hq) r (Finset.mem_toList.mp hr) hne)
  have hb := fit_lower edge x pth P.toList
    (fun q hq => hin q (Finset.mem_toList.mp hq))
    (fun q hq => hx q (Finset.mem_toList.mp hq)) hpw hadm
  simpa only [Finset.length_toList] using hb

section Partition

variable {V K : Type*} [DecidableEq V] [DecidableEq K]

private def fitTagFit (tag : V → K) (y : Finset V) (j : V) : Bool :=
  decide (tag j ∉ y.image tag)

private theorem fit_tagPack_le (x : Finset V) (tag : V → K) (l : ℕ) (y : Finset V)
    (hp : fitPack x (fitTagFit tag) l y) : l ≤ (y.image tag).card := by
  induction l generalizing y with
  | zero => exact Nat.zero_le _
  | succ l ih =>
    obtain ⟨u, v, j, _, hu, huv, hvy, hlive, hdead⟩ := hp
    have hnot : tag j ∉ u.image tag := by simpa [fitTagFit] using hlive
    have hmem : tag j ∈ v.image tag := by simpa [fitTagFit] using hdead
    have hstrict : u.image tag ⊂ y.image tag := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.image_subset_image (huv.trans hvy), ?_⟩
      intro heq
      apply hnot
      rw [heq]
      exact Finset.image_subset_image hvy hmem
    exact Nat.lt_of_le_of_lt (ih u hu) (Finset.card_lt_card hstrict)

private theorem fit_tagCount_le (edge : V → V → Bool) (x y : Finset V) (hy : y ⊆ x)
    (hirr : ∀ i, edge i i = false) (tag : V → K) (E : Finset K)
    (hsep : ∀ a ∈ x, ∀ b ∈ x, tag a ∉ E → tag b ∉ E → tag a ≠ tag b → edge a b = false) :
    (y.image tag).card ≤ fitAlpha edge y + E.card := by
  classical
  let A := y.image tag \ E
  have hpick (k : {k // k ∈ A}) : ∃ i ∈ y, tag i = k.val :=
    Finset.mem_image.mp (Finset.mem_sdiff.mp k.property).1
  let rep (k : {k // k ∈ A}) := Classical.choose (hpick k)
  have hyrep (k : {k // k ∈ A}) : rep k ∈ y := (Classical.choose_spec (hpick k)).1
  have htag (k : {k // k ∈ A}) : tag (rep k) = k.val := (Classical.choose_spec (hpick k)).2
  let R := A.attach.image rep
  have hR : R ⊆ y := by
    intro a ha
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
    exact hyrep k
  have hind : ∀ a ∈ R, ∀ b ∈ R, edge a b = false := by
    intro a ha b hb
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hb
    by_cases hk : k = m
    · subst m
      exact hirr _
    · apply hsep _ (hy (hyrep k)) _ (hy (hyrep m))
      · rw [htag]
        exact (Finset.mem_sdiff.mp k.property).2
      · rw [htag]
        exact (Finset.mem_sdiff.mp m.property).2
      · simp only [htag]
        exact fun h => hk (Subtype.ext h)
  have hcard : A.card ≤ R.card := by
    have hA : A ⊆ R.image tag := by
      intro k hk
      let a : {k // k ∈ A} := ⟨k, hk⟩
      exact Finset.mem_image.mpr
        ⟨rep a, Finset.mem_image_of_mem rep (Finset.mem_attach A a), htag a⟩
    exact (Finset.card_le_card hA).trans Finset.card_image_le
  have halpha : R.card ≤ fitAlpha edge y := by
    unfold fitAlpha
    exact Finset.le_sup (f := Finset.card)
      ((fit_indep_filter_mem (edge := edge)).mpr ⟨hR, hind⟩)
  exact (Finset.card_le_card_sdiff_add_card (s := y.image tag) (t := E)).trans
    (Nat.add_le_add_right (hcard.trans halpha) E.card)

/-- All classes must be cliques; only exceptional classes may have edges to other classes. -/
theorem fit_upper_partition (edge : V → V → Bool) (x : Finset V) {e : ℕ}
    (hirr : ∀ i, edge i i = false) (tag : V → K) (E : Finset K)
    (hclique : ∀ a ∈ x, ∀ b ∈ x, tag a = tag b → a = b ∨ edge a b = true)
    (hsep : ∀ a ∈ x, ∀ b ∈ x, tag a ∉ E → tag b ∉ E → tag a ≠ tag b → edge a b = false)
    (hE : E.card ≤ e) : fitAdmits edge x e := by
  refine ⟨fitTagFit tag, ?_, ?_, ?_, ?_⟩
  · intro y hy j hj h
    simp only [fitTagFit, decide_eq_true_eq]
    intro hmem
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hmem
    rcases hclique i (hy hi) j hj hij with heq | he
    · exact h.1 (heq ▸ hi)
    · have hfalse := h.2 i hi
      simp [he] at hfalse
  · intro y _ j hj
    have hmem : tag j ∈ y.image tag := Finset.mem_image_of_mem tag hj
    simp [fitTagFit, hmem]
  · intro u v huv _ j _ hlive
    simp only [fitTagFit, decide_eq_true_eq] at hlive ⊢
    exact fun hmem => hlive (Finset.image_subset_image huv hmem)
  · intro y l hy hp
    exact (fit_tagPack_le x tag l y hp).trans
      ((fit_tagCount_le edge x y hy hirr tag E hsep).trans (Nat.add_le_add_left hE _))

end Partition

abbrev FitRelated {V : Type*} (edge : V → V → Bool) (a b : V) : Prop := a = b ∨ edge a b = true

private theorem fit_related_symm {V : Type*} {edge : V → V → Bool}
    (hsym : ∀ a b, edge a b = edge b a) {a b : V} (hab : FitRelated edge a b) :
    FitRelated edge b a :=
  hab.elim (fun h => Or.inl h.symm) (fun h => Or.inr ((hsym b a).trans h))

/-- On a P3-free set adjacency-or-equality is transitive. -/
theorem fit_p3Free_trans {V : Type*} {edge : V → V → Bool} {r : Finset V}
    (hsym : ∀ a b, edge a b = edge b a) (hfree : FitP3Free edge r)
    {a b c : V} (ha : a ∈ r) (hb : b ∈ r) (hc : c ∈ r)
    (hab : FitRelated edge a b) (hbc : FitRelated edge b c) : FitRelated edge a c := by
  rcases hab with rfl | hab
  · exact hbc
  rcases hbc with rfl | hbc
  · exact Or.inr hab
  by_cases hca : c = a
  · exact Or.inl hca.symm
  by_cases he : edge a c = true
  · exact Or.inr he
  · have hca' := (hsym c a).trans (Bool.eq_false_of_not_eq_true he)
    let p : Fin 3 → V := ![a, b, c]
    have hp : ∀ t, p t ∈ r := by
      intro t
      fin_cases t
      · simpa [p] using ha
      · simpa [p] using hb
      · simpa [p] using hc
    have hp3 : FitP3 edge p := by
      simpa [p, FitP3] using And.intro hab (And.intro hbc (And.intro hca' hca))
    exact (hfree p hp hp3).elim

theorem fit_p3Free_equivalence {V : Type*} {edge : V → V → Bool} {r : Finset V}
    (hsym : ∀ a b, edge a b = edge b a) (hfree : FitP3Free edge r) :
    Equivalence (fun a b : {v // v ∈ r} => FitRelated edge a.val b.val) := by
  refine ⟨fun _ => Or.inl rfl, fun h => fit_related_symm hsym h, ?_⟩
  intro a b c hab hbc
  exact fit_p3Free_trans hsym hfree a.property b.property c.property hab hbc

def fitClosedNeighborhood {V : Type*} [DecidableEq V] (edge : V → V → Bool)
    (r : Finset V) (a : V) : Finset V := r.filter (fun b => a = b ∨ edge a b = true)

/-- Closed neighborhoods name the clique classes on the residual. -/
theorem fit_closedNeighborhood_eq_iff {V : Type*} [DecidableEq V]
    {edge : V → V → Bool} {r : Finset V}
    (hsym : ∀ a b, edge a b = edge b a) (hfree : FitP3Free edge r)
    {a b : V} (ha : a ∈ r) (hb : b ∈ r) :
    fitClosedNeighborhood edge r a = fitClosedNeighborhood edge r b ↔ FitRelated edge a b := by
  constructor
  · intro h
    have hm : b ∈ fitClosedNeighborhood edge r b := Finset.mem_filter.mpr ⟨hb, Or.inl rfl⟩
    rw [← h] at hm
    exact (Finset.mem_filter.mp hm).2
  · intro hab
    ext c
    simp only [fitClosedNeighborhood, Finset.mem_filter]
    constructor
    · rintro ⟨hc, hac⟩
      exact ⟨hc, fit_p3Free_trans hsym hfree hb ha hc (fit_related_symm hsym hab) hac⟩
    · rintro ⟨hc, hbc⟩
      exact ⟨hc, fit_p3Free_trans hsym hfree ha hb hc hab hbc⟩

/-- Assign covered vertices to their covering clique, and residual vertices to their closed
neighborhood in the P3-free residual. -/
theorem fit_upper_residual {V K : Type*} [DecidableEq V] [DecidableEq K]
    (edge : V → V → Bool) (x : Finset V) {e : ℕ}
    (hirr : ∀ i, edge i i = false) (hsym : ∀ a b, edge a b = edge b a)
    (cover : V → Option K) (E : Finset K)
    (hcover : ∀ a ∈ x, ∀ k, cover a = some k → k ∈ E)
    (hclique : ∀ a ∈ x, ∀ b ∈ x, ∀ k, cover a = some k → cover b = some k → FitRelated edge a b)
    (hfree : FitP3Free edge (x.filter (fun a => cover a = none)))
    (hE : E.card ≤ e) : fitAdmits edge x e := by
  let r := x.filter (fun a => cover a = none)
  let tag (a : V) : K ⊕ Finset V :=
    match cover a with
    | some k => Sum.inl k
    | none => Sum.inr (fitClosedNeighborhood edge r a)
  let D := E.image (Sum.inl : K → K ⊕ Finset V)
  refine fit_upper_partition edge x hirr tag D ?_ ?_ (Finset.card_image_le.trans hE)
  · intro a ha b hb ht
    cases ha' : cover a with
    | none =>
      cases hb' : cover b with
      | none =>
        have har : a ∈ r := Finset.mem_filter.mpr ⟨ha, ha'⟩
        have hbr : b ∈ r := Finset.mem_filter.mpr ⟨hb, hb'⟩
        exact (fit_closedNeighborhood_eq_iff hsym hfree har hbr).mp (by simpa [tag, ha', hb'] using ht)
      | some k => simp [tag, ha', hb'] at ht
    | some k =>
      cases hb' : cover b with
      | none => simp [tag, ha', hb'] at ht
      | some m =>
        have hkm : k = m := by simpa [tag, ha', hb'] using ht
        exact hclique a ha b hb k ha' (hkm.symm ▸ hb')
  · intro a ha b hb hna hnb hne
    have hnone (u : V) (hu : u ∈ x) (hn : tag u ∉ D) : cover u = none := by
      cases hu' : cover u with
      | none => rfl
      | some k =>
        have hm : Sum.inl k ∈ D := Finset.mem_image_of_mem _ (hcover u hu k hu')
        exact (hn (by simpa [tag, hu'] using hm)).elim
    have ha' := hnone a ha hna
    have hb' := hnone b hb hnb
    have har : a ∈ r := Finset.mem_filter.mpr ⟨ha, ha'⟩
    have hbr : b ∈ r := Finset.mem_filter.mpr ⟨hb, hb'⟩
    have hnrel : ¬ FitRelated edge a b := by
      intro hab
      have hn : fitClosedNeighborhood edge r a = fitClosedNeighborhood edge r b :=
        (fit_closedNeighborhood_eq_iff hsym hfree har hbr).mpr hab
      apply hne
      simpa only [tag, ha', hb'] using (congrArg (Sum.inr : Finset V → K ⊕ Finset V) hn)
    exact Bool.eq_false_of_not_eq_true (fun h => hnrel (Or.inr h))

/-- A transversal for the unions of the three supports of all enabled induced paths
bounds the fit excess, provided vertices sharing a support point are equal or adjacent. -/
theorem fit_upper_hit {V K : Type*} [DecidableEq V] [DecidableEq K]
    (edge : V → V → Bool) (x : Finset V) {e : ℕ}
    (hirr : ∀ i, edge i i = false) (hsym : ∀ a b, edge a b = edge b a)
    (support : V → Finset K) (H : Finset K)
    (hclique : ∀ a ∈ x, ∀ b ∈ x, ∀ k, k ∈ support a → k ∈ support b → FitRelated edge a b)
    (hhit : ∀ p : Fin 3 → V, (∀ t, p t ∈ x) → FitP3 edge p →
      ∃ t k, k ∈ H ∧ k ∈ support (p t))
    (hH : H.card ≤ e) : fitAdmits edge x e := by
  classical
  let hit (a : V) := ∃ k ∈ H, k ∈ support a
  let cover (a : V) : Option K := if ha : hit a then some (Classical.choose ha) else none
  have hcover (a : V) (k : K) (hk : cover a = some k) : k ∈ H ∧ k ∈ support a := by
    by_cases ha : hit a
    · have heq : Classical.choose ha = k := by simpa [cover, ha] using hk
      simpa only [heq] using Classical.choose_spec ha
    · simp [cover, ha] at hk
  refine fit_upper_residual edge x hirr hsym cover H (fun a _ k hk => (hcover a k hk).1) ?_ ?_ hH
  · intro a ha b hb k hka hkb
    exact hclique a ha b hb k (hcover a k hka).2 (hcover b k hkb).2
  · intro p hp hp3
    have hpx : ∀ t, p t ∈ x := fun t => (Finset.mem_filter.mp (hp t)).1
    obtain ⟨t, k, hk, hkp⟩ := hhit p hpx hp3
    have ht : hit (p t) := ⟨k, hk, hkp⟩
    have hnone := (Finset.mem_filter.mp (hp t)).2
    simp [cover, ht] at hnone

open SimpleGraph

abbrev PathIndex {n : Nat} (g : Fin n → Fin n → Bool) := {p : Fin 3 → Fin n // FitP3 g p}

def foot {V : Type*} [DecidableEq V] {n : Nat} (S : Fin n → Finset V) (p : Fin 3 → Fin n) : Finset V :=
  S (p 0) ∪ S (p 1) ∪ S (p 2)

lemma mem_foot {V : Type*} [DecidableEq V] {n : Nat} (S : Fin n → Finset V)
    (p : Fin 3 → Fin n) (w : V) : w ∈ foot S p ↔ ∃ t, w ∈ S (p t) := by
  simp only [foot, Finset.mem_union]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨t, ht⟩
    fin_cases t
    · exact Or.inl (Or.inl ht)
    · exact Or.inl (Or.inr ht)
    · exact Or.inr ht

lemma foot_convex {n t : Nat} {T : SimpleGraph (Fin t)} (h : T.IsTree)
    (S : Fin n → Finset (Fin t)) (g : Fin n → Fin n → Bool)
    (hs : ∀ i, (T.induce (↑(S i) : Set (Fin t))).Connected)
    (hirr : ∀ i, g i i = false)
    (hg : ∀ i j, i ≠ j → (g i j = true ↔ ((S i) ∩ (S j)).Nonempty))
    (p : PathIndex g) : TreeConvex h (foot S p.val) := by
  obtain ⟨h₀, h₁, _, _⟩ := p.property
  have hi (a b : Fin n) (he : g a b = true) : ((S a) ∩ (S b)).Nonempty := by
    have hn : a ≠ b := by
      intro e
      subst b
      simp [hirr] at he
    exact (hg a b hn).mp he
  have h01 := convex_union h (convex_connected h (hs (p.val 0))) (convex_connected h (hs (p.val 1)))
    (hi _ _ h₀)
  apply convex_union h h01 (convex_connected h (hs (p.val 2)))
  obtain ⟨w, hw⟩ := hi _ _ h₁
  have hw' := Finset.mem_inter.mp hw
  exact ⟨w, Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hw'.1, hw'.2⟩⟩

lemma foot_nonempty {n : Nat} {V : Type*} [DecidableEq V]
    (S : Fin n → Finset V) (hs : ∀ i, (S i).Nonempty) (p : Fin 3 → Fin n) : (foot S p).Nonempty := by
  obtain ⟨w, hw⟩ := hs (p 0)
  exact ⟨w, (mem_foot S p w).mpr ⟨0, hw⟩⟩

noncomputable def enabledPaths {n : Nat} (g : Fin n → Fin n → Bool) (x : Finset (Fin n)) :
    Finset (PathIndex g) :=
  letI := Classical.propDecidable
  Finset.univ.filter fun i => ∀ s, i.val s ∈ x

lemma mem_enabledPaths {n : Nat} {g : Fin n → Fin n → Bool} {x : Finset (Fin n)} {i : PathIndex g} :
    i ∈ enabledPaths g x ↔ ∀ s, i.val s ∈ x := by
  classical
  simp [enabledPaths]

lemma admits_iff_opt {n t : Nat} {T : SimpleGraph (Fin t)} (h : T.IsTree) (r : Fin t)
    (S : Fin n → Finset (Fin t)) (g : Fin n → Fin n → Bool)
    (hs : ∀ i, (S i).Nonempty ∧ (T.induce (↑(S i) : Set (Fin t))).Connected)
    (hirr : ∀ i, g i i = false) (hsym : ∀ i j, g i j = g j i)
    (hg : ∀ i j, i ≠ j → (g i j = true ↔ ((S i) ∩ (S j)).Nonempty))
    (x : Finset (Fin n)) (e : Nat) :
    fitAdmits g x e ↔ Opt (fun p : PathIndex g => foot S p.val) (enabledPaths g x) ≤ e := by
  classical
  let F := fun p : PathIndex g => foot S p.val
  constructor
  · intro hadm
    apply opt_le
    intro P hP hgood
    apply fit_lower_finset g x (fun p : PathIndex g => p.val) P (fun p _ => p.property)
      (fun p hp => mem_enabledPaths.mp (hP hp)) _ hadm
    intro q hq p hp hn s t
    have hdis := Finset.disjoint_left.mp (hgood hq hp hn)
    have hne : q.val s ≠ p.val t := by
      intro he
      obtain ⟨w, hw⟩ := (hs (q.val s)).1
      exact hdis ((mem_foot S q.val w).mpr ⟨s, hw⟩)
        ((mem_foot S p.val w).mpr ⟨t, he ▸ hw⟩)
    refine ⟨hne, ?_⟩
    by_contra hb
    obtain ⟨w, hw⟩ := (hg _ _ hne).mp (by simpa using hb)
    exact hdis ((mem_foot S q.val w).mpr ⟨s, (Finset.mem_inter.mp hw).1⟩)
      ((mem_foot S p.val w).mpr ⟨t, (Finset.mem_inter.mp hw).2⟩)
  · intro he
    have hc : ∀ p, TreeConvex h (F p) := foot_convex h S g (fun i => (hs i).2) hirr hg
    choose d hd₁ hd₂ using fun p => convex_top h r (hc p) (foot_nonempty S (fun i => (hs i).1) p.val)
    obtain ⟨H, hH, hhit⟩ := packing_transversal h r F d (fun p => ⟨hd₁ p, hd₂ p⟩) hc (enabledPaths g x)
    apply fit_upper_hit g x hirr hsym S H _ _ (hH.trans he)
    · intro a _ b _ w ha hb
      by_cases hab : a = b
      · exact Or.inl hab
      · exact Or.inr ((hg a b hab).mpr ⟨w, Finset.mem_inter.mpr ⟨ha, hb⟩⟩)
    · intro p hpx hp
      let i : PathIndex g := ⟨p, hp⟩
      obtain ⟨w, hw, hwF⟩ := hhit i (mem_enabledPaths.mpr hpx)
      obtain ⟨s, hs⟩ := (mem_foot S p w).mp hwF
      exact ⟨s, w, hw, hs⟩

lemma path_opt_le_n {n : Nat} {V : Type*} [DecidableEq V]
    (S : Fin n → Finset V) (g : Fin n → Fin n → Bool) (hs : ∀ i, (S i).Nonempty)
    (A : Finset (PathIndex g)) : Opt (fun p : PathIndex g => foot S p.val) A ≤ n := by
  classical
  apply opt_le
  intro P _ hP
  let f := fun p : PathIndex g => p.val 0
  have h_inj : Set.InjOn f (↑P : Set (PathIndex g)) := by
    intro a ha b hb he
    have he' : a.val 0 = b.val 0 := he
    by_contra hne
    obtain ⟨w, hw⟩ := hs (a.val 0)
    exact Finset.disjoint_left.mp (hP ha hb hne)
      ((mem_foot S a.val w).mpr ⟨0, hw⟩) ((mem_foot S b.val w).mpr ⟨0, he' ▸ hw⟩)
  have hcard := Finset.card_image_of_injOn h_inj
  rw [← hcard]
  simpa using Finset.card_le_univ (P.image f)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The four list lemmas below are adapted from Outside/L_meta_48148.lean,
-- proof repository commit 596fdbbc5fe5f46ed55b1dc21351d3d46d7db044.
private lemma bridge_wires_append (gs₁ gs₂ : List Gate) (x : List Bool) :
    Circuit.wires ⟨gs₁ ++ gs₂, 0⟩ x =
    Circuit.wires ⟨gs₂, 0⟩ (Circuit.wires ⟨gs₁, 0⟩ x) := by
  simp [Circuit.wires, List.foldl_append]

private lemma bridge_wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton]
    have : (List.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x gs).length =
        x.length + gs.length := ih
    omega

private lemma bridge_wires_getD_append_left (gs₁ gs₂ : List Gate) (x : List Bool) {i : Nat}
    (hi : i < x.length + gs₁.length) :
    (Circuit.wires ⟨gs₁ ++ gs₂, 0⟩ x).getD i false =
    (Circuit.wires ⟨gs₁, 0⟩ x).getD i false := by
  rw [bridge_wires_append]
  induction gs₂ using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs₂ g ih =>
    let w := Circuit.wires ⟨gs₂, 0⟩ (Circuit.wires ⟨gs₁, 0⟩ x)
    have hlen : i < w.length := by
      simp only [w, bridge_wires_length]; omega
    have hstep : Circuit.wires ⟨gs₂ ++ [g], 0⟩ (Circuit.wires ⟨gs₁, 0⟩ x) =
        w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)] := by
      simp [w, Circuit.wires, List.foldl_append]
    rw [hstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlen, ← List.getD_eq_getElem?_getD]
    exact ih

private lemma bridge_wires_snoc_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.wires ⟨gs ++ [g], 0⟩ x).getD (x.length + gs.length) false =
    g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false) := by
  let w := Circuit.wires ⟨gs, 0⟩ x
  have hlen : w.length = x.length + gs.length := bridge_wires_length gs x
  have hstep : Circuit.wires ⟨gs ++ [g], 0⟩ x =
      w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)] := by
    simp [w, Circuit.wires, List.foldl_append]
  rw [hstep, List.getD_eq_getElem?_getD, ← hlen, List.getElem?_append_right (le_refl _)]
  simp [w]

private lemma bridge_readsBack_append {m : Nat} {gs₁ gs₂ : List Gate} {o₁ o₂ o : Nat}
    (h1 : ReadsBack m ⟨gs₁, o₁⟩)
    (h2 : ∀ j < gs₂.length, ∀ i ∈ (gateAt ⟨gs₂, o₂⟩ j).inputs, i < m + gs₁.length + j) :
    ReadsBack m ⟨gs₁ ++ gs₂, o⟩ := by
  intro j hj i hi
  simp only [gateAt, List.getD_eq_getElem?_getD] at hi
  by_cases hj1 : j < gs₁.length
  · rw [List.getElem?_append_left hj1] at hi
    exact h1 j hj1 i (by simpa [gateAt, List.getD_eq_getElem?_getD] using hi)
  · have hge : gs₁.length ≤ j := by omega
    rw [List.getElem?_append_right hge] at hi
    have hj2 : j - gs₁.length < gs₂.length := by simp at hj; omega
    have h := h2 (j - gs₁.length) hj2 i (by simpa [gateAt, List.getD_eq_getElem?_getD] using hi)
    omega

/-- A gate program on `m` inputs. Its output is picked separately. -/
def GateProgram (m : Nat) :=
  { gs : List Gate // ReadsBack m ⟨gs, 0⟩ ∧ Monotone2 ⟨gs, 0⟩ }

namespace GateProgram

variable {m : Nat}

def empty (m : Nat) : GateProgram m :=
  ⟨[], by simp [ReadsBack], by simp [Monotone2]⟩

def gates (p : GateProgram m) : List Gate := p.1

lemma readsBack (p : GateProgram m) : ReadsBack m ⟨p.gates, 0⟩ := p.2.1

lemma monotone (p : GateProgram m) : Monotone2 ⟨p.gates, 0⟩ := p.2.2

def size (p : GateProgram m) : Nat := p.gates.length

def limit (p : GateProgram m) : Nat := m + p.size

def circuit (p : GateProgram m) (output : Nat) : Circuit := ⟨p.gates, output⟩

def value (p : GateProgram m) (x : List Bool) (i : Nat) : Bool :=
  ((p.circuit 0).wires x).getD i false

@[simp] lemma size_empty : (empty m).size = 0 := rfl
@[simp] lemma limit_empty : (empty m).limit = m := Nat.add_zero m

@[simp] lemma circuit_size (p : GateProgram m) (o : Nat) : (p.circuit o).size = p.size := rfl

lemma circuit_readsBack (p : GateProgram m) (o : Nat) : ReadsBack m (p.circuit o) := p.readsBack

lemma circuit_monotone (p : GateProgram m) (o : Nat) : Monotone2 (p.circuit o) := p.monotone

@[simp] lemma value_empty (x : List Bool) (i : Nat) : (empty m).value x i = x.getD i false := rfl

/-- Extension can only append gates; it cannot replace old wires. -/
def Extends (p q : GateProgram m) : Prop := ∃ gs, q.gates = p.gates ++ gs

namespace Extends

protected lemma refl (p : GateProgram m) : p.Extends p := ⟨[], by simp⟩

protected lemma trans {p q r : GateProgram m} (hpq : p.Extends q) (hqr : q.Extends r) :
    p.Extends r := by
  obtain ⟨a, ha⟩ := hpq
  obtain ⟨b, hb⟩ := hqr
  exact ⟨a ++ b, by rw [hb, ha, List.append_assoc]⟩

lemma size_mono {p q : GateProgram m} (h : p.Extends q) : p.size ≤ q.size := by
  obtain ⟨gs, hgs⟩ := h
  simp [size, hgs]

lemma lt {p q : GateProgram m} (h : p.Extends q) {i : Nat} (hi : i < p.limit) : i < q.limit :=
  Nat.lt_of_lt_of_le hi (Nat.add_le_add_left h.size_mono m)

lemma value {p q : GateProgram m} (h : p.Extends q) {x : List Bool} (hx : x.length = m)
    {i : Nat} (hi : i < p.limit) : q.value x i = p.value x i := by
  obtain ⟨gs, hgs⟩ := h
  simp only [GateProgram.value, circuit, hgs]
  apply bridge_wires_getD_append_left
  simpa only [hx, limit, size] using hi

end Extends

lemma empty_extends (p : GateProgram m) : (empty m).Extends p :=
  ⟨p.gates, rfl⟩

lemma value_input (p : GateProgram m) {x : List Bool} (hx : x.length = m) {i : Nat}
    (hi : i < m) : p.value x i = x.getD i false := by
  have hi' : i < (empty m).limit := by simpa using hi
  simpa using p.empty_extends.value hx hi'

def push (p : GateProgram m) (g : Gate)
    (hr : ∀ i ∈ g.inputs, i < p.limit)
    (hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    GateProgram m := by
  refine ⟨p.gates ++ [g], ?_, ?_⟩
  · refine bridge_readsBack_append (o₂ := 0) p.readsBack ?_
    intro j hj i hi
    have hj0 : j = 0 := by simp at hj; omega
    subst j
    have hi' : i ∈ g.inputs := by simpa [gateAt] using hi
    simpa [limit, size] using hr i hi'
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact p.monotone z hz
    · have : z = g := List.mem_singleton.mp hz
      subst z
      exact hm

lemma push_extends (p : GateProgram m) (g : Gate) (hr hm) : p.Extends (p.push g hr hm) :=
  ⟨[g], rfl⟩

@[simp] lemma size_push (p : GateProgram m) (g : Gate) (hr hm) :
    (p.push g hr hm).size = p.size + 1 := by simp [push, size, gates]

@[simp] lemma limit_push (p : GateProgram m) (g : Gate) (hr hm) :
    (p.push g hr hm).limit = p.limit + 1 := by simp [limit, Nat.add_assoc]

lemma value_push (p : GateProgram m) (g : Gate) (hr hm) {x : List Bool} (hx : x.length = m) :
    (p.push g hr hm).value x p.limit = g.op.eval (g.inputs.map fun i => p.value x i) := by
  simpa only [GateProgram.value, circuit, push, limit, size, gates, hx] using
    bridge_wires_snoc_last p.gates g x

end GateProgram

/-- An append-only circuit fragment with `ι`-indexed outputs, a gate budget and semantics. -/
def GateBlock {m : Nat} (before : GateProgram m) (ι : Type*) (budget : Nat)
    (spec : List Bool → ι → Bool) :=
  { a : GateProgram m × (ι → Nat) //
    before.Extends a.1 ∧
    a.1.size ≤ before.size + budget ∧
    (∀ i, a.2 i < a.1.limit) ∧
    (∀ x : List Bool, x.length = m → ∀ i, a.1.value x (a.2 i) = spec x i) }

namespace GateBlock

variable {m cost : Nat} {p : GateProgram m} {ι : Type*} {f g : List Bool → ι → Bool}

def mk (after : GateProgram m) (tap : ι → Nat) (extension : p.Extends after)
    (size_le : after.size ≤ p.size + cost) (tap_lt : ∀ i, tap i < after.limit)
    (eval : ∀ x : List Bool, x.length = m → ∀ i, after.value x (tap i) = f x i) :
    GateBlock p ι cost f :=
  ⟨(after, tap), extension, size_le, tap_lt, eval⟩

def after (b : GateBlock p ι cost f) : GateProgram m := b.1.1

def tap (b : GateBlock p ι cost f) : ι → Nat := b.1.2

lemma append_only (b : GateBlock p ι cost f) : p.Extends b.after := b.2.1

lemma size_le (b : GateBlock p ι cost f) : b.after.size ≤ p.size + cost := b.2.2.1

lemma tap_lt (b : GateBlock p ι cost f) (i : ι) : b.tap i < b.after.limit := b.2.2.2.1 i

lemma eval (b : GateBlock p ι cost f) (x : List Bool) (hx : x.length = m) (i : ι) :
    b.after.value x (b.tap i) = f x i := b.2.2.2.2 x hx i

/-- Expose valid old wires without using gates. -/
def existing (p : GateProgram m) (tap : ι → Nat) (ht : ∀ i, tap i < p.limit) :
    GateBlock p ι 0 (fun x i => p.value x (tap i)) :=
  mk p tap (GateProgram.Extends.refl p) (Nat.le_refl p.size) ht (fun _ _ _ => rfl)

def congr (b : GateBlock p ι cost f) (h : ∀ x : List Bool, x.length = m → ∀ i, f x i = g x i) :
    GateBlock p ι cost g :=
  mk b.after b.tap b.append_only b.size_le b.tap_lt
    (fun x hx i => (b.eval x hx i).trans (h x hx i))

def widen (b : GateBlock p ι cost f) {c : Nat} (h : cost ≤ c) : GateBlock p ι c f :=
  mk b.after b.tap b.append_only (b.size_le.trans (Nat.add_le_add_left h p.size)) b.tap_lt b.eval

end GateBlock

namespace GateProgram

variable {m : Nat}

/-- Append one binary gate. The flag selects AND instead of OR. -/
def binary (p : GateProgram m) (isAnd : Bool) (a b : Nat)
    (ha : a < p.limit) (hb : b < p.limit) :
    GateBlock p Unit 1 (fun x _ =>
      if isAnd then p.value x a && p.value x b else p.value x a || p.value x b) := by
  let g : Gate := ⟨if isAnd then GateOp.and else GateOp.or, [a, b]⟩
  have hr : ∀ i ∈ g.inputs, i < p.limit := by
    intro i hi
    change i ∈ [a, b] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  have hm : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
    cases isAnd <;> simp [g]
  refine GateBlock.mk (p.push g hr hm) (fun _ => p.limit) (p.push_extends g hr hm)
    (by simp) (fun _ => by simp) ?_
  intro x hx u
  rw [p.value_push g hr hm hx]
  cases isAnd <;> simp [g, GateOp.eval]

def andGate (p : GateProgram m) (a b : Nat) (ha : a < p.limit) (hb : b < p.limit) :
    GateBlock p Unit 1 (fun x _ => p.value x a && p.value x b) := p.binary true a b ha hb

def orGate (p : GateProgram m) (a b : Nat) (ha : a < p.limit) (hb : b < p.limit) :
    GateBlock p Unit 1 (fun x _ => p.value x a || p.value x b) := p.binary false a b ha hb

/-- Assemble independently compilable scalar rows into a vector of taps. -/
def compileFin (p : GateProgram m) (cost : Nat) :
    (k : Nat) → (f : List Bool → Fin k → Bool) →
    (∀ q, p.Extends q → ∀ i, GateBlock q Unit cost (fun x _ => f x i)) →
    GateBlock p (Fin k) (k * cost) f
  | 0, _, _ => GateBlock.mk p Fin.elim0 (Extends.refl p) (Nat.le_add_right _ _)
      (fun i => i.elim0) (fun _ _ i => i.elim0)
  | k + 1, f, row =>
    let l := compileFin p cost k (fun x i => f x i.succ) (fun q hq i => row q hq i.succ)
    let r := row l.after l.append_only 0
    GateBlock.mk r.after (Fin.cases (r.tap ()) l.tap) (l.append_only.trans r.append_only)
      (by
        have hl := l.size_le
        have hr := r.size_le
        simp only [Nat.add_mul, Nat.one_mul]
        omega)
      (by
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cases_zero] using r.tap_lt ()
        · simpa only [Fin.cases_succ] using r.append_only.lt (l.tap_lt j))
      (by
        intro x hx i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cases_zero] using r.eval x hx ()
        · simpa only [Fin.cases_succ] using
            (r.append_only.value hx (l.tap_lt j)).trans (l.eval x hx j))

/-- Compile scalar blocks and OR their values with an existing seed wire. -/
def compileOrListRaw {α : Type*} (p : GateProgram m) (cost zero : Nat) (hz : zero < p.limit)
    (f : List Bool → α → Bool) :
    (ys : List α) →
    (∀ q, p.Extends q → ∀ i ∈ ys, GateBlock q Unit cost (fun x _ => f x i)) →
    GateBlock p Unit (ys.length * (cost + 1)) (fun x _ => ys.any (f x) || p.value x zero)
  | [], _ => GateBlock.mk p (fun _ => zero) (Extends.refl p)
      (Nat.le_add_right _ _) (fun _ => hz) (by intro x hx u; simp)
  | i :: is, row =>
    let l := compileOrListRaw p cost zero hz f is
      (fun q hq j hj => row q hq j (List.mem_cons_of_mem _ hj))
    let r := row l.after l.append_only i (List.mem_cons_self)
    let b := r.after.orGate (r.tap ()) (l.tap ()) (r.tap_lt ()) (r.append_only.lt (l.tap_lt ()))
    GateBlock.mk b.after b.tap (l.append_only.trans (r.append_only.trans b.append_only))
      (by
        have hl := l.size_le
        have hr := r.size_le
        have hb := b.size_le
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega)
      b.tap_lt
      (by
        intro x hx u
        calc
          b.after.value x (b.tap u) = (r.after.value x (r.tap ()) || r.after.value x (l.tap ())) :=
            b.eval x hx u
          _ = (f x i || (is.any (f x) || p.value x zero)) := by
            rw [r.eval x hx (), r.append_only.value hx (l.tap_lt ()), l.eval x hx ()]
          _ = ((i :: is).any (f x) || p.value x zero) := by
            simp only [List.any_cons, Bool.or_assoc])

private def thresholdSplit {n : Nat} (k : Fin (n + 1)) (i : Fin (k.val + 1)) :
    Fin (n + 1) × Fin (n + 1) :=
  (⟨i.val, lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) k.isLt⟩,
   ⟨k.val - i.val, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩)

private def thresholdSplits {n : Nat} (k : Fin (n + 1)) : List (Fin (n + 1) × Fin (n + 1)) :=
  List.ofFn (thresholdSplit k)

/-- Boolean convolution for unary threshold addition. -/
def thresholdSumBits {n : Nat} (a b : Fin (n + 1) → Bool) (k : Fin (n + 1)) : Bool :=
  (thresholdSplits k).any (fun ij => a ij.1 && b ij.2)

lemma thresholdSumBits_true {n : Nat} (a b : Fin (n + 1) → Bool) (k : Fin (n + 1)) :
    thresholdSumBits a b k = true ↔
      ∃ i j : Fin (n + 1), i.val + j.val = k.val ∧ a i = true ∧ b j = true := by
  rw [thresholdSumBits, List.any_eq_true]
  constructor
  · rintro ⟨ij, hij, htrue⟩
    change ij ∈ List.ofFn (thresholdSplit k) at hij
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hij
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp htrue
    refine ⟨(thresholdSplit k i).1, (thresholdSplit k i).2, ?_, ha, hb⟩
    have hi := Nat.le_of_lt_succ i.isLt
    change i.val + (k.val - i.val) = k.val
    omega
  · rintro ⟨i, j, hij, ha, hb⟩
    let ii : Fin (k.val + 1) := ⟨i.val, by omega⟩
    have hi : (thresholdSplit k ii).1 = i := Fin.ext rfl
    have hj : (thresholdSplit k ii).2 = j := Fin.ext (by
      change k.val - i.val = j.val
      omega)
    refine ⟨thresholdSplit k ii, List.mem_ofFn.mpr ⟨ii, rfl⟩, ?_⟩
    rw [Bool.and_eq_true_iff, hi, hj]
    exact ⟨ha, hb⟩

lemma thresholdSumBits_eval {n : Nat} (k : Fin (n + 1)) (A B : Nat) :
    thresholdSumBits (fun i => decide (i.val ≤ A)) (fun i => decide (i.val ≤ B)) k =
      decide (k.val ≤ A + B) := by
  apply Bool.eq_iff_iff.mpr
  change _ = true ↔ _ = true
  simp only [thresholdSumBits_true, decide_eq_true_iff]
  constructor
  · rintro ⟨i, j, hsum, ha, hb⟩
    omega
  · intro h
    let i : Fin (n + 1) := ⟨min A k.val, lt_of_le_of_lt (min_le_right _ _) k.isLt⟩
    let j : Fin (n + 1) := ⟨k.val - i.val, lt_of_le_of_lt (Nat.sub_le _ _) k.isLt⟩
    have hi : i.val ≤ k.val := min_le_right _ _
    refine ⟨i, j, ?_, min_le_left _ _, ?_⟩
    · change i.val + (k.val - i.val) = k.val
      omega
    · change k.val - min A k.val ≤ B
      by_cases hAk : A ≤ k.val
      · rw [min_eq_left hAk]
        omega
      · rw [min_eq_right (show k.val ≤ A by omega)]
        omega

/-- Compile the Boolean convolution, OR'd with a seed wire. This theorem also applies
    when the input does not encode unary vectors. -/
def thresholdAddBits (p : GateProgram m) {n : Nat} (zero : Nat) (hz : zero < p.limit)
    (a b : Fin (n + 1) → Nat) (ha : ∀ i, a i < p.limit) (hb : ∀ i, b i < p.limit) :
    GateBlock p (Fin (n + 1)) (2 * (n + 1)^2) (fun x k =>
      thresholdSumBits (fun i => p.value x (a i)) (fun i => p.value x (b i)) k ||
        p.value x zero) := by
  have hcost : (n + 1) * ((n + 1) * 2) = 2 * (n + 1)^2 := by ring
  rw [← hcost]
  refine p.compileFin ((n + 1) * 2) (n + 1) _ ?_
  intro q hq k
  have row := q.compileOrListRaw 1 zero (hq.lt hz)
    (fun x (ij : Fin (n + 1) × Fin (n + 1)) =>
      p.value x (a ij.1) && p.value x (b ij.2)) (thresholdSplits k)
    (fun r hr ij _ =>
      let hpr := hq.trans hr
      (r.andGate (a ij.1) (b ij.2) (hpr.lt (ha ij.1)) (hpr.lt (hb ij.2))).congr
        (by
          intro x hx u
          rw [hpr.value hx (ha ij.1), hpr.value hx (hb ij.2)]))
  have hrow := row.congr
    (g := fun x _ => thresholdSumBits (fun i => p.value x (a i)) (fun i => p.value x (b i)) k ||
      p.value x zero)
    (fun x hx _ => by simp only [thresholdSumBits, hq.value hx hz])
  refine hrow.widen ?_
  simpa only [thresholdSplits, List.length_ofFn] using
    Nat.mul_le_mul_right 2 (Nat.succ_le_of_lt k.isLt)

end GateProgram

noncomputable def pathInput {n : Nat} (x : Finset (Fin n)) : List Bool :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

lemma pathInput_length {n : Nat} (x : Finset (Fin n)) : (pathInput x).length = n + 2 := by
  simp [pathInput]

abbrev WireVector (n : Nat) := Fin (n + 1) → Nat

abbrev VectorOK {n : Nat} (p : GateProgram (n + 2)) (w : WireVector n) (f : Finset (Fin n) → Nat) : Prop :=
  (∀ k, w k < p.limit) ∧
  ∀ x k, p.value (pathInput x) (w k) = decide (k.val ≤ f x)

section Vectors
variable {n : Nat}

lemma input_lt (p : GateProgram (n + 2)) {i : Nat} (hi : i < n + 2) : i < p.limit := by
  unfold GateProgram.limit
  omega

lemma pathInput_zero (p : GateProgram (n + 2)) (x : Finset (Fin n)) :
    p.value (pathInput x) n = false := by
  rw [p.value_input (pathInput_length x) (by omega)]
  simp [pathInput, List.getD_eq_getElem?_getD, List.getElem?_append_right]

lemma pathInput_one (p : GateProgram (n + 2)) (x : Finset (Fin n)) :
    p.value (pathInput x) (n + 1) = true := by
  rw [p.value_input (pathInput_length x) (by omega)]
  simp [pathInput, List.getD_eq_getElem?_getD, List.getElem?_append_right, Nat.add_sub_cancel_left]

lemma pathInput_bit (p : GateProgram (n + 2)) (x : Finset (Fin n)) (i : Fin n) :
    p.value (pathInput x) i.val = true ↔ i ∈ x := by
  rw [p.value_input (pathInput_length x) (by have := i.isLt; omega)]
  have hlt : (i : Nat) < (List.ofFn fun j : Fin n => decide (j ∈ x)).length := by simpa using i.isLt
  unfold pathInput
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hlt)]
  simp [List.getElem?_ofFn, i.isLt]

lemma vector_keep {p q : GateProgram (n + 2)} (h : p.Extends q) {w : WireVector n}
    {f : Finset (Fin n) → Nat} (hw : VectorOK p w f) : VectorOK q w f :=
  ⟨fun k => h.lt (hw.1 k), fun x k => (h.value (pathInput_length x) (hw.1 k)).trans (hw.2 x k)⟩

lemma vector_zero (p : GateProgram (n + 2)) :
    VectorOK p (fun k => if k.val = 0 then n + 1 else n) (fun _ => 0) := by
  constructor
  · intro k
    by_cases hk : k.val = 0 <;> simp only [hk, if_true, if_false] <;> apply input_lt <;> omega
  · intro x k
    by_cases h : k.val = 0 <;> simp [h, pathInput_zero, pathInput_one]

lemma vector_add (p : GateProgram (n + 2)) {a b : WireVector n} {f g : Finset (Fin n) → Nat}
    (ha : VectorOK p a f) (hb : VectorOK p b g) :
    ∃ (q : GateProgram (n + 2)) (w : WireVector n), p.Extends q ∧ q.size ≤ p.size + 2 * (n + 1)^2 ∧
      VectorOK q w (fun x => f x + g x) := by
  let c := p.thresholdAddBits n (input_lt p (by omega)) a b ha.1 hb.1
  refine ⟨c.after, c.tap, c.append_only, c.size_le, c.tap_lt, ?_⟩
  intro x k
  rw [c.eval _ (pathInput_length x) k]
  simp only [ha.2, hb.2, pathInput_zero, Bool.or_false]
  exact GateProgram.thresholdSumBits_eval k (f x) (g x)

lemma vector_max (p : GateProgram (n + 2)) {a b : WireVector n} {f g : Finset (Fin n) → Nat}
    (ha : VectorOK p a f) (hb : VectorOK p b g) :
    ∃ (q : GateProgram (n + 2)) (w : WireVector n), p.Extends q ∧ q.size ≤ p.size + (n + 1) ∧
      VectorOK q w (fun x => max (f x) (g x)) := by
  let c := p.compileFin 1 (n + 1) (fun x k => p.value x (a k) || p.value x (b k))
    (fun q hq k => (q.orGate (a k) (b k) (hq.lt (ha.1 k)) (hq.lt (hb.1 k))).congr
      (fun x hx _ => by rw [hq.value hx (ha.1 k), hq.value hx (hb.1 k)]))
  refine ⟨c.after, c.tap, c.append_only, by simpa using c.size_le, c.tap_lt, ?_⟩
  intro x k
  rw [c.eval _ (pathInput_length x) k, ha.2, hb.2]
  simp [le_max_iff]

lemma vector_sums {J : Type*} (L : List J) (w : J → WireVector n) (f : J → Finset (Fin n) → Nat)
    (p : GateProgram (n + 2)) (hw : ∀ j ∈ L, VectorOK p (w j) (f j)) :
    ∃ (q : GateProgram (n + 2)) (a : WireVector n), p.Extends q ∧
      q.size ≤ p.size + 2 * (n + 1)^2 * L.length ∧
      VectorOK q a (fun x => (L.map fun j => f j x).sum) := by
  induction L with
  | nil =>
    exact ⟨p, _, GateProgram.Extends.refl p, by simp, by simpa using vector_zero p⟩
  | cons j L ih =>
    obtain ⟨q, a, hpq, hq, hqa⟩ := ih (fun j hj => hw j (List.mem_cons_of_mem _ hj))
    obtain ⟨r, b, hqr, hr, hrb⟩ := vector_add q
      (vector_keep hpq (hw j List.mem_cons_self)) hqa
    refine ⟨r, b, hpq.trans hqr, ?_, ?_⟩
    · simp only [List.length_cons, Nat.mul_succ]
      omega
    · simpa using hrb

lemma vector_pick (p : GateProgram (n + 2)) (i : Fin 3 → Fin n)
    {a : WireVector n} {f : Finset (Fin n) → Nat} (ha : VectorOK p a f) :
    ∃ (q : GateProgram (n + 2)) (w : WireVector n), p.Extends q ∧ q.size ≤ p.size + (n + 1) + 2 ∧
      VectorOK q w (fun x => if ∀ s, i s ∈ x then 1 + f x else 0) := by
  have ht (s : Fin 3) : (i s).val < n + 2 := by have := (i s).isLt; omega
  let c₁ := p.andGate (i 0).val (i 1).val (input_lt _ (ht 0)) (input_lt _ (ht 1))
  let c₂ := c₁.after.andGate (c₁.tap ()) (i 2).val (c₁.tap_lt ()) (input_lt _ (ht 2))
  let q := c₂.after
  have hpq : p.Extends q := c₁.append_only.trans c₂.append_only
  have he (x : Finset (Fin n)) : q.value (pathInput x) (c₂.tap ()) = true ↔ ∀ s, i s ∈ x := by
    rw [c₂.eval _ (pathInput_length x) (), c₁.eval _ (pathInput_length x) ()]
    simp only [Bool.and_eq_true, pathInput_bit]
    constructor
    · intro h s
      fin_cases s
      · exact h.1.1
      · exact h.1.2
      · exact h.2
    · intro H
      exact ⟨⟨H 0, H 1⟩, H 2⟩
  let src (k : Fin (n + 1)) : Fin (n + 1) := ⟨k.val - 1, by have := k.isLt; omega⟩
  let c := q.compileFin 1 (n + 1) (fun x k => if k.val = 0 then q.value x (n + 1)
    else q.value x (c₂.tap ()) && q.value x (a (src k))) (fun r hqr k => by
      by_cases H : k.val = 0
      · refine ((GateBlock.existing r (fun _ : Unit => n + 1) (fun _ => input_lt r (by omega))).congr
           (g := fun x _ => if k.val = 0 then q.value x (n + 1) else
               q.value x (c₂.tap ()) && q.value x (a (src k))) ?_).widen (by omega)
        exact fun x hx _ => by rw [if_pos H, hqr.value hx (input_lt q (by omega))]
      · have hu := c₂.tap_lt ()
        have hv := hpq.lt (ha.1 (src k))
        refine (r.andGate (c₂.tap ()) (a (src k)) (hqr.lt hu) (hqr.lt hv)).congr ?_
        exact fun x hx _ => by rw [if_neg H, hqr.value hx hu, hqr.value hx hv])
  refine ⟨c.after, c.tap, hpq.trans c.append_only, ?_, c.tap_lt, ?_⟩
  · have h₁ := c₁.size_le
    have h₂ := c₂.size_le
    have h₃ := c.size_le
    simp only [Nat.mul_one] at h₃
    change c.after.size ≤ p.size + (n + 1) + 2
    have h₂' : q.size ≤ c₁.after.size + 1 := h₂
    omega
  · intro x k
    rw [c.eval _ (pathInput_length x) k]
    by_cases hk : k.val = 0
    · simp [hk, pathInput_one]
    · rw [if_neg hk, (vector_keep hpq ha).2]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, he, decide_eq_true_eq]
      change ((∀ s, i s ∈ x) ∧ k.val - 1 ≤ f x) ↔ k.val ≤ if ∀ s, i s ∈ x then 1 + f x else 0
      by_cases H : ∀ s, i s ∈ x
      · rw [if_pos H, and_iff_right H]
        omega
      · rw [if_neg H]
        exact ⟨fun h => (H h.1).elim, fun h => (hk (Nat.eq_zero_of_le_zero h)).elim⟩

end Vectors

open SimpleGraph

lemma vector_maxs {J : Type*} {n : Nat} (L : List J)
    (p : GateProgram (n + 2)) (cost : Nat) (f : J → Finset (Fin n) → Nat)
    (each : ∀ j ∈ L, ∀ q, p.Extends q → ∃ (u : GateProgram (n + 2)) (w : WireVector n),
      q.Extends u ∧ u.size ≤ q.size + cost ∧ VectorOK u w (f j)) :
    ∃ (q : GateProgram (n + 2)) (w : WireVector n), p.Extends q ∧
      q.size ≤ p.size + (cost + (n + 1)) * L.length ∧
      VectorOK q w (fun x => (L.map fun j => f j x).foldr max 0) := by
  induction L with
  | nil => exact ⟨p, _, GateProgram.Extends.refl p, by simp, vector_zero p⟩
  | cons j L ih =>
    obtain ⟨q, w, hq, hqs, hqw⟩ := ih (fun a ha => each a (List.mem_cons_of_mem _ ha))
    obtain ⟨u, a, hu, hus, hua⟩ := each j List.mem_cons_self q hq
    obtain ⟨v, b, hv, hvs, hvb⟩ := vector_max u hua (vector_keep hu hqw)
    refine ⟨v, b, hq.trans (hu.trans hv), ?_, hvb⟩
    simp only [List.length_cons, Nat.mul_succ]
    omega

lemma list_foldMax_toList {J : Type*} (L : Finset J) (f : J → Nat) :
    (L.toList.map f).foldr max 0 = L.sup f := by
  have h : ∀ (K : List J) (g : Nat), (K.map f).foldr max 0 ≤ g ↔ ∀ j ∈ K, f j ≤ g := by
    intro K g
    induction K with
    | nil => simp
    | cons j K ih => simp [max_le_iff, ih, or_imp, forall_and]
  apply le_antisymm
  · exact (h _ _).2 fun j hj => Finset.le_sup (Finset.mem_toList.mp hj)
  · exact Finset.sup_le fun j hj => (h _ _).1 le_rfl j (Finset.mem_toList.mpr hj)

section Compile
variable {n t : Nat} {T : SimpleGraph (Fin t)} (h : T.IsTree) (r : Fin t)
variable (S : Fin n → Finset (Fin t)) (g : Fin n → Fin n → Bool)
variable [Fintype (PathIndex g)] (d : PathIndex g → Fin t)

noncomputable def nodeVal (v : Fin t) (x : Finset (Fin n)) : Nat :=
  Opt (fun i : PathIndex g => foot S i.val) (active h r d (enabledPaths g x) v)

def optionCost (n t : Nat) : Nat := 2 * (n + 1)^2 * t + (n + 1) + 2

def rowUnit (n t : Nat) : Nat := optionCost n t + (n + 1)

lemma compile_option (v : Fin t) (a : Option (PathIndex g)) (ha : a ∈ optionRows d v)
    (hd : ∀ i, d i ∈ foot S i.val)
    (p : GateProgram (n + 2)) (w : Fin t → WireVector n)
    (hw : ∀ b, Depth h r v < Depth h r b → VectorOK p (w b) (nodeVal h r S g d b)) :
    ∃ (q : GateProgram (n + 2)) (tap : WireVector n), p.Extends q ∧ q.size ≤ p.size + optionCost n t ∧
      VectorOK q tap (fun x => optionValue h r (fun i : PathIndex g => foot S i.val) d (enabledPaths g x) v a) := by
  classical
  let C := a.elim {v} (fun i => foot S i.val)
  have hv : v ∈ C := by
    cases a with
    | none => exact Finset.mem_singleton_self v
    | some i => exact ((mem_optionRows_some d).mp ha) ▸ hd i
  let B := branches h r v C
  have hb b (hb : b ∈ B.toList) := hw b (boundary_depth h r hv
    ((mem_branches h r).mp (Finset.mem_toList.mp hb)))
  obtain ⟨q, u, hpq, hq, hqu⟩ := vector_sums B.toList w (nodeVal h r S g d) p hb
  have hqu' : VectorOK q u (fun x => ∑ b ∈ B, nodeVal h r S g d b x) := by
    simpa [Finset.sum_toList] using hqu
  have ht : B.toList.length ≤ t := by simpa using Finset.card_le_univ B
  have hq' := hq.trans (Nat.add_le_add_left (Nat.mul_le_mul_left (2 * (n + 1)^2) ht) p.size)
  cases a with
  | none =>
    refine ⟨q, u, hpq, ?_, hqu'⟩
    unfold optionCost
    omega
  | some i =>
    obtain ⟨q', w', hqq, hq'', hw'⟩ := vector_pick q i.val hqu'
    refine ⟨q', w', hpq.trans hqq, ?_, ?_⟩
    · unfold optionCost
      omega
    · simpa [optionValue, C, B, nodeVal, mem_enabledPaths] using hw'

lemma compile_row (v : Fin t) (hd : ∀ i : PathIndex g,
    d i ∈ foot S i.val ∧ ∀ w ∈ foot S i.val, Below h r (d i) w)
    (hc : ∀ i : PathIndex g, TreeConvex h (foot S i.val))
    (p : GateProgram (n + 2)) (w : Fin t → WireVector n)
    (hw : ∀ b, Depth h r v < Depth h r b → VectorOK p (w b) (nodeVal h r S g d b)) :
    ∃ (q : GateProgram (n + 2)) (tap : WireVector n), p.Extends q ∧
      q.size ≤ p.size + rowUnit n t * (optionRows d v).card ∧
      VectorOK q tap (nodeVal h r S g d v) := by
  classical
  obtain ⟨q, tap, hpq, hq, ht⟩ := vector_maxs (optionRows d v).toList p (optionCost n t)
    (fun a x => optionValue h r (fun i : PathIndex g => foot S i.val) d (enabledPaths g x) v a)
    (fun a ha u hpu => compile_option h r S g d v a (Finset.mem_toList.mp ha)
      (fun i => (hd i).1) u w (fun b hb => vector_keep hpu (hw b hb)))
  refine ⟨q, tap, hpq, ?_, ht.1, ?_⟩
  · simpa [rowUnit] using hq
  · intro x k
    change q.value (pathInput x) (tap k) =
      decide (k.val ≤ Opt (fun i : PathIndex g => foot S i.val) (active h r d (enabledPaths g x) v))
    rw [opt_tree_step h r (fun i : PathIndex g => foot S i.val) d (enabledPaths g x) v hd hc]
    simpa only [list_foldMax_toList] using ht.2 x k

lemma compile_remaining
    (hd : ∀ i : PathIndex g, d i ∈ foot S i.val ∧ ∀ w ∈ foot S i.val, Below h r (d i) w)
    (hc : ∀ i : PathIndex g, TreeConvex h (foot S i.val)) (R : Finset (Fin t)) :
    ∀ (p : GateProgram (n + 2)) (w : Fin t → WireVector n),
      (∀ v, v ∉ R → VectorOK p (w v) (nodeVal h r S g d v)) →
      ∃ (q : GateProgram (n + 2)) (tap : Fin t → WireVector n), p.Extends q ∧
        q.size ≤ p.size + ∑ v ∈ R, rowUnit n t * (optionRows d v).card ∧
        ∀ v, VectorOK q (tap v) (nodeVal h r S g d v) := by
  classical
  refine Finset.strongInductionOn R ?_
  intro R ih p w hw
  by_cases hR : R.Nonempty
  · obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image R (Depth h r) hR
    obtain ⟨q, a, hpq, hq, ha⟩ := compile_row h r S g d v hd hc p w
      (fun b hb => hw b fun hbr => Nat.not_lt_of_ge (hmax b hbr) hb)
    have hw' b (hb : b ∉ R.erase v) :
        VectorOK q (Function.update w v a b) (nodeVal h r S g d b) := by
      by_cases e : b = v
      · subst b
        simpa using ha
      · rw [Function.update_of_ne e]
        exact vector_keep hpq (hw b fun hbr => hb (Finset.mem_erase.mpr ⟨e, hbr⟩))
    obtain ⟨u, b, hqu, hu, hb⟩ := ih (R.erase v) (Finset.erase_ssubset hv) q _ hw'
    refine ⟨u, b, hpq.trans hqu, ?_, hb⟩
    have he := Finset.sum_erase_add R (fun b => rowUnit n t * (optionRows d b).card) hv
    omega
  · have he := Finset.not_nonempty_iff_eq_empty.mp hR
    refine ⟨p, w, GateProgram.Extends.refl p, ?_, fun v => hw v (by simp [he])⟩
    simp [he]

lemma count_options :
    (∑ v : Fin t, (optionRows d v).card) = t + Fintype.card (PathIndex g) := by
  classical
  have hp (v : Fin t) : (optionRows d v).card = (rowChoices d v).card + 1 := by
    rw [optionRows, Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (Option.some_injective _)]
  rw [Finset.sum_congr rfl (fun v _ => hp v), Finset.sum_add_distrib]
  have hcount := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (PathIndex g)))
    (t := (Finset.univ : Finset (Fin t))) (f := d) (by simp)
  simp only [rowChoices, Finset.card_univ] at hcount ⊢
  rw [← hcount]
  simp [Nat.add_comm]

lemma compile_root
    (hd : ∀ i : PathIndex g, d i ∈ foot S i.val ∧ ∀ w ∈ foot S i.val, Below h r (d i) w)
    (hc : ∀ i : PathIndex g, TreeConvex h (foot S i.val)) :
    ∃ (q : GateProgram (n + 2)) (tap : WireVector n),
      q.size ≤ 12*(n+1)^2*(t+1)*(t+n^3+1) ∧
      VectorOK q tap (fun x => Opt (fun i : PathIndex g => foot S i.val) (enabledPaths g x)) := by
  classical
  obtain ⟨q, tap, _, hq, ht⟩ := compile_remaining h r S g d hd hc Finset.univ (GateProgram.empty (n+2))
    (fun _ _ => 0) (fun v hv => (hv (Finset.mem_univ v)).elim)
  have he (x : Finset (Fin n)) : active h r d (enabledPaths g x) r = enabledPaths g x := by
    ext i
    simp [mem_active, below_root]
  refine ⟨q, tap r, ?_, (ht r).1, fun x k => ?_⟩
  · have hc : Fintype.card (PathIndex g) ≤ n^3 := by
      simpa using (Fintype.card_subtype_le (FitP3 g))
    rw [← Finset.mul_sum, count_options g d] at hq
    have hu : rowUnit n t ≤ 12*(n+1)^2*(t+1) := by
      unfold rowUnit optionCost
      nlinarith
    exact (by simpa using hq : q.size ≤ rowUnit n t * (t + Fintype.card (PathIndex g))).trans
      (Nat.mul_le_mul hu (by omega))
  · simpa only [nodeVal, he] using (ht r).2 x k

end Compile

end PEqualNP.Outside.L_meta_48151_aux

open PEqualNP.Outside.L_meta_48151_aux

theorem PEqualNP.Outside.L_meta_48151 :
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∀ (n t : Nat) (T : SimpleGraph (Fin t)) (S : Fin n → Finset (Fin t)),
    T.IsTree → (∀ i, (S i).Nonempty ∧ (T.induce (↑(S i) : Set (Fin t))).Connected) →
    ∀ (g : Fin n → Fin n → Bool),
      (∀ i, g i i = false) → (∀ i j, g i j = g j i) →
      (∀ i j, i ≠ j → (g i j = true ↔ ((S i) ∩ (S j)).Nonempty)) →
      let X := Finset (Fin n)
      let alpha := fun (y : X) =>
        (y.powerset.filter (fun z => ∀ a ∈ z, ∀ b ∈ z, g a b = false)).sup Finset.card
      let admits := fun (x : X) (e : Nat) =>
        ∃ f : X → Fin n → Bool,
          (∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, g i j = false) → f y j = true) ∧
          (∀ y, y ⊆ x → ∀ j ∈ y, f y j = false) ∧
          (∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true) ∧
          let pack := Nat.rec (motive := fun _ => X → Prop) (fun _ => True)
            (fun _ prev y => ∃ (u v : X) (j : Fin n), j ∈ x ∧ prev u ∧ u ⊆ v ∧ v ⊆ y ∧
              f u j = true ∧ f v j = false)
          ∀ y l, y ⊆ x → pack l y → l ≤ alpha y + e
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin (n+1) → Fin (n+2+C.size)),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
        C.output < n+2+C.size ∧ C.size ≤ 12*(n+1)^2*(t+1)*(t+n^3+1) ∧
        ∀ (x : X) (k : Fin (n+1)),
          let input := List.ofFn (fun i : Fin n => decide (i∈x)) ++ [false,true]
          (C.wires input).getD (tap k).val false = true ↔ ¬ admits x k.val := by
  intro n t T S h hs g hirr hsym hg X alpha admits
  classical
  obtain ⟨r⟩ := h.connected.nonempty
  have hg' (i j : Fin n) (hne : i ≠ j) :
      g i j = true ↔ ((S i) ∩ (S j)).Nonempty := by
    have he : (fun a b : Fin t => Classical.propDecidable (a = b)) = instDecidableEqFin t :=
      Subsingleton.elim _ _
    have H := congrArg (fun D : DecidableEq (Fin t) =>
      @Min.min (Finset (Fin t)) (@Finset.instMin (Fin t) D) (S i) (S j)) he
    exact (hg i j hne).trans (iff_of_eq (congrArg (fun A : Finset (Fin t) => A.Nonempty) H))
  have hc (p : PathIndex g) := foot_convex h S g (fun i => (hs i).2) hirr hg' p
  choose d hd₁ hd₂ using fun p => convex_top h r (hc p) (foot_nonempty S (fun i => (hs i).1) p.val)
  letI : Fintype (PathIndex g) := Fintype.ofFinite _
  obtain ⟨p, w, hsize, hw⟩ := compile_root h r S g d (fun i => ⟨hd₁ i, hd₂ i⟩) hc
  let C := p.circuit 0
  let tap (k : Fin (n+1)) : Fin (n+2+C.size) := if hk : k.val < n then
    ⟨w ⟨k.val + 1, by omega⟩, hw.1 _⟩ else ⟨n, input_lt p (by omega)⟩
  refine ⟨C, tap, p.circuit_monotone 0, p.circuit_readsBack 0, ?_, hsize, ?_⟩
  · change 0 < n + 2 + p.size
    omega
  · intro x k input
    change p.value (pathInput x) (tap k).val = true ↔ ¬ fitAdmits g x k.val
    rw [admits_iff_opt h r S g hs hirr hsym hg']
    by_cases hk : k.val < n
    · simp only [tap, dif_pos hk, hw.2, decide_eq_true_eq]
      omega
    · simp only [tap, dif_neg hk, pathInput_zero, Bool.false_eq_true, false_iff, not_not]
      exact (path_opt_le_n S g (fun i => (hs i).1) (enabledPaths g x)).trans (Nat.le_of_not_gt hk)
