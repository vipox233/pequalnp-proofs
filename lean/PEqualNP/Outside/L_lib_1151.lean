import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1151_aux

def cutOf {n h : Nat} (a b : Fin h → Fin n) (S : Finset (Fin n)) : Finset (Fin h) :=
  (Finset.univ : Finset (Fin h)).filter (fun i => decide (a i ∈ S) != decide (b i ∈ S))

def compOf {n h : Nat} (a b : Fin h → Fin n) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun C =>
    C.Nonempty ∧ (cutOf a b C).card = 0 ∧
      ∀ D ∈ C.powerset, D.Nonempty → (cutOf a b D).card = 0 → D = C)

def strongOf {n h : Nat} (a b : Fin h → Fin n) : Finset (Fin h) :=
  (Finset.univ : Finset (Fin h)).filter (fun i =>
    ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      (decide (a i ∈ S) != decide (b i ∈ S)) = true → 3 ≤ (cutOf a b S).card)

noncomputable def goodOf {n h : Nat} (a b : Fin h → Fin n) (C : Finset (Fin n)) : Bool :=
  (strongOf a b).toList.any (fun i => decide (a i ∈ C))

noncomputable def badOf {n h : Nat} (a b : Fin h → Fin n) : Nat :=
  ((compOf a b).filter (fun C => goodOf a b C = false)).card

def decodesOf {n h : Nat} (a b : Fin h → Fin n) : Prop :=
  let sat := fun (A : Finset (Finset (Fin n))) (p : Fin h → Bool × Bool) =>
    ∃ x ∈ A, ∀ i, (decide (a i ∈ x), decide (b i ∈ x)) ≠ p i
  ∀ A B : Finset (Finset (Fin n)), (∀ p, (sat A p ↔ sat B p)) → A = B

def adjE {n h : Nat} (a b : Fin h → Fin n) (E : Finset (Fin h)) (x y : Fin n) : Prop :=
  ∃ i ∈ E, (a i = x ∧ b i = y) ∨ (b i = x ∧ a i = y)

lemma adjE_symm {n h : Nat} {a b : Fin h → Fin n} {E : Finset (Fin h)} {x y : Fin n}
    (hxy : adjE a b E x y) : adjE a b E y x := by
  rcases hxy with ⟨i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩

lemma reachE_symm {n h : Nat} {a b : Fin h → Fin n} {E : Finset (Fin h)} {x y : Fin n}
    (hxy : Relation.ReflTransGen (adjE a b E) x y) :
    Relation.ReflTransGen (adjE a b E) y x := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (adjE_symm hstep) ih

lemma reachE_mono {n h : Nat} {a b : Fin h → Fin n} {E1 E2 : Finset (Fin h)}
    (hsub : E1 ⊆ E2) {x y : Fin n} (hxy : Relation.ReflTransGen (adjE a b E1) x y) :
    Relation.ReflTransGen (adjE a b E2) x y := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨i, hi, hab⟩
    exact Relation.ReflTransGen.tail ih ⟨i, hsub hi, hab⟩

def IsPath {α : Type*} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => R x y ∧ IsPath R (y :: rest)

lemma isPath_append_left {α : Type*} {R : α → α → Prop} :
    ∀ (l1 l2 : List α), IsPath R (l1 ++ l2) → IsPath R l1
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | _ :: y :: rest, l2, h => ⟨h.1, isPath_append_left (y :: rest) l2 h.2⟩

lemma isPath_concat {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α} {b c : α}, IsPath R l → l.getLast? = some b → R b c → IsPath R (l ++ [c])
  | [], _, _, _, hlast, _ => by simp at hlast
  | [x], b, c, _, hlast, hbc => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    exact ⟨hbc, trivial⟩
  | _ :: y :: rest, b, c, h, hlast, hbc => by
    have hlast' : (y :: rest).getLast? = some b := by simpa using hlast
    exact ⟨h.1, isPath_concat h.2 hlast' hbc⟩

lemma exists_nodup_path {α : Type*} {R : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen R a b) :
    ∃ p : List α, p.head? = some a ∧ p.getLast? = some b ∧ IsPath R p ∧ p.Nodup := by
  classical
  induction h with
  | refl => exact ⟨[a], rfl, rfl, trivial, List.nodup_singleton a⟩
  | @tail b c _ hbc ih =>
    rcases ih with ⟨p, hhead, hlast, hpath, hnodup⟩
    by_cases hc : c ∈ p
    · rcases List.append_of_mem hc with ⟨p1, p2, rfl⟩
      refine ⟨p1 ++ [c], ?_, ?_, ?_, ?_⟩
      · cases p1 <;> simpa using hhead
      · simp
      · have hp : IsPath R ((p1 ++ [c]) ++ p2) := by simpa [List.append_assoc] using hpath
        exact isPath_append_left (p1 ++ [c]) p2 hp
      · have hsub : (p1 ++ [c]).Sublist ((p1 ++ [c]) ++ p2) := List.sublist_append_left _ _
        have hnd : ((p1 ++ [c]) ++ p2).Nodup := by simpa [List.append_assoc] using hnodup
        exact hnd.sublist hsub
    · refine ⟨p ++ [c], ?_, ?_, ?_, ?_⟩
      · cases p with
        | nil => simp at hhead
        | cons _ _ => simpa using hhead
      · simp
      · exact isPath_concat hpath hlast hbc
      · rw [List.nodup_append]
        exact ⟨hnodup, List.nodup_singleton c, fun x hx y hy => by
          simp only [List.mem_singleton] at hy
          subst hy
          exact fun h => hc (h ▸ hx)⟩

lemma cut_eq_zero_iff {n h : Nat} (a b : Fin h → Fin n) (S : Finset (Fin n)) :
    (cutOf a b S).card = 0 ↔ ∀ i : Fin h, (a i ∈ S ↔ b i ∈ S) := by
  unfold cutOf
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro H i
    have hi := H (Finset.mem_univ i)
    by_cases h1 : a i ∈ S <;> by_cases h2 : b i ∈ S <;> simp_all
  · intro H i _
    have hi := H i
    by_cases h1 : a i ∈ S <;> by_cases h2 : b i ∈ S <;> simp_all

lemma cut_mem_iff {n h : Nat} (a b : Fin h → Fin n) (S : Finset (Fin n)) (i : Fin h) :
    i ∈ cutOf a b S ↔ ¬ (a i ∈ S ↔ b i ∈ S) := by
  simp only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h1 : a i ∈ S <;> by_cases h2 : b i ∈ S <;> simp [h1, h2]

lemma cut_compl {n h : Nat} (a b : Fin h → Fin n) (S : Finset (Fin n)) :
    cutOf a b (Finset.univ \ S) = cutOf a b S := by
  ext i
  simp only [cut_mem_iff, Finset.mem_sdiff, Finset.mem_univ, true_and]
  by_cases h1 : a i ∈ S <;> by_cases h2 : b i ∈ S <;> simp [h1, h2]

open Classical in
lemma mem_compOf_iff_reach {n h : Nat} (a b : Fin h → Fin n) (C : Finset (Fin n)) :
    C ∈ compOf a b ↔
      ∃ x : Fin n, C = Finset.univ.filter (fun y =>
        @Relation.ReflTransGen (Fin n) (adjE a b Finset.univ) x y) := by
  have hcomp_ok : ∀ x : Fin n,
      (Finset.univ.filter (fun y => Relation.ReflTransGen (adjE a b Finset.univ) x y)) ∈ compOf a b := by
    intro x
    let K := Finset.univ.filter (fun y => Relation.ReflTransGen (adjE a b Finset.univ) x y)
    have hK_cut : (cutOf a b K).card = 0 := by
      rw [cut_eq_zero_iff]
      intro i
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => Relation.ReflTransGen.tail h ⟨i, Finset.mem_univ i, Or.inl ⟨rfl, rfl⟩⟩,
             fun h => Relation.ReflTransGen.tail h ⟨i, Finset.mem_univ i, Or.inr ⟨rfl, rfl⟩⟩⟩
    simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨x, by simp [K, Relation.ReflTransGen.refl]⟩, hK_cut, fun D hD hDne hDcut => ?_⟩
    have hDsub : D ⊆ K := Finset.mem_powerset.mp hD
    rw [cut_eq_zero_iff] at hDcut
    rcases hDne with ⟨y, hyD⟩
    have hyK : Relation.ReflTransGen (adjE a b Finset.univ) x y := (Finset.mem_filter.mp (hDsub hyD)).2
    apply Finset.Subset.antisymm hDsub
    intro z hzK
    have hzR : Relation.ReflTransGen (adjE a b Finset.univ) x z := (Finset.mem_filter.mp hzK).2
    have hyz : Relation.ReflTransGen (adjE a b Finset.univ) y z := (reachE_symm hyK).trans hzR
    clear hzK hzR
    induction hyz with
    | refl => exact hyD
    | tail _ hstep ih =>
      rcases hstep with ⟨i, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact (hDcut i).mp ih
      · exact (hDcut i).mpr ih
  constructor
  · intro hC
    simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hC
    rcases hC with ⟨⟨x, hxC⟩, hCcut, hCmin⟩
    refine ⟨x, ?_⟩
    rw [cut_eq_zero_iff] at hCcut
    let K := Finset.univ.filter (fun y => Relation.ReflTransGen (adjE a b Finset.univ) x y)
    have hKsub : K ⊆ C := by
      intro y hy
      have hxy : Relation.ReflTransGen (adjE a b Finset.univ) x y := (Finset.mem_filter.mp hy).2
      clear hy
      induction hxy with
      | refl => exact hxC
      | tail _ hstep ih =>
        rcases hstep with ⟨i, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact (hCcut i).mp ih
        · exact (hCcut i).mpr ih
    have hKmem := hcomp_ok x
    simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hKmem
    exact (hCmin K (Finset.mem_powerset.mpr hKsub) hKmem.1 hKmem.2.1).symm
  · rintro ⟨x, rfl⟩
    exact hcomp_ok x

lemma compOf_disjoint {n h : Nat} (a b : Fin h → Fin n) {C1 C2 : Finset (Fin n)}
    (h1 : C1 ∈ compOf a b) (h2 : C2 ∈ compOf a b) (hne : C1 ≠ C2) : Disjoint C1 C2 := by
  classical
  rcases (mem_compOf_iff_reach a b C1).mp h1 with ⟨x1, rfl⟩
  rcases (mem_compOf_iff_reach a b C2).mp h2 with ⟨x2, rfl⟩
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  apply hne
  have h1z : Relation.ReflTransGen (adjE a b Finset.univ) x1 z := (Finset.mem_filter.mp hz1).2
  have h2z : Relation.ReflTransGen (adjE a b Finset.univ) x2 z := (Finset.mem_filter.mp hz2).2
  have h12 : Relation.ReflTransGen (adjE a b Finset.univ) x1 x2 := h1z.trans (reachE_symm h2z)
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hw => (reachE_symm h12).trans hw, fun hw => h12.trans hw⟩

lemma sum_card_compOf {n h : Nat} (a b : Fin h → Fin n) :
    (compOf a b).sum Finset.card = n := by
  classical
  have hdisj : (compOf a b : Set (Finset (Fin n))).PairwiseDisjoint id := by
    intro C1 h1 C2 h2 hne
    exact compOf_disjoint a b h1 h2 hne
  have hunion : (compOf a b).biUnion id = Finset.univ := by
    ext x
    simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
    let K := Finset.univ.filter (fun y => Relation.ReflTransGen (adjE a b Finset.univ) x y)
    exact ⟨K, (mem_compOf_iff_reach a b K).mpr ⟨x, rfl⟩, by simp [K, Relation.ReflTransGen.refl]⟩
  have hcard := Finset.card_biUnion hdisj
  rw [hunion, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard.symm

lemma sum_edges_compOf {n h : Nat} (a b : Fin h → Fin n) :
    (compOf a b).sum (fun C => ((Finset.univ : Finset (Fin h)).filter (fun i => a i ∈ C)).card) = h := by
  classical
  have hdisj : (compOf a b : Set (Finset (Fin n))).PairwiseDisjoint
      (fun C => (Finset.univ : Finset (Fin h)).filter (fun i => a i ∈ C)) := by
    intro C1 h1 C2 h2 hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hD := compOf_disjoint a b h1 h2 hne
    exact Finset.disjoint_left.mp hD (Finset.mem_filter.mp hi1).2 (Finset.mem_filter.mp hi2).2
  have hunion : (compOf a b).biUnion (fun C => (Finset.univ : Finset (Fin h)).filter (fun i => a i ∈ C)) =
      Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    let K := Finset.univ.filter (fun y => Relation.ReflTransGen (adjE a b Finset.univ) (a i) y)
    exact ⟨K, (mem_compOf_iff_reach a b K).mpr ⟨a i, rfl⟩, by simp [K, Relation.ReflTransGen.refl]⟩
  have hcard := Finset.card_biUnion hdisj
  rw [hunion, Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard.symm

lemma goodOf_eq_true_iff {n h : Nat} (a b : Fin h → Fin n) (C : Finset (Fin n)) :
    goodOf a b C = true ↔ ∃ i ∈ strongOf a b, a i ∈ C := by
  simp [goodOf, List.any_eq_true]

noncomputable def compIn {n h : Nat} (a b : Fin h → Fin n) (V : Finset (Fin n)) (E : Finset (Fin h))
    (x : Fin n) : Finset (Fin n) :=
  by classical exact V.filter (fun y => Relation.ReflTransGen (adjE a b E) x y)

noncomputable def compCount {n h : Nat} (a b : Fin h → Fin n) (V : Finset (Fin n))
    (E : Finset (Fin h)) : Nat :=
  (V.image (compIn a b V E)).card

lemma compIn_closed {n h : Nat} (a b : Fin h → Fin n) (V : Finset (Fin n)) (E : Finset (Fin h))
    (hEV : ∀ i ∈ E, a i ∈ V ∧ b i ∈ V) (x : Fin n) (i : Fin h) (hi : i ∈ E) :
    a i ∈ compIn a b V E x ↔ b i ∈ compIn a b V E x := by
  classical
  simp only [compIn, Finset.mem_filter]
  exact ⟨fun ⟨_, hr⟩ => ⟨(hEV i hi).2, Relation.ReflTransGen.tail hr ⟨i, hi, Or.inl ⟨rfl, rfl⟩⟩⟩,
         fun ⟨_, hr⟩ => ⟨(hEV i hi).1, Relation.ReflTransGen.tail hr ⟨i, hi, Or.inr ⟨rfl, rfl⟩⟩⟩⟩

lemma compCount_insert {n h : Nat} (a b : Fin h → Fin n) (V : Finset (Fin n))
    (E : Finset (Fin h)) (e : Fin h)
    (hEV : ∀ i ∈ E, a i ∈ V ∧ b i ∈ V) (heV : a e ∈ V ∧ b e ∈ V) :
    (b e ∈ compIn a b V E (a e) → compCount a b V (insert e E) = compCount a b V E) ∧
    (b e ∉ compIn a b V E (a e) → compCount a b V (insert e E) + 1 = compCount a b V E) := by
  classical
  have hstep_same : b e ∈ compIn a b V E (a e) →
      ∀ x y : Fin n, Relation.ReflTransGen (adjE a b (insert e E)) x y ↔
        Relation.ReflTransGen (adjE a b E) x y := by
    intro hbe x y
    have hab : Relation.ReflTransGen (adjE a b E) (a e) (b e) := by
      simp only [compIn, Finset.mem_filter] at hbe
      exact hbe.2
    constructor
    · intro hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        rcases hstep with ⟨i, hi, hor⟩
        rcases Finset.mem_insert.mp hi with rfl | hiE
        · rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ih.trans hab
          · exact ih.trans (reachE_symm hab)
        · exact Relation.ReflTransGen.tail ih ⟨i, hiE, hor⟩
    · exact reachE_mono (Finset.subset_insert e E)
  constructor
  · intro hbe
    unfold compCount
    congr 1
    refine Finset.image_congr fun x _ => ?_
    ext y
    simp only [compIn, Finset.mem_filter]
    exact and_congr_right fun _ => hstep_same hbe x y
  · intro hnot
    let Ca := compIn a b V E (a e)
    let Cb := compIn a b V E (b e)
    have hCab_ne : Ca ≠ Cb := by
      intro heq
      apply hnot
      rw [show compIn a b V E (a e) = Ca from rfl, heq]
      simp only [Cb, compIn, Finset.mem_filter]
      exact ⟨heV.2, Relation.ReflTransGen.refl⟩
    have hnew : ∀ x ∈ V, compIn a b V (insert e E) x =
        if compIn a b V E x = Ca ∨ compIn a b V E x = Cb then Ca ∪ Cb else compIn a b V E x := by
      intro x hxV
      have hreach_ab : ∀ y : Fin n,
          Relation.ReflTransGen (adjE a b (insert e E)) x y ↔
            Relation.ReflTransGen (adjE a b E) x y ∨
            ((Relation.ReflTransGen (adjE a b E) x (a e) ∨ Relation.ReflTransGen (adjE a b E) x (b e)) ∧
             (Relation.ReflTransGen (adjE a b E) (a e) y ∨ Relation.ReflTransGen (adjE a b E) (b e) y)) := by
        intro y
        constructor
        · intro hxy
          induction hxy with
          | refl => exact Or.inl Relation.ReflTransGen.refl
          | @tail u v _ hstep ih =>
            rcases hstep with ⟨i, hi, hor⟩
            rcases Finset.mem_insert.mp hi with rfl | hiE
            · rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rcases ih with hxa | ⟨hxab, _⟩
                · exact Or.inr ⟨Or.inl hxa, Or.inr Relation.ReflTransGen.refl⟩
                · exact Or.inr ⟨hxab, Or.inr Relation.ReflTransGen.refl⟩
              · rcases ih with hxb | ⟨hxab, _⟩
                · exact Or.inr ⟨Or.inr hxb, Or.inl Relation.ReflTransGen.refl⟩
                · exact Or.inr ⟨hxab, Or.inl Relation.ReflTransGen.refl⟩
            · have huv : adjE a b E u v := ⟨i, hiE, hor⟩
              rcases ih with hxu | ⟨hxab, habu⟩
              · exact Or.inl (Relation.ReflTransGen.tail hxu huv)
              · rcases habu with hau | hbu
                · exact Or.inr ⟨hxab, Or.inl (Relation.ReflTransGen.tail hau huv)⟩
                · exact Or.inr ⟨hxab, Or.inr (Relation.ReflTransGen.tail hbu huv)⟩
        · rintro (hxy | ⟨hxa | hxb, hay | hby⟩)
          · exact reachE_mono (Finset.subset_insert e E) hxy
          · exact (reachE_mono (Finset.subset_insert e E) hxa).trans
              (reachE_mono (Finset.subset_insert e E) hay)
          · exact ((reachE_mono (Finset.subset_insert e E) hxa).tail
              ⟨e, Finset.mem_insert_self e E, Or.inl ⟨rfl, rfl⟩⟩).trans
              (reachE_mono (Finset.subset_insert e E) hby)
          · exact ((reachE_mono (Finset.subset_insert e E) hxb).tail
              ⟨e, Finset.mem_insert_self e E, Or.inr ⟨rfl, rfl⟩⟩).trans
              (reachE_mono (Finset.subset_insert e E) hay)
          · exact (reachE_mono (Finset.subset_insert e E) hxb).trans
              (reachE_mono (Finset.subset_insert e E) hby)
      have hiff_a : compIn a b V E x = Ca ↔ Relation.ReflTransGen (adjE a b E) x (a e) := by
        constructor
        · intro heq
          have ha_mem : a e ∈ compIn a b V E x := by
            rw [heq]; simp [Ca, compIn, heV.1, Relation.ReflTransGen.refl]
          exact (Finset.mem_filter.mp ha_mem).2
        · intro hxa
          ext y; simp only [Ca, compIn, Finset.mem_filter]
          exact and_congr_right fun _ => ⟨fun h => (reachE_symm hxa).trans h, fun h => hxa.trans h⟩
      have hiff_b : compIn a b V E x = Cb ↔ Relation.ReflTransGen (adjE a b E) x (b e) := by
        constructor
        · intro heq
          have hb_mem : b e ∈ compIn a b V E x := by
            rw [heq]; simp [Cb, compIn, heV.2, Relation.ReflTransGen.refl]
          exact (Finset.mem_filter.mp hb_mem).2
        · intro hxb
          ext y; simp only [Cb, compIn, Finset.mem_filter]
          exact and_congr_right fun _ => ⟨fun h => (reachE_symm hxb).trans h, fun h => hxb.trans h⟩
      split_ifs with hcond
      · have hxab : Relation.ReflTransGen (adjE a b E) x (a e) ∨ Relation.ReflTransGen (adjE a b E) x (b e) := by
          rcases hcond with h1 | h2
          · exact Or.inl (hiff_a.mp h1)
          · exact Or.inr (hiff_b.mp h2)
        ext y
        simp only [compIn, Finset.mem_filter, Finset.mem_union, Ca, Cb]
        rw [hreach_ab y]
        constructor
        · rintro ⟨hyV, hxy | ⟨_, hay | hby⟩⟩
          · rcases hxab with hxa | hxb
            · exact Or.inl ⟨hyV, (reachE_symm hxa).trans hxy⟩
            · exact Or.inr ⟨hyV, (reachE_symm hxb).trans hxy⟩
          · exact Or.inl ⟨hyV, hay⟩
          · exact Or.inr ⟨hyV, hby⟩
        · rintro (⟨hyV, hay⟩ | ⟨hyV, hby⟩)
          · exact ⟨hyV, Or.inr ⟨hxab, Or.inl hay⟩⟩
          · exact ⟨hyV, Or.inr ⟨hxab, Or.inr hby⟩⟩
      · push_neg at hcond
        have hna : ¬ Relation.ReflTransGen (adjE a b E) x (a e) := fun h => hcond.1 (hiff_a.mpr h)
        have hnb : ¬ Relation.ReflTransGen (adjE a b E) x (b e) := fun h => hcond.2 (hiff_b.mpr h)
        ext y
        simp only [compIn, Finset.mem_filter]
        rw [hreach_ab y]
        tauto
    let S0 := V.image (compIn a b V E)
    let S1 := V.image (compIn a b V (insert e E))
    have hCa_mem : Ca ∈ S0 := Finset.mem_image.mpr ⟨a e, heV.1, rfl⟩
    have hCb_mem : Cb ∈ S0 := Finset.mem_image.mpr ⟨b e, heV.2, rfl⟩
    have hCab_notin : Ca ∪ Cb ∉ (S0.erase Ca).erase Cb := by
      intro hmem
      have hS0 := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem)
      rcases Finset.mem_image.mp hS0 with ⟨z, _, hz⟩
      have hza : a e ∈ compIn a b V E z := by
        rw [hz]; exact Finset.mem_union_left _ (by simp [Ca, compIn, heV.1, Relation.ReflTransGen.refl])
      have hzb : b e ∈ compIn a b V E z := by
        rw [hz]; exact Finset.mem_union_right _ (by simp [Cb, compIn, heV.2, Relation.ReflTransGen.refl])
      have h1 : Relation.ReflTransGen (adjE a b E) z (a e) := (Finset.mem_filter.mp hza).2
      have h2 : Relation.ReflTransGen (adjE a b E) z (b e) := (Finset.mem_filter.mp hzb).2
      apply hnot
      simp only [compIn, Finset.mem_filter]
      exact ⟨heV.2, (reachE_symm h1).trans h2⟩
    have hS1_eq : S1 = insert (Ca ∪ Cb) ((S0.erase Ca).erase Cb) := by
      ext K
      simp only [S1, S0, Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨x, hxV, rfl⟩
        rw [hnew x hxV]
        split_ifs with hcond
        · exact Or.inl rfl
        · push_neg at hcond
          exact Or.inr ⟨hcond.2, hcond.1, ⟨x, hxV, rfl⟩⟩
      · rintro (rfl | ⟨hneB, hneA, ⟨x, hxV, rfl⟩⟩)
        · refine ⟨a e, heV.1, ?_⟩
          rw [hnew (a e) heV.1]
          simp [Ca]
        · refine ⟨x, hxV, ?_⟩
          rw [hnew x hxV]
          simp [hneA, hneB]
    change S1.card + 1 = S0.card
    rw [hS1_eq, Finset.card_insert_of_notMem hCab_notin,
        Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hCab_ne.symm, hCb_mem⟩),
        Finset.card_erase_of_mem hCa_mem]
    have h2 : 2 ≤ S0.card := by
      have hsub : ({Ca, Cb} : Finset (Finset (Fin n))) ⊆ S0 := by
        intro K hK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hK
        rcases hK with rfl | rfl <;> assumption
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hCab_ne] at this
      exact this
    omega

lemma compCount_add_card_ge {n h : Nat} (a b : Fin h → Fin n) (V : Finset (Fin n))
    (E : Finset (Fin h)) (hEV : ∀ i ∈ E, a i ∈ V ∧ b i ∈ V) :
    V.card ≤ compCount a b V E + E.card := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, add_zero]
    unfold compCount
    have hinj : Set.InjOn (compIn a b V ∅) (V : Set (Fin n)) := by
      intro x hx y hy hxy
      have hx_mem : x ∈ compIn a b V ∅ y := by
        rw [← hxy]; simp [compIn, Finset.mem_coe.mp hx, Relation.ReflTransGen.refl]
      have hreach : Relation.ReflTransGen (adjE a b ∅) y x := (Finset.mem_filter.mp hx_mem).2
      cases hreach with
      | refl => rfl
      | tail _ hstep => rcases hstep with ⟨_, hi, _⟩; simp at hi
    rw [Finset.card_image_of_injOn hinj]
  | @insert e s he ih =>
    have hsV : ∀ i ∈ s, a i ∈ V ∧ b i ∈ V := fun i hi => hEV i (Finset.mem_insert_of_mem hi)
    have heV := hEV e (Finset.mem_insert_self e s)
    have hih := ih hsV
    have hci := compCount_insert a b V s e hsV heV
    rw [Finset.card_insert_of_notMem he]
    by_cases hbe : b e ∈ compIn a b V s (a e)
    · rw [hci.1 hbe]; omega
    · have := hci.2 hbe; omega

lemma compCount_eq_one_of_comp {n h : Nat} (a b : Fin h → Fin n)
    {C : Finset (Fin n)} (hC : C ∈ compOf a b) :
    let EC := (Finset.univ : Finset (Fin h)).filter (fun i => a i ∈ C)
    (∀ i ∈ EC, a i ∈ C ∧ b i ∈ C) ∧ compCount a b C EC = 1 := by
  classical
  intro EC
  have hCcut : (cutOf a b C).card = 0 := (Finset.mem_filter.mp hC).2.2.1
  rw [cut_eq_zero_iff] at hCcut
  have hEV : ∀ i ∈ EC, a i ∈ C ∧ b i ∈ C := by
    intro i hi
    have hai : a i ∈ C := (Finset.mem_filter.mp hi).2
    exact ⟨hai, (hCcut i).mp hai⟩
  refine ⟨hEV, ?_⟩
  rcases (mem_compOf_iff_reach a b C).mp hC with ⟨x0, rfl⟩
  have hreach_in : ∀ x y, x ∈ Finset.univ.filter (fun z => Relation.ReflTransGen (adjE a b Finset.univ) x0 z) →
      Relation.ReflTransGen (adjE a b Finset.univ) x y →
      Relation.ReflTransGen (adjE a b EC) x y := by
    intro x y hx hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | @tail u v hxu hstep ih =>
      have huC : u ∈ Finset.univ.filter (fun z => Relation.ReflTransGen (adjE a b Finset.univ) x0 z) := by
        have hxR := (Finset.mem_filter.mp hx).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hxR.trans hxu
      rcases hstep with ⟨i, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Relation.ReflTransGen.tail ih ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, huC⟩, Or.inl ⟨rfl, rfl⟩⟩
      · have hai : a i ∈ Finset.univ.filter (fun z => Relation.ReflTransGen (adjE a b Finset.univ) x0 z) :=
          (hCcut i).mpr huC
        exact Relation.ReflTransGen.tail ih ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩, Or.inr ⟨rfl, rfl⟩⟩
  have hx0C : x0 ∈ Finset.univ.filter (fun z => Relation.ReflTransGen (adjE a b Finset.univ) x0 z) := by
    simp [Relation.ReflTransGen.refl]
  have himg : (Finset.univ.filter (fun z => Relation.ReflTransGen (adjE a b Finset.univ) x0 z)).image
      (compIn a b (Finset.univ.filter (fun z => Relation.ReflTransGen (adjE a b Finset.univ) x0 z)) EC) =
      {Finset.univ.filter (fun z => Relation.ReflTransGen (adjE a b Finset.univ) x0 z)} := by
    ext K
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      ext y
      simp only [compIn, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      intro hy
      have hxR := (Finset.mem_filter.mp hx).2
      exact hreach_in x y hx ((reachE_symm hxR).trans hy)
    · rintro rfl
      refine ⟨x0, hx0C, ?_⟩
      ext y
      simp only [compIn, Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      intro hy
      exact hreach_in x0 y hx0C hy
  unfold compCount
  rw [himg, Finset.card_singleton]

lemma exists_nonbridge_of_ge {n h : Nat} (a b : Fin h → Fin n)
    (V : Finset (Fin n)) (E : Finset (Fin h))
    (hEV : ∀ i ∈ E, a i ∈ V ∧ b i ∈ V)
    (hlt : V.card < compCount a b V E + E.card) :
    ∃ e ∈ E, b e ∈ compIn a b V (E.erase e) (a e) := by
  classical
  by_contra hnone
  push_neg at hnone
  have heq : ∀ S : Finset (Fin h), S ⊆ E →
      (∀ e ∈ S, b e ∉ compIn a b V (S.erase e) (a e)) →
      V.card = compCount a b V S + S.card := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ _
      simp only [Finset.card_empty, add_zero]
      unfold compCount
      have hinj : Set.InjOn (compIn a b V ∅) (V : Set (Fin n)) := by
        intro x hx y hy hxy
        have hx_mem : x ∈ compIn a b V ∅ y := by
          rw [← hxy]; simp [compIn, Finset.mem_coe.mp hx, Relation.ReflTransGen.refl]
        have hreach : Relation.ReflTransGen (adjE a b ∅) y x := (Finset.mem_filter.mp hx_mem).2
        cases hreach with
        | refl => rfl
        | tail _ hstep => rcases hstep with ⟨_, hi, _⟩; simp at hi
      rw [Finset.card_image_of_injOn hinj]
    | @insert e s he ih =>
      intro hsub hnb
      have hsE : s ⊆ E := fun i hi => hsub (Finset.mem_insert_of_mem hi)
      have hsnb : ∀ i ∈ s, b i ∉ compIn a b V (s.erase i) (a i) := by
        intro i hi hmem
        apply hnb i (Finset.mem_insert_of_mem hi)
        simp only [compIn, Finset.mem_filter] at hmem ⊢
        refine ⟨hmem.1, reachE_mono ?_ hmem.2⟩
        intro j hj
        have h1 := Finset.mem_erase.mp hj
        exact Finset.mem_erase.mpr ⟨h1.1, Finset.mem_insert_of_mem h1.2⟩
      have hih := ih hsE hsnb
      have he_not : b e ∉ compIn a b V s (a e) := by
        have := hnb e (Finset.mem_insert_self e s)
        rwa [Finset.erase_insert he] at this
      have hci := (compCount_insert a b V s e (fun i hi => hEV i (hsE hi))
        (hEV e (hsub (Finset.mem_insert_self e s)))).2 he_not
      rw [Finset.card_insert_of_notMem he]
      omega
  have := heq E Finset.Subset.rfl hnone
  omega

lemma tree_all_bridges {n h : Nat} (a b : Fin h → Fin n)
    (V : Finset (Fin n)) (E : Finset (Fin h))
    (hEV : ∀ i ∈ E, a i ∈ V ∧ b i ∈ V)
    (heq : V.card = compCount a b V E + E.card)
    {e : Fin h} (he : e ∈ E) :
    b e ∉ compIn a b V (E.erase e) (a e) := by
  classical
  intro hmem
  have hge := compCount_add_card_ge a b V (E.erase e)
    (fun i hi => hEV i (Finset.mem_of_mem_erase hi))
  have hci := (compCount_insert a b V (E.erase e) e
    (fun i hi => hEV i (Finset.mem_of_mem_erase hi)) (hEV e he)).1 hmem
  rw [Finset.insert_erase he] at hci
  rw [Finset.card_erase_of_mem he] at hge
  have hpos : 1 ≤ E.card := Finset.card_pos.mpr ⟨e, he⟩
  omega

lemma good_component_edges_ge {n h : Nat} (a b : Fin h → Fin n) (hne : ∀ i, a i ≠ b i)
    {C : Finset (Fin n)} (hC : C ∈ compOf a b) (hgood : goodOf a b C = true) :
    C.card + 1 ≤ ((Finset.univ : Finset (Fin h)).filter (fun i => a i ∈ C)).card := by
  classical
  let EC := (Finset.univ : Finset (Fin h)).filter (fun i => a i ∈ C)
  rcases compCount_eq_one_of_comp a b hC with ⟨hEV, hcc1⟩
  rcases (goodOf_eq_true_iff a b C).mp hgood with ⟨i0, hi0_str, hi0C⟩
  have hi0_strong : ∀ S : Finset (Fin n), ¬ (a i0 ∈ S ↔ b i0 ∈ S) → 3 ≤ (cutOf a b S).card := by
    intro S hsep
    have hs := (Finset.mem_filter.mp hi0_str).2 S (Finset.mem_univ S)
    apply hs
    by_cases h1 : a i0 ∈ S <;> by_cases h2 : b i0 ∈ S <;> simp_all
  have hi0_EC : i0 ∈ EC := Finset.mem_filter.mpr ⟨Finset.mem_univ i0, hi0C⟩
  let E1 := EC.erase i0
  have hE1V : ∀ i ∈ E1, a i ∈ C ∧ b i ∈ C := fun i hi => hEV i (Finset.mem_of_mem_erase hi)
  have hbi0_reach : b i0 ∈ compIn a b C E1 (a i0) := by
    by_contra hnot
    let S := compIn a b C E1 (a i0)
    have haS : a i0 ∈ S := by simp [S, compIn, (hEV i0 hi0_EC).1, Relation.ReflTransGen.refl]
    have hbS : b i0 ∉ S := hnot
    have hsub : cutOf a b S ⊆ {i0} := by
      intro j hj
      rw [cut_mem_iff] at hj
      simp only [Finset.mem_singleton]
      by_contra hji0
      have hCcut : (cutOf a b C).card = 0 := (Finset.mem_filter.mp hC).2.2.1
      rw [cut_eq_zero_iff] at hCcut
      have hSsub : S ⊆ C := Finset.filter_subset _ _
      by_cases hjEC : j ∈ EC
      · have hjE1 : j ∈ E1 := Finset.mem_erase.mpr ⟨hji0, hjEC⟩
        have hcl := compIn_closed a b C E1 hE1V (a i0) j hjE1
        exact hj hcl
      · have haNC : a j ∉ C := fun h => hjEC (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
        have hbNC : b j ∉ C := fun h => haNC ((hCcut j).mpr h)
        have haNS : a j ∉ S := fun h => haNC (hSsub h)
        have hbNS : b j ∉ S := fun h => hbNC (hSsub h)
        exact hj (by simp [haNS, hbNS])
    have hle1 : (cutOf a b S).card ≤ 1 := by
      calc (cutOf a b S).card ≤ ({i0} : Finset (Fin h)).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton i0
    have hge3 := hi0_strong S (by simp [haS, hbS])
    omega
  have hccE1 : compCount a b C E1 = 1 := by
    have hci := (compCount_insert a b C E1 i0 hE1V (hEV i0 hi0_EC)).1 hbi0_reach
    rw [Finset.insert_erase hi0_EC] at hci
    rw [← hci, hcc1]
  have hge1 : C.card ≤ 1 + E1.card := by
    have := compCount_add_card_ge a b C E1 hE1V
    rwa [hccE1] at this
  by_contra hlt
  change ¬ (C.card + 1 ≤ EC.card) at hlt
  have hEC_pos : 1 ≤ EC.card := Finset.card_pos.mpr ⟨i0, hi0_EC⟩
  have hE1_card : E1.card = EC.card - 1 := Finset.card_erase_of_mem hi0_EC
  have hE1_eq : C.card = compCount a b C E1 + E1.card := by
    rw [hccE1]; omega
  have hreach1 : Relation.ReflTransGen (adjE a b E1) (a i0) (b i0) := (Finset.mem_filter.mp hbi0_reach).2
  rcases exists_nodup_path hreach1 with ⟨p, hhead, hlast, hpath, hnd⟩
  cases p with
  | nil => simp at hhead
  | cons x xs =>
    cases xs with
    | nil =>
      simp at hhead hlast
      exact hne i0 (hhead.symm.trans hlast)
    | cons y rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      rcases hpath.1 with ⟨e1, he1_E1, he1_end⟩
      let E2 := E1.erase e1
      have hE2V : ∀ i ∈ E2, a i ∈ C ∧ b i ∈ C := fun i hi => hE1V i (Finset.mem_of_mem_erase hi)
      have hbridge := tree_all_bridges a b C E1 hE1V hE1_eq he1_E1
      have hrest_in_E2 : Relation.ReflTransGen (adjE a b E2) y (b i0) := by
        have hx_notin : a i0 ∉ y :: rest := (List.nodup_cons.mp hnd).1
        have hgo : ∀ (l : List (Fin n)) (u : Fin n),
            IsPath (adjE a b E1) l → a i0 ∉ l → l.head? = some u → l.getLast? = some (b i0) →
            Relation.ReflTransGen (adjE a b E2) u (b i0) := by
          intro l
          induction l with
          | nil => intro _ _ _ hh _; simp at hh
          | cons u us ih =>
            intro u' hp hnot hh hl
            simp only [List.head?_cons, Option.some.injEq] at hh
            subst hh
            cases us with
            | nil =>
              simp at hl
              subst hl
              exact Relation.ReflTransGen.refl
            | cons v vs =>
              rcases hp.1 with ⟨j, hjE1, hjend⟩
              have hje1 : j ≠ e1 := by
                intro heq
                subst heq
                have hu_ne : u ≠ a i0 := fun h => hnot (h ▸ List.mem_cons_self)
                have hv_ne : v ≠ a i0 := fun h => hnot (List.mem_cons_of_mem _ (h ▸ List.mem_cons_self))
                rcases he1_end with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hjend with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp_all
              have hjE2 : j ∈ E2 := Finset.mem_erase.mpr ⟨hje1, hjE1⟩
              have hrest := ih v hp.2 (fun h => hnot (List.mem_cons_of_mem _ h)) rfl (by simpa using hl)
              exact Relation.ReflTransGen.head ⟨j, hjE2, hjend⟩ hrest
        exact hgo (y :: rest) y hpath.2 hx_notin rfl (by simpa using hlast)
      let S := compIn a b C E2 (a i0)
      have haS : a i0 ∈ S := by simp [S, compIn, (hEV i0 hi0_EC).1, Relation.ReflTransGen.refl]
      have hyNS : y ∉ S := by
        intro hyS
        have hxy : Relation.ReflTransGen (adjE a b E2) (a i0) y := (Finset.mem_filter.mp hyS).2
        apply hbridge
        simp only [compIn, Finset.mem_filter]
        rcases he1_end with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact ⟨(hE1V e1 he1_E1).2 |> fun h => by rwa [← h2], hxy⟩
        · rw [h1, h2]; exact ⟨(hE1V e1 he1_E1).2 |> fun h => by rwa [← h1], reachE_symm hxy⟩
      have hbNS : b i0 ∉ S := by
        intro hbS
        apply hyNS
        have h1 : Relation.ReflTransGen (adjE a b E2) (a i0) (b i0) := (Finset.mem_filter.mp hbS).2
        simp only [S, compIn, Finset.mem_filter]
        have hyC : y ∈ C := by
          rcases he1_end with ⟨_, h2⟩ | ⟨_, h2⟩
          · rw [← h2]; exact (hE1V e1 he1_E1).2
          · rw [← h2]; exact (hE1V e1 he1_E1).1
        exact ⟨hyC, h1.trans (reachE_symm hrest_in_E2)⟩
      have hsub : cutOf a b S ⊆ {i0, e1} := by
        intro j hj
        rw [cut_mem_iff] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_contra hnot
        push_neg at hnot
        have hCcut : (cutOf a b C).card = 0 := (Finset.mem_filter.mp hC).2.2.1
        rw [cut_eq_zero_iff] at hCcut
        have hSsub : S ⊆ C := Finset.filter_subset _ _
        by_cases hjEC : j ∈ EC
        · have hjE2 : j ∈ E2 := Finset.mem_erase.mpr ⟨hnot.2, Finset.mem_erase.mpr ⟨hnot.1, hjEC⟩⟩
          exact hj (compIn_closed a b C E2 hE2V (a i0) j hjE2)
        · have haNC : a j ∉ C := fun h => hjEC (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
          have hbNC : b j ∉ C := fun h => haNC ((hCcut j).mpr h)
          have haNS : a j ∉ S := fun h => haNC (hSsub h)
          have hbNS' : b j ∉ S := fun h => hbNC (hSsub h)
          exact hj (by simp [haNS, hbNS'])
      have hle2 : (cutOf a b S).card ≤ 2 := by
        calc (cutOf a b S).card ≤ ({i0, e1} : Finset (Fin h)).card := Finset.card_le_card hsub
          _ ≤ 2 := Finset.card_le_two
      have hge3 := hi0_strong S (by simp [haS, hbNS])
      omega

def flowDiv {n h : Nat} (a b : Fin h → Fin n) (f : Fin h → Int) (x : Fin n) : Int :=
  (Finset.univ : Finset (Fin h)).sum (fun e => (if a e = x then f e else 0) - (if b e = x then f e else 0))

lemma sum_flowDiv {n h : Nat} (a b : Fin h → Fin n) (f : Fin h → Int) (S : Finset (Fin n)) :
    S.sum (flowDiv a b f) =
      (Finset.univ : Finset (Fin h)).sum (fun e =>
        if a e ∈ S ∧ b e ∉ S then f e else if b e ∈ S ∧ a e ∉ S then -f e else 0) := by
  unfold flowDiv
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_sub_distrib]
  by_cases ha : a e ∈ S <;> by_cases hb : b e ∈ S <;> simp [ha, hb]

def resArc {n h : Nat} (a b : Fin h → Fin n) (E : Finset (Fin h)) (f : Fin h → Int) (x y : Fin n) : Prop :=
  ∃ e ∈ E, (a e = x ∧ b e = y ∧ f e < 1) ∨ (b e = x ∧ a e = y ∧ -1 < f e)

lemma augment_path {n h : Nat} (a b : Fin h → Fin n) (E : Finset (Fin h)) (f : Fin h → Int)
    (hbound : ∀ e, -1 ≤ f e ∧ f e ≤ 1) (hsupp : ∀ e, e ∉ E → f e = 0) :
    ∀ (p : List (Fin n)) (u v : Fin n),
      p.head? = some u → p.getLast? = some v → IsPath (resArc a b E f) p → p.Nodup →
      ∃ f' : Fin h → Int,
        (∀ e, -1 ≤ f' e ∧ f' e ≤ 1) ∧
        (∀ e, e ∉ E → f' e = 0) ∧
        (∀ e, a e ∉ p ∨ b e ∉ p → f' e = f e) ∧
        (∀ z, flowDiv a b f' z = flowDiv a b f z + (if z = u then 1 else 0) - (if z = v then 1 else 0)) := by
  classical
  intro p
  induction p with
  | nil => intro _ _ hh; simp at hh
  | cons x xs ih =>
    intro u v hh hl hp hnd
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases xs with
    | nil =>
      simp at hl
      subst hl
      exact ⟨f, hbound, hsupp, fun _ _ => rfl, fun z => by split_ifs <;> ring⟩
    | cons y rest =>
      have hnd' := List.nodup_cons.mp hnd
      rcases ih y v rfl (by simpa using hl) hp.2 hnd'.2 with ⟨f1, hb1, hs1, hmod1, hdiv1⟩
      rcases hp.1 with ⟨e, heE, ⟨hae, hbe, hlt⟩ | ⟨hbe, hae, hgt⟩⟩
      · have hfe1 : f1 e = f e := hmod1 e (Or.inl (by rw [hae]; exact hnd'.1))
        let f2 := Function.update f1 e (f1 e + 1)
        refine ⟨f2, ?_, ?_, ?_, ?_⟩
        · intro j
          by_cases hje : j = e
          · subst hje; simp only [f2, Function.update_self]; have := hb1 j; omega
          · simp only [f2, Function.update_of_ne hje]; exact hb1 j
        · intro j hj
          have hje : j ≠ e := fun h => hj (h ▸ heE)
          simp only [f2, Function.update_of_ne hje]; exact hs1 j hj
        · intro j hj
          by_cases hje : j = e
          · subst hje
            exfalso
            rcases hj with h1 | h2
            · exact h1 (by rw [hae]; exact List.mem_cons_self)
            · exact h2 (by rw [hbe]; exact List.mem_cons_of_mem _ List.mem_cons_self)
          · simp only [f2, Function.update_of_ne hje]
            apply hmod1 j
            rcases hj with h1 | h2
            · exact Or.inl (fun h => h1 (List.mem_cons_of_mem _ h))
            · exact Or.inr (fun h => h2 (List.mem_cons_of_mem _ h))
        · intro z
          have hdiff : flowDiv a b f2 z - flowDiv a b f1 z =
              (if z = x then 1 else 0) - (if z = y then 1 else 0) := by
            unfold flowDiv
            rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e]
            · simp only [f2, Function.update_self, hae, hbe]
              by_cases hzx : z = x
              · subst hzx; by_cases hzy : z = y
                · subst hzy; simp
                · simp [hzy, Ne.symm hzy]
              · by_cases hzy : z = y
                · subst hzy; simp [hzx, Ne.symm hzx]
                · simp [hzx, hzy, Ne.symm hzx, Ne.symm hzy]
            · intro j _ hje
              simp [f2, Function.update_of_ne hje]
            · intro h; exact absurd (Finset.mem_univ e) h
          have h1z := hdiv1 z
          linarith
      · have hfe1 : f1 e = f e := hmod1 e (Or.inr (by rw [hbe]; exact hnd'.1))
        let f2 := Function.update f1 e (f1 e - 1)
        refine ⟨f2, ?_, ?_, ?_, ?_⟩
        · intro j
          by_cases hje : j = e
          · subst hje; simp only [f2, Function.update_self]; have := hb1 j; omega
          · simp only [f2, Function.update_of_ne hje]; exact hb1 j
        · intro j hj
          have hje : j ≠ e := fun h => hj (h ▸ heE)
          simp only [f2, Function.update_of_ne hje]; exact hs1 j hj
        · intro j hj
          by_cases hje : j = e
          · subst hje
            exfalso
            rcases hj with h1 | h2
            · exact h1 (by rw [hae]; exact List.mem_cons_of_mem _ List.mem_cons_self)
            · exact h2 (by rw [hbe]; exact List.mem_cons_self)
          · simp only [f2, Function.update_of_ne hje]
            apply hmod1 j
            rcases hj with h1 | h2
            · exact Or.inl (fun h => h1 (List.mem_cons_of_mem _ h))
            · exact Or.inr (fun h => h2 (List.mem_cons_of_mem _ h))
        · intro z
          have hdiff : flowDiv a b f2 z - flowDiv a b f1 z =
              (if z = x then 1 else 0) - (if z = y then 1 else 0) := by
            unfold flowDiv
            rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e]
            · simp only [f2, Function.update_self, hae, hbe]
              by_cases hzx : z = x
              · subst hzx; by_cases hzy : z = y
                · subst hzy; simp
                · simp [hzy, Ne.symm hzy]
              · by_cases hzy : z = y
                · subst hzy; simp [hzx, Ne.symm hzx]
                · simp [hzx, hzy, Ne.symm hzx, Ne.symm hzy]
            · intro j _ hje
              simp [f2, Function.update_of_ne hje]
            · intro h; exact absurd (Finset.mem_univ e) h
          have h1z := hdiv1 z
          linarith

lemma augment_once {n h : Nat} (a b : Fin h → Fin n) (E : Finset (Fin h)) (u0 v0 : Fin n)
    (hcut2 : ∀ S : Finset (Fin n), u0 ∈ S → v0 ∉ S →
      2 ≤ (E.filter (fun i => decide (a i ∈ S) != decide (b i ∈ S))).card)
    (f : Fin h → Int) (d : Int) (hd : d ≤ 1)
    (hbound : ∀ e, -1 ≤ f e ∧ f e ≤ 1) (hsupp : ∀ e, e ∉ E → f e = 0)
    (hdiv : ∀ z, flowDiv a b f z = (if z = u0 then d else 0) - (if z = v0 then d else 0)) :
    ∃ f' : Fin h → Int,
      (∀ e, -1 ≤ f' e ∧ f' e ≤ 1) ∧
      (∀ e, e ∉ E → f' e = 0) ∧
      (∀ z, flowDiv a b f' z = (if z = u0 then d + 1 else 0) - (if z = v0 then d + 1 else 0)) := by
  classical
  have hreach : Relation.ReflTransGen (resArc a b E f) u0 v0 := by
    by_contra hnot
    let S := Finset.univ.filter (fun y => Relation.ReflTransGen (resArc a b E f) u0 y)
    have huS : u0 ∈ S := by simp [S, Relation.ReflTransGen.refl]
    have hvS : v0 ∉ S := by simpa [S] using hnot
    have hsum_lhs : S.sum (flowDiv a b f) = d := by
      have h1 : S.sum (flowDiv a b f) =
          S.sum (fun z => (if z = u0 then d else 0) - (if z = v0 then d else 0)) :=
        Finset.sum_congr rfl fun z _ => hdiv z
      rw [h1, Finset.sum_sub_distrib]
      simp [huS, hvS]
    have hsum_rhs : S.sum (flowDiv a b f) =
        ((E.filter (fun i => decide (a i ∈ S) != decide (b i ∈ S))).card : Int) := by
      rw [sum_flowDiv]
      have hcard_sum : ((E.filter (fun i => decide (a i ∈ S) != decide (b i ∈ S))).card : Int) =
          (Finset.univ : Finset (Fin h)).sum (fun e =>
            if e ∈ E ∧ (decide (a e ∈ S) != decide (b e ∈ S)) = true then (1 : Int) else 0) := by
        rw [Finset.card_eq_sum_ones]
        push_cast
        rw [← Finset.sum_filter]
        congr 1; ext e; simp [Finset.mem_filter]
      rw [hcard_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases heE : e ∈ E
      · by_cases ha : a e ∈ S <;> by_cases hb : b e ∈ S
        · simp [heE, ha, hb]
        · have hge1 : ¬ f e < 1 := by
            intro hlt
            apply hb
            have haR := (Finset.mem_filter.mp ha).2
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Relation.ReflTransGen.tail haR ⟨e, heE, Or.inl ⟨rfl, rfl, hlt⟩⟩
          have hf1 : f e = 1 := by have := hbound e; omega
          simp [heE, ha, hb, hf1]
        · have hle1 : ¬ -1 < f e := by
            intro hgt
            apply ha
            have hbR := (Finset.mem_filter.mp hb).2
            simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Relation.ReflTransGen.tail hbR ⟨e, heE, Or.inr ⟨rfl, rfl, hgt⟩⟩
          have hf1 : f e = -1 := by have := hbound e; omega
          simp [heE, ha, hb, hf1]
        · simp [heE, ha, hb]
      · simp [heE, hsupp e heE]
    have hc2 := hcut2 S huS hvS
    omega
  rcases exists_nodup_path hreach with ⟨p, hhead, hlast, hpath, hnd⟩
  rcases augment_path a b E f hbound hsupp p u0 v0 hhead hlast hpath hnd with ⟨f', hb', hs', _, hdiv'⟩
  refine ⟨f', hb', hs', fun z => ?_⟩
  rw [hdiv' z, hdiv z]
  split_ifs <;> ring

def flowArc {n h : Nat} (a b : Fin h → Fin n) (E : Finset (Fin h)) (f : Fin h → Int) (x y : Fin n) : Prop :=
  ∃ e ∈ E, (a e = x ∧ b e = y ∧ f e = 1) ∨ (b e = x ∧ a e = y ∧ f e = -1)

def impArc {n h : Nat} (a b : Fin h → Fin n) (p : Fin h → Bool × Bool) (x y : Fin n) : Prop :=
  ∃ i : Fin h, (a i = x ∧ b i = y ∧ p i = (true, false)) ∨ (b i = x ∧ a i = y ∧ p i = (false, true))

def impArcOn {n h : Nat} (a b : Fin h → Fin n) (S : Finset (Fin h)) (p : Fin h → Bool × Bool)
    (x y : Fin n) : Prop :=
  ∃ i ∈ S, (a i = x ∧ b i = y ∧ p i = (true, false)) ∨ (b i = x ∧ a i = y ∧ p i = (false, true))

lemma impArcOn_mono {n h : Nat} {a b : Fin h → Fin n} {S : Finset (Fin h)}
    {p1 p2 : Fin h → Bool × Bool} (heq : ∀ i ∈ S, p1 i = p2 i)
    {x y : Fin n} (hr : Relation.ReflTransGen (impArcOn a b S p1) x y) :
    Relation.ReflTransGen (impArc a b p2) x y := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨i, hiS, hst⟩
    rw [heq i hiS] at hst
    exact Relation.ReflTransGen.tail ih ⟨i, hst⟩

lemma impArcOn_rev {n h : Nat} {a b : Fin h → Fin n} {S : Finset (Fin h)}
    {p : Fin h → Bool × Bool} {x y : Fin n}
    (hr : Relation.ReflTransGen (impArcOn a b S p) x y) :
    Relation.ReflTransGen (impArcOn a b S (fun i => (p i).swap)) y x := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨i, hiS, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
    · exact Relation.ReflTransGen.head ⟨i, hiS, Or.inr ⟨h2, h1, by simp [h3]⟩⟩ ih
    · exact Relation.ReflTransGen.head ⟨i, hiS, Or.inl ⟨h2, h1, by simp [h3]⟩⟩ ih

lemma extract_flow_path {n h : Nat} (a b : Fin h → Fin n) (E : Finset (Fin h)) (f : Fin h → Int)
    (hbound : ∀ e, -1 ≤ f e ∧ f e ≤ 1) (hsupp : ∀ e, e ∉ E → f e = 0) :
    ∀ (p : List (Fin n)) (u v : Fin n),
      p.head? = some u → p.getLast? = some v → IsPath (flowArc a b E f) p → p.Nodup →
      ∃ (f' : Fin h → Int) (used : Finset (Fin h)) (ori : Fin h → Bool × Bool),
        used ⊆ E ∧
        (∀ e ∈ used, f e ≠ 0) ∧
        (∀ e, -1 ≤ f' e ∧ f' e ≤ 1) ∧
        (∀ e, e ∉ E → f' e = 0) ∧
        (∀ e ∈ used, f' e = 0) ∧
        (∀ e ∉ used, f' e = f e) ∧
        (∀ e ∈ used, a e ∈ p ∧ b e ∈ p) ∧
        (∀ e ∈ used, ori e = (true, false) ∨ ori e = (false, true)) ∧
        (∀ z ∈ p, Relation.ReflTransGen (impArcOn a b used ori) z v) ∧
        (∀ z ∈ p, Relation.ReflTransGen (impArcOn a b used ori) u z) ∧
        (∀ z, flowDiv a b f' z = flowDiv a b f z - (if z = u then 1 else 0) + (if z = v then 1 else 0)) := by
  classical
  intro p
  induction p with
  | nil => intro _ _ hh; simp at hh
  | cons x xs ih =>
    intro u v hh hl hp hnd
    simp only [List.head?_cons, Option.some.injEq] at hh
    subst hh
    cases xs with
    | nil =>
      simp at hl
      subst hl
      refine ⟨f, ∅, fun _ => (true, false), Finset.empty_subset _, by simp, hbound, hsupp,
        by simp, fun _ _ => rfl, by simp, by simp, ?_, ?_, fun z => by split_ifs <;> ring⟩
      · intro z hz; simp only [List.mem_singleton] at hz; subst hz; exact Relation.ReflTransGen.refl
      · intro z hz; simp only [List.mem_singleton] at hz; subst hz; exact Relation.ReflTransGen.refl
    | cons y rest =>
      have hnd' := List.nodup_cons.mp hnd
      rcases ih y v rfl (by simpa using hl) hp.2 hnd'.2 with
        ⟨f1, used1, ori1, husub, hnz1, hb1, hs1, hzero1, hkeep1, hmem1, hori1, hreach_v1, hreach_u1, hdiv1⟩
      rcases hp.1 with ⟨e, heE, ⟨hae, hbe, hfe⟩ | ⟨hbe, hae, hfe⟩⟩
      · have he_notin : e ∉ used1 := fun h => hnd'.1 (hae ▸ (hmem1 e h).1)
        have hfe1 : f1 e = 1 := by rw [hkeep1 e he_notin, hfe]
        let f2 := Function.update f1 e 0
        let ori2 := Function.update ori1 e (true, false)
        have hlift : ∀ w1 w2, Relation.ReflTransGen (impArcOn a b used1 ori1) w1 w2 →
            Relation.ReflTransGen (impArcOn a b (insert e used1) ori2) w1 w2 := by
          intro w1 w2 hr
          induction hr with
          | refl => exact Relation.ReflTransGen.refl
          | tail _ hstep ihw =>
            rcases hstep with ⟨j, hj1, hst⟩
            have hje : j ≠ e := fun h => he_notin (h ▸ hj1)
            refine Relation.ReflTransGen.tail ihw ⟨j, Finset.mem_insert_of_mem hj1, ?_⟩
            simpa [ori2, Function.update_of_ne hje] using hst
        refine ⟨f2, insert e used1, ori2, Finset.insert_subset heE husub, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj1
          · omega
          · exact hnz1 j hj1
        · intro j
          by_cases hje : j = e
          · subst hje; simp [f2]
          · simp only [f2, Function.update_of_ne hje]; exact hb1 j
        · intro j hj
          have hje : j ≠ e := fun h => hj (h ▸ heE)
          simp only [f2, Function.update_of_ne hje]; exact hs1 j hj
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj1
          · simp [f2]
          · have hje : j ≠ e := fun h => he_notin (h ▸ hj1)
            simp only [f2, Function.update_of_ne hje]; exact hzero1 j hj1
        · intro j hj
          have hje : j ≠ e := fun h => hj (h ▸ Finset.mem_insert_self e used1)
          have hj1 : j ∉ used1 := fun h => hj (Finset.mem_insert_of_mem h)
          simp only [f2, Function.update_of_ne hje]; exact hkeep1 j hj1
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj1
          · exact ⟨by rw [hae]; exact List.mem_cons_self,
                   by rw [hbe]; exact List.mem_cons_of_mem _ List.mem_cons_self⟩
          · exact ⟨List.mem_cons_of_mem _ (hmem1 j hj1).1,
                   List.mem_cons_of_mem _ (hmem1 j hj1).2⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj1
          · left; simp [ori2]
          · have hje : j ≠ e := fun h => he_notin (h ▸ hj1)
            simp only [ori2, Function.update_of_ne hje]; exact hori1 j hj1
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact Relation.ReflTransGen.head
              ⟨e, Finset.mem_insert_self e used1, Or.inl ⟨hae, hbe, by simp [ori2]⟩⟩
              (hlift y v (hreach_v1 y List.mem_cons_self))
          · exact hlift z v (hreach_v1 z hz')
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.head
              ⟨e, Finset.mem_insert_self e used1, Or.inl ⟨hae, hbe, by simp [ori2]⟩⟩
              (hlift y z (hreach_u1 z hz'))
        · intro z
          have hdiff : flowDiv a b f2 z - flowDiv a b f1 z =
              -(if z = x then 1 else 0) + (if z = y then 1 else 0) := by
            unfold flowDiv
            rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e]
            · simp only [f2, Function.update_self, hfe1, hae, hbe]
              by_cases hzx : z = x
              · subst hzx; by_cases hzy : z = y
                · subst hzy; simp
                · simp [hzy, Ne.symm hzy]
              · by_cases hzy : z = y
                · subst hzy; simp [hzx, Ne.symm hzx]
                · simp [hzx, hzy, Ne.symm hzx, Ne.symm hzy]
            · intro j _ hje
              simp [f2, Function.update_of_ne hje]
            · intro h; exact absurd (Finset.mem_univ e) h
          have h1z := hdiv1 z
          linarith
      · have he_notin : e ∉ used1 := fun h => hnd'.1 (hbe ▸ (hmem1 e h).2)
        have hfe1 : f1 e = -1 := by rw [hkeep1 e he_notin, hfe]
        let f2 := Function.update f1 e 0
        let ori2 := Function.update ori1 e (false, true)
        have hlift : ∀ w1 w2, Relation.ReflTransGen (impArcOn a b used1 ori1) w1 w2 →
            Relation.ReflTransGen (impArcOn a b (insert e used1) ori2) w1 w2 := by
          intro w1 w2 hr
          induction hr with
          | refl => exact Relation.ReflTransGen.refl
          | tail _ hstep ihw =>
            rcases hstep with ⟨j, hj1, hst⟩
            have hje : j ≠ e := fun h => he_notin (h ▸ hj1)
            refine Relation.ReflTransGen.tail ihw ⟨j, Finset.mem_insert_of_mem hj1, ?_⟩
            simpa [ori2, Function.update_of_ne hje] using hst
        refine ⟨f2, insert e used1, ori2, Finset.insert_subset heE husub, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj1
          · omega
          · exact hnz1 j hj1
        · intro j
          by_cases hje : j = e
          · subst hje; simp [f2]
          · simp only [f2, Function.update_of_ne hje]; exact hb1 j
        · intro j hj
          have hje : j ≠ e := fun h => hj (h ▸ heE)
          simp only [f2, Function.update_of_ne hje]; exact hs1 j hj
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj1
          · simp [f2]
          · have hje : j ≠ e := fun h => he_notin (h ▸ hj1)
            simp only [f2, Function.update_of_ne hje]; exact hzero1 j hj1
        · intro j hj
          have hje : j ≠ e := fun h => hj (h ▸ Finset.mem_insert_self e used1)
          have hj1 : j ∉ used1 := fun h => hj (Finset.mem_insert_of_mem h)
          simp only [f2, Function.update_of_ne hje]; exact hkeep1 j hj1
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj1
          · exact ⟨by rw [hae]; exact List.mem_cons_of_mem _ List.mem_cons_self,
                   by rw [hbe]; exact List.mem_cons_self⟩
          · exact ⟨List.mem_cons_of_mem _ (hmem1 j hj1).1,
                   List.mem_cons_of_mem _ (hmem1 j hj1).2⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj1
          · right; simp [ori2]
          · have hje : j ≠ e := fun h => he_notin (h ▸ hj1)
            simp only [ori2, Function.update_of_ne hje]; exact hori1 j hj1
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact Relation.ReflTransGen.head
              ⟨e, Finset.mem_insert_self e used1, Or.inr ⟨hbe, hae, by simp [ori2]⟩⟩
              (hlift y v (hreach_v1 y List.mem_cons_self))
          · exact hlift z v (hreach_v1 z hz')
        · intro z hz
          rcases List.mem_cons.mp hz with rfl | hz'
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.head
              ⟨e, Finset.mem_insert_self e used1, Or.inr ⟨hbe, hae, by simp [ori2]⟩⟩
              (hlift y z (hreach_u1 z hz'))
        · intro z
          have hdiff : flowDiv a b f2 z - flowDiv a b f1 z =
              -(if z = x then 1 else 0) + (if z = y then 1 else 0) := by
            unfold flowDiv
            rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e]
            · simp only [f2, Function.update_self, hfe1, hae, hbe]
              by_cases hzx : z = x
              · subst hzx; by_cases hzy : z = y
                · subst hzy; simp
                · simp [hzy, Ne.symm hzy]
              · by_cases hzy : z = y
                · subst hzy; simp [hzx, Ne.symm hzx]
                · simp [hzx, hzy, Ne.symm hzx, Ne.symm hzy]
            · intro j _ hje
              simp [f2, Function.update_of_ne hje]
            · intro h; exact absurd (Finset.mem_univ e) h
          have h1z := hdiv1 z
          linarith

lemma flow_reaches {n h : Nat} (a b : Fin h → Fin n) (E : Finset (Fin h)) (f : Fin h → Int)
    (u0 v0 : Fin n) (d : Int) (hd : 0 < d)
    (hbound : ∀ e, -1 ≤ f e ∧ f e ≤ 1) (hsupp : ∀ e, e ∉ E → f e = 0)
    (hdiv : ∀ z, flowDiv a b f z = (if z = u0 then d else 0) - (if z = v0 then d else 0)) :
    Relation.ReflTransGen (flowArc a b E f) u0 v0 := by
  classical
  by_contra hnot
  let S := Finset.univ.filter (fun y => Relation.ReflTransGen (flowArc a b E f) u0 y)
  have huS : u0 ∈ S := by simp [S, Relation.ReflTransGen.refl]
  have hvS : v0 ∉ S := by simpa [S] using hnot
  have hsum_lhs : S.sum (flowDiv a b f) = d := by
    have h1 : S.sum (flowDiv a b f) =
        S.sum (fun z => (if z = u0 then d else 0) - (if z = v0 then d else 0)) :=
      Finset.sum_congr rfl fun z _ => hdiv z
    rw [h1, Finset.sum_sub_distrib]
    simp [huS, hvS]
  have hsum_le : S.sum (flowDiv a b f) ≤ 0 := by
    rw [sum_flowDiv]
    refine Finset.sum_nonpos fun e _ => ?_
    by_cases heE : e ∈ E
    · by_cases ha : a e ∈ S <;> by_cases hb : b e ∈ S
      · simp [ha, hb]
      · simp only [ha, hb, not_false_eq_true, and_self, ite_true]
        have hne1 : f e ≠ 1 := by
          intro h1
          apply hb
          have haR := (Finset.mem_filter.mp ha).2
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Relation.ReflTransGen.tail haR ⟨e, heE, Or.inl ⟨rfl, rfl, h1⟩⟩
        have := hbound e
        omega
      · simp only [ha, hb, not_false_eq_true, and_self, false_and, ite_true, ite_false]
        have hne1 : f e ≠ -1 := by
          intro h1
          apply ha
          have hbR := (Finset.mem_filter.mp hb).2
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Relation.ReflTransGen.tail hbR ⟨e, heE, Or.inr ⟨rfl, rfl, h1⟩⟩
        have := hbound e
        omega
      · simp [ha, hb]
    · rw [hsupp e heE]; split_ifs <;> omega
  omega

open Classical in
lemma feed_remaining {n h : Nat} (a b : Fin h → Fin n)
    {C : Finset (Fin n)} (hC : C ∈ compOf a b) (u0 : Fin n) (hu0 : u0 ∈ C) :
    ∀ (k : Nat) (locked : Finset (Fin h)) (p : Fin h → Bool × Bool),
      (∀ i, p i ≠ (false, false)) →
      (∀ e ∈ locked, Relation.ReflTransGen (impArc a b p) (a e) u0 ∧
                     Relation.ReflTransGen (impArc a b p) (b e) u0) →
      (C.filter (fun w => ¬ Relation.ReflTransGen (impArc a b p) w u0)).card = k →
      ∃ p' : Fin h → Bool × Bool,
        (∀ i, p' i ≠ (false, false)) ∧
        (∀ e ∈ locked, p' e = p e) ∧
        (∀ w ∈ C, Relation.ReflTransGen (impArc a b p') w u0) := by
  classical
  have hCcut : (cutOf a b C).card = 0 := (Finset.mem_filter.mp hC).2.2.1
  rw [cut_eq_zero_iff] at hCcut
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro locked p hp_nz hlock hk
    cases k with
    | zero =>
      refine ⟨p, hp_nz, fun _ _ => rfl, fun w hwC => ?_⟩
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hk
      exact not_not.mp (hk hwC)
    | succ k' =>
      let W := C.filter (fun w => Relation.ReflTransGen (impArc a b p) w u0)
      let Rem := C.filter (fun w => ¬ Relation.ReflTransGen (impArc a b p) w u0)
      have hRem_ne : Rem.Nonempty := Finset.card_pos.mp (by rw [hk]; omega)
      have hW_ne : W.Nonempty := ⟨u0, Finset.mem_filter.mpr ⟨hu0, Relation.ReflTransGen.refl⟩⟩
      have hW_sub : W ⊆ C := Finset.filter_subset _ _
      have hW_ne_C : W ≠ C := by
        intro heq
        rcases hRem_ne with ⟨w, hw⟩
        have hwC := (Finset.mem_filter.mp hw).1
        rw [← heq] at hwC
        exact (Finset.mem_filter.mp hw).2 (Finset.mem_filter.mp hwC).2
      have hcut_ne : (cutOf a b W).Nonempty := by
        rw [← Finset.card_pos]
        by_contra h0
        have h0' : (cutOf a b W).card = 0 := by omega
        have hCmin := (Finset.mem_filter.mp hC).2.2.2 W (Finset.mem_powerset.mpr hW_sub) hW_ne h0'
        exact hW_ne_C hCmin
      rcases hcut_ne with ⟨e, he_cut⟩
      rw [cut_mem_iff] at he_cut
      have he_not_locked : e ∉ locked := by
        intro hloc
        have hboth := hlock e hloc
        have haC : a e ∈ C := by
          by_cases h1 : a e ∈ W
          · exact hW_sub h1
          · have h2 : b e ∈ W := by by_contra hb; exact he_cut (by simp [h1, hb])
            exact (hCcut e).mpr (hW_sub h2)
        have hbC : b e ∈ C := (hCcut e).mp haC
        have haW : a e ∈ W := Finset.mem_filter.mpr ⟨haC, hboth.1⟩
        have hbW : b e ∈ W := Finset.mem_filter.mpr ⟨hbC, hboth.2⟩
        exact he_cut (by simp [haW, hbW])
      have horient : ∃ val : Bool × Bool, val ≠ (false, false) ∧
          ∃ x ∈ Rem, ∃ y ∈ W,
            (a e = x ∧ b e = y ∧ val = (true, false)) ∨
            (b e = x ∧ a e = y ∧ val = (false, true)) := by
        by_cases haW : a e ∈ W
        · have hbNW : b e ∉ W := by intro h; exact he_cut (by simp [haW, h])
          have hbC : b e ∈ C := (hCcut e).mp (hW_sub haW)
          have hbRem : b e ∈ Rem := Finset.mem_filter.mpr ⟨hbC, fun h => hbNW (Finset.mem_filter.mpr ⟨hbC, h⟩)⟩
          exact ⟨(false, true), by decide, b e, hbRem, a e, haW, Or.inr ⟨rfl, rfl, rfl⟩⟩
        · have hbW : b e ∈ W := by by_contra h; exact he_cut (by simp [haW, h])
          have haC : a e ∈ C := (hCcut e).mpr (hW_sub hbW)
          have haRem : a e ∈ Rem := Finset.mem_filter.mpr ⟨haC, fun h => haW (Finset.mem_filter.mpr ⟨haC, h⟩)⟩
          exact ⟨(true, false), by decide, a e, haRem, b e, hbW, Or.inl ⟨rfl, rfl, rfl⟩⟩
      rcases horient with ⟨val, hval_nz, x, hxRem, y, hyW, hori⟩
      let p1 := Function.update p e val
      have himp_memC : ∀ z, Relation.ReflTransGen (impArc a b p) z u0 → z ∈ C := by
        intro z hz
        induction hz using Relation.ReflTransGen.head_induction_on with
        | refl => exact hu0
        | head hstep _ ihz =>
          rcases hstep with ⟨j, ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩⟩
          · exact (hCcut j).mpr ihz
          · exact (hCcut j).mp ihz
      have hreach_keep : ∀ z, Relation.ReflTransGen (impArc a b p) z u0 →
          Relation.ReflTransGen (impArc a b p1) z u0 := by
        intro z hz
        induction hz using Relation.ReflTransGen.head_induction_on with
        | refl => exact Relation.ReflTransGen.refl
        | @head v1 v2 hstep hv2 ihz =>
          rcases hstep with ⟨j, hst⟩
          have hv1u : Relation.ReflTransGen (impArc a b p) v1 u0 := Relation.ReflTransGen.head ⟨j, hst⟩ hv2
          have hv1W : v1 ∈ W := Finset.mem_filter.mpr ⟨himp_memC v1 hv1u, hv1u⟩
          have hv2W : v2 ∈ W := Finset.mem_filter.mpr ⟨himp_memC v2 hv2, hv2⟩
          have hje : j ≠ e := by
            intro hEq
            subst hEq
            rcases hst with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> exact he_cut (by simp [hv1W, hv2W])
          have hst1 : impArc a b p1 v1 v2 := by
            refine ⟨j, ?_⟩
            simpa [p1, Function.update_of_ne hje] using hst
          exact Relation.ReflTransGen.head hst1 ihz
      have hx_reach1 : Relation.ReflTransGen (impArc a b p1) x u0 := by
        have hy_r := hreach_keep y (Finset.mem_filter.mp hyW).2
        have hxy : impArc a b p1 x y := by
          refine ⟨e, ?_⟩
          simpa [p1, Function.update_self] using hori
        exact Relation.ReflTransGen.head hxy hy_r
      let Rem1 := C.filter (fun w => ¬ Relation.ReflTransGen (impArc a b p1) w u0)
      have hRem1_sub : Rem1 ⊆ Rem.erase x := by
        intro w hw
        simp only [Rem1, Finset.mem_filter] at hw
        refine Finset.mem_erase.mpr ⟨fun hwx => hw.2 (hwx ▸ hx_reach1), ?_⟩
        exact Finset.mem_filter.mpr ⟨hw.1, fun h => hw.2 (hreach_keep w h)⟩
      have hRem1_lt : Rem1.card < k' + 1 := by
        have h1 := Finset.card_le_card hRem1_sub
        rw [Finset.card_erase_of_mem hxRem, hk] at h1
        omega
      have hp1_nz : ∀ i, p1 i ≠ (false, false) := by
        intro i
        by_cases hie : i = e
        · subst hie; simpa [p1] using hval_nz
        · simp only [p1, Function.update_of_ne hie]; exact hp_nz i
      have hlock1 : ∀ j ∈ locked, Relation.ReflTransGen (impArc a b p1) (a j) u0 ∧
          Relation.ReflTransGen (impArc a b p1) (b j) u0 := fun j hj =>
        ⟨hreach_keep _ (hlock j hj).1, hreach_keep _ (hlock j hj).2⟩
      rcases ih Rem1.card hRem1_lt locked p1 hp1_nz hlock1 rfl with ⟨p', hp'_nz, hp'_eq, hp'_all⟩
      refine ⟨p', hp'_nz, fun j hj => ?_, hp'_all⟩
      rw [hp'_eq j hj]
      have hje : j ≠ e := fun h => he_not_locked (h ▸ hj)
      simp [p1, Function.update_of_ne hje]

lemma component_signing {n h : Nat} (a b : Fin h → Fin n)
    {C : Finset (Fin n)} (hC : C ∈ compOf a b) (hgood : goodOf a b C = true) :
    ∃ p : Fin h → Bool × Bool,
      (∀ i, p i ≠ (false, false)) ∧
      (∀ x : Finset (Fin n), (x ∩ C).Nonempty →
        ∃ i : Fin h, a i ∈ C ∧ (decide (a i ∈ x), decide (b i ∈ x)) = p i) := by
  classical
  rcases (goodOf_eq_true_iff a b C).mp hgood with ⟨i0, hi0_str, hi0C⟩
  have hCcut : (cutOf a b C).card = 0 := (Finset.mem_filter.mp hC).2.2.1
  rw [cut_eq_zero_iff] at hCcut
  let E' : Finset (Fin h) := Finset.univ.erase i0
  have hcut2 : ∀ S : Finset (Fin n), a i0 ∈ S → b i0 ∉ S →
      2 ≤ (E'.filter (fun i => decide (a i ∈ S) != decide (b i ∈ S))).card := by
    intro S haS hbS
    have hge3 : 3 ≤ (cutOf a b S).card := by
      have hs := (Finset.mem_filter.mp hi0_str).2 S (Finset.mem_univ S)
      exact hs (by simp [haS, hbS])
    have heq : E'.filter (fun i => decide (a i ∈ S) != decide (b i ∈ S)) =
        (cutOf a b S).erase i0 := by
      ext i
      simp only [E', cutOf, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
      tauto
    rw [heq, Finset.card_erase_of_mem (by rw [cut_mem_iff]; simp [haS, hbS])]
    omega
  rcases augment_once a b E' (a i0) (b i0) hcut2 (fun _ => 0) 0 (by omega)
    (fun _ => by omega) (fun _ _ => rfl) (fun z => by simp [flowDiv]) with ⟨f1, hb1, hs1, hdiv1⟩
  rcases augment_once a b E' (a i0) (b i0) hcut2 f1 1 (by omega) hb1 hs1
    (fun z => by simpa using hdiv1 z) with ⟨f2, hb2, hs2, hdiv2⟩
  have hdiv2' : ∀ z, flowDiv a b f2 z = (if z = a i0 then 2 else 0) - (if z = b i0 then 2 else 0) := by
    intro z; simpa using hdiv2 z
  have hr1 := flow_reaches a b E' f2 (a i0) (b i0) 2 (by omega) hb2 hs2 hdiv2'
  rcases exists_nodup_path hr1 with ⟨p1, hh1, hl1, hp1, hnd1⟩
  rcases extract_flow_path a b E' f2 hb2 hs2 p1 (a i0) (b i0) hh1 hl1 hp1 hnd1 with
    ⟨f1', used1, ori1, husub1, _, hb1', hs1', hzero1, _, hmem1, hori1, hreach_v1, _, hdiv1'⟩
  have hdiv1'' : ∀ z, flowDiv a b f1' z = (if z = a i0 then 1 else 0) - (if z = b i0 then 1 else 0) := by
    intro z; rw [hdiv1' z, hdiv2' z]; split_ifs <;> ring
  have hr2 := flow_reaches a b E' f1' (a i0) (b i0) 1 (by omega) hb1' hs1' hdiv1''
  rcases exists_nodup_path hr2 with ⟨p2, hh2, hl2, hp2, hnd2⟩
  rcases extract_flow_path a b E' f1' hb1' hs1' p2 (a i0) (b i0) hh2 hl2 hp2 hnd2 with
    ⟨_, used2, ori2, husub2, hnz2, _, _, _, _, hmem2, hori2, _, hreach_u2, _⟩
  have hdisj12 : Disjoint used1 used2 := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    exact hnz2 e he2 (hzero1 e he1)
  have hi0_not1 : i0 ∉ used1 := fun h => (Finset.mem_erase.mp (husub1 h)).1 rfl
  have hi0_not2 : i0 ∉ used2 := fun h => (Finset.mem_erase.mp (husub2 h)).1 rfl
  let p0 : Fin h → Bool × Bool := fun i =>
    if i = i0 then (true, true)
    else if i ∈ used1 then ori1 i
    else if i ∈ used2 then (ori2 i).swap
    else (true, false)
  have hp0_nz : ∀ i, p0 i ≠ (false, false) := by
    intro i
    dsimp only [p0]
    split_ifs with h1 h2 h3
    · decide
    · rcases hori1 i h2 with h | h <;> rw [h] <;> decide
    · rcases hori2 i h3 with h | h <;> rw [h] <;> decide
    · decide
  have hp0_used1 : ∀ i ∈ used1, ori1 i = p0 i := by
    intro i hi
    have hne : i ≠ i0 := fun h => hi0_not1 (h ▸ hi)
    simp [p0, hne, hi]
  have hp0_used2 : ∀ i ∈ used2, (ori2 i).swap = p0 i := by
    intro i hi
    have hne : i ≠ i0 := fun h => hi0_not2 (h ▸ hi)
    have hn1 : i ∉ used1 := Finset.disjoint_right.mp hdisj12 hi
    simp [p0, hne, hn1, hi]
  have hba0 : Relation.ReflTransGen (impArc a b p0) (b i0) (a i0) := by
    have hbl : b i0 ∈ p2 := List.mem_of_getLast? hl2
    exact impArcOn_mono hp0_used2 (impArcOn_rev (hreach_u2 (b i0) hbl))
  have hab0 : Relation.ReflTransGen (impArc a b p0) (a i0) (b i0) := by
    have hal : a i0 ∈ p1 := List.mem_of_head? hh1
    exact impArcOn_mono hp0_used1 (hreach_v1 (a i0) hal)
  let locked : Finset (Fin h) := insert i0 (used1 ∪ used2)
  have hlock : ∀ e ∈ locked,
      Relation.ReflTransGen (impArc a b p0) (a e) (a i0) ∧
      Relation.ReflTransGen (impArc a b p0) (b e) (a i0) := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he12
    · exact ⟨Relation.ReflTransGen.refl, hba0⟩
    · rcases Finset.mem_union.mp he12 with he1 | he2
      · exact ⟨(impArcOn_mono hp0_used1 (hreach_v1 (a e) (hmem1 e he1).1)).trans hba0,
               (impArcOn_mono hp0_used1 (hreach_v1 (b e) (hmem1 e he1).2)).trans hba0⟩
      · exact ⟨impArcOn_mono hp0_used2 (impArcOn_rev (hreach_u2 (a e) (hmem2 e he2).1)),
               impArcOn_mono hp0_used2 (impArcOn_rev (hreach_u2 (b e) (hmem2 e he2).2))⟩
  rcases feed_remaining a b hC (a i0) hi0C _ locked p0 hp0_nz hlock rfl with ⟨p', hp'_nz, hp'_eq, hp'_all⟩
  have hp'_ab : Relation.ReflTransGen (impArc a b p') (a i0) (b i0) := by
    have hal : a i0 ∈ p1 := List.mem_of_head? hh1
    refine impArcOn_mono (fun i hi => ?_) (hreach_v1 (a i0) hal)
    rw [hp0_used1 i hi, ← hp'_eq i (Finset.mem_insert_of_mem (Finset.mem_union_left _ hi))]
  have hp'_i0 : p' i0 = (true, true) := by
    rw [hp'_eq i0 (Finset.mem_insert_self i0 _)]
    simp [p0]
  refine ⟨p', hp'_nz, fun x hxne => ?_⟩
  by_contra hnone
  push_neg at hnone
  have hclosed : ∀ z1 z2, Relation.ReflTransGen (impArc a b p') z1 z2 → z1 ∈ C → z1 ∈ x → z2 ∈ x := by
    intro z1 z2 hr
    induction hr with
    | refl => intro _ hx1; exact hx1
    | @tail u v h1u hstep ihz =>
      intro hz1C hz1x
      have huC : u ∈ C := by
        clear hstep ihz
        induction h1u with
        | refl => exact hz1C
        | tail _ hst ihu =>
          rcases hst with ⟨j, ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩⟩
          · exact (hCcut j).mp ihu
          · exact (hCcut j).mpr ihu
      have hux : u ∈ x := ihz hz1C hz1x
      rcases hstep with ⟨j, ⟨rfl, rfl, hpj⟩ | ⟨rfl, rfl, hpj⟩⟩
      · by_contra hvx
        have hbad := hnone j huC
        rw [hpj] at hbad
        exact hbad (by simp [hux, hvx])
      · by_contra hvx
        have hbad := hnone j ((hCcut j).mpr huC)
        rw [hpj] at hbad
        exact hbad (by simp [hux, hvx])
  rcases hxne with ⟨w, hw⟩
  rcases Finset.mem_inter.mp hw with ⟨hwx, hwC⟩
  have hai0_x : a i0 ∈ x := hclosed w (a i0) (hp'_all w hwC) hwC hwx
  have hbi0_x : b i0 ∈ x := hclosed (a i0) (b i0) hp'_ab hi0C hai0_x
  have hbad := hnone i0 hi0C
  rw [hp'_i0] at hbad
  exact hbad (by simp [hai0_x, hbi0_x])

lemma decodes_iff_all_good {n h : Nat} (a b : Fin h → Fin n) :
    decodesOf a b ↔ ∀ C ∈ compOf a b, goodOf a b C = true := by
  classical
  constructor
  · intro hdec C hC
    have hsat_ne : (Finset.univ : Finset (Finset (Fin n))) ≠ Finset.univ.erase ∅ := by
      intro heq
      have h1 : (∅ : Finset (Fin n)) ∈ (Finset.univ : Finset (Finset (Fin n))) := Finset.mem_univ _
      rw [heq] at h1
      exact (Finset.mem_erase.mp h1).1 rfl
    have hdiff : ∃ p : Fin h → Bool × Bool,
        (∃ x ∈ (Finset.univ : Finset (Finset (Fin n))), ∀ i, (decide (a i ∈ x), decide (b i ∈ x)) ≠ p i) ∧
        ¬ (∃ x ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
            ∀ i, (decide (a i ∈ x), decide (b i ∈ x)) ≠ p i) := by
      by_contra hall
      push_neg at hall
      apply hsat_ne
      apply hdec
      intro p
      constructor
      · exact hall p
      · rintro ⟨x, hx, hxp⟩
        exact ⟨x, Finset.mem_univ x, hxp⟩
    rcases hdiff with ⟨p, ⟨x0, _, hx0⟩, hno_ne⟩
    have hx0_empty : x0 = ∅ := by
      by_contra hne
      exact hno_ne ⟨x0, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x0⟩, hx0⟩
    subst hx0_empty
    have hp_nz : ∀ i, p i ≠ (false, false) := by
      intro i
      simpa using (hx0 i).symm
    have hno_nonempty : ∀ K : Finset (Fin n), K.Nonempty →
        ∃ i, (decide (a i ∈ K), decide (b i ∈ K)) = p i := by
      intro K hKne
      by_contra hok
      push_neg at hok
      exact hno_ne ⟨K, Finset.mem_erase.mpr ⟨hKne.ne_empty, Finset.mem_univ K⟩, hok⟩
    have hCcut : (cutOf a b C).card = 0 := (Finset.mem_filter.mp hC).2.2.1
    rw [cut_eq_zero_iff] at hCcut
    let Closed := C.powerset.filter (fun K =>
      K.Nonempty ∧ ∀ x ∈ K, ∀ y, impArc a b p x y → y ∈ K)
    have hC_closed : C ∈ Closed := by
      simp only [Closed, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.Subset.rfl, (Finset.mem_filter.mp hC).2.1, fun x hx y hxy => ?_⟩
      rcases hxy with ⟨i, ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩⟩
      · exact (hCcut i).mp hx
      · exact (hCcut i).mpr hx
    rcases Finset.exists_min_image Closed Finset.card ⟨C, hC_closed⟩ with ⟨K, hK_cl, hK_min⟩
    simp only [Closed, Finset.mem_filter, Finset.mem_powerset] at hK_cl
    rcases hK_cl with ⟨hKC, hKne, hKimp⟩
    have hstrong_conn : ∀ x ∈ K, ∀ y ∈ K, Relation.ReflTransGen (impArc a b p) x y := by
      intro x hxK
      let Rx := K.filter (fun y => Relation.ReflTransGen (impArc a b p) x y)
      have hRx_sub : Rx ⊆ K := Finset.filter_subset _ _
      have hRx_cl : Rx ∈ Closed := by
        simp only [Closed, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨hRx_sub.trans hKC, ⟨x, Finset.mem_filter.mpr ⟨hxK, Relation.ReflTransGen.refl⟩⟩,
          fun u hu v huv => ?_⟩
        rcases Finset.mem_filter.mp hu with ⟨huK, hxu⟩
        exact Finset.mem_filter.mpr ⟨hKimp u huK v huv, Relation.ReflTransGen.tail hxu huv⟩
      have hcard_le : K.card ≤ Rx.card := hK_min Rx hRx_cl
      have hRx_eq : Rx = K := Finset.eq_of_subset_of_card_le hRx_sub hcard_le
      intro y hyK
      rw [← hRx_eq] at hyK
      exact (Finset.mem_filter.mp hyK).2
    rcases hno_nonempty K hKne with ⟨i0, hi0⟩
    have hi0_tt : p i0 = (true, true) ∧ a i0 ∈ K ∧ b i0 ∈ K := by
      cases haK : decide (a i0 ∈ K) <;> cases hbK : decide (b i0 ∈ K)
      · rw [haK, hbK] at hi0; exact absurd hi0.symm (hp_nz i0)
      · exfalso
        rw [haK, hbK] at hi0
        have hb : b i0 ∈ K := of_decide_eq_true hbK
        have ha : a i0 ∉ K := of_decide_eq_false haK
        exact ha (hKimp (b i0) hb (a i0) ⟨i0, Or.inr ⟨rfl, rfl, hi0.symm⟩⟩)
      · exfalso
        rw [haK, hbK] at hi0
        have ha : a i0 ∈ K := of_decide_eq_true haK
        have hb : b i0 ∉ K := of_decide_eq_false hbK
        exact hb (hKimp (a i0) ha (b i0) ⟨i0, Or.inl ⟨rfl, rfl, hi0.symm⟩⟩)
      · rw [haK, hbK] at hi0
        exact ⟨hi0.symm, of_decide_eq_true haK, of_decide_eq_true hbK⟩
    rw [goodOf_eq_true_iff]
    refine ⟨i0, ?_, hKC hi0_tt.2.1⟩
    simp only [strongOf, Finset.mem_filter, Finset.mem_univ, true_and]
    intro S _ hsep
    have hcross : ∀ (T : Finset (Fin n)), a i0 ∈ T → b i0 ∉ T → 3 ≤ (cutOf a b T).card := by
      intro T haT hbT
      have hreach_out : ∀ {u v}, Relation.ReflTransGen (impArc a b p) u v → u ∈ T → v ∉ T →
          ∃ i ∈ cutOf a b T,
            (a i ∈ T ∧ b i ∉ T ∧ p i = (true, false)) ∨
            (b i ∈ T ∧ a i ∉ T ∧ p i = (false, true)) := by
        intro u v hr
        induction hr with
        | refl => intro h1 h2; exact absurd h1 h2
        | @tail w z hrw hstep ih =>
          intro huT hzT
          by_cases hwT : w ∈ T
          · rcases hstep with ⟨i, ⟨rfl, rfl, hp1⟩ | ⟨rfl, rfl, hp1⟩⟩
            · exact ⟨i, (cut_mem_iff a b T i).mpr (by simp [hwT, hzT]), Or.inl ⟨hwT, hzT, hp1⟩⟩
            · exact ⟨i, (cut_mem_iff a b T i).mpr (by simp [hwT, hzT]), Or.inr ⟨hwT, hzT, hp1⟩⟩
          · exact ih huT hwT
      have hreach_in : ∀ {u v}, Relation.ReflTransGen (impArc a b p) u v → u ∉ T → v ∈ T →
          ∃ i ∈ cutOf a b T,
            (a i ∉ T ∧ b i ∈ T ∧ p i = (true, false)) ∨
            (b i ∉ T ∧ a i ∈ T ∧ p i = (false, true)) := by
        intro u v hr
        induction hr with
        | refl => intro h1 h2; exact absurd h2 h1
        | @tail w z hrw hstep ih =>
          intro huT hzT
          by_cases hwT : w ∈ T
          · exact ih huT hwT
          · rcases hstep with ⟨i, ⟨rfl, rfl, hp1⟩ | ⟨rfl, rfl, hp1⟩⟩
            · exact ⟨i, (cut_mem_iff a b T i).mpr (by simp [hwT, hzT]), Or.inl ⟨hwT, hzT, hp1⟩⟩
            · exact ⟨i, (cut_mem_iff a b T i).mpr (by simp [hwT, hzT]), Or.inr ⟨hwT, hzT, hp1⟩⟩
      rcases hreach_out (hstrong_conn (a i0) hi0_tt.2.1 (b i0) hi0_tt.2.2) haT hbT with ⟨i1, hi1_cut, hi1_prop⟩
      rcases hreach_in (hstrong_conn (b i0) hi0_tt.2.2 (a i0) hi0_tt.2.1) hbT haT with ⟨i2, hi2_cut, hi2_prop⟩
      have hi0_cut : i0 ∈ cutOf a b T := (cut_mem_iff a b T i0).mpr (by simp [haT, hbT])
      have h01 : i0 ≠ i1 := by
        intro heq; subst heq
        rcases hi1_prop with ⟨_, _, hp1⟩ | ⟨_, _, hp1⟩ <;> rw [hi0_tt.1] at hp1 <;> simp at hp1
      have h02 : i0 ≠ i2 := by
        intro heq; subst heq
        rcases hi2_prop with ⟨_, _, hp2⟩ | ⟨_, _, hp2⟩ <;> rw [hi0_tt.1] at hp2 <;> simp at hp2
      have h12 : i1 ≠ i2 := by
        intro heq; subst heq
        rcases hi1_prop with ⟨h1a, h1b, h1p⟩ | ⟨h1b, h1a, h1p⟩ <;>
        rcases hi2_prop with ⟨h2a, h2b, h2p⟩ | ⟨h2b, h2a, h2p⟩
        · exact h2a h1a
        · rw [h1p] at h2p; simp at h2p
        · rw [h1p] at h2p; simp at h2p
        · exact h2b h1b
      have hsub : ({i0, i1, i2} : Finset (Fin h)) ⊆ cutOf a b T := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> assumption
      have hcard3 : ({i0, i1, i2} : Finset (Fin h)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
            Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
      calc 3 = ({i0, i1, i2} : Finset (Fin h)).card := hcard3.symm
        _ ≤ (cutOf a b T).card := Finset.card_le_card hsub
    by_cases haS : a i0 ∈ S
    · have hbS : b i0 ∉ S := by intro hb; simp [haS, hb] at hsep
      exact hcross S haS hbS
    · have hbS : b i0 ∈ S := by by_contra hb; simp [haS, hb] at hsep
      rw [← cut_compl]
      exact hcross (Finset.univ \ S) (by simp [haS]) (by simp [hbS])
  · intro hall
    have hcomp_sig : ∀ C : Finset (Fin n), C ∈ compOf a b →
        ∃ p : Fin h → Bool × Bool, (∀ i, p i ≠ (false, false)) ∧
          (∀ x : Finset (Fin n), (x ∩ C).Nonempty →
            ∃ i : Fin h, a i ∈ C ∧ (decide (a i ∈ x), decide (b i ∈ x)) = p i) :=
      fun C hC => component_signing a b hC (hall C hC)
    let cOf : Fin n → Finset (Fin n) := fun v =>
      Finset.univ.filter (fun y => Relation.ReflTransGen (adjE a b Finset.univ) v y)
    have hcOf_mem : ∀ v : Fin n, cOf v ∈ compOf a b := fun v =>
      (mem_compOf_iff_reach a b (cOf v)).mpr ⟨v, rfl⟩
    let pC : ∀ C : Finset (Fin n), C ∈ compOf a b → (Fin h → Bool × Bool) :=
      fun C hC => Classical.choose (hcomp_sig C hC)
    let p0 : Fin h → Bool × Bool := fun i => pC (cOf (a i)) (hcOf_mem (a i)) i
    have hp0_nz : ∀ i, p0 i ≠ (false, false) := fun i =>
      (Classical.choose_spec (hcomp_sig (cOf (a i)) (hcOf_mem (a i)))).1 i
    have hp0_nonempty : ∀ x : Finset (Fin n), x.Nonempty →
        ∃ i, (decide (a i ∈ x), decide (b i ∈ x)) = p0 i := by
      rintro x ⟨w, hwx⟩
      let C := cOf w
      have hC := hcOf_mem w
      have hxC : (x ∩ C).Nonempty := ⟨w, Finset.mem_inter.mpr ⟨hwx, by simp [C, cOf, Relation.ReflTransGen.refl]⟩⟩
      rcases (Classical.choose_spec (hcomp_sig C hC)).2 x hxC with ⟨i, haiC, hpi⟩
      have hCi_eq : cOf (a i) = C := by
        by_contra hne
        have hdisj := compOf_disjoint a b (hcOf_mem (a i)) hC hne
        exact Finset.disjoint_left.mp hdisj (by simp [cOf, Relation.ReflTransGen.refl]) haiC
      refine ⟨i, ?_⟩
      simpa [p0, hCi_eq] using hpi
    intro A B hAB
    ext x0
    let px : Fin h → Bool × Bool := fun i =>
      (xor (p0 i).1 (decide (a i ∈ x0)), xor (p0 i).2 (decide (b i ∈ x0)))
    have hsat_iff : ∀ S : Finset (Finset (Fin n)),
        (∃ x ∈ S, ∀ i, (decide (a i ∈ x), decide (b i ∈ x)) ≠ px i) ↔ x0 ∈ S := by
      intro S
      constructor
      · rintro ⟨x, hxS, hxp⟩
        have hsd : symmDiff x x0 = ∅ := by
          by_contra hne
          rcases hp0_nonempty (symmDiff x x0) (Finset.nonempty_iff_ne_empty.mpr hne) with ⟨i, hi⟩
          apply hxp i
          have h1 : decide (a i ∈ symmDiff x x0) = xor (decide (a i ∈ x)) (decide (a i ∈ x0)) := by
            by_cases hxa : a i ∈ x <;> by_cases hx0a : a i ∈ x0 <;> simp [Finset.mem_symmDiff, hxa, hx0a]
          have h2 : decide (b i ∈ symmDiff x x0) = xor (decide (b i ∈ x)) (decide (b i ∈ x0)) := by
            by_cases hxb : b i ∈ x <;> by_cases hx0b : b i ∈ x0 <;> simp [Finset.mem_symmDiff, hxb, hx0b]
          have hp1 : (p0 i).1 = xor (decide (a i ∈ x)) (decide (a i ∈ x0)) := by
            have := congrArg Prod.fst hi; simpa [h1] using this.symm
          have hp2 : (p0 i).2 = xor (decide (b i ∈ x)) (decide (b i ∈ x0)) := by
            have := congrArg Prod.snd hi; simpa [h2] using this.symm
          ext
          · simp only [px, hp1]; cases decide (a i ∈ x) <;> cases decide (a i ∈ x0) <;> rfl
          · simp only [px, hp2]; cases decide (b i ∈ x) <;> cases decide (b i ∈ x0) <;> rfl
        have hxeq : x = x0 := symmDiff_eq_bot.mp hsd
        rwa [← hxeq]
      · intro hx0S
        refine ⟨x0, hx0S, fun i heq => ?_⟩
        apply hp0_nz i
        have h1 : (p0 i).1 = false := by
          have hfst := congrArg Prod.fst heq
          dsimp only [px] at hfst
          cases hpa : (p0 i).1 <;> cases hxa : decide (a i ∈ x0) <;> rw [hpa, hxa] at hfst <;> first | rfl | cases hfst
        have h2 : (p0 i).2 = false := by
          have hsnd := congrArg Prod.snd heq
          dsimp only [px] at hsnd
          cases hpb : (p0 i).2 <;> cases hxb : decide (b i ∈ x0) <;> rw [hpb, hxb] at hsnd <;> first | rfl | cases hsnd
        exact Prod.ext h1 h2
    rw [← hsat_iff A, ← hsat_iff B]
    exact hAB px

lemma badOf_equiv {n h1 h2 : Nat} (a1 b1 : Fin h1 → Fin n) (a2 b2 : Fin h2 → Fin n)
    (e : Fin h1 ≃ Fin h2) (ha : ∀ i, a2 (e i) = a1 i) (hb : ∀ i, b2 (e i) = b1 i) :
    badOf a1 b1 = badOf a2 b2 := by
  have hcut : ∀ S : Finset (Fin n), (cutOf a1 b1 S).card = (cutOf a2 b2 S).card := by
    intro S
    refine Finset.card_bij (fun i _ => e i) ?_ ?_ ?_
    · intro i hi
      simp only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rwa [ha i, hb i]
    · intro i1 _ i2 _ heq; exact e.injective heq
    · intro j hj
      refine ⟨e.symm j, ?_, e.apply_symm_apply j⟩
      simp only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have ha' := ha (e.symm j); rw [e.apply_symm_apply] at ha'
      have hb' := hb (e.symm j); rw [e.apply_symm_apply] at hb'
      rwa [← ha', ← hb']
  have hcomp : compOf a1 b1 = compOf a2 b2 := by
    ext C
    simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and, hcut]
  have hgood : ∀ C : Finset (Fin n), goodOf a1 b1 C = goodOf a2 b2 C := by
    intro C
    apply Bool.eq_iff_iff.mpr
    simp only [goodOf_eq_true_iff, strongOf, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hstr, hiC⟩
      refine ⟨e i, ?_, by rwa [ha i]⟩
      intro S _ hsep
      rw [ha i, hb i] at hsep
      rw [← hcut S]
      exact hstr S trivial hsep
    · rintro ⟨j, hstr, hjC⟩
      have ha' := ha (e.symm j); rw [e.apply_symm_apply] at ha'
      have hb' := hb (e.symm j); rw [e.apply_symm_apply] at hb'
      refine ⟨e.symm j, ?_, by rwa [← ha']⟩
      intro S _ hsep
      rw [← ha', ← hb'] at hsep
      rw [hcut S]
      exact hstr S trivial hsep
  unfold badOf
  rw [hcomp]
  congr 1
  refine Finset.filter_congr fun C _ => by rw [hgood C]

lemma bad_add_one_edge {n h : Nat} (a b : Fin h → Fin n) (x y : Fin n) :
    badOf a b ≤ badOf (Fin.snoc (α := fun _ => Fin n) a x) (Fin.snoc (α := fun _ => Fin n) b y) + 1 := by
  classical
  let a' : Fin (h + 1) → Fin n := Fin.snoc (α := fun _ => Fin n) a x
  let b' : Fin (h + 1) → Fin n := Fin.snoc (α := fun _ => Fin n) b y
  have hcut_snoc : ∀ S : Finset (Fin n),
      (cutOf a' b' S).card = (cutOf a b S).card + (if (decide (x ∈ S) != decide (y ∈ S)) = true then 1 else 0) := by
    intro S
    have hsplit : cutOf a' b' S = (cutOf a b S).image Fin.castSucc ∪
        (if (decide (x ∈ S) != decide (y ∈ S)) = true then {Fin.last h} else ∅) := by
      ext j
      simp only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
      refine Fin.lastCases ?_ ?_ j
      · simp only [a', b', Fin.snoc_last]
        constructor
        · intro hxy; right; simp [hxy]
        · rintro (⟨i, _, hi⟩ | hlast)
          · exact absurd hi (Fin.castSucc_ne_last i)
          · split_ifs at hlast with hxy
            · exact hxy
            · simp at hlast
      · intro i
        simp only [a', b', Fin.snoc_castSucc]
        constructor
        · intro hi; left; exact ⟨i, hi, rfl⟩
        · rintro (⟨i', hi', heq⟩ | hlast)
          · rwa [← Fin.castSucc_inj.mp heq]
          · split_ifs at hlast
            · simp only [Finset.mem_singleton] at hlast
              exact absurd hlast (Fin.castSucc_ne_last i)
            · simp at hlast
    rw [hsplit, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ (Fin.castSucc_injective h)]
      split_ifs <;> simp
    · rw [Finset.disjoint_left]
      intro j hj1 hj2
      rcases Finset.mem_image.mp hj1 with ⟨i, _, rfl⟩
      split_ifs at hj2
      · simp only [Finset.mem_singleton] at hj2
        exact Fin.castSucc_ne_last i hj2
      · simp at hj2
  have hcut_sub : ∀ C ∈ compOf a b, ∀ S : Finset (Fin n),
      (cutOf a b (S ∩ C)).card ≤ (cutOf a b S).card := by
    intro C hC S
    have hCcut := (cut_eq_zero_iff a b C).mp (Finset.mem_filter.mp hC).2.2.1
    refine Finset.card_le_card fun i hi => ?_
    rw [cut_mem_iff] at hi ⊢
    by_cases haC : a i ∈ C
    · have hbC := (hCcut i).mp haC
      simpa [Finset.mem_inter, haC, hbC] using hi
    · have hbC : b i ∉ C := fun h => haC ((hCcut i).mpr h)
      exfalso; apply hi; simp [haC, hbC]
  let cG : Fin n → Finset (Fin n) := fun v =>
    Finset.univ.filter (fun z => Relation.ReflTransGen (adjE a b Finset.univ) v z)
  let Cx := cG x
  let Cy := cG y
  have hCx_mem : Cx ∈ compOf a b := (mem_compOf_iff_reach a b Cx).mpr ⟨x, rfl⟩
  have hCy_mem : Cy ∈ compOf a b := (mem_compOf_iff_reach a b Cy).mpr ⟨y, rfl⟩
  have hxCx : x ∈ Cx := by simp [Cx, cG, Relation.ReflTransGen.refl]
  have hyCy : y ∈ Cy := by simp [Cy, cG, Relation.ReflTransGen.refl]
  have hgood_other : ∀ C ∈ compOf a b, C ≠ Cx → C ≠ Cy → goodOf a' b' C = true → goodOf a b C = true := by
    intro C hC hneX hneY hg'
    have hdisjX := compOf_disjoint a b hC hCx_mem hneX
    have hdisjY := compOf_disjoint a b hC hCy_mem hneY
    have hxNC : x ∉ C := Finset.disjoint_right.mp hdisjX hxCx
    have hyNC : y ∉ C := Finset.disjoint_right.mp hdisjY hyCy
    rcases (goodOf_eq_true_iff a' b' C).mp hg' with ⟨j, hj_str, hjC⟩
    have hj_not_last : j ≠ Fin.last h := by
      intro heq; subst heq; simp [a'] at hjC; exact hxNC hjC
    rcases Fin.exists_castSucc_eq.mpr hj_not_last with ⟨i, rfl⟩
    rw [goodOf_eq_true_iff]
    refine ⟨i, ?_, by simpa [a'] using hjC⟩
    simp only [strongOf, Finset.mem_filter, Finset.mem_univ, true_and]
    intro S _ hsep
    have hCcut := (cut_eq_zero_iff a b C).mp (Finset.mem_filter.mp hC).2.2.1
    have haiC : a i ∈ C := by simpa [a'] using hjC
    have hbiC : b i ∈ C := (hCcut i).mp haiC
    have hsep' : (decide (a' i.castSucc ∈ S ∩ C) != decide (b' i.castSucc ∈ S ∩ C)) = true := by
      simpa [a', b', Finset.mem_inter, haiC, hbiC] using hsep
    have hge3 := (Finset.mem_filter.mp hj_str).2 (S ∩ C) (Finset.mem_univ _) hsep'
    rw [hcut_snoc (S ∩ C)] at hge3
    have hxNS : x ∉ S ∩ C := fun h => hxNC (Finset.mem_inter.mp h).2
    have hyNS : y ∉ S ∩ C := fun h => hyNC (Finset.mem_inter.mp h).2
    simp [hxNS, hyNS] at hge3
    exact hge3.trans (hcut_sub C hC S)
  by_cases hxy_eq : Cx = Cy
  · have hcomp_eq : compOf a' b' = compOf a b := by
      have hcut0 : ∀ S : Finset (Fin n), (cutOf a' b' S).card = 0 ↔ (cutOf a b S).card = 0 := by
        intro S
        rw [hcut_snoc S]
        constructor
        · intro h0; omega
        · intro h0
          have h0' := (cut_eq_zero_iff a b S).mp h0
          have hreach_iff : ∀ u v, Relation.ReflTransGen (adjE a b Finset.univ) u v → (u ∈ S ↔ v ∈ S) := by
            intro u v hr
            induction hr with
            | refl => rfl
            | tail _ hstep ih =>
              rcases hstep with ⟨i, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
              · exact ih.trans (h0' i)
              · exact ih.trans (h0' i).symm
          have hxy_iff : x ∈ S ↔ y ∈ S := by
            have hyCx : y ∈ Cx := by rw [hxy_eq]; exact hyCy
            exact hreach_iff x y (Finset.mem_filter.mp hyCx).2
          by_cases hxS : x ∈ S
          · have hyS := hxy_iff.mp hxS; simp [hxS, hyS, h0]
          · have hyS : y ∉ S := fun h => hxS (hxy_iff.mpr h); simp [hxS, hyS, h0]
      ext C
      simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and, hcut0]
    have hsub : (compOf a b).filter (fun C => goodOf a b C = false) ⊆
        insert Cx ((compOf a' b').filter (fun C => goodOf a' b' C = false)) := by
      intro C hC
      simp only [Finset.mem_filter, Finset.mem_insert] at hC ⊢
      by_cases hCCx : C = Cx
      · exact Or.inl hCCx
      · refine Or.inr ⟨by rw [hcomp_eq]; exact hC.1, ?_⟩
        by_contra hg'
        have hgt : goodOf a' b' C = true := by cases h : goodOf a' b' C <;> simp_all
        have := hgood_other C hC.1 hCCx (hxy_eq ▸ hCCx) hgt
        rw [this] at hC
        exact Bool.noConfusion hC.2
    calc badOf a b ≤ (insert Cx ((compOf a' b').filter (fun C => goodOf a' b' C = false))).card :=
          Finset.card_le_card hsub
      _ ≤ badOf a' b' + 1 := Finset.card_insert_le _ _
  · have hdisjXY : Disjoint Cx Cy := compOf_disjoint a b hCx_mem hCy_mem hxy_eq
    have hcomp_other : ∀ C ∈ compOf a b, C ≠ Cx → C ≠ Cy → C ∈ compOf a' b' := by
      intro C hC hneX hneY
      have hdisjX := compOf_disjoint a b hC hCx_mem hneX
      have hdisjY := compOf_disjoint a b hC hCy_mem hneY
      have hxNC : x ∉ C := Finset.disjoint_right.mp hdisjX hxCx
      have hyNC : y ∉ C := Finset.disjoint_right.mp hdisjY hyCy
      simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
      refine ⟨hC.1, ?_, fun D hD hDne hDcut => ?_⟩
      · rw [hcut_snoc C]; simp [hxNC, hyNC, hC.2.1]
      · rw [hcut_snoc D] at hDcut
        exact hC.2.2 D hD hDne (by omega)
    have hcomp_union : Cx ∪ Cy ∈ compOf a' b' := by
      have hCxcut := (cut_eq_zero_iff a b Cx).mp (Finset.mem_filter.mp hCx_mem).2.2.1
      have hCycut := (cut_eq_zero_iff a b Cy).mp (Finset.mem_filter.mp hCy_mem).2.2.1
      simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨x, Finset.mem_union_left _ hxCx⟩, ?_, fun D hD hDne hDcut => ?_⟩
      · rw [hcut_snoc (Cx ∪ Cy)]
        have h0 : (cutOf a b (Cx ∪ Cy)).card = 0 := by
          rw [cut_eq_zero_iff]; intro i
          simp only [Finset.mem_union, hCxcut i, hCycut i]
        simp [hxCx, hyCy, h0]
      · have hDsub : D ⊆ Cx ∪ Cy := Finset.mem_powerset.mp hD
        rw [hcut_snoc D] at hDcut
        have hDcut0 : (cutOf a b D).card = 0 := by omega
        have hxy_same : x ∈ D ↔ y ∈ D := by
          by_cases hxD : x ∈ D <;> by_cases hyD : y ∈ D <;> simp_all
        have hDx_cut : (cutOf a b (D ∩ Cx)).card = 0 := by
          rw [cut_eq_zero_iff] at hDcut0 ⊢
          intro i; simp only [Finset.mem_inter, hDcut0 i, hCxcut i]
        have hDy_cut : (cutOf a b (D ∩ Cy)).card = 0 := by
          rw [cut_eq_zero_iff] at hDcut0 ⊢
          intro i; simp only [Finset.mem_inter, hDcut0 i, hCycut i]
        have hDx_cases : D ∩ Cx = ∅ ∨ D ∩ Cx = Cx := by
          by_cases hne : (D ∩ Cx).Nonempty
          · right
            exact (Finset.mem_filter.mp hCx_mem).2.2.2 (D ∩ Cx)
              (Finset.mem_powerset.mpr Finset.inter_subset_right) hne hDx_cut
          · left; exact Finset.not_nonempty_iff_eq_empty.mp hne
        have hDy_cases : D ∩ Cy = ∅ ∨ D ∩ Cy = Cy := by
          by_cases hne : (D ∩ Cy).Nonempty
          · right
            exact (Finset.mem_filter.mp hCy_mem).2.2.2 (D ∩ Cy)
              (Finset.mem_powerset.mpr Finset.inter_subset_right) hne hDy_cut
          · left; exact Finset.not_nonempty_iff_eq_empty.mp hne
        have hD_eq : D = (D ∩ Cx) ∪ (D ∩ Cy) := by
          ext v; simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · intro hv; rcases Finset.mem_union.mp (hDsub hv) with h1 | h2
            · exact Or.inl ⟨hv, h1⟩
            · exact Or.inr ⟨hv, h2⟩
          · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
        rcases hDx_cases with h1 | h1 <;> rcases hDy_cases with h2 | h2
        · exfalso; rw [h1, h2, Finset.empty_union] at hD_eq; exact hDne.ne_empty hD_eq
        · exfalso
          have hyD : y ∈ D := (Finset.mem_inter.mp (h2.symm ▸ hyCy)).1
          have hxD : x ∈ D := hxy_same.mpr hyD
          have hx_in : x ∈ D ∩ Cx := Finset.mem_inter.mpr ⟨hxD, hxCx⟩
          rw [h1] at hx_in; simp at hx_in
        · exfalso
          have hxD : x ∈ D := (Finset.mem_inter.mp (h1.symm ▸ hxCx)).1
          have hyD : y ∈ D := hxy_same.mp hxD
          have hy_in : y ∈ D ∩ Cy := Finset.mem_inter.mpr ⟨hyD, hyCy⟩
          rw [h2] at hy_in; simp at hy_in
        · rw [hD_eq, h1, h2]
    have hbad_union : goodOf a b Cx = false → goodOf a b Cy = false → goodOf a' b' (Cx ∪ Cy) = false := by
      intro hbx hby
      by_contra hg'
      have hgt : goodOf a' b' (Cx ∪ Cy) = true := by cases h : goodOf a' b' (Cx ∪ Cy) <;> simp_all
      rcases (goodOf_eq_true_iff a' b' (Cx ∪ Cy)).mp hgt with ⟨j, hj_str, hjU⟩
      have hj_not_last : j ≠ Fin.last h := by
        intro heq; subst heq
        have hyNCx : y ∉ Cx := Finset.disjoint_right.mp hdisjXY hyCy
        have hge3 := (Finset.mem_filter.mp hj_str).2 Cx (Finset.mem_univ Cx) (by simp [a', b', hxCx, hyNCx])
        rw [hcut_snoc Cx, (Finset.mem_filter.mp hCx_mem).2.2.1] at hge3
        simp [hxCx, hyNCx] at hge3
      rcases Fin.exists_castSucc_eq.mpr hj_not_last with ⟨i, rfl⟩
      have hCxcut := (cut_eq_zero_iff a b Cx).mp (Finset.mem_filter.mp hCx_mem).2.2.1
      have hCycut := (cut_eq_zero_iff a b Cy).mp (Finset.mem_filter.mp hCy_mem).2.2.1
      simp only [a', Fin.snoc_castSucc, Finset.mem_union] at hjU
      rcases hjU with haiX | haiY
      · have hnot_str : i ∉ strongOf a b := by
          intro hst
          have : goodOf a b Cx = true := (goodOf_eq_true_iff a b Cx).mpr ⟨i, hst, haiX⟩
          rw [this] at hbx; exact Bool.noConfusion hbx
        simp only [strongOf, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hnot_str
        rcases hnot_str with ⟨S, _, hsep, hlt3⟩
        let S' : Finset (Fin n) := if x ∈ S then (S ∩ Cx) ∪ Cy else S ∩ Cx
        have hbiX : b i ∈ Cx := (hCxcut i).mp haiX
        have hai_iff : a i ∈ S' ↔ a i ∈ S := by
          have haNY : a i ∉ Cy := Finset.disjoint_left.mp hdisjXY haiX
          dsimp only [S']; split_ifs <;> simp [haiX, haNY]
        have hbi_iff : b i ∈ S' ↔ b i ∈ S := by
          have hbNY : b i ∉ Cy := Finset.disjoint_left.mp hdisjXY hbiX
          dsimp only [S']; split_ifs <;> simp [hbiX, hbNY]
        have hxy_same : x ∈ S' ↔ y ∈ S' := by
          have hyNX : y ∉ Cx := Finset.disjoint_right.mp hdisjXY hyCy
          have hxNY : x ∉ Cy := Finset.disjoint_left.mp hdisjXY hxCx
          dsimp only [S']; split_ifs with hxS <;> simp [hxS, hxCx, hyCy, hyNX, hxNY]
        have hcut_le : (cutOf a b S').card ≤ (cutOf a b S).card := by
          refine Finset.card_le_card fun e he => ?_
          rw [cut_mem_iff] at he ⊢
          by_cases haeX : a e ∈ Cx
          · have hbeX := (hCxcut e).mp haeX
            have haeNY : a e ∉ Cy := Finset.disjoint_left.mp hdisjXY haeX
            have hbeNY : b e ∉ Cy := Finset.disjoint_left.mp hdisjXY hbeX
            dsimp only [S'] at he
            split_ifs at he <;> simpa [haeX, hbeX, haeNY, hbeNY] using he
          · have hbeX : b e ∉ Cx := fun h => haeX ((hCxcut e).mpr h)
            exfalso; apply he
            dsimp only [S']
            split_ifs
            · simp [haeX, hbeX, hCycut e]
            · simp [haeX, hbeX]
        have hge3 := (Finset.mem_filter.mp hj_str).2 S' (Finset.mem_univ S')
          (by simpa [a', b', hai_iff, hbi_iff] using hsep)
        rw [hcut_snoc S'] at hge3
        have hxy_false : (decide (x ∈ S') != decide (y ∈ S')) = false := by
          by_cases h1 : x ∈ S'
          · have h2 := hxy_same.mp h1; simp [h1, h2]
          · have h2 : y ∉ S' := fun h => h1 (hxy_same.mpr h); simp [h1, h2]
        simp [hxy_false] at hge3
        omega
      · have hnot_str : i ∉ strongOf a b := by
          intro hst
          have : goodOf a b Cy = true := (goodOf_eq_true_iff a b Cy).mpr ⟨i, hst, haiY⟩
          rw [this] at hby; exact Bool.noConfusion hby
        simp only [strongOf, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hnot_str
        rcases hnot_str with ⟨S, _, hsep, hlt3⟩
        let S' : Finset (Fin n) := if y ∈ S then (S ∩ Cy) ∪ Cx else S ∩ Cy
        have hbiY : b i ∈ Cy := (hCycut i).mp haiY
        have hai_iff : a i ∈ S' ↔ a i ∈ S := by
          have haNX : a i ∉ Cx := Finset.disjoint_right.mp hdisjXY haiY
          dsimp only [S']; split_ifs <;> simp [haiY, haNX]
        have hbi_iff : b i ∈ S' ↔ b i ∈ S := by
          have hbNX : b i ∉ Cx := Finset.disjoint_right.mp hdisjXY hbiY
          dsimp only [S']; split_ifs <;> simp [hbiY, hbNX]
        have hxy_same : x ∈ S' ↔ y ∈ S' := by
          have hyNX : y ∉ Cx := Finset.disjoint_right.mp hdisjXY hyCy
          have hxNY : x ∉ Cy := Finset.disjoint_left.mp hdisjXY hxCx
          dsimp only [S']; split_ifs with hyS <;> simp [hyS, hxCx, hyCy, hyNX, hxNY]
        have hcut_le : (cutOf a b S').card ≤ (cutOf a b S).card := by
          refine Finset.card_le_card fun e he => ?_
          rw [cut_mem_iff] at he ⊢
          by_cases haeY : a e ∈ Cy
          · have hbeY := (hCycut e).mp haeY
            have haeNX : a e ∉ Cx := Finset.disjoint_right.mp hdisjXY haeY
            have hbeNX : b e ∉ Cx := Finset.disjoint_right.mp hdisjXY hbeY
            dsimp only [S'] at he
            split_ifs at he <;> simpa [haeY, hbeY, haeNX, hbeNX] using he
          · have hbeY : b e ∉ Cy := fun h => haeY ((hCycut e).mpr h)
            exfalso; apply he
            dsimp only [S']
            split_ifs
            · simp [haeY, hbeY, hCxcut e]
            · simp [haeY, hbeY]
        have hge3 := (Finset.mem_filter.mp hj_str).2 S' (Finset.mem_univ S')
          (by simpa [a', b', hai_iff, hbi_iff] using hsep)
        rw [hcut_snoc S'] at hge3
        have hxy_false : (decide (x ∈ S') != decide (y ∈ S')) = false := by
          by_cases h1 : x ∈ S'
          · have h2 := hxy_same.mp h1; simp [h1, h2]
          · have h2 : y ∉ S' := fun h => h1 (hxy_same.mpr h); simp [h1, h2]
        simp [hxy_false] at hge3
        omega
    let B0 := (compOf a b).filter (fun C => goodOf a b C = false)
    let B1 := (compOf a' b').filter (fun C => goodOf a' b' C = false)
    have hother_sub : (B0.erase Cx).erase Cy ⊆ B1.erase (Cx ∪ Cy) := by
      intro C hC
      simp only [Finset.mem_erase, B0, B1, Finset.mem_filter] at hC ⊢
      rcases hC with ⟨hneY, hneX, hCcomp, hCbad⟩
      have hC_in' := hcomp_other C hCcomp hneX hneY
      have hC_neU : C ≠ Cx ∪ Cy := by
        intro heq
        have hxC : x ∈ C := by rw [heq]; exact Finset.mem_union_left _ hxCx
        exact Finset.disjoint_right.mp (compOf_disjoint a b hCcomp hCx_mem hneX) hxCx hxC
      refine ⟨hC_neU, hC_in', ?_⟩
      by_contra hg'
      have hgt : goodOf a' b' C = true := by cases h : goodOf a' b' C <;> simp_all
      have := hgood_other C hCcomp hneX hneY hgt
      rw [this] at hCbad; exact Bool.noConfusion hCbad
    have hcard_other : ((B0.erase Cx).erase Cy).card ≤ (B1.erase (Cx ∪ Cy)).card :=
      Finset.card_le_card hother_sub
    by_cases hbx : goodOf a b Cx = false
    · by_cases hby : goodOf a b Cy = false
      · have hCxB : Cx ∈ B0 := Finset.mem_filter.mpr ⟨hCx_mem, hbx⟩
        have hCyB : Cy ∈ B0.erase Cx := Finset.mem_erase.mpr ⟨Ne.symm hxy_eq, Finset.mem_filter.mpr ⟨hCy_mem, hby⟩⟩
        have hUB : Cx ∪ Cy ∈ B1 := Finset.mem_filter.mpr ⟨hcomp_union, hbad_union hbx hby⟩
        rw [Finset.card_erase_of_mem hCyB, Finset.card_erase_of_mem hCxB,
            Finset.card_erase_of_mem hUB] at hcard_other
        have hB0_2 : 2 ≤ B0.card := by
          have hsub : ({Cx, Cy} : Finset (Finset (Fin n))) ⊆ B0 := by
            intro K hK; simp only [Finset.mem_insert, Finset.mem_singleton] at hK
            rcases hK with rfl | rfl
            · exact hCxB
            · exact Finset.mem_of_mem_erase hCyB
          have := Finset.card_le_card hsub; rw [Finset.card_pair hxy_eq] at this; exact this
        have hB1_1 : 1 ≤ B1.card := Finset.card_pos.mpr ⟨Cx ∪ Cy, hUB⟩
        change B0.card ≤ B1.card + 1
        omega
      · have hCyNB : Cy ∉ B0 := fun h => hby (Finset.mem_filter.mp h).2
        have hCyNE : Cy ∉ B0.erase Cx := fun h => hCyNB (Finset.mem_of_mem_erase h)
        rw [Finset.erase_eq_of_notMem hCyNE] at hcard_other
        have h1 : (B0.erase Cx).card ≤ B1.card := hcard_other.trans (Finset.card_erase_le)
        have h2 : B0.card ≤ (B0.erase Cx).card + 1 := by
          by_cases hCxB : Cx ∈ B0
          · rw [Finset.card_erase_of_mem hCxB]
            have : 1 ≤ B0.card := Finset.card_pos.mpr ⟨Cx, hCxB⟩
            omega
          · rw [Finset.erase_eq_of_notMem hCxB]; omega
        change B0.card ≤ B1.card + 1
        omega
    · have hCxNB : Cx ∉ B0 := fun h => hbx (Finset.mem_filter.mp h).2
      rw [Finset.erase_eq_of_notMem hCxNB] at hcard_other
      have h1 : (B0.erase Cy).card ≤ B1.card := hcard_other.trans (Finset.card_erase_le)
      have h2 : B0.card ≤ (B0.erase Cy).card + 1 := by
        by_cases hCyB : Cy ∈ B0
        · rw [Finset.card_erase_of_mem hCyB]
          have : 1 ≤ B0.card := Finset.card_pos.mpr ⟨Cy, hCyB⟩
          omega
        · rw [Finset.erase_eq_of_notMem hCyB]; omega
      change B0.card ≤ B1.card + 1
      omega

lemma bad_le_addCases {n m : Nat} (u v : Fin m → Fin n) :
    ∀ (s : Nat) (left right : Fin s → Fin n),
      badOf u v ≤ badOf (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n) + s := by
  intro s
  induction s with
  | zero =>
    intro left right
    have hu : (Fin.addCases (m := m) (n := 0) u left : Fin (m + 0) → Fin n) = u := by
      funext i
      exact Fin.addCases_left i
    have hv : (Fin.addCases (m := m) (n := 0) v right : Fin (m + 0) → Fin n) = v := by
      funext i
      exact Fin.addCases_left i
    rw [hu, hv]
    omega
  | succ s ih =>
    intro left right
    let left0 : Fin s → Fin n := Fin.init left
    let right0 : Fin s → Fin n := Fin.init right
    have hih := ih left0 right0
    have hstep := bad_add_one_edge (Fin.addCases u left0) (Fin.addCases v right0)
      (left (Fin.last s)) (right (Fin.last s))
    have hu : (Fin.snoc (α := fun _ => Fin n) (Fin.addCases u left0) (left (Fin.last s)) : Fin (m + (s + 1)) → Fin n) =
        Fin.addCases (m := m) (n := s + 1) u left := by
      funext j
      refine Fin.lastCases ?_ ?_ j
      · simp only [Fin.snoc_last]
        trans Fin.addCases (m := m) (n := s + 1) u left (Fin.natAdd m (Fin.last s))
        · rw [Fin.addCases_right]
        · exact congrArg (Fin.addCases (m := m) (n := s + 1) u left) (Fin.ext rfl)
      · intro k
        simp only [Fin.snoc_castSucc]
        refine Fin.addCases (m := m) (n := s) ?_ ?_ k
        · intro i
          have h1 : (Fin.castAdd s i).castSucc = (Fin.castAdd (s + 1) i : Fin (m + (s + 1))) := by
            ext; simp
          rw [h1, Fin.addCases_left, Fin.addCases_left]
        · intro i
          have h1 : (Fin.natAdd m i).castSucc = (Fin.natAdd m i.castSucc : Fin (m + (s + 1))) := by
            ext; simp
          rw [h1, Fin.addCases_right, Fin.addCases_right]
          rfl
    have hv : (Fin.snoc (α := fun _ => Fin n) (Fin.addCases v right0) (right (Fin.last s)) : Fin (m + (s + 1)) → Fin n) =
        Fin.addCases (m := m) (n := s + 1) v right := by
      funext j
      refine Fin.lastCases ?_ ?_ j
      · simp only [Fin.snoc_last]
        trans Fin.addCases (m := m) (n := s + 1) v right (Fin.natAdd m (Fin.last s))
        · rw [Fin.addCases_right]
        · exact congrArg (Fin.addCases (m := m) (n := s + 1) v right) (Fin.ext rfl)
      · intro k
        simp only [Fin.snoc_castSucc]
        refine Fin.addCases (m := m) (n := s) ?_ ?_ k
        · intro i
          have h1 : (Fin.castAdd s i).castSucc = (Fin.castAdd (s + 1) i : Fin (m + (s + 1))) := by
            ext; simp
          rw [h1, Fin.addCases_left, Fin.addCases_left]
        · intro i
          have h1 : (Fin.natAdd m i).castSucc = (Fin.natAdd m i.castSucc : Fin (m + (s + 1))) := by
            ext; simp
          rw [h1, Fin.addCases_right, Fin.addCases_right]
          rfl
    rw [hu, hv] at hstep
    omega

lemma cut_mono_addCases {n m s : Nat} (u v : Fin m → Fin n) (left right : Fin s → Fin n)
    (S : Finset (Fin n)) :
    (cutOf u v S).card ≤ (cutOf (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n) S).card := by
  refine Finset.card_le_card_of_injOn (Fin.castAdd s) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, cutOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simpa [Fin.addCases_left] using hi
  · intro i1 _ i2 _ heq; exact Fin.castAdd_injective m s heq

lemma strong_mono_addCases {n m s : Nat} (u v : Fin m → Fin n) (left right : Fin s → Fin n)
    {i : Fin m} (hi : i ∈ strongOf u v) :
    Fin.castAdd s i ∈ strongOf (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n) := by
  simp only [strongOf, Finset.mem_filter, Finset.mem_univ, true_and, Fin.addCases_left] at hi ⊢
  intro S _ hsep
  exact (hi S trivial hsep).trans (cut_mono_addCases u v left right S)

lemma reach_mono_addCases {n m s : Nat} (u v : Fin m → Fin n) (left right : Fin s → Fin n)
    {x y : Fin n} (hxy : Relation.ReflTransGen (adjE u v Finset.univ) x y) :
    Relation.ReflTransGen (adjE (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n) Finset.univ) x y := by
  induction hxy with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨i, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Relation.ReflTransGen.tail ih
        ⟨Fin.castAdd s i, Finset.mem_univ _, Or.inl ⟨Fin.addCases_left i, Fin.addCases_left i⟩⟩
    · exact Relation.ReflTransGen.tail ih
        ⟨Fin.castAdd s i, Finset.mem_univ _, Or.inr ⟨Fin.addCases_left i, Fin.addCases_left i⟩⟩

theorem main :
∀ (n m : Nat) (u v : Fin m → Fin n), (∀ i, u i ≠ v i) →
  let Bits := Finset (Fin n)
  let cube := (Finset.univ : Finset Bits)
  let labels := (Finset.univ : Finset (Fin m))
  let cut := fun (S : Bits) => labels.filter
    (fun i => decide (u i ∈ S) != decide (v i ∈ S))
  let components := cube.filter (fun C => C.Nonempty ∧ (cut C).card = 0 ∧
    ∀ D ∈ C.powerset, D.Nonempty → (cut D).card = 0 → D = C)
  let strong := labels.filter (fun i => ∀ S ∈ cube,
    (decide (u i ∈ S) != decide (v i ∈ S)) = true → 3 ≤ (cut S).card)
  let good := fun (C : Bits) => strong.toList.any (fun i => decide (u i ∈ C))
  2 ≤ n →
  let bad := (components.filter (fun C => good C = false)).card
  let forest := components.toList.all (fun C =>
    (labels.filter (fun i => u i ∈ C)).card + 1 == C.card)
  let decodes := fun (h : Nat) (a b : Fin h → Fin n) =>
    let sat := fun (A : Finset Bits) (p : Fin h → Bool × Bool) =>
      ∃ x ∈ A, ∀ i, (decide (a i ∈ x), decide (b i ∈ x)) ≠ p i
    ∀ A B : Finset Bits, (∀ p, (sat A p ↔ sat B p)) → A = B
  ∀ k : Nat,
    (∃ (s : Nat) (left right : Fin s → Fin n), s ≤ k ∧ (∀ j, left j ≠ right j) ∧
      decodes (m+s) (Fin.addCases u left) (Fin.addCases v right)) ↔
      bad + (if forest then 1 else 0) ≤ k := by
  classical
  intro n m u v huv
  dsimp only
  intro hn2 k
  have hforest_iff : ((compOf u v).toList.all (fun C =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => u i ∈ C)).card + 1 == C.card)) = true ↔
      ∀ C ∈ compOf u v, ((Finset.univ : Finset (Fin m)).filter (fun i => u i ∈ C)).card + 1 = C.card := by
    simp [List.all_eq_true]
  change (∃ (s : Nat) (left right : Fin s → Fin n), s ≤ k ∧ (∀ j, left j ≠ right j) ∧
      decodesOf (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n)) ↔
      badOf u v + (if ((compOf u v).toList.all (fun C =>
        ((Finset.univ : Finset (Fin m)).filter (fun i => u i ∈ C)).card + 1 == C.card))
        then 1 else 0) ≤ k
  constructor
  · rintro ⟨s, left, right, hsk, hlr, hdec⟩
    have hall_good := (decodes_iff_all_good (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n)).mp hdec
    have hbad_zero : badOf (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n) = 0 := by
      unfold badOf
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro C hC
      rw [hall_good C hC]
      decide
    have hbad_le_s : badOf u v ≤ s := by
      have := bad_le_addCases u v s left right
      omega
    split_ifs with hf
    · have hfor := hforest_iff.mp hf
      have hall_bad : ∀ C ∈ compOf u v, goodOf u v C = false := by
        intro C hC
        by_contra hnb
        have hgt : goodOf u v C = true := by cases h : goodOf u v C <;> simp_all
        have hge := good_component_edges_ge u v huv hC hgt
        have heq := hfor C hC
        omega
      have hbad_eq_c : badOf u v = (compOf u v).card := by
        unfold badOf
        congr 1
        ext C
        simp only [Finset.mem_filter, and_iff_left_iff_imp]
        exact hall_bad C
      have hmn : m + badOf u v = n := by
        rw [hbad_eq_c]
        have hsum := Finset.sum_congr rfl fun C hC => hfor C hC
        rw [Finset.sum_add_distrib, sum_edges_compOf, Finset.sum_const, smul_eq_mul, mul_one,
            sum_card_compOf] at hsum
        exact hsum
      have hne_all : ∀ j : Fin (m + s), (Fin.addCases (m := m) (n := s) u left j : Fin n) ≠ Fin.addCases (m := m) (n := s) v right j := by
        intro j
        refine Fin.addCases (m := m) (n := s) ?_ ?_ j
        · intro i; simpa using huv i
        · intro i; simpa using hlr i
      have hsum_plus : n + (compOf (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n)).card ≤ m + s := by
        have h1 : (compOf (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n)).sum (fun K => K.card + 1) ≤
            (compOf (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n)).sum
              (fun K => ((Finset.univ : Finset (Fin (m + s))).filter
                (fun i => (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) i ∈ K)).card) :=
          Finset.sum_le_sum fun K hK =>
            good_component_edges_ge _ _ hne_all hK (hall_good K hK)
        rw [Finset.sum_add_distrib, sum_card_compOf, Finset.sum_const, smul_eq_mul, mul_one,
            sum_edges_compOf] at h1
        exact h1
      have hc_pos : 1 ≤ (compOf (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n)).card := by
        let x0 : Fin n := ⟨0, by omega⟩
        let K0 := Finset.univ.filter (fun y =>
          Relation.ReflTransGen (adjE (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n) Finset.univ) x0 y)
        exact Finset.card_pos.mpr ⟨K0, (mem_compOf_iff_reach _ _ K0).mpr ⟨x0, rfl⟩⟩
      omega
    · omega
  · intro hk
    let rep : Finset (Fin n) → Fin n := fun C =>
      if h : C.Nonempty then h.choose else ⟨0, by omega⟩
    have hrep_mem : ∀ C ∈ compOf u v, rep C ∈ C := by
      intro C hC
      have hne : C.Nonempty := (Finset.mem_filter.mp hC).2.1
      simp only [rep, dif_pos hne]
      exact hne.choose_spec
    have hof_list : ∀ (L : List (Fin n × Fin n)),
        L.length ≤ k →
        (∀ e ∈ L, e.1 ≠ e.2) →
        (∀ K ∈ compOf (Fin.addCases (m := m) (n := L.length) u (fun j : Fin L.length => (L.get j).1) : Fin (m + L.length) → Fin n)
          (Fin.addCases (m := m) (n := L.length) v (fun j : Fin L.length => (L.get j).2) : Fin (m + L.length) → Fin n),
          goodOf (Fin.addCases (m := m) (n := L.length) u (fun j : Fin L.length => (L.get j).1) : Fin (m + L.length) → Fin n)
            (Fin.addCases (m := m) (n := L.length) v (fun j : Fin L.length => (L.get j).2) : Fin (m + L.length) → Fin n) K = true) →
        ∃ (s : Nat) (left right : Fin s → Fin n), s ≤ k ∧ (∀ j, left j ≠ right j) ∧
          decodesOf (Fin.addCases (m := m) (n := s) u left : Fin (m + s) → Fin n) (Fin.addCases (m := m) (n := s) v right : Fin (m + s) → Fin n) := by
      intro L hLlen hLne hLgood
      refine ⟨L.length, fun j => (L.get j).1, fun j => (L.get j).2, hLlen,
        fun j => hLne (L.get j) (List.get_mem L j), ?_⟩
      exact (decodes_iff_all_good _ _).mpr hLgood
    by_cases hhas_good : ∃ C0 ∈ compOf u v, goodOf u v C0 = true
    · rcases hhas_good with ⟨C0, hC0, hC0_good⟩
      have hf_false : ((compOf u v).toList.all (fun C =>
          ((Finset.univ : Finset (Fin m)).filter (fun i => u i ∈ C)).card + 1 == C.card)) = false := by
        by_contra hnt
        have hft : ((compOf u v).toList.all (fun C =>
            ((Finset.univ : Finset (Fin m)).filter (fun i => u i ∈ C)).card + 1 == C.card)) = true := by
          cases h : ((compOf u v).toList.all (fun C =>
            ((Finset.univ : Finset (Fin m)).filter (fun i => u i ∈ C)).card + 1 == C.card)) <;> simp_all
        have hge := good_component_edges_ge u v huv hC0 hC0_good
        have heq := hforest_iff.mp hft C0 hC0
        omega
      simp only [hf_false, Bool.false_eq_true, ite_false, add_zero] at hk
      let badList := ((compOf u v).filter (fun C => goodOf u v C = false)).toList
      let r0 := rep C0
      have hr0 : r0 ∈ C0 := hrep_mem C0 hC0
      let L := badList.map (fun C => (r0, rep C))
      refine hof_list L (by simpa [L, badList, badOf] using hk) ?_ ?_
      · intro e he
        rcases List.mem_map.mp he with ⟨C, hC_in, rfl⟩
        have hCf := Finset.mem_toList.mp hC_in
        rcases Finset.mem_filter.mp hCf with ⟨hC_comp, hC_bad⟩
        have hneC : C0 ≠ C := by
          intro heq; subst heq; rw [hC0_good] at hC_bad; exact Bool.noConfusion hC_bad
        exact fun heq => by
          dsimp only at heq
          exact Finset.disjoint_left.mp (compOf_disjoint u v hC0 hC_comp hneC) hr0 (heq ▸ hrep_mem C hC_comp)
      · intro K hK
        let left : Fin L.length → Fin n := fun j => (L.get j).1
        let right : Fin L.length → Fin n := fun j => (L.get j).2
        let a' : Fin (m + L.length) → Fin n := Fin.addCases u left
        let b' : Fin (m + L.length) → Fin n := Fin.addCases v right
        rcases (mem_compOf_iff_reach a' b' K).mp hK with ⟨x, hKx⟩
        let Cx := Finset.univ.filter (fun y => Relation.ReflTransGen (adjE u v Finset.univ) x y)
        have hCx : Cx ∈ compOf u v := (mem_compOf_iff_reach u v Cx).mpr ⟨x, rfl⟩
        have hCx_sub : Cx ⊆ K := by
          intro y hy
          rw [hKx]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact reach_mono_addCases u v left right (Finset.mem_filter.mp hy).2
        by_cases hCxg : goodOf u v Cx = true
        · rcases (goodOf_eq_true_iff u v Cx).mp hCxg with ⟨i0, hi0_str, hi0_Cx⟩
          rw [goodOf_eq_true_iff]
          exact ⟨Fin.castAdd L.length i0, strong_mono_addCases u v left right hi0_str,
            by simpa [a'] using hCx_sub hi0_Cx⟩
        · have hCxf : goodOf u v Cx = false := by cases h : goodOf u v Cx <;> simp_all
          have hCx_in : Cx ∈ badList := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hCx, hCxf⟩)
          have hpair_in : (r0, rep Cx) ∈ L := List.mem_map.mpr ⟨Cx, hCx_in, rfl⟩
          rcases List.mem_iff_get.mp hpair_in with ⟨j, hj⟩
          have hr_adj : adjE a' b' Finset.univ r0 (rep Cx) := by
            refine ⟨Fin.natAdd m j, Finset.mem_univ _, Or.inl ⟨?_, ?_⟩⟩
            · simp only [a', left, Fin.addCases_right, hj]
            · simp only [b', right, Fin.addCases_right, hj]
          have hrx_reach : Relation.ReflTransGen (adjE a' b' Finset.univ) x r0 := by
            have h1 : Relation.ReflTransGen (adjE a' b' Finset.univ) x (rep Cx) :=
              reach_mono_addCases u v left right (Finset.mem_filter.mp (hrep_mem Cx hCx)).2
            exact h1.tail (adjE_symm hr_adj)
          rcases (goodOf_eq_true_iff u v C0).mp hC0_good with ⟨i0, hi0_str, hi0_C0⟩
          have hr0_i0 : Relation.ReflTransGen (adjE u v Finset.univ) r0 (u i0) := by
            rcases (mem_compOf_iff_reach u v C0).mp hC0 with ⟨z0, hz0⟩
            have h1 : Relation.ReflTransGen (adjE u v Finset.univ) z0 r0 := by
              rw [hz0] at hr0; exact (Finset.mem_filter.mp hr0).2
            have h2 : Relation.ReflTransGen (adjE u v Finset.univ) z0 (u i0) := by
              rw [hz0] at hi0_C0; exact (Finset.mem_filter.mp hi0_C0).2
            exact (reachE_symm h1).trans h2
          have hui0_K : u i0 ∈ K := by
            rw [hKx]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hrx_reach.trans (reach_mono_addCases u v left right hr0_i0)
          rw [goodOf_eq_true_iff]
          exact ⟨Fin.castAdd L.length i0, strong_mono_addCases u v left right hi0_str,
            by simpa [a'] using hui0_K⟩
    · push_neg at hhas_good
      have hall_bad : ∀ C ∈ compOf u v, goodOf u v C = false := by
        intro C hC
        have := hhas_good C hC
        cases h : goodOf u v C <;> simp_all
      have hbad_eq_c : badOf u v = (compOf u v).card := by
        unfold badOf; congr 1; ext C
        simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hall_bad C
      by_cases hf : ((compOf u v).toList.all (fun C =>
          ((Finset.univ : Finset (Fin m)).filter (fun i => u i ∈ C)).card + 1 == C.card)) = true
      · simp only [hf, ite_true] at hk
        have hfor := hforest_iff.mp hf
        have hmn : m + (compOf u v).card = n := by
          have hsum := Finset.sum_congr rfl fun C hC => hfor C hC
          rw [Finset.sum_add_distrib, sum_edges_compOf, Finset.sum_const, smul_eq_mul, mul_one,
              sum_card_compOf] at hsum
          exact hsum
        have hc_pos : 1 ≤ (compOf u v).card := by
          let x0 : Fin n := ⟨0, by omega⟩
          let K0 := Finset.univ.filter (fun y => Relation.ReflTransGen (adjE u v Finset.univ) x0 y)
          exact Finset.card_pos.mpr ⟨K0, (mem_compOf_iff_reach u v K0).mpr ⟨x0, rfl⟩⟩
        by_cases hc1 : (compOf u v).card = 1
        · have hm_pos : 1 ≤ m := by omega
          let i0 : Fin m := ⟨0, by omega⟩
          let L : List (Fin n × Fin n) := [(u i0, v i0), (u i0, v i0)]
          refine hof_list L (by simp [L]; omega) (by intro e he; simp [L] at he; subst he; exact huv i0) ?_
          intro K hK
          let left : Fin L.length → Fin n := fun j => (L.get j).1
          let right : Fin L.length → Fin n := fun j => (L.get j).2
          let a' : Fin (m + L.length) → Fin n := Fin.addCases u left
          let b' : Fin (m + L.length) → Fin n := Fin.addCases v right
          change goodOf a' b' K = true
          have hconn : ∀ x y : Fin n, Relation.ReflTransGen (adjE u v Finset.univ) x y := by
            intro x y
            let Cx := Finset.univ.filter (fun z => Relation.ReflTransGen (adjE u v Finset.univ) x z)
            let Cy := Finset.univ.filter (fun z => Relation.ReflTransGen (adjE u v Finset.univ) y z)
            have hCx : Cx ∈ compOf u v := (mem_compOf_iff_reach u v Cx).mpr ⟨x, rfl⟩
            have hCy : Cy ∈ compOf u v := (mem_compOf_iff_reach u v Cy).mpr ⟨y, rfl⟩
            have heq : Cx = Cy := Finset.card_le_one.mp (by omega : (compOf u v).card ≤ 1) Cx hCx Cy hCy
            have hyCx : y ∈ Cx := by rw [heq]; simp [Cy, Relation.ReflTransGen.refl]
            exact (Finset.mem_filter.mp hyCx).2
          have hui0_K : u i0 ∈ K := by
            rcases (mem_compOf_iff_reach a' b' K).mp hK with ⟨x, hKx⟩
            rw [hKx]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact reach_mono_addCases u v left right (hconn x (u i0))
          rw [goodOf_eq_true_iff]
          refine ⟨Fin.castAdd L.length i0, ?_, by simpa [a'] using hui0_K⟩
          have ha0 : a' (Fin.castAdd L.length i0) = u i0 := Fin.addCases_left i0
          have hb0 : b' (Fin.castAdd L.length i0) = v i0 := Fin.addCases_left i0
          simp only [strongOf, Finset.mem_filter, Finset.mem_univ, true_and, ha0, hb0]
          intro S _ hsep
          let e0 : Fin (m + L.length) := Fin.castAdd L.length i0
          let e1 : Fin (m + L.length) := Fin.natAdd m ⟨0, by simp [L]⟩
          let e2 : Fin (m + L.length) := Fin.natAdd m ⟨1, by simp [L]⟩
          have hsub : ({e0, e1, e2} : Finset (Fin (m + L.length))) ⊆ cutOf a' b' S := by
            intro j hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl | rfl
            · simpa only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and, a', b', e0, Fin.addCases_left] using hsep
            · simpa only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and, a', b', e1, left, right, Fin.addCases_right, L, List.get_eq_getElem, List.getElem_cons_zero] using hsep
            · simpa only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and, a', b', e2, left, right, Fin.addCases_right, L, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero] using hsep
          have h01 : e0 ≠ e1 := by intro h; have := congrArg Fin.val h; simp [e0, e1] at this; omega
          have h02 : e0 ≠ e2 := by intro h; have := congrArg Fin.val h; simp [e0, e2] at this
          have h12 : e1 ≠ e2 := by intro h; have := congrArg Fin.val h; simp [e1, e2] at this
          have hc3 : ({e0, e1, e2} : Finset (Fin (m + L.length))).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
                Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
          calc 3 = ({e0, e1, e2} : Finset (Fin (m + L.length))).card := hc3.symm
            _ ≤ (cutOf a' b' S).card := Finset.card_le_card hsub
        · have hc2 : 2 ≤ (compOf u v).card := by omega
          rcases Finset.one_lt_card.mp (by omega : 1 < (compOf u v).card) with ⟨C0, hC0, C1, hC1, hC01⟩
          let r0 := rep C0
          let r1 := rep C1
          have hr0 : r0 ∈ C0 := hrep_mem C0 hC0
          have hr1 : r1 ∈ C1 := hrep_mem C1 hC1
          have hr01 : r0 ≠ r1 := fun heq => Finset.disjoint_left.mp (compOf_disjoint u v hC0 hC1 hC01) hr0 (heq ▸ hr1)
          let otherList := ((compOf u v).erase C0).toList
          have hother_len : otherList.length = (compOf u v).card - 1 := by
            simp [otherList, Finset.card_erase_of_mem hC0]
          let L : List (Fin n × Fin n) := (r0, r1) :: (r0, r1) :: otherList.map (fun C => (r0, rep C))
          have hL_len : L.length = (compOf u v).card + 1 := by
            simp only [L, List.length_cons, List.length_map, hother_len]; omega
          refine hof_list L (by omega) ?_ ?_
          · intro e he
            simp only [L, List.mem_cons, List.mem_map] at he
            rcases he with rfl | rfl | ⟨C, hCin, rfl⟩
            · exact hr01
            · exact hr01
            · rcases Finset.mem_erase.mp (Finset.mem_toList.mp hCin) with ⟨hCne, hCcomp⟩
              exact fun heq => by
                dsimp only at heq
                exact Finset.disjoint_left.mp (compOf_disjoint u v hC0 hCcomp hCne.symm) hr0 (heq ▸ hrep_mem C hCcomp)
          · intro K hK
            let left : Fin L.length → Fin n := fun j => (L.get j).1
            let right : Fin L.length → Fin n := fun j => (L.get j).2
            let a' : Fin (m + L.length) → Fin n := Fin.addCases u left
            let b' : Fin (m + L.length) → Fin n := Fin.addCases v right
            change goodOf a' b' K = true
            have hC1_in : C1 ∈ otherList :=
              Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hC01.symm, hC1⟩)
            rcases List.mem_iff_get.mp hC1_in with ⟨j1, hj1⟩
            let e0 : Fin (m + L.length) := Fin.natAdd m ⟨0, by simp [L]⟩
            let e1 : Fin (m + L.length) := Fin.natAdd m ⟨1, by simp [L]⟩
            let e2 : Fin (m + L.length) := Fin.natAdd m ⟨j1.val + 2, by simp [L]⟩
            have he0_ab : a' e0 = r0 ∧ b' e0 = r1 := by
              constructor
              · simp only [a', e0, left, Fin.addCases_right, L, List.get_eq_getElem, List.getElem_cons_zero]
              · simp only [b', e0, right, Fin.addCases_right, L, List.get_eq_getElem, List.getElem_cons_zero]
            have he1_ab : a' e1 = r0 ∧ b' e1 = r1 := by
              constructor
              · simp only [a', e1, left, Fin.addCases_right, L, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
              · simp only [b', e1, right, Fin.addCases_right, L, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_cons_zero]
            have he2_ab : a' e2 = r0 ∧ b' e2 = r1 := by
              have hget : L.get ⟨j1.val + 2, by simp [L]⟩ = (r0, r1) := by
                simp only [L, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_map]
                have : otherList[j1.val] = C1 := by simpa [List.get_eq_getElem] using hj1
                simp [this, r1]
              constructor
              · simp only [a', e2, left, Fin.addCases_right, hget]
              · simp only [b', e2, right, Fin.addCases_right, hget]
            have hr0_K : r0 ∈ K := by
              rcases (mem_compOf_iff_reach a' b' K).mp hK with ⟨x, hKx⟩
              rw [hKx]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              let Cx := Finset.univ.filter (fun z => Relation.ReflTransGen (adjE u v Finset.univ) x z)
              have hCx : Cx ∈ compOf u v := (mem_compOf_iff_reach u v Cx).mpr ⟨x, rfl⟩
              have hx_rep : Relation.ReflTransGen (adjE a' b' Finset.univ) x (rep Cx) :=
                reach_mono_addCases u v left right (Finset.mem_filter.mp (hrep_mem Cx hCx)).2
              by_cases hCx0 : Cx = C0
              · rwa [hCx0] at hx_rep
              · have hCx_in : Cx ∈ otherList :=
                  Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hCx0, hCx⟩)
                have hpair : (r0, rep Cx) ∈ L :=
                  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨Cx, hCx_in, rfl⟩))
                rcases List.mem_iff_get.mp hpair with ⟨j, hj⟩
                exact hx_rep.tail ⟨Fin.natAdd m j, Finset.mem_univ _, Or.inr ⟨by simp only [b', right, Fin.addCases_right, hj], by simp only [a', left, Fin.addCases_right, hj]⟩⟩
            rw [goodOf_eq_true_iff]
            refine ⟨e0, ?_, by rw [he0_ab.1]; exact hr0_K⟩
            simp only [strongOf, Finset.mem_filter, Finset.mem_univ, true_and, he0_ab.1, he0_ab.2]
            intro S _ hsep
            have hsub : ({e0, e1, e2} : Finset (Fin (m + L.length))) ⊆ cutOf a' b' S := by
              intro j hj
              simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl | rfl
              · simpa [cutOf, he0_ab.1, he0_ab.2] using hsep
              · simpa [cutOf, he1_ab.1, he1_ab.2] using hsep
              · simpa [cutOf, he2_ab.1, he2_ab.2] using hsep
            have h01 : e0 ≠ e1 := by intro h; have := congrArg Fin.val h; simp [e0, e1] at this
            have h02 : e0 ≠ e2 := by intro h; have := congrArg Fin.val h; simp [e0, e2] at this
            have h12 : e1 ≠ e2 := by intro h; have := congrArg Fin.val h; simp [e1, e2] at this
            have hc3 : ({e0, e1, e2} : Finset (Fin (m + L.length))).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
                  Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
            calc 3 = ({e0, e1, e2} : Finset (Fin (m + L.length))).card := hc3.symm
              _ ≤ (cutOf a' b' S).card := Finset.card_le_card hsub
      · simp only [hf, Bool.false_eq_true, ite_false, add_zero] at hk
        have hnot_all : ¬ ∀ C ∈ compOf u v,
            ((Finset.univ : Finset (Fin m)).filter (fun i => u i ∈ C)).card + 1 = C.card := by
          intro hall; exact hf (hforest_iff.mpr hall)
        push_neg at hnot_all
        rcases hnot_all with ⟨C0, hC0, hC0_ne⟩
        let EC0 := (Finset.univ : Finset (Fin m)).filter (fun i => u i ∈ C0)
        rcases compCount_eq_one_of_comp u v hC0 with ⟨hEV0, hcc0⟩
        have hge0 := compCount_add_card_ge u v C0 EC0 hEV0
        change EC0.card + 1 ≠ C0.card at hC0_ne
        have hlt0 : C0.card < compCount u v C0 EC0 + EC0.card := by rw [hcc0] at hge0 ⊢; omega
        rcases exists_nonbridge_of_ge u v C0 EC0 hEV0 hlt0 with ⟨i0, hi0_EC0, hi0_reach⟩
        have hcut2_i0 : ∀ S : Finset (Fin n),
            (decide (u i0 ∈ S) != decide (v i0 ∈ S)) = true → 2 ≤ (cutOf u v S).card := by
          intro S hsep
          have hreach : Relation.ReflTransGen (adjE u v (EC0.erase i0)) (u i0) (v i0) :=
            (Finset.mem_filter.mp hi0_reach).2
          have hex : ∃ i1 ∈ EC0.erase i0, i1 ∈ cutOf u v S := by
            have hgo : ∀ x y, Relation.ReflTransGen (adjE u v (EC0.erase i0)) x y →
                (decide (x ∈ S) != decide (y ∈ S)) = true →
                ∃ i1 ∈ EC0.erase i0, i1 ∈ cutOf u v S := by
              intro x y hr
              induction hr with
              | refl => intro h; simp at h
              | @tail w z hrw hstep ih =>
                intro hxz
                by_cases hxw : (decide (x ∈ S) != decide (w ∈ S)) = true
                · exact ih hxw
                · rcases hstep with ⟨j, hj, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
                  · refine ⟨j, hj, ?_⟩
                    simp only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and]
                    by_cases hxS : x ∈ S <;> by_cases huS : u j ∈ S <;> by_cases hvS : v j ∈ S <;> simp [hxS, huS, hvS] at hxz hxw ⊢
                  · refine ⟨j, hj, ?_⟩
                    simp only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and]
                    by_cases hxS : x ∈ S <;> by_cases huS : u j ∈ S <;> by_cases hvS : v j ∈ S <;> simp [hxS, huS, hvS] at hxz hxw ⊢
            exact hgo (u i0) (v i0) hreach hsep
          rcases hex with ⟨i1, hi1_er, hi1_cut⟩
          have hi10 : i1 ≠ i0 := (Finset.mem_erase.mp hi1_er).1
          have hi0_cut : i0 ∈ cutOf u v S := by simpa [cutOf] using hsep
          have hsub : ({i0, i1} : Finset (Fin m)) ⊆ cutOf u v S := by
            intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl <;> assumption
          calc 2 = ({i0, i1} : Finset (Fin m)).card := (Finset.card_pair hi10.symm).symm
            _ ≤ (cutOf u v S).card := Finset.card_le_card hsub
        let r0 := rep C0
        have hr0 : r0 ∈ C0 := hrep_mem C0 hC0
        let otherList := ((compOf u v).erase C0).toList
        have hother_len : otherList.length = (compOf u v).card - 1 := by
          simp [otherList, Finset.card_erase_of_mem hC0]
        let L : List (Fin n × Fin n) := (u i0, v i0) :: otherList.map (fun C => (r0, rep C))
        have hC0_pos : 1 ≤ (compOf u v).card := Finset.card_pos.mpr ⟨C0, hC0⟩
        have hL_len : L.length = (compOf u v).card := by
          simp only [L, List.length_cons, List.length_map, hother_len]; omega
        refine hof_list L (by omega) ?_ ?_
        · intro e he
          simp only [L, List.mem_cons, List.mem_map] at he
          rcases he with rfl | ⟨C, hCin, rfl⟩
          · exact huv i0
          · rcases Finset.mem_erase.mp (Finset.mem_toList.mp hCin) with ⟨hCne, hCcomp⟩
            exact fun heq => by
              dsimp only at heq
              exact Finset.disjoint_left.mp (compOf_disjoint u v hC0 hCcomp hCne.symm) hr0 (heq ▸ hrep_mem C hCcomp)
        · intro K hK
          let left : Fin L.length → Fin n := fun j => (L.get j).1
          let right : Fin L.length → Fin n := fun j => (L.get j).2
          let a' : Fin (m + L.length) → Fin n := Fin.addCases u left
          let b' : Fin (m + L.length) → Fin n := Fin.addCases v right
          change goodOf a' b' K = true
          have hui0_K : u i0 ∈ K := by
            rcases (mem_compOf_iff_reach a' b' K).mp hK with ⟨x, hKx⟩
            rw [hKx]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            let Cx := Finset.univ.filter (fun z => Relation.ReflTransGen (adjE u v Finset.univ) x z)
            have hCx : Cx ∈ compOf u v := (mem_compOf_iff_reach u v Cx).mpr ⟨x, rfl⟩
            have hx_rep : Relation.ReflTransGen (adjE a' b' Finset.univ) x (rep Cx) :=
              reach_mono_addCases u v left right (Finset.mem_filter.mp (hrep_mem Cx hCx)).2
            have hxr0 : Relation.ReflTransGen (adjE a' b' Finset.univ) x r0 := by
              by_cases hCx0 : Cx = C0
              · rwa [hCx0] at hx_rep
              · have hCx_in : Cx ∈ otherList :=
                  Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hCx0, hCx⟩)
                have hpair : (r0, rep Cx) ∈ L :=
                  List.mem_cons_of_mem _ (List.mem_map.mpr ⟨Cx, hCx_in, rfl⟩)
                rcases List.mem_iff_get.mp hpair with ⟨j, hj⟩
                exact hx_rep.tail ⟨Fin.natAdd m j, Finset.mem_univ _, Or.inr ⟨by simp only [b', right, Fin.addCases_right, hj], by simp only [a', left, Fin.addCases_right, hj]⟩⟩
            have hr0_ui0 : Relation.ReflTransGen (adjE u v Finset.univ) r0 (u i0) := by
              rcases (mem_compOf_iff_reach u v C0).mp hC0 with ⟨z0, hz0⟩
              have h1 : Relation.ReflTransGen (adjE u v Finset.univ) z0 r0 := by
                rw [hz0] at hr0; exact (Finset.mem_filter.mp hr0).2
              have h2 : Relation.ReflTransGen (adjE u v Finset.univ) z0 (u i0) := by
                have hai0 := (hEV0 i0 hi0_EC0).1
                rw [hz0] at hai0; exact (Finset.mem_filter.mp hai0).2
              exact (reachE_symm h1).trans h2
            exact hxr0.trans (reach_mono_addCases u v left right hr0_ui0)
          rw [goodOf_eq_true_iff]
          refine ⟨Fin.castAdd L.length i0, ?_, by simpa [a'] using hui0_K⟩
          have ha0 : a' (Fin.castAdd L.length i0) = u i0 := Fin.addCases_left i0
          have hb0 : b' (Fin.castAdd L.length i0) = v i0 := Fin.addCases_left i0
          simp only [strongOf, Finset.mem_filter, Finset.mem_univ, true_and, ha0, hb0]
          intro S _ hsep
          have hge2 := hcut2_i0 S hsep
          let eNew : Fin (m + L.length) := Fin.natAdd m ⟨0, by simp [L]⟩
          have heNew_in : eNew ∈ cutOf a' b' S := by
            simpa only [cutOf, Finset.mem_filter, Finset.mem_univ, true_and, a', b', eNew, left, right, Fin.addCases_right, L, List.get_eq_getElem, List.getElem_cons_zero] using hsep
          have himg_sub : (cutOf u v S).image (Fin.castAdd L.length) ⊆ (cutOf a' b' S).erase eNew := by
            intro j hj
            rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
            refine Finset.mem_erase.mpr ⟨?_, ?_⟩
            · intro heq
              have := congrArg Fin.val heq
              simp [eNew] at this
              omega
            · simpa [cutOf, a', b', Fin.addCases_left] using hi
          have hcard_le := Finset.card_le_card himg_sub
          rw [Finset.card_image_of_injective _ (Fin.castAdd_injective m L.length),
              Finset.card_erase_of_mem heNew_in] at hcard_le
          have hpos : 1 ≤ (cutOf a' b' S).card := Finset.card_pos.mpr ⟨eNew, heNew_in⟩
          omega

end PEqualNP.Outside.L_lib_1151_aux

theorem PEqualNP.Outside.L_lib_1151 : ∀ (n m : Nat) (u v : Fin m → Fin n), (∀ i, u i ≠ v i) →
  let Bits := Finset (Fin n)
  let cube := (Finset.univ : Finset Bits)
  let labels := (Finset.univ : Finset (Fin m))
  let cut := fun (S : Bits) => labels.filter
    (fun i => decide (u i ∈ S) != decide (v i ∈ S))
  let components := cube.filter (fun C => C.Nonempty ∧ (cut C).card = 0 ∧
    ∀ D ∈ C.powerset, D.Nonempty → (cut D).card = 0 → D = C)
  let strong := labels.filter (fun i => ∀ S ∈ cube,
    (decide (u i ∈ S) != decide (v i ∈ S)) = true → 3 ≤ (cut S).card)
  let good := fun (C : Bits) => strong.toList.any (fun i => decide (u i ∈ C))
  2 ≤ n →
  let bad := (components.filter (fun C => good C = false)).card
  let forest := components.toList.all (fun C =>
    (labels.filter (fun i => u i ∈ C)).card + 1 == C.card)
  let decodes := fun (h : Nat) (a b : Fin h → Fin n) =>
    let sat := fun (A : Finset Bits) (p : Fin h → Bool × Bool) =>
      ∃ x ∈ A, ∀ i, (decide (a i ∈ x), decide (b i ∈ x)) ≠ p i
    ∀ A B : Finset Bits, (∀ p, (sat A p ↔ sat B p)) → A = B
  ∀ k : Nat,
    (∃ (s : Nat) (left right : Fin s → Fin n), s ≤ k ∧ (∀ j, left j ≠ right j) ∧
      decodes (m+s) (Fin.addCases u left) (Fin.addCases v right)) ↔
      bad + (if forest then 1 else 0) ≤ k :=
  PEqualNP.Outside.L_lib_1151_aux.main
