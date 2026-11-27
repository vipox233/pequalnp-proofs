import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_347_aux

open PEqualNP.ProofComplexity PEqualNP.Expanders

private def FalseAt {E : Type} [DecidableEq E] (T F : Finset E) (D : Clause E) : Prop :=
  ∀ a ∈ D, a.1 ∈ if a.2 then F else T

private def Cert {E : Type} [DecidableEq E] (axioms : Set (Clause E))
    (C T F : Finset E) (L k : ℕ) : Prop :=
  ∃ (nodes inner : Finset (List Bool)) (pivot : List Bool → Option E)
      (line : List Bool → Clause E) (rank : List Bool → ℕ),
    [] ∈ nodes ∧ inner ⊆ nodes ∧ FalseAt T F (line []) ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ nodes → p ∈ inner) ∧
    (nodes \ inner).card ≤ L ∧ rank [] ≤ k ∧
    (∀ p ∈ nodes,
      (List.ofFn (fun i : Fin p.length => pivot (p.take i.val))).Nodup ∧
      (∀ i : Fin p.length, pivot (p.take i.val) ∈ (C \ (T ∪ F)).image some) ∧
      ∀ l ∈ line p, l.1 ∈ C) ∧
    (∀ p ∈ nodes \ inner, line p ∈ axioms ∧ rank p = 0) ∧
    ∀ p ∈ inner, let l := p ++ [false]; let r := p ++ [true]
      l ∈ nodes ∧ r ∈ nodes ∧
      rank p = (if rank l = rank r then rank l+1 else max (rank l) (rank r)) ∧
      ∃ e ∈ C, pivot p = some e ∧ (e,true) ∈ line l ∧ (e,false) ∈ line r ∧
        line p = (line l).erase (e,true) ∪ (line r).erase (e,false)


private theorem prefixPath347 {E : Type*} (q : List Bool → Option E)
    (p : List Bool) (b : Bool) (e : E)
    (he : q [] = some e) (r : List Bool → Option E)
    (hr : ∀ w, q (b :: w) = r w) :
    (List.ofFn (fun i : Fin (b :: p).length => q ((b :: p).take i.val))) =
      some e :: List.ofFn (fun i : Fin p.length => r (p.take i.val)) := by
  rw [List.ofFn_succ]
  simp [he, hr, List.take_succ_cons]

private theorem glueAvail347 {E : Type} [DecidableEq E] {C T F : Finset E} (e : E) :
    (C \ (T ∪ insert e F)).image some ⊆ (C \ (T ∪ F)).image some ∧
    (C \ (insert e T ∪ F)).image some ⊆ (C \ (T ∪ F)).image some ∧
    some e ∉ (C \ (T ∪ insert e F)).image some ∧
    some e ∉ (C \ (insert e T ∪ F)).image some := by
  simp only [Finset.subset_iff, Finset.mem_image, Finset.mem_sdiff, Finset.mem_union,
    Finset.mem_insert, Option.some.injEq]
  aesop

private theorem glueFalse347 {E : Type} [DecidableEq E] {T F : Finset E}
    {D : Clause E} {e : E} (s : Bool)
    (h : FalseAt (if s then T else insert e T) (if s then insert e F else F) D) :
    FalseAt T F (D.erase (e,s)) := by
  rintro ⟨x,t⟩ hxt
  obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hxt
  specialize h (x,t) hm
  cases s <;> cases t <;> simp_all

private theorem glueCons347 {E : Type} [DecidableEq E] {V W : Finset (Option E)}
    {q r : List Bool → Option E} {p : List Bool} {b : Bool} {e : E}
    (he : q [] = some e) (hr : ∀ w, q (b :: w) = r w)
    (hV : some e ∈ V) (hW : some e ∉ W) (hWV : W ⊆ V)
    (hn : (List.ofFn (fun i : Fin p.length => r (p.take i.val))).Nodup)
    (hm : ∀ i : Fin p.length, r (p.take i.val) ∈ W) :
    (List.ofFn (fun i : Fin (b :: p).length => q ((b :: p).take i.val))).Nodup ∧
    ∀ i : Fin (b :: p).length, q ((b :: p).take i.val) ∈ V := by
  have hprefix := prefixPath347 q p b e he r hr
  constructor
  · rw [hprefix, List.nodup_cons]
    refine ⟨?_, hn⟩
    intro hp
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hp
    exact hW (hi ▸ hm i)
  · intro i
    have h : q ((b :: p).take i.val) ∈
        List.ofFn (fun j : Fin (b :: p).length => q ((b :: p).take j.val)) :=
      List.mem_ofFn.mpr ⟨i, rfl⟩
    rw [hprefix, List.mem_cons] at h
    rcases h with h | h
    · rwa [h]
    · obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
      exact hj ▸ hWV (hm j)

private theorem glueMem347 (X Y : Finset (List Bool)) (p : List Bool) (b : Bool) :
    b :: p ∈ insert [] (X.image (List.cons false) ∪ Y.image (List.cons true)) ↔
      p ∈ if b then Y else X := by
  cases b <;> simp [Finset.mem_image]

private theorem glueCard347 (N M I J : Finset (List Bool)) :
    (insert [] (N.image (List.cons false) ∪ M.image (List.cons true)) \
      insert [] (I.image (List.cons false) ∪ J.image (List.cons true))).card ≤
      (N \ I).card + (M \ J).card := by
  calc
    _ ≤ ((N \ I).image (List.cons false) ∪ (M \ J).image (List.cons true)).card := by
      apply Finset.card_le_card
      intro p hp
      cases p with
      | nil => simp at hp
      | cons b p =>
        rw [Finset.mem_sdiff, glueMem347, glueMem347] at hp
        cases b
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr hp))
        · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr hp))
    _ ≤ _ := le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

private theorem glue {E : Type} [DecidableEq E] {axioms : Set (Clause E)}
    {C T F : Finset E} {L R a b : ℕ} {e : E}
    (he : e ∈ C \ (T ∪ F))
    (hl : Cert axioms C T (insert e F) L a) (hr : Cert axioms C (insert e T) F R b) :
    Cert axioms C T F (L+R) (max (max a b) (min a b + 1)) := by
  obtain ⟨havl,havr,hnel,hner⟩ := glueAvail347 (C:=C) (T:=T) (F:=F) e
  obtain ⟨N,I,P,D,K,hn,hi,hd,hprev,hs,hk,hp,ha,hres⟩ := hl
  obtain ⟨M,J,Q,H,S,hm,hj,hh,hprev',hs',hk',hp',ha',hres'⟩ := hr
  by_cases hd' : (e,true) ∈ D []
  swap
  · refine ⟨N,I,P,D,K,hn,hi,?_,hprev,by omega,by omega,?_,ha,hres⟩
    · simpa [Finset.erase_eq_of_notMem hd'] using glueFalse347 true hd
    · intro p h
      obtain ⟨h₁,h₂,h₃⟩ := hp p h
      exact ⟨h₁,fun i => havl (h₂ i),h₃⟩
  by_cases hh' : (e,false) ∈ H []
  swap
  · refine ⟨M,J,Q,H,S,hm,hj,?_,hprev',by omega,by omega,?_,ha',hres'⟩
    · simpa [Finset.erase_eq_of_notMem hh'] using glueFalse347 false hh
    · intro p h
      obtain ⟨h₁,h₂,h₃⟩ := hp' p h
      exact ⟨h₁,fun i => havr (h₂ i),h₃⟩
  let roots := (D []).erase (e,true) ∪ (H []).erase (e,false)
  let rankRoot := if K [] = S [] then K [] + 1 else max (K []) (S [])
  let nodes := insert [] (N.image (List.cons false) ∪ M.image (List.cons true))
  let inner := insert [] (I.image (List.cons false) ∪ J.image (List.cons true))
  let pivot : List Bool → Option E
    | [] => some e
    | false :: p => P p
    | true :: p => Q p
  let line : List Bool → Clause E
    | [] => roots
    | false :: p => D p
    | true :: p => H p
  let rank : List Bool → ℕ
    | [] => rankRoot
    | false :: p => K p
    | true :: p => S p
  have hnode : ∀ b p, b :: p ∈ nodes ↔ p ∈ if b then M else N := fun b p =>
    glueMem347 N M p b
  have hinner : ∀ b p, b :: p ∈ inner ↔ p ∈ if b then J else I := fun b p =>
    glueMem347 I J p b
  have hniln : [] ∈ nodes := Finset.mem_insert_self _ _
  have hnili : [] ∈ inner := Finset.mem_insert_self _ _
  have heroot : some e ∈ (C \ (T ∪ F)).image some := Finset.mem_image_of_mem _ he
  refine ⟨nodes,inner,pivot,line,rank,hniln,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p h
    cases p with
    | nil => exact hniln
    | cons b p =>
      rw [hinner] at h
      rw [hnode]
      cases b
      · exact hi h
      · exact hj h
  · intro l hl
    rcases Finset.mem_union.mp hl with h | h
    · exact glueFalse347 true hd l h
    · exact glueFalse347 false hh l h
  · intro p t h
    cases p with
    | nil => exact hnili
    | cons b p =>
      change b :: (p ++ [t]) ∈ nodes at h
      rw [hnode] at h
      rw [hinner]
      cases b
      · exact hprev p t h
      · exact hprev' p t h
  · exact (glueCard347 N M I J).trans (Nat.add_le_add hs hs')
  · change rankRoot ≤ _
    dsimp [rankRoot]
    split <;> omega
  · intro p h
    cases p with
    | nil =>
      refine ⟨by simp, fun i => Fin.elim0 i, ?_⟩
      intro l hl
      rcases Finset.mem_union.mp hl with h | h
      · exact (hp [] hn).2.2 l (Finset.mem_of_mem_erase h)
      · exact (hp' [] hm).2.2 l (Finset.mem_of_mem_erase h)
    | cons b p =>
      rw [hnode] at h
      cases b
      · obtain ⟨h₁,h₂,h₃⟩ := hp p h
        obtain ⟨hx,hy⟩ := glueCons347 (q:=pivot) (b:=false) rfl (fun _ => rfl)
          heroot hnel havl h₁ h₂
        exact ⟨hx,hy,h₃⟩
      · obtain ⟨h₁,h₂,h₃⟩ := hp' p h
        obtain ⟨hx,hy⟩ := glueCons347 (q:=pivot) (b:=true) rfl (fun _ => rfl)
          heroot hner havr h₁ h₂
        exact ⟨hx,hy,h₃⟩
  · intro p h
    rw [Finset.mem_sdiff] at h
    cases p with
    | nil => exact (h.2 hnili).elim
    | cons b p =>
      rw [hnode, hinner] at h
      cases b
      · exact ha p (Finset.mem_sdiff.mpr h)
      · exact ha' p (Finset.mem_sdiff.mpr h)
  · intro p h
    cases p with
    | nil =>
      exact ⟨(hnode false []).2 hn,(hnode true []).2 hm,rfl,
        e,(Finset.mem_sdiff.mp he).1,rfl,hd',hh',rfl⟩
    | cons b p =>
      rw [hinner] at h
      cases b
      · obtain ⟨h₁,h₂,h₃,h₄⟩ := hres p h
        exact ⟨(hnode false _).2 h₁,(hnode false _).2 h₂,h₃,h₄⟩
      · obtain ⟨h₁,h₂,h₃,h₄⟩ := hres' p h
        exact ⟨(hnode true _).2 h₁,(hnode true _).2 h₂,h₃,h₄⟩

open scoped BigOperators

private theorem active_row {m n : ℕ} {G : BipGraph m n} {P : Finset (Fin m)}
    (Z U T : Finset (GEdge G)) (hdef : (P.biUnion G).card < P.card)
    (hT : ∀ e ∈ T, e.val.1 ∈ P) (hU : ∀ e ∈ U, e.val.1 ∈ P ∧ e ∉ Z)
    (hnc : ∀ e ∈ T, ∀ d ∈ T, e.val.2 = d.val.2 → e.val.1 = d.val.1)
    (hSparse : ∀ (A : Finset (Fin m)) (B : Finset (Fin n)), A ⊆ P → B ⊆ P.biUnion G →
      (((Finset.univ : Finset (GEdge G)).filter (fun e => e.val.1 ∈ P) \ Z).filter
        (fun e => e.val.1 ∈ A ∧ e.val.2 ∈ B)).card ≤ A.card + B.card) :
    ∃ i ∈ P, i ∉ T.image (fun e => e.val.1) ∧
      (U.filter (fun e => e.val.1 = i ∧ e.val.2 ∉ T.image (fun d => d.val.2))).card ≤ 1 := by
  classical
  let R := T.image (fun e => e.val.1)
  let C := T.image (fun e => e.val.2)
  let H := P.biUnion G
  let A := P \ R
  let B := H \ C
  have hR : R ⊆ P := by
    intro i hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    exact hT e he
  have col_mem (e : GEdge G) (he : e.val.1 ∈ P) : e.val.2 ∈ H :=
    Finset.mem_biUnion.mpr ⟨e.val.1, he, e.property⟩
  have hC : C ⊆ H := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact col_mem e (hT e he)
  have hRC : R.card ≤ C.card := by
    have rep (j : C) : ∃ e ∈ T, e.val.2 = j.val := Finset.mem_image.mp j.property
    let f (j : C) : R := ⟨(rep j).choose.val.1,
      Finset.mem_image_of_mem _ (rep j).choose_spec.1⟩
    apply Finset.card_le_card_of_surjective (f := f)
    intro i
    obtain ⟨e, he, hei⟩ := Finset.mem_image.mp i.property
    let j : C := ⟨e.val.2, Finset.mem_image_of_mem _ he⟩
    refine ⟨j, Subtype.ext ?_⟩
    exact (hnc _ (rep j).choose_spec.1 e he (rep j).choose_spec.2).trans hei
  have hBA : B.card < A.card := by
    have h1 : A.card + R.card = P.card := Finset.card_sdiff_add_card_eq_card hR
    have h2 : B.card + C.card = H.card := Finset.card_sdiff_add_card_eq_card hC
    change H.card < P.card at hdef
    omega
  let V := U.filter (fun e => e.val.1 ∈ A ∧ e.val.2 ∈ B)
  have hV : V.card ≤ A.card + B.card := by
    refine Finset.card_le_card (t := _) ?_ |>.trans
      (hSparse A B Finset.sdiff_subset Finset.sdiff_subset)
    intro e he
    obtain ⟨heu, hab⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hU e heu).1⟩, (hU e heu).2⟩, hab⟩
  have hfiber : V.card = ∑ i ∈ A, (V.filter (fun e => e.val.1 = i)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ he => (Finset.mem_filter.mp he).2.1)
  have fiber_eq (i : Fin m) (hi : i ∈ A) :
      V.filter (fun e => e.val.1 = i) = U.filter (fun e => e.val.1 = i ∧ e.val.2 ∉ C) := by
    ext e
    simp only [V, Finset.mem_filter, Finset.mem_sdiff, B]
    constructor
    · rintro ⟨⟨he, _, _, hc⟩, hr⟩
      exact ⟨he, hr, hc⟩
    · rintro ⟨he, rfl, hc⟩
      exact ⟨⟨he, hi, col_mem e (hU e he).1, hc⟩, rfl⟩
  have hex : ∃ i ∈ A, (V.filter (fun e => e.val.1 = i)).card ≤ 1 := by
    by_contra! hh
    have hlower : 2 * A.card ≤ V.card := by
      rw [hfiber]
      calc
        2 * A.card = ∑ _i ∈ A, (2 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ _ := Finset.sum_le_sum (fun i hi => hh i hi)
    omega
  obtain ⟨i, hi, hsmall⟩ := hex
  obtain ⟨hip, hir⟩ := Finset.mem_sdiff.mp hi
  exact ⟨i, hip, hir, fiber_eq i hi ▸ hsmall⟩

private theorem cert_mono {E : Type} [DecidableEq E] {axioms : Set (Clause E)}
    {C T F : Finset E} {a b c d : ℕ} (h : Cert axioms C T F a b)
    (hc : a ≤ c) (hd : b ≤ d) : Cert axioms C T F c d := by
  obtain ⟨N, I, pivot, line, rank, hN, hI, hF, hp, hL, hk, hs, hleaf, hstep⟩ := h
  exact ⟨N, I, pivot, line, rank, hN, hI, hF, hp, hL.trans hc, hk.trans hd, hs, hleaf, hstep⟩

private theorem cert_leaf {E : Type} [DecidableEq E] {axioms : Set (Clause E)}
    {C T F : Finset E} (D : Clause E) (hD : D ∈ axioms)
    (hF : FalseAt T F D) (hC : ∀ l ∈ D, l.1 ∈ C) : Cert axioms C T F 1 0 := by
  refine ⟨{[]}, ∅, fun _ => none, fun _ => D, fun _ => 0, by simp, by simp, hF,
    ?_, by simp, by simp, ?_, ?_, ?_⟩
  · intro p b hp
    simp at hp
  · intro p hp
    have hp' : p = [] := by simpa using hp
    subst p
    refine ⟨by simp, ?_, hC⟩
    intro i
    exact Fin.elim0 i
  · intro p hp
    exact ⟨hD, rfl⟩
  · intro p hp
    simp at hp

private abbrev edges {m n : ℕ} (G : BipGraph m n) (P : Finset (Fin m)) : Finset (GEdge G) :=
  Finset.univ.filter (fun e => e.val.1 ∈ P)

private theorem edge_row {m n : ℕ} {G : BipGraph m n} {P : Finset (Fin m)}
    {e : GEdge G} : e ∈ edges G P ↔ e.val.1 ∈ P := by simp

private theorem row_leaf {m n : ℕ} {G : BipGraph m n} {P : Finset (Fin m)}
    {T F : Finset (GEdge G)} (i : Fin m) (hi : i ∈ P)
    (hF : ∀ e : GEdge G, e.val.1 = i → e ∈ F) :
    Cert (graphPHP G) (edges G P) T F 1 0 := by
  let D : Clause (GEdge G) := Finset.univ.filter (fun l => l.1.val.1 = i ∧ l.2 = true)
  apply cert_leaf D (Or.inl ⟨i, rfl⟩)
  · intro l hl
    have hh := (Finset.mem_filter.mp hl).2
    simpa [hh.2] using hF l.1 hh.1
  · intro l hl
    exact edge_row.mpr ((Finset.mem_filter.mp hl).2.1.symm ▸ hi)

private theorem collision_leaf {m n : ℕ} {G : BipGraph m n} {P : Finset (Fin m)}
    {T F : Finset (GEdge G)} (e d : GEdge G) (he : e ∈ T) (hd : d ∈ T)
    (heC : e ∈ edges G P) (hdC : d ∈ edges G P)
    (hh : e.val.2 = d.val.2) (hi : e.val.1 ≠ d.val.1) :
    Cert (graphPHP G) (edges G P) T F 1 0 := by
  apply cert_leaf ({(e, false), (d, false)} : Clause (GEdge G))
    (Or.inr ⟨e, d, hh, hi, rfl⟩)
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact he
    · exact hd
  · intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact heC
    · exact hdC

private theorem fresh_false {E : Type*} [DecidableEq E] (S T F : Finset E) (e : E) :
    S \ (T ∪ insert e F) = (S \ (T ∪ F)).erase e := by
  ext d
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
  tauto

private theorem fresh_true {E : Type*} [DecidableEq E] (S T F : Finset E) (e : E) :
    S \ (insert e T ∪ F) = (S \ (T ∪ F)).erase e := by
  ext d
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
  tauto

private theorem tail_choice {m n : ℕ} {G : BipGraph m n} {P : Finset (Fin m)}
    (Z T F : Finset (GEdge G)) (hdef : (P.biUnion G).card < P.card)
    (hT : T ⊆ edges G P) (hcovered : Z ⊆ T ∪ F)
    (hSparse : ∀ (A : Finset (Fin m)) (B : Finset (Fin n)), A ⊆ P → B ⊆ P.biUnion G →
      (((edges G P \ Z).filter (fun e => e.val.1 ∈ A ∧ e.val.2 ∈ B)).card ≤ A.card + B.card)) :
    Cert (graphPHP G) (edges G P) T F 1 0 ∨
    ∃ e ∈ edges G P \ (T ∪ F),
      Cert (graphPHP G) (edges G P) T (insert e F) 1 0 ∨
      Cert (graphPHP G) (edges G P) (insert e T) F 1 0 := by
  classical
  let U := edges G P \ (T ∪ F)
  by_cases hc : ∃ e ∈ T, ∃ d ∈ T, e.val.2 = d.val.2 ∧ e.val.1 ≠ d.val.1
  · obtain ⟨e, he, d, hd, hh, hi⟩ := hc
    exact Or.inl (collision_leaf e d he hd (hT he) (hT hd) hh hi)
  have hnc : ∀ e ∈ T, ∀ d ∈ T, e.val.2 = d.val.2 → e.val.1 = d.val.1 := by
    intro e he d hd hh
    by_contra hi
    exact hc ⟨e, he, d, hd, hh, hi⟩
  by_cases hb : ∃ e ∈ U, ∃ d ∈ T, e.val.2 = d.val.2 ∧ e.val.1 ≠ d.val.1
  · obtain ⟨e, he, d, hd, hh, hi⟩ := hb
    exact Or.inr ⟨e, he, Or.inr (collision_leaf e d (Finset.mem_insert_self _ _)
      (Finset.mem_insert_of_mem hd) (Finset.mem_sdiff.mp he).1 (hT hd) hh hi)⟩
  obtain ⟨i, hi, hiT, hrow⟩ := active_row Z U T hdef (fun e he => edge_row.mp (hT he))
    (fun e he => ⟨edge_row.mp (Finset.mem_sdiff.mp he).1, fun hz => (Finset.mem_sdiff.mp he).2 (hcovered hz)⟩)
    hnc hSparse
  let V := U.filter (fun e => e.val.1 = i ∧ e.val.2 ∉ T.image (fun d => d.val.2))
  change V.card ≤ 1 at hrow
  have all_to_V : ∀ e : GEdge G, e.val.1 = i → e ∉ F → e ∈ V := by
    intro e hei heF
    have heT : e ∉ T := fun he => hiT (Finset.mem_image.mpr ⟨e, he, hei⟩)
    have heU : e ∈ U := by
      refine Finset.mem_sdiff.mpr ⟨edge_row.mpr (hei.symm ▸ hi), ?_⟩
      simp [heT, heF]
    refine Finset.mem_filter.mpr ⟨heU, hei, ?_⟩
    intro hh
    obtain ⟨d, hd, heq⟩ := Finset.mem_image.mp hh
    exact hb ⟨e, heU, d, hd, heq.symm,
      fun h => hiT (Finset.mem_image.mpr ⟨d, hd, h.symm.trans hei⟩)⟩
  by_cases hV : V.Nonempty
  · obtain ⟨e, he⟩ := hV
    refine Or.inr ⟨e, (Finset.mem_filter.mp he).1, Or.inl (row_leaf i hi ?_)⟩
    intro d hd
    by_cases hdF : d ∈ F
    · exact Finset.mem_insert_of_mem hdF
    · have hde : d = e := by
        by_contra hne
        have hpair : ({d, e} : Finset (GEdge G)) ⊆ V := by
          intro f hf
          simp only [Finset.mem_insert, Finset.mem_singleton] at hf
          rcases hf with h | h
          · rw [h]
            exact all_to_V d hd hdF
          · rwa [h]
        have h := Finset.card_le_card hpair
        simp [hne] at h
        omega
      exact Finset.mem_insert.mpr (Or.inl hde)
  · refine Or.inl (row_leaf i hi ?_)
    intro e he
    by_contra hf
    exact hV ⟨e, all_to_V e he hf⟩

private theorem tail_cert {m n : ℕ} {G : BipGraph m n} {P : Finset (Fin m)}
    (Z : Finset (GEdge G)) (hdef : (P.biUnion G).card < P.card)
    (hSparse : ∀ (A : Finset (Fin m)) (B : Finset (Fin n)), A ⊆ P → B ⊆ P.biUnion G →
      (((edges G P \ Z).filter (fun e => e.val.1 ∈ A ∧ e.val.2 ∈ B)).card ≤ A.card + B.card))
    (T F : Finset (GEdge G)) (hT : T ⊆ edges G P) (hcovered : Z ⊆ T ∪ F) :
    Cert (graphPHP G) (edges G P) T F ((edges G P \ (T ∪ F)).card + 1) 1 := by
  generalize hs : (edges G P \ (T ∪ F)).card = s
  induction s using Nat.strong_induction_on generalizing T F with
  | ind s ih =>
    rcases tail_choice Z T F hdef hT hcovered hSparse with h | ⟨e, he, hl | hr⟩
    · exact cert_mono h (by omega) (by omega)
    · have hs' : (edges G P \ (insert e T ∪ F)).card + 1 = s := by
        rw [fresh_true, Finset.card_erase_add_one he, hs]
      have hT' : insert e T ⊆ edges G P := Finset.insert_subset (Finset.mem_sdiff.mp he).1 hT
      have hcov' : Z ⊆ insert e T ∪ F := by
        intro d hd
        rcases Finset.mem_union.mp (hcovered hd) with hd | hd
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hd)
        · exact Finset.mem_union_right _ hd
      have hr' := ih _ (by omega) (insert e T) F hT' hcov' rfl
      exact cert_mono (glue he hl hr') (by omega) (by decide)
    · have hs' : (edges G P \ (T ∪ insert e F)).card + 1 = s := by
        rw [fresh_false, Finset.card_erase_add_one he, hs]
      have hcov' : Z ⊆ T ∪ insert e F := by
        intro d hd
        rcases Finset.mem_union.mp (hcovered hd) with hd | hd
        · exact Finset.mem_union_left _ hd
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hd)
      have hl' := ih _ (by omega) T (insert e F) hT hcov' rfl
      exact cert_mono (glue he hl' hr) (by omega) (by decide)

private theorem deleted_cert {m n : ℕ} {G : BipGraph m n} {P : Finset (Fin m)}
    (Z : Finset (GEdge G)) (hZ : Z ⊆ edges G P) (hdef : (P.biUnion G).card < P.card)
    (hSparse : ∀ (A : Finset (Fin m)) (B : Finset (Fin n)), A ⊆ P → B ⊆ P.biUnion G →
      (((edges G P \ Z).filter (fun e => e.val.1 ∈ A ∧ e.val.2 ∈ B)).card ≤ A.card + B.card))
    (T F : Finset (GEdge G)) (hT : T ⊆ edges G P) :
    Cert (graphPHP G) (edges G P) T F
      (((edges G P).card - Z.card + 1) * 2 ^ (Z \ (T ∪ F)).card)
      ((Z \ (T ∪ F)).card + 1) := by
  generalize hs : (Z \ (T ∪ F)).card = s
  induction s using Nat.strong_induction_on generalizing T F with
  | ind s ih =>
    by_cases hcov : Z ⊆ T ∪ F
    · have hs0 : s = 0 := by
        simpa [Finset.sdiff_eq_empty_iff_subset.mpr hcov] using hs.symm
      rw [hs0, pow_zero, mul_one, Nat.zero_add]
      have hsub : edges G P \ (T ∪ F) ⊆ edges G P \ Z := by
        intro e he
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp he).1, fun hz => (Finset.mem_sdiff.mp he).2 (hcov hz)⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset hZ] at hc
      exact cert_mono (tail_cert Z hdef hSparse T F hT hcov)
        (Nat.succ_le_succ hc) (le_refl 1)
    · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr
        (fun h => hcov (Finset.sdiff_eq_empty_iff_subset.mp h))
      have heC : e ∈ edges G P \ (T ∪ F) :=
        Finset.mem_sdiff.mpr ⟨hZ (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩
      have hf : (Z \ (T ∪ insert e F)).card + 1 = s := by
        rw [fresh_false, Finset.card_erase_add_one he, hs]
      have ht : (Z \ (insert e T ∪ F)).card + 1 = s := by
        rw [fresh_true, Finset.card_erase_add_one he, hs]
      let t := (Z \ (T ∪ insert e F)).card
      have hts : t + 1 = s := hf
      have hft : (Z \ (insert e T ∪ F)).card = t := by omega
      have hl := ih t (by omega) T (insert e F) hT rfl
      have hr := ih t (by omega) (insert e T) F
        (Finset.insert_subset (Finset.mem_sdiff.mp heC).1 hT) hft
      apply cert_mono (glue heC hl hr)
      · rw [← hts, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      · simp [← hts]

private theorem output {m n : ℕ} (G : BipGraph m n) (P : Finset (Fin m))
    (hdef : (P.biUnion G).card < P.card) (Z : Finset (GEdge G)) (hZ : Z ⊆ edges G P)
    (hSparse : ∀ (A : Finset (Fin m)) (B : Finset (Fin n)), A ⊆ P → B ⊆ P.biUnion G →
      (((edges G P \ Z).filter (fun e => e.val.1 ∈ A ∧ e.val.2 ∈ B)).card ≤ A.card + B.card)) :
    ∃ (nodes inner : Finset (List Bool)) (pivot : List Bool → Option (GEdge G))
      (line : List Bool → Clause (GEdge G)) (rank : List Bool → ℕ),
      [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = ∅ ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ nodes → p ∈ inner) ∧
      (nodes \ inner).card ≤ ((edges G P).card-Z.card+1)*2^Z.card ∧ rank [] ≤ Z.card+1 ∧
      (∀ p ∈ nodes,
        (List.ofFn (fun i : Fin p.length => pivot (p.take i.val))).Nodup ∧
        p.length ≤ (edges G P).card ∧ ∀ l ∈ line p, l.1 ∈ edges G P) ∧
      (∀ p ∈ nodes \ inner, line p ∈ graphPHP G ∧ rank p = 0) ∧
      ∀ p ∈ inner, let l := p ++ [false]; let r := p ++ [true]
        l ∈ nodes ∧ r ∈ nodes ∧
        rank p = (if rank l = rank r then rank l+1 else max (rank l) (rank r)) ∧
        ∃ e ∈ edges G P, pivot p = some e ∧ (e,true) ∈ line l ∧ (e,false) ∈ line r ∧
          line p = (line l).erase (e,true) ∪ (line r).erase (e,false) := by
  have hc : Cert (graphPHP G) (edges G P) ∅ ∅
      (((edges G P).card-Z.card+1)*2^Z.card) (Z.card+1) := by
    simpa using deleted_cert Z hZ hdef hSparse ∅ ∅ (Finset.empty_subset _)
  obtain ⟨N, I, pivot, line, rank, hN, hI, hF, hp, hL, hk, hs, hleaf, hstep⟩ := hc
  refine ⟨N, I, pivot, line, rank, hN, hI, ?_, hp, hL, hk, ?_, hleaf, hstep⟩
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    have hh := hF l hl
    cases l.2 <;> simp at hh
  · intro p hp
    obtain ⟨hn, hc, hl⟩ := hs p hp
    refine ⟨hn, ?_, hl⟩
    let xs := List.ofFn (fun i : Fin p.length => pivot (p.take i.val))
    have hsub : xs.toFinset ⊆ (edges G P).image some := by
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp he)
      simpa using hc i
    have hh := Finset.card_le_card hsub
    rwa [List.toFinset_card_of_nodup hn, List.length_ofFn,
      Finset.card_image_of_injective _ (Option.some_injective _)] at hh

end PEqualNP.Outside.L_pcx_347_aux

open PEqualNP.Outside.L_pcx_347_aux in
theorem PEqualNP.Outside.L_pcx_347 :
∀ (m n : ℕ) (G : PEqualNP.Expanders.BipGraph m n) (P : Finset (Fin m)),
  let E := PEqualNP.Expanders.GEdge G
  let H := P.biUnion G
  let cells := (Finset.univ : Finset E).filter (fun e => e.val.1 ∈ P)
  H.card < P.card →
  ∀ Z : Finset E, Z ⊆ cells →
    (∀ (A : Finset (Fin m)) (B : Finset (Fin n)), A ⊆ P → B ⊆ H →
      ((cells \ Z).filter (fun e => e.val.1 ∈ A ∧ e.val.2 ∈ B)).card ≤ A.card+B.card) →
    ∃ (nodes inner : Finset (List Bool)) (pivot : List Bool → Option E)
      (line : List Bool → PEqualNP.ProofComplexity.Clause E) (rank : List Bool → ℕ),
      [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = ∅ ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ nodes → p ∈ inner) ∧
      (nodes \ inner).card ≤ (cells.card-Z.card+1)*2^Z.card ∧ rank [] ≤ Z.card+1 ∧
      (∀ p ∈ nodes,
        (List.ofFn (fun i : Fin p.length => pivot (p.take i.val))).Nodup ∧
        p.length ≤ cells.card ∧ ∀ l ∈ line p, l.1 ∈ cells) ∧
      (∀ p ∈ nodes \ inner, line p ∈ PEqualNP.Expanders.graphPHP G ∧ rank p = 0) ∧
      ∀ p ∈ inner, let l := p ++ [false]; let r := p ++ [true]
        l ∈ nodes ∧ r ∈ nodes ∧
        rank p = (if rank l = rank r then rank l+1 else max (rank l) (rank r)) ∧
        ∃ e ∈ cells, pivot p = some e ∧ (e,true) ∈ line l ∧ (e,false) ∈ line r ∧
          line p = (line l).erase (e,true) ∪ (line r).erase (e,false) := by
  intro m n G P E H cells hdef Z hZ hSparse
  exact output G P hdef Z hZ hSparse
