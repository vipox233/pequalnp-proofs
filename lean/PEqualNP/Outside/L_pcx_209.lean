import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_209

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

private def up (A : LinClause V) : LinKLine V :=
  A.image fun q => ({q} : LinTerm V)

private abbrev Der (F : Set (Clause V)) :=
  IsLinKDerivation 1 IsLinKWeakening (linKOfClause '' F)

private def Can (F : Set (Clause V)) (p : List (LinKLine V)) (k : ℕ) (A : LinClause V) : Prop :=
  ∃ t : List (LinKLine V), Der F t ∧ (∀ L ∈ p, L ∈ t) ∧ up A ∈ t ∧ t.length ≤ p.length + k

private theorem width (A : LinClause V) : ∀ T ∈ up A, T.card ≤ 1 := by
  intro T hT
  rcases Finset.mem_image.mp hT with ⟨q,hq,rfl⟩
  simp

private theorem weaken {F : Set (Clause V)} {p : List (LinKLine V)} (dp : Der F p)
    {A B : LinClause V} (ha : up A ∈ p)
    (he : ∀ a q, q ∈ A → LinEqSat a q → ∃ z ∈ B, LinEqSat a z) :
    Can F p 1 B := by
  refine ⟨up B :: p, .weak dp ha ?_ (width B), ?_, by simp, by simp⟩
  · intro T h
    rcases Finset.mem_image.mp h with ⟨q,hq,rfl⟩
    right
    intro a hs
    obtain ⟨z,hz,heq⟩ := he a q hq (hs q (by simp))
    exact ⟨z,Finset.mem_image.mpr ⟨z,hz,rfl⟩,heq⟩
  · intro L h
    exact List.mem_cons_of_mem _ h

private theorem includeW {F : Set (Clause V)} {p : List (LinKLine V)} (dp : Der F p)
    {A B : LinClause V} (ha : up A ∈ p) (sub : A ⊆ B) : Can F p 1 B :=
  weaken dp ha fun _ q h sat => ⟨q,sub h,sat⟩

private theorem enlarge {F : Set (Clause V)} {p : List (LinKLine V)} {k l : ℕ} {A : LinClause V}
    (h : Can F p k A) (kl : k ≤ l) : Can F p l A := by
  obtain ⟨t,dt,old,m,ht⟩ := h
  exact ⟨t,dt,old,m,by omega⟩

private theorem chain {F : Set (Clause V)} {p : List (LinKLine V)} {k l : ℕ} {A B : LinClause V}
    (h : Can F p k A) (next : ∀ t, Der F t → (∀ L ∈ p, L ∈ t) → up A ∈ t → Can F t l B) :
    Can F p (k+l) B := by
  obtain ⟨t,dt,old,m,ht⟩ := h
  obtain ⟨u,du,keep,m',hu⟩ := next t dt old m
  exact ⟨u,du,fun L hL => keep L (old L hL),m',by omega⟩

private theorem cutW {F : Set (Clause V)} {p : List (LinKLine V)} (dp : Der F p)
    {A B R : LinClause V} (ha : up A ∈ p) (hb : up B ∈ p) (e : LinEq V)
    (left : ∀ q ∈ A, q ≠ e → q ∈ R)
    (right : ∀ q ∈ B, q ≠ negLinEq e → q ∈ R) : Can F p 2 R := by
  classical
  by_cases ea : e ∈ A
  · by_cases eb : negLinEq e ∈ B
    · let C := (up A).erase {e} ∪ (up B \ ({e} : LinTerm V).image (fun z => ({negLinEq z} : LinTerm V)))
      have sub : C ⊆ up R := by
        intro T h
        rcases Finset.mem_union.mp h with h | h
        · rcases Finset.mem_erase.mp h with ⟨ne,mem⟩
          rcases Finset.mem_image.mp mem with ⟨q,hq,rfl⟩
          exact Finset.mem_image.mpr ⟨q,left q hq (fun eq => ne (by rw [eq])),rfl⟩
        · rcases Finset.mem_sdiff.mp h with ⟨mem,ne⟩
          rcases Finset.mem_image.mp mem with ⟨q,hq,rfl⟩
          exact Finset.mem_image.mpr ⟨q,right q hq (fun eq => ne (by simp [eq])),rfl⟩
      have hc : IsLinKCut (up A) (up B) C := by
        refine ⟨{e},Finset.mem_image.mpr ⟨e,ea,rfl⟩,?_,rfl⟩
        intro z hz
        have : z=e := Finset.mem_singleton.mp hz
        subst z
        exact Finset.mem_image.mpr ⟨_,eb,rfl⟩
      have dc : Der F (C :: p) := .cut dp ha hb hc (fun T hT => width R T (sub hT))
      have hw : IsLinKWeakening C (up R) := fun T hT => Or.inl ⟨T,sub hT,fun _ h => h⟩
      refine ⟨up R :: C :: p,.weak dc (by simp) hw (width R),?_,by simp,by simp⟩
      intro L hL
      simp [hL]
    · exact enlarge (includeW dp hb (fun q hq => right q hq (fun he => eb (he ▸ hq)))) (by decide)
  · exact enlarge (includeW dp ha (fun q hq => left q hq (fun he => ea (he ▸ hq)))) (by decide)

private def pos (x : V) : LinEq V := ({x},true)
private def neg (x : V) : LinEq V := ({x},false)
private def oddE (U : Finset V) : LinEq V := (U,true)
private def imp (x : V) (U : Finset V) : LinClause V := {neg x, oddE U}

private theorem addAx {F : Set (Clause V)} {p : List (LinKLine V)} (dp : Der F p)
    (C : Clause V) (hc : C ∈ F) : Can F p 1 (linOfClause C) := by
  refine ⟨up (linOfClause C) :: p, .ax dp ⟨C,hc,rfl⟩ (width _),?_,by simp,by simp⟩
  intro L hL
  simp [hL]

private theorem posSat (a : V → Bool) (x : V) : LinEqSat a (pos x) ↔ a x = true := by
  cases h : a x <;> simp [LinEqSat,pos,Finset.filter_singleton,h]

private theorem negSat (a : V → Bool) (x : V) : LinEqSat a (neg x) ↔ a x = false := by
  cases h : a x <;> simp [LinEqSat,neg,Finset.filter_singleton,h]

private theorem liftImp {F : Set (Clause V)} {p : List (LinKLine V)} (dp : Der F p)
    (x y : V) (U : Finset V) (hu : up (imp x U) ∈ p) :
    Can F p 1 (insert (pos y) (imp x (insert y U))) := by
  apply weaken dp hu
  intro a q hq hs
  by_cases hy : a y = true
  · exact ⟨pos y,by simp, (posSat a y).2 hy⟩
  · have hfalse : a y = false := Bool.eq_false_iff.mpr hy
    rcases Finset.mem_insert.mp hq with eq | rest
    · exact ⟨neg x,by simp [imp],eq ▸ hs⟩
    · have eq := Finset.mem_singleton.mp rest
      subst q
      refine ⟨oddE (insert y U),by simp [imp],?_⟩
      simpa [LinEqSat,oddE,Finset.filter_insert,hfalse] using hs

private theorem makeImp {F : Set (Clause V)} {p : List (LinKLine V)} {A : LinClause V}
    (dp : Der F p) (anchor : up A ∈ p) (S : Finset V)
    (ex : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → {(x,false),(y,false)} ∈ F)
    (x : V) (hx : x ∈ S) (U : Finset V) (sub : U ⊆ S) (miss : x ∉ U) :
    Can F p (1 + 4 * U.card) (imp x (insert x U)) := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    simp only [Finset.card_empty, Nat.mul_zero, Nat.add_zero, Finset.insert_empty]
    apply weaken dp anchor
    intro a q hq hs
    cases h : a x with
    | true => exact ⟨pos x,by simp [imp,pos,oddE],(posSat a x).2 h⟩
    | false => exact ⟨neg x,by simp [imp],(negSat a x).2 h⟩
  | @insert y U hy ih =>
    have hxne : x ≠ y := fun e => miss (by simp [e])
    have hyS := sub (Finset.mem_insert_self y U)
    have hU := ih (fun z hz => sub (Finset.mem_insert_of_mem hz)) (fun h => miss (Finset.mem_insert_of_mem h))
    let B : LinClause V := {neg x,neg y}
    have eB : linOfClause {(x,false),(y,false)} = B := by simp [linOfClause,B,neg]
    have hh := chain hU (fun t dt _ ht =>
      chain (liftImp dt x y (insert x U) ht) (fun v dv old hv =>
        chain (addAx dv _ (ex x hx y hyS hxne)) (fun w dw kept hw => by
          rw [eB] at hw
          apply cutW dw (kept _ hv) hw (pos y)
          · intro q hq neq
            simpa [Finset.mem_insert,neq] using hq
          · intro q hq neq
            rcases Finset.mem_insert.mp hq with rfl | eq
            · exact Finset.mem_insert_self _ _
            · have eq' := Finset.mem_singleton.mp eq
              exact False.elim (neq eq'))))
    simpa [Finset.card_insert_of_notMem hy, Finset.insert_comm x y, Nat.mul_add, Nat.add_assoc] using hh

private def remain (S U : Finset V) : LinClause V := insert (oddE S) ((S \ U).image pos)

private theorem foldRows {F : Set (Clause V)} {p : List (LinKLine V)}
    (dp : Der F p) (S : Finset V)
    (ex : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → {(x,false),(y,false)} ∈ F)
    (start : up (remain S ∅) ∈ p) (U : Finset V) (sub : U ⊆ S) :
    Can F p (U.card * (4*S.card+3)) (remain S U) := by
  classical
  induction U using Finset.induction_on with
  | empty =>
    exact ⟨p,dp,fun _ h => h,start,by simp⟩
  | @insert x U hx ih =>
    have hxS := sub (Finset.mem_insert_self x U)
    have hU := ih (fun z hz => sub (Finset.mem_insert_of_mem hz))
    have step (t : List (LinKLine V)) (dt : Der F t) (ht : up (remain S U) ∈ t) :
        Can F t (4*S.card+3) (remain S (insert x U)) := by
      have make := makeImp dt ht S ex x hxS (S.erase x) (Finset.erase_subset x S) (Finset.notMem_erase x S)
      rw [Finset.insert_erase hxS] at make
      apply enlarge (chain make (fun v dv keep hv => by
        apply cutW dv (keep _ ht) hv (pos x)
        · intro q hq neq
          rcases Finset.mem_insert.mp hq with rfl | hq
          · exact Finset.mem_insert_self _ _
          · rcases Finset.mem_image.mp hq with ⟨z,hz,rfl⟩
            refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨z,?_,rfl⟩)
            obtain ⟨inS,outside⟩ := Finset.mem_sdiff.mp hz
            exact Finset.mem_sdiff.mpr ⟨inS,by
              simp only [Finset.mem_insert]
              exact fun h => h.elim (fun e => neq (congrArg pos e)) outside⟩
        · intro q hq neq
          rcases Finset.mem_insert.mp hq with eq | h
          · exact False.elim (neq eq)
          · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h))))
      have le := Finset.card_le_card (Finset.erase_subset x S)
      omega
    have ff := chain hU (fun t dt _ ht => step t dt ht)
    simpa [Finset.card_insert_of_notMem hx,Nat.add_mul] using ff

private theorem finish : ∀ (V : Type) [DecidableEq V] (S : Finset V)
    (F : Set (PEqualNP.ProofComplexity.Clause V)),
  S.image (fun x => (x, true)) ∈ F →
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → {(x, false), (y, false)} ∈ F) →
  ∃ π : List (PEqualNP.ProofComplexity.LinKLine V),
    PEqualNP.ProofComplexity.IsLinKDerivation 1
      PEqualNP.ProofComplexity.IsLinKWeakening
      (PEqualNP.ProofComplexity.linKOfClause '' F) π ∧
    ({({(S, true)} : PEqualNP.ProofComplexity.LinTerm V)} :
      PEqualNP.ProofComplexity.LinKLine V) ∈ π ∧
    π.length ≤ 4 * (S.card + 1) ^ 2 := by
  classical
  intro V _ S F hp hex
  let C : Clause V := S.image (fun z => (z,true))
  have mainEq : linOfClause C = S.image pos := by
    ext q
    simp [C,linOfClause,pos]
  have hax := addAx (F:=F) (p:=[]) IsLinKDerivation.nil C hp
  rw [mainEq] at hax
  have first := chain hax (fun t dt _ ht =>
    includeW (B:=remain S ∅) dt ht (fun q hq => Finset.mem_insert_of_mem (by simpa using hq)))
  have result := chain first (fun t dt _ ht => foldRows dt S hex ht S (Finset.Subset.refl S))
  obtain ⟨t,dt,_,last,hlen⟩ := result
  refine ⟨t,dt,?_,?_⟩
  · simpa [up,remain,oddE] using last
  · simp only [List.length_nil,Nat.zero_add] at hlen
    nlinarith


variable {V W : Type} [DecidableEq V] [DecidableEq W]

abbrev img (project : LinEq V → LinEq W) (L : LinKLine V) : LinKLine W :=
  L.image (fun T => T.image project)

theorem width_img (project : LinEq V → LinEq W) {k : ℕ} {L : LinKLine V}
    (h : ∀ T ∈ L, T.card ≤ k) : ∀ T ∈ img project L, T.card ≤ k := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
  exact Finset.card_image_le.trans (h S hS)

theorem weak_sub {L M : LinKLine W} (h : L ⊆ M) : IsLinKWeakening L M :=
  fun T hT => Or.inl ⟨T, h hT, fun _ ha => ha⟩

theorem termSat_img (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) (a : W → Bool)
    (T : LinTerm V) : LinTermSat a (T.image project) ↔ LinTermSat (extend a) T := by
  constructor
  · intro h e he
    exact (hsat a e).1 (h _ (Finset.mem_image_of_mem _ he))
  · intro h q hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hq
    exact (hsat a e).2 (h e he)

theorem sat_single (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a (({v} : Finset V), s) ↔ a v = s := by
  cases h : a v <;> cases s <;> simp [LinEqSat, h, Finset.filter_singleton]

theorem cut_img (project : LinEq V → LinEq W)
    (hneg : ∀ e, project (negLinEq e) = negLinEq (project e)) {C D R : LinKLine V}
    (h : IsLinKCut C D R) :
    ∃ R', IsLinKCut (img project C) (img project D) R' ∧ R' ⊆ img project R := by
  obtain ⟨T, hT, hD, rfl⟩ := h
  refine ⟨(img project C).erase (T.image project) ∪ (img project D \
    (T.image project).image (fun e => ({negLinEq e} : LinTerm W))),
    ⟨T.image project, Finset.mem_image_of_mem _ hT, ?_, rfl⟩, ?_⟩
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 he
    have h1 : ({negLinEq e0} : LinTerm V).image project = {negLinEq (project e0)} := by
      rw [Finset.image_singleton, hneg]
    rw [← h1]
    exact Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) (hD e0 he0)
  · intro S hS
    rcases Finset.mem_union.1 hS with h1 | h1
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 h1
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hUT, hU⟩))
    · obtain ⟨hS, hn⟩ := Finset.mem_sdiff.1 h1
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      refine Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hU, ?_⟩))
      intro hU'
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hU'
      apply hn
      refine Finset.mem_image.2 ⟨project e, Finset.mem_image_of_mem _ he, ?_⟩
      rw [Finset.image_singleton, hneg]

theorem and_img (project : LinEq V → LinEq W) {C D R : LinKLine V}
    (h : IsLinKAndIntro C D R) :
    ∃ R', IsLinKAndIntro (img project C) (img project D) R' ∧ R' ⊆ img project R := by
  obtain ⟨T₁, T₂, h1, h2, rfl⟩ := h
  refine ⟨((img project C).erase (T₁.image project) ∪ (img project D).erase (T₂.image project))
    ∪ {T₁.image project ∪ T₂.image project},
    ⟨_, _, Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2, rfl⟩, ?_⟩
  intro S hS
  rcases Finset.mem_union.1 hS with hS | hS
  · rcases Finset.mem_union.1 hS with hS | hS
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 hS
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T₁ := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hUT, hU⟩)))
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 hS
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T₂ := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hUT, hU⟩)))
  · rw [Finset.mem_singleton.1 hS, ← Finset.image_union]
    exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

theorem weak_img (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) {L M : LinKLine V}
    (h : IsLinKWeakening L M) : IsLinKWeakening (img project L) (img project M) := by
  intro T' hT'
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT'
  rcases h T hT with ⟨S, hS, hTS⟩ | hq
  · exact Or.inl ⟨S.image project, Finset.mem_image_of_mem _ hS, fun a ha =>
      (termSat_img project extend hsat a S).2 (hTS _ ((termSat_img project extend hsat a T).1 ha))⟩
  · right
    intro a ha
    obtain ⟨q, hq1, hq2⟩ := hq _ ((termSat_img project extend hsat a T).1 ha)
    refine ⟨project q, ?_, (hsat a q).2 hq2⟩
    rw [show ({project q} : LinTerm W) = ({q} : LinTerm V).image project from
      (Finset.image_singleton _ _).symm]
    exact Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) hq1

theorem ax_weak (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) {C : Clause V}
    {D : Clause W} (hCD : ∀ a, ClauseSat a D → ClauseSat (extend a) C) :
    IsLinKWeakening (linKOfClause D) (img project (linKOfClause C)) := by
  intro T hT
  right
  intro a ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hT
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hq
  have hla : a l.1 = l.2 := (sat_single a l.1 l.2).1 (ha _ (Finset.mem_singleton_self _))
  obtain ⟨l', hl', h'⟩ := hCD a ⟨l, hl, hla⟩
  refine ⟨project (({l'.1} : Finset V), l'.2), ?_,
    (hsat a _).2 ((sat_single (extend a) l'.1 l'.2).2 h')⟩
  rw [show ({project (({l'.1} : Finset V), l'.2)} : LinTerm W) =
      ({(({l'.1} : Finset V), l'.2)} : LinTerm V).image project from
      (Finset.image_singleton _ _).symm]
  refine Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) ?_
  exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hl')

theorem width_clause {k : ℕ} (hk : 1 ≤ k) (D : Clause W) :
    ∀ T ∈ linKOfClause D, T.card ≤ k := by
  intro T hT
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hT
  rw [Finset.card_singleton]; exact hk


private theorem translate (k : ℕ) (F : Set (Clause V)) (H : Set (Clause W))
    (extend : (W → Bool) → V → Bool) (project : LinEq V → LinEq W) (hk : 1 ≤ k)
    (hneg : ∀ e, project (negLinEq e) = negLinEq (project e))
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e)
    (seed : List (LinKLine W))
    (dseed : IsLinKDerivation k IsLinKWeakening (linKOfClause '' H) seed)
    (hax : ∀ C ∈ F, (∃ D ∈ H, ∀ a, ClauseSat a D → ClauseSat (extend a) C) ∨ img project (linKOfClause C) ∈ seed)
    (π : List (LinKLine V))
    (h : IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F) π) :
    ∃ τ : List (LinKLine W),
      IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' H) (τ ++ seed) ∧
      τ.length ≤ 2 * π.length ∧ ∀ L ∈ π, img project L ∈ τ ++ seed := by
  induction h with
  | nil => exact ⟨[], dseed, by simp, by simp⟩
  | @ax π C _ hC hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨C0, hC0, rfl⟩ := hC
    rcases hax C0 hC0 with hstep | already
    ·
      obtain ⟨D, hD, hCD⟩ := hstep
      refine ⟨img project (linKOfClause C0) :: linKOfClause D :: τ,
        .weak (.ax hτ ⟨D, hD, rfl⟩ (width_clause hk D)) (List.mem_cons.2 (Or.inl rfl))
          (ax_weak project extend hsat hCD) (width_img project hw), ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · intro L hL
        rcases List.mem_cons.1 hL with rfl | hL
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
    · refine ⟨τ,hτ,by simp only [List.length_cons]; omega,?_⟩
      intro L hL
      rcases List.mem_cons.mp hL with rfl | hL
      · exact List.mem_append_right _ already
      · exact hm _ hL
  | @cut π C D R _ hC hD hcut hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨R', hR', hsub⟩ := cut_img project hneg hcut
    refine ⟨img project R :: R' :: τ,
      .weak (.cut hτ (hm _ hC) (hm _ hD) hR' (fun T hT => width_img project hw T (hsub hT)))
        (List.mem_cons.2 (Or.inl rfl)) (weak_sub hsub) (width_img project hw), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
  | @andIntro π C D R _ hC hD hand hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨R', hR', hsub⟩ := and_img project hand
    refine ⟨img project R :: R' :: τ,
      .weak (.andIntro hτ (hm _ hC) (hm _ hD) hR'
        (fun T hT => width_img project hw T (hsub hT)))
        (List.mem_cons.2 (Or.inl rfl)) (weak_sub hsub) (width_img project hw), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
  | @weak π C D _ hC hW hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    refine ⟨img project D :: τ,
      .weak hτ (hm _ hC) (weak_img project extend hsat hW) (width_img project hw), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (hm L hL)


def par (a : V → Bool) (f : Finset V) : Prop := Odd (f.filter (fun v => a v = true)).card

theorem card_sd (s t : Finset V) : (symmDiff s t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have h1 := Finset.card_union_add_card_inter s t
  have h2 : s ∪ t = (symmDiff s t) ∪ (s ∩ t) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff s t) (s ∩ t) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1; omega

theorem par_sd (a : V → Bool) (s t : Finset V) : par a (symmDiff s t) ↔ ¬ (par a s ↔ par a t) := by
  unfold par
  have hf : (symmDiff s t).filter (fun v => a v = true) =
      symmDiff (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true)) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf]
  have := card_sd (s.filter (fun v => a v = true)) (t.filter (fun v => a v = true))
  simp only [Nat.odd_iff]; omega


private def paritySupport {X : Type} (map : X → Finset V) : List X → Finset V
  | [] => ∅
  | x :: xs => symmDiff (map x) (paritySupport map xs)

private noncomputable def value {X : Type} (map : X → Finset V) (a : V → Bool) (x : X) : Bool := by
  classical
  exact decide (par a (map x))

private noncomputable def projection {X : Type} (map : X → Finset V) (e : LinEq X) : LinEq V :=
  (paritySupport map e.1.toList, e.2)

private theorem parityList {X : Type} (map : X → Finset V) (a : V → Bool) (l : List X) :
    par a (paritySupport map l) ↔ Odd (l.filter (value map a)).length := by
  induction l with
  | nil => simp [par,paritySupport]
  | cons x l ih =>
    rw [paritySupport,par_sd,ih]
    by_cases hx : par a (map x)
    · have hh : value map a x = true := by simp [value,hx]
      simp [List.filter_cons,hh,hx,Nat.odd_iff] <;> omega
    · have hh : value map a x = false := by simp [value,hx]
      simp [List.filter_cons,hh,hx]

private theorem projection_sat {X : Type} (map : X → Finset V) (a : V → Bool) (e : LinEq X) :
    LinEqSat a (projection map e) ↔ LinEqSat (value map a) e := by
  classical
  rcases e with ⟨s,b⟩
  change (par a (paritySupport map s.toList) ↔ b = true) ↔ _
  rw [parityList]
  have eq : (s.toList.filter (value map a)).toFinset = s.filter (fun x => value map a x = true) := by
    ext x
    simp
  have nd : (s.toList.filter (value map a)).Nodup := s.nodup_toList.filter _
  have hlen := List.toFinset_card_of_nodup nd
  rw [eq] at hlen
  simp only [LinEqSat,hlen]

private theorem singleProj {X : Type} [DecidableEq X] (map : X → Finset V) (x : X) (b : Bool) :
    projection map ({x}, b) = (map x,b) := by
  simp [projection,paritySupport]

private def pref {n : ℕ} (v : Fin n → V) (j : Fin (n+1)) : Finset V :=
  (Finset.univ.filter fun u : Fin n => u.val < j.val).image v

private def supports {r n : ℕ} (v : Fin r → Fin n → V) :
    V ⊕ (Fin r × Fin (n+1)) → Finset V :=
  Sum.elim (fun x => {x}) (fun z => pref (v z.1) z.2)

private theorem prefZero {n : ℕ} (v : Fin n → V) : pref v 0 = ∅ := by simp [pref]
private theorem prefLast {n : ℕ} (v : Fin n → V) : pref v (Fin.last n) = Finset.univ.image v := by
  simp [pref,Fin.is_lt]
private theorem prefNext {n : ℕ} (v : Fin n → V) (j : Fin n) :
    pref v j.succ = insert (v j) (pref v j.castSucc) := by
  classical
  have h : (Finset.univ.filter fun x : Fin n => x.val < j.succ.val) =
      insert j (Finset.univ.filter fun x : Fin n => x.val < j.castSucc.val) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Fin.ext_iff,
      Fin.val_succ,Fin.val_castSucc]
    omega
  unfold pref
  rw [h,Finset.image_insert]

private theorem onOld {r n : ℕ} (v : Fin r → Fin n → V) (a : V → Bool) (x : V) :
    value (supports v) a (Sum.inl x) = a x := by
  cases hx : a x <;> simp [value,supports,par,Finset.filter_singleton,hx]

private abbrev Dk (F : Set (Clause V)) (k : ℕ) :=
  IsLinKDerivation k IsLinKWeakening (linKOfClause '' F)

private theorem wider {F : Set (Clause V)} {k : ℕ} (hk : 1 ≤ k) {p : List (LinKLine V)}
    (h : Der F p) : Dk F k p := by
  induction h with
  | nil => exact .nil
  | ax _ a w ih => exact .ax ih a (fun t ht => (w t ht).trans hk)
  | cut _ a b c w ih => exact .cut ih a b c (fun t ht => (w t ht).trans hk)
  | andIntro _ a b c w ih => exact .andIntro ih a b c (fun t ht => (w t ht).trans hk)
  | weak _ a b w ih => exact .weak ih a b (fun t ht => (w t ht).trans hk)

private theorem appendDer {F : Set (Clause V)} {k : ℕ} {p q : List (LinKLine V)}
    (hp : Dk F k p) (hq : Dk F k q) : Dk F k (p ++ q) := by
  induction hp with
  | nil => exact hq
  | ax _ a w ih => exact .ax ih a w
  | cut _ a b c w ih => exact .cut ih (List.mem_append_left _ a) (List.mem_append_left _ b) c w
  | andIntro _ a b c w ih => exact .andIntro ih (List.mem_append_left _ a) (List.mem_append_left _ b) c w
  | weak _ a b w ih => exact .weak ih (List.mem_append_left _ a) b w

private theorem prelude {r n k : ℕ} (v : Fin r → Fin n → V) (F : Set (Clause V)) (hk : 1 ≤ k)
    (ax : ∀ i, Finset.univ.image (fun j => (v i j,true)) ∈ F)
    (pair : ∀ i j l, j ≠ l → {(v i j,false),(v i l,false)} ∈ F) (selected : Finset (Fin r)) :
    ∃ p : List (LinKLine V), Dk F k p ∧ p.length ≤ 4 * selected.card * (n+1)^2 ∧
      ∀ i ∈ selected, ({({(Finset.univ.image (v i),true)} : LinTerm V)} : LinKLine V) ∈ p := by
  classical
  induction selected using Finset.induction_on with
  | empty => exact ⟨[],.nil,by simp,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨p,dp,lp,mp⟩ := ih
    let S := Finset.univ.image (v i)
    have h1 : S.image (fun x => (x,true)) ∈ F := by simpa [S,Finset.image_image,Function.comp_def] using ax i
    have h2 : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → {(x,false),(y,false)} ∈ F := by
      intro x hx y hy ne
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hy
      exact pair i j l (fun h => ne (congrArg (v i) h))
    obtain ⟨q,dq,mq,lq⟩ := finish V S F h1 h2
    refine ⟨q++p,appendDer (wider hk dq) dp,?_,?_⟩
    · have sc : S.card ≤ n := by
        exact (Finset.card_image_le).trans (by simp)
      have lc : 4 * (S.card + 1)^2 ≤ 4 * (n+1)^2 := by gcongr
      simp only [List.length_append, Finset.card_insert_of_notMem hi]
      nlinarith
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact List.mem_append_left _ mq
      · exact List.mem_append_right _ (mp j hj)

private theorem answer : ∀ (V : Type) [DecidableEq V] (r n k : ℕ) (v : Fin r → Fin n → V)
    (R : Set (PEqualNP.ProofComplexity.Clause V)),
  (∀ i, Function.Injective (v i)) → 1 ≤ k →
  let A := fun i : Fin r => Finset.univ.image (fun j => (v i j, true))
  let F := R ∪ Set.range A
  (∀ i (j l : Fin n), j ≠ l → {(v i j, false), (v i l, false)} ∈ F) →
  let X := V ⊕ (Fin r × Fin (n + 1))
  let old := fun x : V => (Sum.inl x : X)
  let flag := fun (i : Fin r) (j : Fin (n + 1)) => (Sum.inr (i, j) : X)
  let H : Set (PEqualNP.ProofComplexity.Clause X) :=
    (fun C : PEqualNP.ProofComplexity.Clause V => C.image (fun l => (old l.1, l.2))) '' R ∪
    {C | ∃ i : Fin r, C = {(flag i 0, false)} ∨ C = {(flag i (Fin.last n), true)}} ∪
    {C | ∃ (i : Fin r) (j : Fin n),
      C = {(flag i j.castSucc, true), (old (v i j), true), (flag i j.succ, false)}}
  ∀ π : List (PEqualNP.ProofComplexity.LinKLine X),
    PEqualNP.ProofComplexity.IsLinKRefutation k H π →
    ∃ τ : List (PEqualNP.ProofComplexity.LinKLine V),
      PEqualNP.ProofComplexity.IsLinKRefutation k F τ ∧
      τ.length ≤ 2 * π.length + 4 * r * (n + 1) ^ 2 := by
  classical
  intro V inst r n k v R hi hk A F pair X old flag H π refu
  let m := supports v
  have row (i : Fin r) : Finset.univ.image (fun j => (v i j,true)) ∈ F :=
    Or.inr ⟨i,rfl⟩
  obtain ⟨seed,ds,ls,hs⟩ := prelude v F hk row pair Finset.univ
  have negP (e : LinEq X) : projection m (negLinEq e) = negLinEq (projection m e) := rfl
  have axP (C : Clause X) (mem : C ∈ H) :
      (∃ D ∈ F, ∀ a, ClauseSat a D → ClauseSat (value m a) C) ∨
      img (projection m) (linKOfClause C) ∈ seed := by
    rcases mem with (⟨D,hD,rfl⟩ | ⟨i,hz | hend⟩) | ⟨i,j,rfl⟩
    · left
      refine ⟨D,Or.inl hD,?_⟩
      rintro a ⟨l,hl,ok⟩
      exact ⟨(old l.1,l.2),Finset.mem_image.mpr ⟨l,hl,rfl⟩,(onOld v a l.1).trans ok⟩
    · left
      subst C
      refine ⟨A i,row i,?_⟩
      intro a _
      refine ⟨(flag i 0,false),by simp,?_⟩
      simp [m,flag,value,supports,prefZero,par]
    · right
      subst C
      simpa [m,flag,img,linKOfClause,linOfClause,singleProj,supports,prefLast] using
        hs i (Finset.mem_univ i)
    · left
      refine ⟨A i,row i,?_⟩
      intro a _
      by_cases bit : a (v i j) = true
      · exact ⟨(old (v i j),true),by simp,(onOld v a _).trans bit⟩
      · by_cases before : value m a (flag i j.castSucc) = true
        · exact ⟨(flag i j.castSucc,true),by simp,before⟩
        · have hp : ¬par a (pref (v i) j.castSucc) := by
            intro hp
            exact before (by simp [m,flag,value,supports,hp])
          have hn : ¬par a (pref (v i) j.succ) := by
            rw [prefNext]
            simpa [par,Finset.filter_insert,bit] using hp
          exact ⟨(flag i j.succ,false),by simp,by simp [m,flag,value,supports,hn]⟩
  obtain ⟨t,dt,lt,mem⟩ := translate k H F (value m) (projection m) hk negP (projection_sat m) seed ds axP π refu.1
  refine ⟨t++seed,⟨dt,?_⟩,?_⟩
  · simpa [img] using mem ∅ refu.2
  · simp only [Finset.card_univ,Fintype.card_fin] at ls
    simp only [List.length_append]
    omega

end PEqualNP.Outside.L_pcx_209

theorem PEqualNP.Outside.L_pcx_209 : ∀ (V : Type) [DecidableEq V] (r n k : ℕ) (v : Fin r → Fin n → V)
    (R : Set (PEqualNP.ProofComplexity.Clause V)),
  (∀ i, Function.Injective (v i)) → 1 ≤ k →
  let A := fun i : Fin r => Finset.univ.image (fun j => (v i j, true))
  let F := R ∪ Set.range A
  (∀ i (j l : Fin n), j ≠ l → {(v i j, false), (v i l, false)} ∈ F) →
  let X := V ⊕ (Fin r × Fin (n + 1))
  let old := fun x : V => (Sum.inl x : X)
  let flag := fun (i : Fin r) (j : Fin (n + 1)) => (Sum.inr (i, j) : X)
  let H : Set (PEqualNP.ProofComplexity.Clause X) :=
    (fun C : PEqualNP.ProofComplexity.Clause V => C.image (fun l => (old l.1, l.2))) '' R ∪
    {C | ∃ i : Fin r, C = {(flag i 0, false)} ∨ C = {(flag i (Fin.last n), true)}} ∪
    {C | ∃ (i : Fin r) (j : Fin n),
      C = {(flag i j.castSucc, true), (old (v i j), true), (flag i j.succ, false)}}
  ∀ π : List (PEqualNP.ProofComplexity.LinKLine X),
    PEqualNP.ProofComplexity.IsLinKRefutation k H π →
    ∃ τ : List (PEqualNP.ProofComplexity.LinKLine V),
      PEqualNP.ProofComplexity.IsLinKRefutation k F τ ∧
      τ.length ≤ 2 * π.length + 4 * r * (n + 1) ^ 2 := by
  exact PEqualNP.Outside.L_pcx_209.answer
