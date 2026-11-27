import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_365_aux

open PEqualNP.ProofComplexity

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

theorem widthG {C G : LinKLine W} {k : ℕ}
    (hc : ∀ T ∈ C, T.card ≤ k) (hg : ∀ T ∈ G, T.card ≤ k) :
    ∀ T ∈ C ∪ G, T.card ≤ k := by
  intro T h
  exact (Finset.mem_union.mp h).elim (hc T) (hg T)

theorem cutG (G : LinKLine W) {C D r R : LinKLine W}
    (hr : IsLinKCut C D r) (hs : r ⊆ R) :
    ∃ z, IsLinKCut (C ∪ G) (D ∪ G) z ∧ z ⊆ R ∪ G := by
  obtain ⟨T,hT,hD,rfl⟩ := hr
  refine ⟨_, ⟨T,Finset.mem_union_left _ hT,fun e he => Finset.mem_union_left _ (hD e he),rfl⟩,?_⟩
  intro U h
  by_cases hG : U ∈ G
  · exact Finset.mem_union_right _ hG
  apply Finset.mem_union_left _ (hs ?_)
  simp only [Finset.mem_union,Finset.mem_erase,Finset.mem_sdiff,hG,or_false] at h ⊢
  exact h

theorem andG (G : LinKLine W) {C D r R : LinKLine W}
    (hr : IsLinKAndIntro C D r) (hs : r ⊆ R) :
    ∃ z, IsLinKAndIntro (C ∪ G) (D ∪ G) z ∧ z ⊆ R ∪ G := by
  obtain ⟨T,S,hT,hS,rfl⟩ := hr
  refine ⟨_, ⟨T,S,Finset.mem_union_left _ hT,Finset.mem_union_left _ hS,rfl⟩,?_⟩
  intro U h
  by_cases hG : U ∈ G
  · exact Finset.mem_union_right _ hG
  apply Finset.mem_union_left _ (hs ?_)
  simp only [Finset.mem_union,Finset.mem_erase,hG,or_false] at h ⊢
  exact h

theorem weakG (G : LinKLine W) {C D : LinKLine W} (h : IsLinKWeakening C D) :
    IsLinKWeakening (C ∪ G) (D ∪ G) := by
  intro T hT
  rcases Finset.mem_union.mp hT with ht | ht
  · rcases h T ht with ⟨S,hs,H⟩ | H
    · exact Or.inl ⟨S,Finset.mem_union_left _ hs,H⟩
    · right
      intro a ha
      obtain ⟨q,hq,sq⟩ := H a ha
      exact ⟨q,Finset.mem_union_left _ hq,sq⟩
  · exact Or.inl ⟨T,Finset.mem_union_right _ ht, fun _ s => s⟩
theorem width_clause {k : ℕ} (hk : 1 ≤ k) (D : Clause W) :
    ∀ T ∈ linKOfClause D, T.card ≤ k := by
  intro T hT
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hT
  rw [Finset.card_singleton]; exact hk

theorem simulate (G : LinKLine W) (k : ℕ) (F : Set (Clause V)) (H : Set (Clause W))
    (extend : (W → Bool) → V → Bool) (project : LinEq V → LinEq W) (hk : 1 ≤ k) (hwG : ∀ T ∈ G, T.card ≤ k)
    (hneg : ∀ e, project (negLinEq e) = negLinEq (project e))
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e)
    (hax : ∀ C ∈ F, ∃ D ∈ H, IsLinKWeakening (linKOfClause D) (img project (linKOfClause C) ∪ G))
    (π : List (LinKLine V))
    (h : IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F) π) :
    ∃ τ : List (LinKLine W),
      IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' H) τ ∧
      τ.length ≤ 2 * π.length ∧ ∀ L ∈ π, (img project L ∪ G) ∈ τ := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp⟩
  | @ax π C _ hC hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨C0, hC0, rfl⟩ := hC
    obtain ⟨D, hD, hCD⟩ := hax C0 hC0
    refine ⟨(img project (linKOfClause C0) ∪ G) :: linKOfClause D :: τ,
      .weak (.ax hτ ⟨D, hD, rfl⟩ (width_clause hk D)) (List.mem_cons.2 (Or.inl rfl))
        hCD (widthG (width_img project hw) hwG), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
  | @cut π C D R _ hC hD hcut hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨r, hr, hs⟩ := cut_img project hneg hcut
    obtain ⟨R', hR', hsub⟩ := cutG G hr hs
    refine ⟨(img project R ∪ G) :: R' :: τ,
      .weak (.cut hτ (hm _ hC) (hm _ hD) hR' (fun T hT => widthG (width_img project hw) hwG T (hsub hT)))
        (List.mem_cons.2 (Or.inl rfl)) (weak_sub hsub) (widthG (width_img project hw) hwG), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
  | @andIntro π C D R _ hC hD hand hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨r, hr, hs⟩ := and_img project hand
    obtain ⟨R', hR', hsub⟩ := andG G hr hs
    refine ⟨(img project R ∪ G) :: R' :: τ,
      .weak (.andIntro hτ (hm _ hC) (hm _ hD) hR'
        (fun T hT => widthG (width_img project hw) hwG T (hsub hT)))
        (List.mem_cons.2 (Or.inl rfl)) (weak_sub hsub) (widthG (width_img project hw) hwG), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
  | @weak π C D _ hC hW hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    refine ⟨(img project D ∪ G) :: τ,
      .weak hτ (hm _ hC) (weakG G (weak_img project extend hsat hW)) (widthG (width_img project hw) hwG), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (hm L hL)

def bit (s : Finset V) (x : V → Bool) : Bool := decide ((s.filter (fun i => x i = true)).card % 2 = 1)

def Aff (f : (V → Bool) → Bool) : Prop := ∃ s : Finset V, ∃ b : Bool, ∀ x, f x = xor (bit s x) b

theorem aff_const (b : Bool) : Aff (V := V) (fun _ => b) :=
  ⟨∅, b, by simp [bit]⟩

theorem aff_var (i : V) : Aff (fun x : V → Bool => x i) := by
  refine ⟨{i}, false, ?_⟩
  intro x
  cases h : x i <;> simp [bit,Finset.filter_singleton,h]

theorem bit_add (s t : Finset V) (x : V → Bool) :
    bit ((s \ t) ∪ (t \ s)) x = xor (bit s x) (bit t x) := by
  classical
  let a := s.filter (fun i => x i = true)
  let b := t.filter (fun i => x i = true)
  have he : ((s \ t ∪ (t \ s)).filter (fun i => x i = true)) = (a \ b) ∪ (b \ a) := by
    ext v
    cases hv : x v <;> simp [a,b,hv]
  have hd : Disjoint (a \ b) (b \ a) := Finset.disjoint_left.mpr (by simp_all)
  have ha := Finset.card_sdiff_add_card_inter a b
  have hb := Finset.card_sdiff_add_card_inter b a
  rw [Finset.inter_comm b a] at hb
  unfold bit
  rw [he, Finset.card_union_of_disjoint hd]
  change decide (_ % 2 = 1) = xor (decide (a.card % 2 = 1)) (decide (b.card % 2 = 1))
  by_cases h1 : a.card % 2 = 1 <;> by_cases h2 : b.card % 2 = 1 <;> simp [h1,h2] <;> omega

theorem aff_xor {f g : (V → Bool) → Bool} (hf : Aff f) (hg : Aff g) : Aff (fun x => xor (f x) (g x)) := by
  obtain ⟨s,b,hs⟩ := hf
  obtain ⟨t,c,ht⟩ := hg
  refine ⟨(s \ t) ∪ (t \ s), xor b c, fun x => ?_⟩
  simp only [hs, ht, bit_add]
  cases bit s x <;> cases bit t x <;> cases b <;> cases c <;> rfl

theorem aff_not {f : (V → Bool) → Bool} (h : Aff f) : Aff (fun x => !(f x)) := by
  simpa using aff_xor h (aff_const true)

theorem aff_par (u : W → (V → Bool) → Bool) (hu : ∀ w, Aff (u w)) (s : Finset W) :
    Aff (fun x => bit s (fun w => u w x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [bit] using (aff_const (V := V) false)
  | @insert w s hw ih =>
    convert aff_xor (hu w) ih using 1
    funext x
    cases h : u w x
    · simp [bit, Finset.filter_insert,h]
    · simp [bit, Finset.filter_insert,h, hw]
      generalize (s.filter (fun i => u i x = true)).card = m
      by_cases hm : m % 2 = 1 <;> simp [hm] <;> omega

theorem sat_bit (x : V → Bool) (q : LinEq V) : LinEqSat x q ↔ bit q.1 x = q.2 := by
  simp only [LinEqSat, bit, Nat.odd_iff]
  cases q.2 <;> simp

noncomputable def proj (u : W → (V → Bool) → Bool) (hu : ∀ w, Aff (u w)) (q : LinEq W) : LinEq V :=
  let h := aff_par u hu q.1
  (h.choose, xor q.2 h.choose_spec.choose)

theorem proj_neg (u : W → (V → Bool) → Bool) (hu : ∀ w, Aff (u w)) (q : LinEq W) :
    proj u hu (negLinEq q) = negLinEq (proj u hu q) := by
  simp [proj,negLinEq]

theorem proj_sat (u : W → (V → Bool) → Bool) (hu : ∀ w, Aff (u w)) (x : V → Bool) (q : LinEq W) :
    LinEqSat x (proj u hu q) ↔ LinEqSat (fun w => u w x) q := by
  let h := aff_par u hu q.1
  have he : bit q.1 (fun w => u w x) = _ := h.choose_spec.choose_spec x
  rw [sat_bit,sat_bit,he]
  change (bit h.choose x = xor q.2 h.choose_spec.choose) ↔ (xor (bit h.choose x) h.choose_spec.choose = q.2)
  cases bit h.choose x <;> cases q.2 <;> cases h.choose_spec.choose <;> decide
open PEqualNP.CircuitLowerBounds

abbrev X (V : Type) := V → Bool
abbrev Form (V : Type) := X V → Bool

inductive Piece (V : Type) : ℕ → (X V → List Bool) → Prop
  | leaf {z} (h : ∀ i, Aff (fun x => (z x).getD i false)) : Piece V 0 z
  | fork {z : X V → List Bool} {d} (q : Form V) (hq : Aff q) (f : Bool → X V → List Bool)
      (hh : ∀ b, Piece V d (f b)) (hz : ∀ x, f (q x) x = z x) : Piece V (d+1) z

theorem input_tree (vs : List V) (f : List Bool → List Bool) :
    Piece V vs.length (fun x => f (vs.map x)) := by
  induction vs generalizing f with
  | nil => exact .leaf (fun i => aff_const ((f []).getD i false))
  | cons v vs ih =>
    exact .fork (fun x => x v) (aff_var v) (fun b x => f (b :: vs.map x))
      (fun b => ih (fun l => f (b :: l))) (fun _ => rfl)

def execute (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) w

noncomputable def nonlinear (g : Gate) : Bool :=
  @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)

def GateOK (g : Gate) := ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)

def readF (w : List (Form V)) (i : ℕ) := w.getD i (fun _ => false)

theorem eval_read (w : List (Form V)) (x : X V) (i : ℕ) :
    (w.map (fun f => f x)).getD i false = readF w i x :=
  List.getD_map w (fun _ => false) (fun f => f x)

theorem aff_read {w : List (Form V)} (hw : ∀ f ∈ w, Aff f) (i : ℕ) :
    Aff (readF w i) := by
  by_cases hi : i < w.length
  · rw [readF, List.getD_eq_getElem _ _ hi]
    exact hw _ (List.getElem_mem hi)
  · rw [readF, List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    exact aff_const false

theorem mod_aff (l : List (Form V)) (h : ∀ f ∈ l, Aff f) :
    Aff (fun x => GateOp.eval (.mod 2) (l.map (fun f => f x))) := by
  induction l with
  | nil => exact aff_const true
  | cons f l ih =>
    convert aff_xor (h f (by simp)) (ih (fun g hg => h g (by simp [hg]))) using 1
    funext x
    cases e : f x <;> simp [GateOp.eval,e]
    generalize (List.map (fun f : Form V => f x) l).count true = m
    by_cases hm : m % 2 = 0 <;> simp [hm] <;> omega

theorem gate_tree (gs : List Gate) (ok : ∀ g ∈ gs, GateOK g)
    (w : List (Form V)) (hw : ∀ f ∈ w, Aff f) :
    Piece V (gs.countP nonlinear) (fun x => execute gs (w.map (fun f => f x))) := by
  induction gs generalizing w with
  | nil => exact .leaf (fun i => by simpa only [execute,List.foldl_nil,eval_read] using aff_read hw i)
  | cons g gs ih =>
    have cont (f : Form V) (hf : Aff f) :
        Piece V (gs.countP nonlinear) (fun x => execute gs ((w.map (fun z => z x)) ++ [f x])) := by
      simpa only [List.map_append,List.map_cons,List.map_nil] using
        ih (fun g hg => ok g (List.mem_cons_of_mem _ hg)) (w ++ [f]) (by
          intro u hu
          rcases List.mem_append.mp hu with h | h
          · exact hw _ h
          · simpa only [List.mem_singleton.mp h] using hf)
    rcases ok g (by simp) with ⟨hop,hlen⟩ | hmod | ⟨hnot,hlen⟩
    · obtain ⟨i,j,hij⟩ : ∃ i j, g.inputs = [i,j] := by
        generalize g.inputs = l at hlen ⊢
        obtain _ | ⟨i,l⟩ := l <;> simp_all
        obtain _ | ⟨j,l⟩ := l <;> simp_all
      have hn : nonlinear g = true := by simp [nonlinear,hop]
      simp only [List.countP_cons,hn, Bool.false_eq_true, ite_false, Nat.add_zero,ite_true]
      let next := fun b (x : X V) => g.op.eval [b,readF w j x]
      have hf (b : Bool) : Aff (next b) := by
        rcases hop with ha | ha <;> cases b <;> simp [next,ha, GateOp.eval] <;>
          first | exact aff_const _ | exact aff_read hw j
      exact .fork (readF w i) (aff_read hw i) _
        (fun b => cont (next b) (hf b)) (fun x => by simp only [execute, List.foldl_cons, next, hij, List.map_cons, List.map_nil, eval_read])
    · have hn : nonlinear g = false := by simp [nonlinear,hmod]
      simp only [List.countP_cons,hn, Bool.false_eq_true, ite_false, Nat.add_zero,ite_true]
      let l := g.inputs.map (readF w)
      have hm := mod_aff l (by
        intro f hf
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
        exact aff_read hw i)
      convert cont _ hm using 1
      funext x
      simp only [execute,List.foldl_cons,hmod,l,List.map_map,Function.comp_def,eval_read]
    · have hn : nonlinear g = false := by simp [nonlinear,hnot]
      simp only [List.countP_cons,hn, Bool.false_eq_true, ite_false, Nat.add_zero,ite_true]
      obtain ⟨i,hi⟩ : ∃ i, g.inputs = [i] := by
        generalize g.inputs = l at hlen ⊢
        obtain _ | ⟨i,l⟩ := l <;> simp_all
      convert cont _ (aff_not (aff_read hw i)) using 1
      funext x
      simp only [execute,List.foldl_cons,hnot,hi,List.map_cons,List.map_nil,eval_read,GateOp.eval,List.headD_cons]
def guard (G : LinClause V) : LinKLine V := G.image (fun q => ({q} : LinTerm V))
def valid (G : LinClause V) (x : X V) := ∀ q ∈ G, ¬ LinEqSat x q

theorem axG (G : LinClause W) (project : LinEq V → LinEq W) (extend : X W → X V)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) {C : Clause V}
    {D : Clause W} (hCD : ∀ a, valid G a → ClauseSat a D → ClauseSat (extend a) C) :
    IsLinKWeakening (linKOfClause D) (img project (linKOfClause C) ∪ guard G) := by
  classical
  intro T hT
  right
  intro a ha
  by_cases hv : valid G a
  · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hT
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hq
    have hla : a l.1 = l.2 := (sat_single a l.1 l.2).1 (ha _ (Finset.mem_singleton_self _))
    obtain ⟨l', hl', h'⟩ := hCD a hv ⟨l, hl, hla⟩
    refine ⟨project (({l'.1} : Finset V), l'.2), Finset.mem_union_left _ ?_,
      (hsat a _).2 ((sat_single (extend a) l'.1 l'.2).2 h')⟩
    rw [show ({project (({l'.1} : Finset V), l'.2)} : LinTerm W) =
        ({(({l'.1} : Finset V), l'.2)} : LinTerm V).image project from
        (Finset.image_singleton _ _).symm]
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hl'))
  · unfold valid at hv
    push_neg at hv
    obtain ⟨q,hq,hs⟩ := hv
    exact ⟨q,Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq),hs⟩

abbrev Der (k : ℕ) (F : Set (Clause V)) :=
  IsLinKDerivation k IsLinKWeakening (linKOfClause '' F)

theorem appendDer {k : ℕ} {F : Set (Clause V)} {s r : List (LinKLine V)}
    (hs : Der k F s) (hr : Der k F r) : Der k F (s ++ r) := by
  induction hs with
  | nil => exact hr
  | ax _ h w ih => exact .ax ih h w
  | cut _ h j p w ih => exact .cut ih (List.mem_append_left _ h) (List.mem_append_left _ j) p w
  | andIntro _ h j p w ih => exact .andIntro ih (List.mem_append_left _ h) (List.mem_append_left _ j) p w
  | weak _ h p w ih => exact .weak ih (List.mem_append_left _ h) p w

theorem width_guard {k : ℕ} (hk : 1 ≤ k) (G : LinClause V) :
    ∀ T ∈ guard G, T.card ≤ k := by
  intro T h
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp h
  simpa using hk

def Ach (k : ℕ) (F : Set (Clause V)) (G : LinClause V) (bound : ℕ) : Prop :=
    ∃ p : List (LinKLine V), Der k F p ∧ guard G ∈ p ∧ p.length + 1 ≤ bound

theorem glue {k B : ℕ} {F : Set (Clause V)} {G : LinClause V} (hk : 1 ≤ k) (s : Finset V)
    (h : ∀ b : Bool, Ach k F (insert (s,b) G) B) : Ach k F G (B*2) := by
  obtain ⟨p,hp,mp,lp⟩ := h false
  obtain ⟨r,hr,mr,lr⟩ := h true
  have hc : IsLinKCut (guard (insert (s,false) G)) (guard (insert (s,true) G)) (guard G) := by
    refine ⟨{(s,false)}, by simp [guard], ?_, ?_⟩
    · intro e he
      subst_eqs
      rw [Finset.mem_singleton.mp he]
      simp [guard,negLinEq]
    · simp only [guard, Finset.image_insert, Finset.image_singleton,negLinEq]
      ext T
      simp only [Finset.mem_union,Finset.mem_erase,Finset.mem_insert,Finset.mem_sdiff,Finset.mem_singleton]
      have hn : ({(s,false)} : LinTerm V) ≠ {(s,true)} := by simp
      simp only [Bool.not_false]
      grind only
  exact ⟨guard G :: (p ++ r), .cut (appendDer hp hr) (List.mem_append_left _ mp)
    (List.mem_append_right _ mr) hc (width_guard hk _), by simp, by simp only [List.length_cons,List.length_append]; omega⟩

theorem assemble {z orig : X V → List Bool} {d k B : ℕ} {F : Set (Clause V)}
    (tree : Piece V d z) (hk : 1 ≤ k)
    (hleaf : ∀ (G : LinClause V) (z : X V → List Bool), (∀ i, Aff (fun x => (z x).getD i false)) →
      (∀ x, valid G x → z x = orig x) → Ach k F G B)
    (G : LinClause V) (ag : ∀ x, valid G x → z x = orig x) : Ach k F G (B*2^d) := by
  induction tree generalizing G with
  | leaf h => simpa using hleaf G _ h ag
  | @fork z d q hq f hh hz ih =>
    obtain ⟨s,c,hs⟩ := hq
    rw [pow_succ,← Nat.mul_assoc]
    apply glue hk s
    intro b
    apply ih (xor (!b) c)
    intro x hv
    have hG : valid G x := fun e he => hv e (Finset.mem_insert_of_mem he)
    have hn := hv (s,b) (Finset.mem_insert_self ..)
    rw [sat_bit] at hn
    have hbit : bit s x = !b := by cases he : bit s x <;> cases b <;> simp_all
    rw [← hbit, ← hs]
    exact (hz x).trans (ag x hG)
theorem circuit_piece (n : ℕ) (order : Fin n ≃ V) (H : Circuit) (ok : ∀ g ∈ H.gates, GateOK g) :
    Piece V (min n (H.gates.countP nonlinear))
      (fun x => H.wires ([false,true] ++ List.ofFn (fun j => x (order j)))) := by
  let vs := List.ofFn (fun j => order j)
  have hv (x : X V) : vs.map x = List.ofFn (fun j => x (order j)) := by
    simp [vs,List.map_ofFn,Function.comp_def]
  by_cases hn : n ≤ H.gates.countP nonlinear
  · rw [Nat.min_eq_left hn]
    simpa only [vs,List.length_ofFn,List.map_ofFn,Function.comp_def] using
      input_tree vs (fun l => H.wires ([false,true] ++ l))
  · rw [Nat.min_eq_right (by omega)]
    let w : List (Form V) := [fun _ => false, fun _ => true] ++ vs.map (fun i x => x i)
    have hw : ∀ f ∈ w, Aff f := by
      intro f hf
      rcases List.mem_append.mp hf with h | h
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl | rfl <;> exact aff_const _
      · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
        exact aff_var _
    simpa only [w,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
      vs,List.map_ofFn, Circuit.wires,execute] using gate_tree H.gates ok w hw

theorem finish {V : Type} [DecidableEq V] {a k : ℕ}
    (F : Set (Clause V)) (extra : Set (Clause (V ⊕ Fin a))) (orig : X V → List Bool)
    (pick : Fin a → ℕ) {d : ℕ} (tree : Piece V d orig)
    (hF : F.Nonempty) (hk : 1 ≤ k)
    (he : ∀ x : X V, Satisfies (Sum.elim x (fun i => (orig x).getD (pick i) false)) extra)
    (π : List (LinKLine (V ⊕ Fin a)))
    (hπ : IsLinKRefutation k ((fun cl : Clause V =>
      cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin a), l.2))) '' F ∪ extra) π) :
    ∃ τ : List (LinKLine V), IsLinKRefutation k F τ ∧ τ.length ≤ (2*π.length+1)*2^d := by
  have leaf (G : LinClause V) (z : X V → List Bool) (hz : ∀ i, Aff (fun x => (z x).getD i false))
      (ag : ∀ x, valid G x → z x = orig x) : Ach k F G (2*π.length+1) := by
    let u : V ⊕ Fin a → Form V := Sum.elim (fun v x => x v) (fun i x => (z x).getD (pick i) false)
    have hu : ∀ v, Aff (u v) := by
      intro v
      cases v with
      | inl v => exact aff_var v
      | inr i => exact hz (pick i)
    let ext := fun x v => u v x
    have hax : ∀ C ∈ ((fun cl : Clause V =>
        cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin a), l.2))) '' F ∪ extra),
        ∃ D ∈ F, IsLinKWeakening (linKOfClause D) (img (proj u hu) (linKOfClause C) ∪ guard G) := by
      intro C hc
      rcases hc with ⟨D,hD,rfl⟩ | hc
      · refine ⟨D,hD,axG G _ ext (proj_sat u hu) ?_⟩
        rintro x hv ⟨l,hl,hs⟩
        exact ⟨_,Finset.mem_image_of_mem _ hl,hs⟩
      · obtain ⟨D,hD⟩ := hF
        refine ⟨D,hD,axG G _ ext (proj_sat u hu) ?_⟩
        intro x hv _
        have eq : ext x = Sum.elim x (fun i => (orig x).getD (pick i) false) := by
          funext v
          cases v with
          | inl v => rfl
          | inr i => simp [ext,u,ag x hv]
        rw [eq]
        exact he x C hc
    obtain ⟨τ,ht,hl,hm⟩ := simulate (guard G) k _ F ext (proj u hu) hk (width_guard hk G)
      (proj_neg u hu) (proj_sat u hu) hax π hπ.1
    exact ⟨τ,ht,by simpa [img] using hm ∅ hπ.2,by omega⟩
  obtain ⟨τ,ht,m,hl⟩ := assemble tree hk leaf ∅ (fun _ _ => rfl)
  exact ⟨τ,⟨ht,by simpa [guard] using m⟩,by omega⟩

end PEqualNP.Outside.L_pcx_365_aux

open PEqualNP.Outside.L_pcx_365_aux
theorem PEqualNP.Outside.L_pcx_365 : (∀ (V : Type) [DecidableEq V] (n a k : ℕ) (order : Fin n ≃ V)
    (F : Set (PEqualNP.ProofComplexity.Clause V))
    (extra : Set (PEqualNP.ProofComplexity.Clause (V ⊕ Fin a)))
    (H : PEqualNP.CircuitLowerBounds.Circuit) (pick : Fin a → Fin (2+n+H.size)),
  let t := H.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _))
  let extend := fun (x : V → Bool) => Sum.elim x (fun i : Fin a =>
    (H.wires ([false,true] ++ List.ofFn (fun j => x (order j)))).getD (pick i).val false)
  let lift := fun (cl : PEqualNP.ProofComplexity.Clause V) =>
    cl.image (fun l => ((Sum.inl l.1 : V ⊕ Fin a), l.2))
  F.Nonempty → 1 ≤ k → PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+n) H →
  (∀ g ∈ H.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) →
  (∀ x : V → Bool, PEqualNP.ProofComplexity.Satisfies (extend x) extra) →
  ∀ π : List (PEqualNP.ProofComplexity.LinKLine (V ⊕ Fin a)),
    PEqualNP.ProofComplexity.IsLinKRefutation k (Set.image lift F ∪ extra) π →
    ∃ τ : List (PEqualNP.ProofComplexity.LinKLine V),
      PEqualNP.ProofComplexity.IsLinKRefutation k F τ ∧
      τ.length ≤ (2*π.length+1)*2^(min n t)) := by
  intro V _ n a k order F extra H pick
  dsimp only
  intro hF hk _ ok he π hπ
  exact finish F extra _ (fun i => (pick i).val) (circuit_piece n order H ok) hF hk he π hπ
