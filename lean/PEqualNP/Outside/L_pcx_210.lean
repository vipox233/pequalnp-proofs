import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_210

namespace Cycles210

private theorem rotate_constant {n : Nat} (f : Fin n → Bool)
    (h : ∀ a, f a = true → f (finRotate n a) = true) (i j : Fin n) : f i = f j := by
  by_cases hn : 2 ≤ n
  · have nonfixed (x : Fin n) : finRotate n x ≠ x := by
      apply Equiv.Perm.mem_support.mp
      rw [support_finRotate_of_le hn]
      exact Finset.mem_univ _
    have reach (a b : Fin n) (ha : f a = true) : f b = true := by
      obtain ⟨m,hm⟩ := (isCycle_finRotate_of_le hn).exists_pow_eq (nonfixed a) (nonfixed b)
      have go (s : Nat) : f ((finRotate n ^ s) a) = true := by
        induction s with
        | zero => simpa using ha
        | succ s ih =>
            rw [pow_succ', Equiv.Perm.mul_apply]
            exact h _ ih
      rw [← hm]
      exact go m
    cases hi : f i <;> cases hj : f j
    · rfl
    · exact Bool.noConfusion (hi.symm.trans (reach j i hj))
    · exact Bool.noConfusion (hj.symm.trans (reach i j hi))
    · rfl
  · have hsame : i = j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
    rw [hsame]

noncomputable def onFiber {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (b : β) :
    Equiv.Perm {a : α // f a = b} :=
  let e := Fintype.equivFin {a : α // f a = b}
  e.trans ((finRotate _).trans e.symm)

noncomputable def cycle {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) : Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (onFiber f)).trans (Equiv.sigmaFiberEquiv f))

theorem keeps {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (a : α) :
    f (cycle f a) = f a :=
  (onFiber f (f a) ⟨a,rfl⟩).property

theorem on_value {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (b : β)
    (a : {a : α // f a = b}) : cycle f a.val = (onFiber f b a).val := by
  obtain ⟨a, ha⟩ := a
  subst b
  rfl

theorem equal {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (a : α → Bool)
    (h : ∀ x, a x = true → a (cycle f x) = true) {x y : α} (he : f x = f y) : a x = a y := by
  let e := Fintype.equivFin {z : α // f z = f x}
  let g := fun j => a (e.symm j).val
  have step (z : Fin _) (hz : g z = true) : g (finRotate _ z) = true := by
    let v := e.symm z
    have same := on_value f (f x) v
    have h' := h v.val hz
    rw [same] at h'
    change a ((Fintype.equivFin {z : α // f z = f x}).symm
      (finRotate _ (e (e.symm z)))).val = true at h'
    simpa only [Equiv.apply_symm_apply] using h'
  have res := rotate_constant g step (e ⟨x,rfl⟩) (e ⟨y,he.symm⟩)
  simpa only [g, Equiv.symm_apply_apply] using res

end Cycles210

namespace Replay210

open PEqualNP.ProofComplexity MvPolynomial

def litMap {V W : Type} (f : V → W) (l : Literal V) : Literal W :=
  (f l.1, l.2)

theorem litMap_injective {V W : Type} {f : V → W} (hf : Function.Injective f) :
    Function.Injective (litMap f) := by
  intro x y h
  have hs := congrArg (fun l : Literal W => l.2) h
  exact Prod.ext (hf (congrArg Prod.fst h)) hs

theorem renameReplay {V W : Type} (f : V → W)
    {F : Set (MvPolynomial V (ZMod 2))} {G : Set (MvPolynomial W (ZMod 2))}
    {D : ℕ} {p : MvPolynomial V (ZMod 2)}
    (hax : ∀ a ∈ F, a.totalDegree ≤ D → PCDerivable G D (rename f a))
    (hp : PCDerivable F D p) : PCDerivable G D (rename f p) := by
  induction hp with
  | ax ha hd => exact hax _ ha hd
  | zero => simpa using (PCDerivable.zero : PCDerivable G D 0)
  | add _ _ h₁ h₂ => simpa only [map_add] using h₁.add h₂
  | @mulX j p _ hd ih =>
      rw [map_mul, rename_X]
      apply PCDerivable.mulX (f j) ih
      simpa only [map_mul, rename_X] using (totalDegree_rename_le f (X j * p)).trans hd

theorem clausePoly_image {V W : Type} [DecidableEq W] (f : V → W) (A : Clause V)
    (hf : Set.InjOn (litMap f) (↑A : Set (Literal V))) :
    rename f (clausePoly A) = clausePoly (A.image (litMap f)) := by
  unfold clausePoly
  rw [map_prod, Finset.prod_image]
  · refine Finset.prod_congr rfl ?_
    rintro ⟨v,b⟩ _
    cases b <;> simp [litMap]
  · exact fun x hx y hy h => hf hx hy h

theorem clausePoly_pair {W : Type} [DecidableEq W] (w : W) :
    clausePoly ({(w, true), (w, false)} : Clause W) = X w * X w + X w := by
  simp [clausePoly, Finset.prod_insert, add_mul, add_comm]

theorem link_image {V W : Type} [DecidableEq V] [DecidableEq W]
    (f : V → W) (x y : V) (b : Bool) (hxy : f x = f y) :
    let A : Clause V := {(x, b), (y, !b)}
    Set.InjOn (litMap f) (↑A : Set (Literal V)) ∧
      A.image (litMap f) = {(f x, true), (f x, false)} := by
  dsimp only
  constructor
  · intro u hu v hv huv
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · have he := congrArg Prod.snd huv
      cases b <;> simp [litMap] at he
    · have he := congrArg Prod.snd huv
      cases b <;> simp [litMap] at he
    · rfl
  · cases b <;> simp [litMap, hxy, Finset.pair_comm]

theorem refutable {V W : Type} [DecidableEq W] (f : V → W)
    (F : Set (Clause V)) (G : Set (Clause W))
    (h : ∀ A ∈ F, Set.InjOn (litMap f) (↑A : Set (Literal V)) ∧
      (A.image (litMap f) ∈ G ∨ ∃ w : W, A.image (litMap f) = {(w, true), (w, false)}))
    {D : ℕ} (hp : PCRefutable (cnfSystem F) D) : PCRefutable (cnfSystem G) D := by
  have hg := renameReplay f (G := cnfSystem G) (p := 1) ?_ hp
  · simpa only [PCRefutable, map_one] using hg
  · intro a ha hdeg
    refine .ax ?_ ((totalDegree_rename_le f a).trans hdeg)
    rcases ha with ⟨v, rfl⟩ | ⟨A, hA, rfl⟩
    · exact Or.inl ⟨f v, by simp⟩
    · obtain ⟨hinj, himage⟩ := h A hA
      rw [clausePoly_image f A hinj]
      rcases himage with hAG | ⟨w, hw⟩
      · exact Or.inr ⟨_, hAG, rfl⟩
      · exact Or.inl ⟨w, by rw [hw, clausePoly_pair]⟩

theorem refutable_subset {V : Type} {F G : Set (Clause V)} (h : F ⊆ G)
    {D : ℕ} (hp : PCRefutable (cnfSystem F) D) : PCRefutable (cnfSystem G) D := by
  classical
  apply refutable id F G ?_ hp
  intro A hA
  have he : (litMap id : Literal V → Literal V) = id := by
    funext p
    exact Prod.eta p
  rw [he, Finset.image_id]
  exact ⟨fun _ _ _ _ hab => hab, Or.inl (h hA)⟩

end Replay210

namespace Split210

open PEqualNP.ProofComplexity

abbrev Occ {v : Nat} (F : Finset (Clause (Fin v))) := Σ C : ↑F, ↥C.val

def label {v : Nat} {F : Finset (Clause (Fin v))} (x : Occ F) : Fin v := x.2.val.1

def sign {v : Nat} {F : Finset (Clause (Fin v))} (x : Occ F) : Bool := x.2.val.2

noncomputable def next {v : Nat} (F : Finset (Clause (Fin v))) : Equiv.Perm (Occ F) :=
  Cycles210.cycle label

def lift {v : Nat} {F : Finset (Clause (Fin v))} (C : ↑F) (l : ↥C.val) : Literal (Occ F) :=
  (⟨C,l⟩,l.val.2)

theorem lift_inj {v : Nat} {F : Finset (Clause (Fin v))} (C : ↑F) : Function.Injective (lift C) := by
  intro a b eq
  obtain ⟨_, h⟩ := Sigma.mk.inj (congrArg Prod.fst eq)
  exact eq_of_heq h

noncomputable def copyClause {v : Nat} {F : Finset (Clause (Fin v))} (C : ↑F) : Clause (Occ F) := by
  classical
  exact Finset.univ.image (lift C)

noncomputable def link {v : Nat} {F : Finset (Clause (Fin v))} (x : Occ F) : Clause (Occ F) := by
  classical
  exact {(x,false), (next F x,true)}

noncomputable def base {v : Nat} (F : Finset (Clause (Fin v))) : Finset (Clause (Occ F)) := by
  classical
  exact Finset.univ.image copyClause

noncomputable def links {v : Nat} (F : Finset (Clause (Fin v))) : Finset (Clause (Occ F)) := by
  classical
  exact Finset.univ.image link

noncomputable def split {v : Nat} (F : Finset (Clause (Fin v))) : Finset (Clause (Occ F)) := by
  classical
  exact base F ∪ links F

theorem card_occ {v : Nat} (F : Finset (Clause (Fin v))) :
    Fintype.card (Occ F) = F.sum (fun C => C.card) := by
  classical
  simpa [Occ, Fintype.card_sigma] using Finset.sum_attach F (fun C => C.card)

theorem width {v w : Nat} (F : Finset (Clause (Fin v)))
    (h : ∀ C ∈ F, C.Nonempty ∧ C.card ≤ w) :
    ∀ C ∈ split F, C.Nonempty ∧ C.card ≤ max 2 w := by
  classical
  intro C hC
  rcases Finset.mem_union.mp hC with hC | hC
  · obtain ⟨old, _, rfl⟩ := Finset.mem_image.mp hC
    have cw : (copyClause old).card = old.val.card := by
      rw [copyClause, Finset.card_image_of_injective _ (lift_inj old)]
      simp
    refine ⟨Finset.card_pos.mp ?_, ?_⟩ <;> rw [cw]
    · exact Finset.card_pos.mpr (h old.val old.property).1
    · exact (h old.val old.property).2.trans (le_max_right _ _)
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨Finset.insert_nonempty _ _, Finset.card_le_two.trans (le_max_left _ _)⟩

theorem map_copy {v : Nat} {F : Finset (Clause (Fin v))} (C : ↑F) :
    Set.InjOn (Replay210.litMap label) (↑(copyClause C) : Set (Literal (Occ F))) ∧
    (copyClause C).image (Replay210.litMap label) = C.val := by
  classical
  constructor
  · intro a ha b hb eq
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hb
    exact congrArg (lift C) (Subtype.ext eq)
  · ext l
    constructor
    · intro hl
      obtain ⟨lifted, hlifted, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hlifted
      exact m.property
    · intro hl
      exact Finset.mem_image.mpr ⟨lift C ⟨l,hl⟩, Finset.mem_image.mpr ⟨⟨l,hl⟩,Finset.mem_univ _,rfl⟩, rfl⟩

theorem replay {v : Nat} (F : Finset (Clause (Fin v))) {D : Nat} :
    PCRefutable (cnfSystem (↑(split F) : Set (Clause (Occ F)))) D →
      PCRefutable (cnfSystem (↑F : Set (Clause (Fin v)))) D := by
  classical
  apply Replay210.refutable label
  intro C hC
  rcases Finset.mem_union.mp hC with hb | hl
  · obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨h, eq⟩ := map_copy B
    exact ⟨h, Or.inl (eq.symm ▸ B.property)⟩
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hl
    have h := Replay210.link_image label x (next F x) false (Cycles210.keeps label x).symm
    refine ⟨?_, Or.inr ⟨label x, ?_⟩⟩
    · simpa only [link, Bool.not_false] using h.1
    · simpa only [link, Bool.not_false] using h.2

theorem unsat {v : Nat} (F : Finset (Clause (Fin v)))
    (hF : ¬Satisfiable (↑F : Set (Clause (Fin v)))) :
    ¬Satisfiable (↑(split F) : Set (Clause (Occ F))) := by
  classical
  rintro ⟨a, hs⟩
  have hnext (x : Occ F) (hx : a x = true) : a (next F x) = true := by
    have hlink : link x ∈ (↑(split F) : Set (Clause (Occ F))) :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩))
    obtain ⟨l, hl, hv⟩ := hs (link x) hlink
    change l ∈ ({(x,false),(next F x,true)} : Clause (Occ F)) at hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp [hx] at hv
    · exact hv
  let project (i : Fin v) : Bool := if h : ∃ x : Occ F, label x = i then a h.choose else false
  have project_at (x : Occ F) : project (label x) = a x := by
    have h : ∃ y : Occ F, label y = label x := ⟨x,rfl⟩
    unfold project
    rw [dite_eq_left h]
    exact Cycles210.equal label a hnext h.choose_spec
  apply hF
  refine ⟨project, ?_⟩
  intro C hC
  let old : ↑F := ⟨C,hC⟩
  have mem : copyClause old ∈ (↑(split F) : Set (Clause (Occ F))) :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨old,Finset.mem_univ _,rfl⟩))
  obtain ⟨l, hl, val⟩ := hs (copyClause old) mem
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hl
  refine ⟨m.val,m.property,?_⟩
  exact (project_at ⟨old,m⟩).trans val

end Split210

namespace Split210

open PEqualNP.ProofComplexity

abbrev has {v : Nat} {F : Finset (Clause (Fin v))} (x : Occ F) (b : Bool)
    (C : Clause (Occ F)) : Prop := (x,b) ∈ C

theorem counts {v : Nat} (F : Finset (Clause (Fin v))) : (by
    classical
    exact ∀ x : Occ F,
      ((split F).filter (has x true)).card + ((split F).filter (has x false)).card ≤ 3) := by
  classical
  intro x
  have base_at (b : Bool) {C : Clause (Occ F)} (h : C ∈ (base F).filter (has x b)) :
      C = copyClause x.1 ∧ sign x = b := by
    obtain ⟨hC, hx⟩ := Finset.mem_filter.mp h
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp (show (x,b) ∈ copyClause C from hx)
    have hx' : (⟨C,l⟩ : Occ F) = x :=
      congrArg (fun p : Literal (Occ F) => p.1) he
    rw [← hx']
    exact ⟨rfl, congrArg (fun p : Literal (Occ F) => p.2) he⟩
  have base_card (b : Bool) : ((base F).filter (has x b)).card ≤ 1 := by
    calc
      _ ≤ ({copyClause x.1} : Finset (Clause (Occ F))).card :=
        Finset.card_le_card fun _ h => Finset.mem_singleton.mpr (base_at b h).1
      _ = 1 := Finset.card_singleton _
  have base_zero (b : Bool) (hb : sign x ≠ b) : ((base F).filter (has x b)).card = 0 := by
    exact Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr
      fun _ h => hb (base_at b h).2)
  have base_sum :
      ((base F).filter (has x true)).card + ((base F).filter (has x false)).card ≤ 1 := by
    cases hx : sign x
    · rw [base_zero true (by simp [hx]), zero_add]
      exact base_card false
    · rw [base_zero false (by simp [hx]), add_zero]
      exact base_card true
  have link_card (b : Bool) : ((links F).filter (has x b)).card ≤ 1 := by
    let source := if b then (next F).symm x else x
    calc
      _ ≤ ({link source} : Finset (Clause (Occ F))).card := by
        apply Finset.card_le_card
        intro C h
        obtain ⟨hC, hx⟩ := Finset.mem_filter.mp h
        obtain ⟨o, _, rfl⟩ := Finset.mem_image.mp hC
        change (x,b) ∈ ({(o,false), (next F o,true)} : Clause (Occ F)) at hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        apply Finset.mem_singleton.mpr
        rcases hx with hl | hl
        · have hv := congrArg (fun p : Literal (Occ F) => p.1) hl
          have hb := congrArg (fun p : Literal (Occ F) => p.2) hl
          change x = o at hv
          change b = false at hb
          simp [source, hb, hv]
        · have hv := congrArg (fun p : Literal (Occ F) => p.1) hl
          have hb := congrArg (fun p : Literal (Occ F) => p.2) hl
          change x = next F o at hv
          change b = true at hb
          simp [source, hb, hv]
      _ = 1 := Finset.card_singleton _
  have split_le (b : Bool) : ((split F).filter (has x b)).card ≤
      ((base F).filter (has x b)).card + ((links F).filter (has x b)).card := by
    rw [split, Finset.filter_union]
    exact Finset.card_union_le _ _
  have ht := split_le true
  have hf := split_le false
  have hlt := link_card true
  have hlf := link_card false
  omega

end Split210

namespace Core

open PEqualNP.ProofComplexity
open MvPolynomial

variable {V W : Type}

theorem choose_core [DecidableEq V] (F : Finset (Clause V)) (hU : ¬ Satisfiable (↑F : Set (Clause V))) :
    ∃ K ⊆ F, ¬ Satisfiable (↑K : Set (Clause V)) ∧
      ∀ C ∈ K, Satisfiable (↑(K.erase C) : Set (Clause V)) := by
  classical
  revert hU
  refine Finset.strongInductionOn F ?_
  intro J ih hUJ
  by_cases hm : ∃ C ∈ J, ¬ Satisfiable (↑(J.erase C) : Set (Clause V))
  · obtain ⟨C, hC, hcU⟩ := hm
    obtain ⟨K, hK, hu, hmin⟩ := ih (J.erase C) (Finset.erase_ssubset hC) hcU
    exact ⟨K, hK.trans (Finset.erase_subset _ _), hu, hmin⟩
  · refine ⟨J, Finset.Subset.rfl, hUJ, ?_⟩
    intro C hC
    by_contra h
    exact hm ⟨C,hC,h⟩

theorem opposite_used [DecidableEq V] (K : Finset (Clause V)) (hU : ¬ Satisfiable (↑K : Set (Clause V)))
    (hmin : ∀ C ∈ K, Satisfiable (↑(K.erase C) : Set (Clause V))) (x : V) (b : Bool)
    (hb : ∃ C ∈ K, (x,b) ∈ C) : ∃ C ∈ K, (x,!b) ∈ C := by
  classical
  by_contra hn
  obtain ⟨C, hC, hl⟩ := hb
  obtain ⟨a, ha⟩ := hmin C hC
  refine hU ⟨Function.update a x b, ?_⟩
  intro D hD
  change D ∈ K at hD
  by_cases hd : (x,b) ∈ D
  · exact ⟨(x,b), hd, Function.update_self _ _ _⟩
  · have hnot : (x,!b) ∉ D := fun h => hn ⟨D,hD,h⟩
    have dne : D ≠ C := fun h => hd (h ▸ hl)
    obtain ⟨⟨y,s⟩, hys, hy⟩ := ha D (Finset.mem_erase.mpr ⟨dne,hD⟩)
    have hne : y ≠ x := by
      intro he
      subst y
      cases b <;> cases s <;> simp_all
    exact ⟨(y,s), hys, by simpa only [Function.update_of_ne hne] using hy⟩

def literalEmbed (e : W ↪ V) : Literal W ↪ Literal V := e.prodMap (Function.Embedding.refl Bool)

private theorem clause_sat_map (e : W ↪ V) (a : V → Bool) (C : Clause W) :
    ClauseSat a (C.map (literalEmbed e)) ↔ ClauseSat (fun j => a (e j)) C := by
  constructor
  · rintro ⟨l, hl, ha⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hl
    exact ⟨q, hq, ha⟩
  · rintro ⟨l, hl, ha⟩
    exact ⟨literalEmbed e l, Finset.mem_map.mpr ⟨l, hl, rfl⟩, ha⟩

def pullClause [Fintype W] [DecidableEq V] (e : W ↪ V) (C : Clause V) : Clause W :=
  Finset.univ.filter (fun l => literalEmbed e l ∈ C)

private theorem mem_pullClause [Fintype W] [DecidableEq V] (e : W ↪ V) (C : Clause V) (l : Literal W) :
    l ∈ pullClause e C ↔ literalEmbed e l ∈ C := by simp [pullClause]

private theorem map_pullClause [Fintype W] [DecidableEq V] (e : W ↪ V) (C : Clause V)
    (hC : ∀ l ∈ C, ∃ q : Literal W, literalEmbed e q = l) :
    (pullClause e C).map (literalEmbed e) = C := by
  ext l
  constructor
  · intro hl
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hl
    exact (mem_pullClause e C q).mp hq
  · intro hl
    obtain ⟨q, rfl⟩ := hC l hl
    exact Finset.mem_map.mpr ⟨q, (mem_pullClause e C q).mpr hl, rfl⟩

private theorem rename_clausePoly (e : W ↪ V) (C : Clause W) :
    rename e (clausePoly C) = clausePoly (C.map (literalEmbed e)) := by
  simp only [clausePoly, map_prod, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro l _
  cases h : l.2 <;> simp [h, literalEmbed]

private theorem rename_derivation (e : W ↪ V)
    (F : Set (MvPolynomial W (ZMod 2))) (G : Set (MvPolynomial V (ZMod 2))) (D : ℕ)
    (hax : ∀ p ∈ F, rename e p ∈ G) (p : MvPolynomial W (ZMod 2))
    (hp : PCDerivable F D p) : PCDerivable G D (rename e p) := by
  induction hp with
  | ax hm hd => exact .ax (hax _ hm) ((totalDegree_rename_le _ _).trans hd)
  | zero => simpa only [map_zero] using (PCDerivable.zero (F := G) (B := D))
  | add _ _ ih₁ ih₂ => simpa only [map_add] using PCDerivable.add ih₁ ih₂
  | mulX j _ hd ih =>
    rw [map_mul, rename_X]
    apply PCDerivable.mulX (e j) ih
    simpa only [map_mul, rename_X] using (totalDegree_rename_le e _).trans hd

theorem rename_refutation (e : W ↪ V) (F : Finset (Clause V)) (H : Finset (Clause W))
    (hmap : ∀ C ∈ H, C.map (literalEmbed e) ∈ F) (D : ℕ)
    (hp : PCRefutable (cnfSystem (↑H : Set (Clause W))) D) :
    PCRefutable (cnfSystem (↑F : Set (Clause V))) D := by
  have hax : ∀ p ∈ cnfSystem (↑H : Set (Clause W)),
      rename e p ∈ cnfSystem (↑F : Set (Clause V)) := by
    intro p hp
    rcases hp with ⟨x,rfl⟩ | ⟨C,hC,rfl⟩
    · exact Or.inl ⟨e x, by simp⟩
    · exact Or.inr ⟨C.map (literalEmbed e), hmap C hC, rename_clausePoly e C⟩
  have hh := rename_derivation e _ _ D hax 1 hp
  simpa only [map_one, PCRefutable] using hh

theorem reduce (V : Type) [Fintype V] [DecidableEq V] (w : ℕ) (F : Finset (Clause V))
    (hwidth : ∀ C ∈ F, C.Nonempty ∧ C.card ≤ w)
    (hocc : ∀ x : V, (F.filter (fun C => (x,true) ∈ C)).card +
      (F.filter (fun C => (x,false) ∈ C)).card ≤ 3)
    (hU : ¬ Satisfiable (↑F : Set (Clause V))) :
    ∃ m ≤ Fintype.card V, ∃ H : Finset (Clause (Fin m)),
      (∀ C ∈ H, C.Nonempty ∧ C.card ≤ w) ∧
      (∀ x : Fin m,
        let pos := (H.filter (fun A => (x,true) ∈ A)).card
        let neg := (H.filter (fun A => (x,false) ∈ A)).card
        1 ≤ pos ∧ 1 ≤ neg ∧ pos + neg ≤ 3) ∧
      ¬ Satisfiable (↑H : Set (Clause (Fin m))) ∧
      (∀ C ∈ H, Satisfiable (↑(H.erase C) : Set (Clause (Fin m)))) ∧
      ∀ D : ℕ, PCRefutable (cnfSystem (↑H : Set (Clause (Fin m)))) D →
        PCRefutable (cnfSystem (↑F : Set (Clause V))) D := by
  classical
  obtain ⟨K,hKF,hKU,hKm⟩ := choose_core F hU
  let S : Finset V := K.biUnion (fun C => C.image Prod.fst)
  let m := S.card
  let e : Fin m ≃ ↥S := S.equivFin.symm
  let emb : Fin m ↪ V := e.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  let H : Finset (Clause (Fin m)) := K.image (pullClause emb)
  have hpre (C : Clause V) (hC : C ∈ K) : (pullClause emb C).map (literalEmbed emb) = C := by
    apply map_pullClause
    intro l hl
    have hv : l.1 ∈ S := Finset.mem_biUnion.mpr ⟨C,hC,Finset.mem_image.mpr ⟨l,hl,rfl⟩⟩
    refine ⟨(e.symm ⟨l.1,hv⟩,l.2), ?_⟩
    exact Prod.ext (congrArg Subtype.val (e.apply_symm_apply _)) rfl
  refine ⟨m, by simpa [m] using Finset.card_le_card (Finset.subset_univ S), H, ?_, ?_, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨_, hbound⟩ := hwidth A (hKF hA)
    have eqcard : (pullClause emb A).card = A.card :=
      (Finset.card_map _).symm.trans (congrArg Finset.card (hpre A hA))
    refine ⟨Finset.card_pos.mp ?_, eqcard.trans_le hbound⟩
    rw [eqcard]
    exact Finset.card_pos.mpr (hwidth A (hKF hA)).1
  · intro j
    have hj : emb j ∈ S := (e j).property
    obtain ⟨A,hA,hmem⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨l,hl,he⟩ := Finset.mem_image.mp hmem
    have hl0 : (emb j,l.2) ∈ A := by rw [← he]; simpa using hl
    have all_signs (b : Bool) : ∃ C ∈ K, (emb j,b) ∈ C := by
      by_cases h : b = l.2
      · exact ⟨A,hA,by rwa [h]⟩
      · have heq : b = !l.2 := Bool.eq_not_iff.mpr h
        rw [heq]
        exact opposite_used K hKU hKm (emb j) l.2 ⟨A,hA,hl0⟩
    have hfilter (b : Bool) : H.filter (fun C => (j,b) ∈ C) =
        (K.filter (fun C => (emb j,b) ∈ C)).image (pullClause emb) := by
      ext C
      simp only [H, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨A,hA,rfl⟩,hc⟩
        exact ⟨A, ⟨hA, (mem_pullClause emb A (j,b)).mp hc⟩, rfl⟩
      · rintro ⟨A,⟨hA,ha⟩,rfl⟩
        exact ⟨⟨A,hA,rfl⟩, (mem_pullClause emb A (j,b)).mpr ha⟩
    have lower (b : Bool) : 1 ≤ (H.filter (fun C => (j,b) ∈ C)).card := by
      obtain ⟨A,hA,ha⟩ := all_signs b
      apply Finset.card_pos.mpr
      rw [hfilter]
      exact ⟨pullClause emb A, Finset.mem_image.mpr ⟨A,Finset.mem_filter.mpr ⟨hA,ha⟩,rfl⟩⟩
    have upper (b : Bool) : (H.filter (fun C => (j,b) ∈ C)).card ≤
        (F.filter (fun C => (emb j,b) ∈ C)).card := by
      rw [hfilter]
      apply Finset.card_image_le.trans
      apply Finset.card_le_card
      intro A hA
      obtain ⟨hAK, ha⟩ := Finset.mem_filter.mp hA
      exact Finset.mem_filter.mpr ⟨hKF hAK,ha⟩
    exact ⟨lower true, lower false, (Nat.add_le_add (upper true) (upper false)).trans (hocc _)⟩
  · rintro ⟨a,ha⟩
    let extend := fun x : V => if hx : x ∈ S then a (e.symm ⟨x,hx⟩) else false
    have agree (j : Fin m) : extend (emb j) = a j := by
      unfold extend
      rw [dite_eq_left (c := emb j ∈ S) (e j).property]
      change a (e.symm (e j)) = a j
      rw [e.symm_apply_apply]
    refine hKU ⟨extend, ?_⟩
    intro C hC
    change C ∈ K at hC
    have hp := ha (pullClause emb C) (Finset.mem_image.mpr ⟨C,hC,rfl⟩)
    rw [← hpre C hC, clause_sat_map]
    simpa only [agree] using hp
  · intro C hC
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨a,ha⟩ := hKm A hA
    refine ⟨fun j => a (emb j), ?_⟩
    intro C hC
    obtain ⟨hneq,hCH⟩ := Finset.mem_erase.mp hC
    obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hCH
    apply (clause_sat_map emb a _).mp
    rw [hpre B hB]
    exact ha B (Finset.mem_erase.mpr ⟨fun h => hneq (congrArg (pullClause emb) h),hB⟩)
  · intro D hp
    apply rename_refutation emb F H ?_ D hp
    intro C hC
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hC
    rw [hpre A hA]
    exact hKF hA

end Core

namespace Pad

open PEqualNP.ProofComplexity

def Good (bound : Nat) {m : Nat} (H : Finset (Clause (Fin m))) : Prop :=
  (∀ C ∈ H, C.Nonempty ∧ C.card ≤ bound) ∧
  (∀ x : Fin m,
    let pos := (H.filter (fun C => (x, true) ∈ C)).card
    let neg := (H.filter (fun C => (x, false) ∈ C)).card
    1 ≤ pos ∧ 1 ≤ neg ∧ pos + neg ≤ 3) ∧
  ¬ Satisfiable (↑H : Set (Clause (Fin m))) ∧
  ∀ C ∈ H, Satisfiable (↑(H.erase C) : Set (Clause (Fin m)))

private def litLift (m : Nat) : Literal (Fin m) ↪ Literal (Fin (m+1)) where
  toFun l := (l.1.castSucc, l.2)
  inj' _ _ e := Prod.ext (Fin.ext (congrArg (fun l => l.1.val) e))
    (congrArg (fun l : Literal (Fin (m+1)) => l.2) e)

private def clLift (m : Nat) : Clause (Fin m) ↪ Clause (Fin (m+1)) where
  toFun C := C.map (litLift m)
  inj' _ _ e := Finset.map_injective (litLift m) e

private def fresh (m : Nat) (b : Bool) : Literal (Fin (m+1)) := (Fin.last m,b)

private theorem old_ne (m : Nat) (l : Literal (Fin m)) (b : Bool) : litLift m l ≠ fresh m b := by
  intro h
  have e : l.1.val = m := congrArg (fun a => a.1.val) h
  have := l.1.isLt
  omega

@[simp] private theorem fresh_not_lift (m : Nat) (C : Clause (Fin m)) (b : Bool) :
    fresh m b ∉ clLift m C := by
  intro h
  obtain ⟨l, _, he⟩ := Finset.mem_map.mp h
  exact old_ne m l b he

@[simp] private theorem old_mem_lift (m : Nat) (C : Clause (Fin m)) (l : Literal (Fin m)) :
    litLift m l ∈ clLift m C ↔ l ∈ C := by
  change litLift m l ∈ C.map (litLift m) ↔ l ∈ C
  simp

private def rest (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m)) :=
  (H.erase C).map (clLift m)

private def first (m : Nat) (C : Clause (Fin m)) (l : Literal (Fin m)) : Clause (Fin (m+1)) :=
  insert (fresh m l.2) (clLift m (C.erase l))

private def second (m : Nat) (l : Literal (Fin m)) : Clause (Fin (m+1)) :=
  {fresh m (!l.2), litLift m l}

private def padded (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (l : Literal (Fin m)) := insert (first m C l) (insert (second m l) (rest m H C))

@[simp] private theorem old_mem_first (m : Nat) (C : Clause (Fin m)) (l p : Literal (Fin m)) :
    litLift m p ∈ first m C l ↔ p ∈ C.erase l := by
  simp [first, old_ne]

@[simp] private theorem old_mem_second (m : Nat) (l p : Literal (Fin m)) :
    litLift m p ∈ second m l ↔ p = l := by
  simp [second, old_ne]

@[simp] private theorem fresh_mem_first (m : Nat) (C : Clause (Fin m)) (l : Literal (Fin m)) (b : Bool) :
    fresh m b ∈ first m C l ↔ b = l.2 := by
  simp only [first, Finset.mem_insert, fresh_not_lift, or_false]
  simp [fresh]

@[simp] private theorem fresh_mem_second (m : Nat) (l : Literal (Fin m)) (b : Bool) :
    fresh m b ∈ second m l ↔ b = !l.2 := by
  have hn := (old_ne m l b).symm
  simp only [second, Finset.mem_insert, Finset.mem_singleton, hn, or_false]
  simp [fresh]

private theorem sign_ne_neg : ∀ b : Bool, b ≠ !b := by decide

private theorem first_ne_second (m : Nat) (C : Clause (Fin m)) (l : Literal (Fin m)) :
    first m C l ≠ second m l := by
  intro e
  have hm : fresh m l.2 ∈ first m C l := (fresh_mem_first ..).mpr rfl
  rw [e, fresh_mem_second] at hm
  exact sign_ne_neg _ hm

private theorem first_not_rest (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (l : Literal (Fin m)) : first m C l ∉ rest m H C := by
  intro hm
  obtain ⟨A, _, he⟩ := Finset.mem_map.mp hm
  exact fresh_not_lift m A l.2 (he.symm ▸ (fresh_mem_first m C l l.2).mpr rfl)

private theorem second_not_rest (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (l : Literal (Fin m)) : second m l ∉ rest m H C := by
  intro hm
  obtain ⟨A, _, he⟩ := Finset.mem_map.mp hm
  exact fresh_not_lift m A (!l.2) (he.symm ▸ (fresh_mem_second m l (!l.2)).mpr rfl)

private def restrict (m : Nat) (a : Fin (m+1) → Bool) : Fin m → Bool := fun x => a x.castSucc

private def extend (m : Nat) (a : Fin m → Bool) (b : Bool) : Fin (m+1) → Bool := Fin.lastCases b a

@[simp] private theorem restrict_extend (m : Nat) (a : Fin m → Bool) (b : Bool) :
    restrict m (extend m a b) = a := by
  funext x
  simp [restrict, extend]

@[simp] private theorem extend_last (m : Nat) (a : Fin m → Bool) (b : Bool) :
    extend m a b (Fin.last m) = b := by simp [extend]

private theorem sat_lift (m : Nat) (a : Fin (m+1) → Bool) (C : Clause (Fin m)) :
    ClauseSat a (clLift m C) ↔ ClauseSat (restrict m a) C := by
  constructor
  · rintro ⟨l, hl, he⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hl
    exact ⟨p,hp,he⟩
  · rintro ⟨l, hl, he⟩
    exact ⟨litLift m l, Finset.mem_map.mpr ⟨l,hl,rfl⟩, he⟩

private theorem sat_first (m : Nat) (a : Fin (m+1) → Bool) (C : Clause (Fin m)) (l : Literal (Fin m)) :
    ClauseSat a (first m C l) ↔ a (Fin.last m) = l.2 ∨ ClauseSat (restrict m a) (C.erase l) := by
  constructor
  · rintro ⟨p, hp, he⟩
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h] at he
      exact Or.inl he
    · exact Or.inr ((sat_lift m a _).mp ⟨p,h,he⟩)
  · rintro (h | h)
    · exact ⟨fresh m l.2, Finset.mem_insert_self _ _, h⟩
    · obtain ⟨p,hp,he⟩ := (sat_lift m a _).mpr h
      exact ⟨p,Finset.mem_insert_of_mem hp,he⟩

private theorem sat_second (m : Nat) (a : Fin (m+1) → Bool) (l : Literal (Fin m)) :
    ClauseSat a (second m l) ↔ a (Fin.last m) = !l.2 ∨ restrict m a l.1 = l.2 := by
  constructor
  · rintro ⟨p, hp, he⟩
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h] at he
      exact Or.inl he
    · rw [Finset.mem_singleton.mp h] at he
      exact Or.inr he
  · rintro (h | h)
    · exact ⟨fresh m (!l.2), Finset.mem_insert_self _ _, h⟩
    · exact ⟨litLift m l, by simp [second], h⟩

private theorem sat_merge {m : Nat} (a : Fin (m+1) → Bool) (C : Clause (Fin m))
    (l : Literal (Fin m)) (hl : l ∈ C) (h1 : ClauseSat a (first m C l))
    (h2 : ClauseSat a (second m l)) : ClauseSat (restrict m a) C := by
  rcases (sat_first m a C l).mp h1 with e | ⟨p,hp,hq⟩
  · rcases (sat_second m a l).mp h2 with f | f
    · have hbad : l.2 = !l.2 := e.symm.trans f
      exact (sign_ne_neg _ hbad).elim
    · exact ⟨l,hl,f⟩
  · exact ⟨p, (Finset.mem_erase.mp hp).2, hq⟩

private theorem sat_split {m : Nat} (a : Fin m → Bool) (C : Clause (Fin m))
    (l : Literal (Fin m)) (hs : ClauseSat a C) :
    ClauseSat (extend m a (a l.1)) (first m C l) ∧
      ClauseSat (extend m a (a l.1)) (second m l) := by
  constructor
  · apply (sat_first m _ C l).mpr
    obtain ⟨p,hp,he⟩ := hs
    by_cases e : p = l
    · subst p
      exact Or.inl (by simpa using he)
    · exact Or.inr (by rw [restrict_extend]; exact ⟨p,Finset.mem_erase.mpr ⟨e,hp⟩,he⟩)
  · apply (sat_second m _ l).mpr
    rw [extend_last, restrict_extend]
    cases l.2 <;> cases a l.1 <;> simp

private theorem mem_padded (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (l : Literal (Fin m)) (B : Clause (Fin (m+1))) :
    B ∈ padded m H C l ↔ B = first m C l ∨ B = second m l ∨
      ∃ A ∈ H.erase C, clLift m A = B := by
  simp only [padded, rest, Finset.mem_insert, Finset.mem_map]

private theorem padded_unsat {m : Nat} (H : Finset (Clause (Fin m)))
    (C : Clause (Fin m)) (l : Literal (Fin m)) (hl : l ∈ C)
    (hus : ¬ Satisfiable (↑H : Set (Clause (Fin m)))) :
    ¬ Satisfiable (↑(padded m H C l) : Set (Clause (Fin (m+1)))) := by
  intro ⟨a,ha⟩
  apply hus
  refine ⟨restrict m a, ?_⟩
  intro B hB
  by_cases e : B = C
  · subst B
    apply sat_merge a C l hl
    · exact ha _ ((mem_padded ..).mpr (Or.inl rfl))
    · exact ha _ ((mem_padded ..).mpr (Or.inr (Or.inl rfl)))
  · exact (sat_lift m a B).mp (ha _ ((mem_padded ..).mpr
      (Or.inr (Or.inr ⟨B,Finset.mem_erase.mpr ⟨e,hB⟩,rfl⟩))))

private theorem padded_min {m : Nat} (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (hC : C ∈ H) (l : Literal (Fin m))
    (hmin : ∀ A ∈ H, Satisfiable (↑(H.erase A) : Set (Clause (Fin m)))) :
    ∀ B ∈ padded m H C l, Satisfiable (↑((padded m H C l).erase B) : Set (Clause (Fin (m+1)))) := by
  intro B hB
  rcases (mem_padded m H C l B).mp hB with h₁ | h₂ | ⟨A,hA,h₃⟩
  · subst B
    obtain ⟨a,ha⟩ := hmin C hC
    refine ⟨extend m a (!l.2), ?_⟩
    intro X hX
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hX
    rcases (mem_padded m H C l X).mp hmem with e | e | ⟨D,hD,e⟩
    · exact (hne e).elim
    · subst X
      exact (sat_second m _ l).mpr (Or.inl (extend_last ..))
    · subst X
      apply (sat_lift m _ D).mpr
      rw [restrict_extend]
      exact ha D hD
  · subst B
    obtain ⟨a,ha⟩ := hmin C hC
    refine ⟨extend m a l.2, ?_⟩
    intro X hX
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hX
    rcases (mem_padded m H C l X).mp hmem with e | e | ⟨D,hD,e⟩
    · subst X
      exact (sat_first m _ C l).mpr (Or.inl (extend_last ..))
    · exact (hne e).elim
    · subst X
      apply (sat_lift m _ D).mpr
      rw [restrict_extend]
      exact ha D hD
  · subst B
    have hAC := (Finset.mem_erase.mp hA).1
    obtain ⟨a,ha⟩ := hmin A (Finset.mem_erase.mp hA).2
    have hs := sat_split a C l (ha C (Finset.mem_erase.mpr ⟨Ne.symm hAC,hC⟩))
    refine ⟨extend m a (a l.1), ?_⟩
    intro X hX
    obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp hX
    rcases (mem_padded m H C l X).mp hmem with e | e | ⟨D,hD,e⟩
    · subst X
      exact hs.1
    · subst X
      exact hs.2
    · subst X
      have hDA : D ≠ A := fun e => hne (congrArg (clLift m) e)
      apply (sat_lift m _ D).mpr
      rw [restrict_extend]
      exact ha D (Finset.mem_erase.mpr ⟨hDA,(Finset.mem_erase.mp hD).2⟩)

private def occ {V : Type} [DecidableEq V] (H : Finset (Clause V)) (l : Literal V) : Nat :=
  (H.filter (fun B => l ∈ B)).card

private theorem occ_insert {V : Type} [DecidableEq V] (H : Finset (Clause V))
    (B : Clause V) (l : Literal V) (hB : B ∉ H) :
    occ (insert B H) l = occ H l + if l ∈ B then 1 else 0 := by
  by_cases h : l ∈ B
  · have H' : B ∉ H.filter (fun A => l ∈ A) := fun hb => hB (Finset.mem_filter.mp hb).1
    simp [occ, Finset.filter_insert, h, Finset.card_insert_of_notMem H']
  · simp [occ, Finset.filter_insert, h]

private theorem occ_rest (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (p : Literal (Fin m)) : occ (rest m H C) (litLift m p) = occ (H.erase C) p := by
  unfold occ
  have h : (rest m H C).filter (fun A => litLift m p ∈ A) =
      ((H.erase C).filter (fun A => p ∈ A)).map (clLift m) := by
    ext A
    constructor
    · intro hA
      obtain ⟨hB, hmem⟩ := Finset.mem_filter.mp hA
      obtain ⟨B,hB',rfl⟩ := Finset.mem_map.mp hB
      exact Finset.mem_map.mpr ⟨B, Finset.mem_filter.mpr ⟨hB', (old_mem_lift m B p).mp hmem⟩, rfl⟩
    · intro hA
      obtain ⟨B,hB,rfl⟩ := Finset.mem_map.mp hA
      obtain ⟨hB', hmem⟩ := Finset.mem_filter.mp hB
      exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨B,hB',rfl⟩, (old_mem_lift m B p).mpr hmem⟩
  rw [h, Finset.card_map]

private theorem occ_old (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m)) (hC : C ∈ H)
    (l : Literal (Fin m)) (hl : l ∈ C) (p : Literal (Fin m)) :
    occ (padded m H C l) (litLift m p) = occ H p := by
  have hh : occ H p = occ (H.erase C) p + if p ∈ C then 1 else 0 := by
    conv_lhs => rw [← Finset.insert_erase hC]
    exact occ_insert _ _ _ (Finset.notMem_erase _ _)
  rw [padded, occ_insert _ _ _ (by simp [first_ne_second, first_not_rest]),
    occ_insert _ _ _ (second_not_rest m H C l), occ_rest, hh]
  simp only [old_mem_first, old_mem_second, Finset.mem_erase]
  by_cases h : p = l
  · subst p
    simp [hl]
  · by_cases hc : p ∈ C <;> simp [h,hc]

private theorem occ_fresh (m : Nat) (H : Finset (Clause (Fin m))) (C : Clause (Fin m))
    (l : Literal (Fin m)) (b : Bool) : occ (padded m H C l) (fresh m b) = 1 := by
  have e : occ (rest m H C) (fresh m b) = 0 := by
    unfold occ
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro A hA
    obtain ⟨hB,hm⟩ := Finset.mem_filter.mp hA
    obtain ⟨B,_,rfl⟩ := Finset.mem_map.mp hB
    exact fresh_not_lift m B b hm
  rw [padded, occ_insert _ _ _ (by simp [first_ne_second, first_not_rest]),
    occ_insert _ _ _ (second_not_rest m H C l), e]
  simp only [fresh_mem_first, fresh_mem_second]
  cases b <;> cases l.2 <;> decide

private theorem padded_good (bound m : Nat) (h₂ : 2 ≤ bound) (H : Finset (Clause (Fin m)))
    (hH : Good bound H) (C : Clause (Fin m)) (hC : C ∈ H) (l : Literal (Fin m)) (hl : l ∈ C) :
    Good bound (padded m H C l) := by
  rcases hH with ⟨hw,hs,hu,hm⟩
  refine ⟨?_, ?_, padded_unsat H C l hl hu, padded_min H C hC l hm⟩
  · intro B hB
    rcases (mem_padded m H C l B).mp hB with rfl | rfl | ⟨A,hA,rfl⟩
    · refine ⟨⟨fresh m l.2, by simp [first]⟩, ?_⟩
      rw [first, Finset.card_insert_of_notMem (fresh_not_lift m (C.erase l) l.2)]
      change ((C.erase l).map (litLift m)).card + 1 ≤ bound
      rw [Finset.card_map, Finset.card_erase_of_mem hl]
      have hp := Finset.card_pos.mpr (hw C hC).1
      have hc := (hw C hC).2
      omega
    · refine ⟨⟨fresh m (!l.2), by simp [second]⟩, ?_⟩
      exact ((Finset.card_insert_le _ _).trans (show ({litLift m l} : Clause (Fin (m+1))).card + 1 ≤ 2 by simp)).trans h₂
    · obtain ⟨hne,hca⟩ := hw A (Finset.mem_erase.mp hA).2
      obtain ⟨p,hp⟩ := hne
      refine ⟨⟨litLift m p, (old_mem_lift m A p).mpr hp⟩, ?_⟩
      change (A.map (litLift m)).card ≤ bound
      simpa using hca
  · intro x
    refine Fin.lastCases ?_ (fun y => ?_) x
    · change 1 ≤ occ (padded m H C l) (fresh m true) ∧
        1 ≤ occ (padded m H C l) (fresh m false) ∧
          occ (padded m H C l) (fresh m true) + occ (padded m H C l) (fresh m false) ≤ 3
      rw [occ_fresh, occ_fresh]
      decide
    · change 1 ≤ occ (padded m H C l) (litLift m (y,true)) ∧
        1 ≤ occ (padded m H C l) (litLift m (y,false)) ∧
          occ (padded m H C l) (litLift m (y,true)) + occ (padded m H C l) (litLift m (y,false)) ≤ 3
      rw [occ_old m H C hC l hl, occ_old m H C hC l hl]
      exact hs y

private def project (m : Nat) (l : Literal (Fin m)) : Fin (m+1) → Fin m := Fin.lastCases l.1 id

@[simp] private theorem project_old (m : Nat) (l p : Literal (Fin m)) :
    Replay210.litMap (project m l) (litLift m p) = p := by
  change (Fin.lastCases l.1 id p.1.castSucc, p.2) = p
  simp

@[simp] private theorem project_fresh (m : Nat) (l : Literal (Fin m)) (b : Bool) :
    Replay210.litMap (project m l) (fresh m b) = (l.1,b) := by
  change (Fin.lastCases l.1 id (Fin.last m), b) = (l.1,b)
  simp

private theorem project_lift_inj (m : Nat) (l : Literal (Fin m)) (C : Clause (Fin m)) :
    Set.InjOn (Replay210.litMap (project m l)) (↑(clLift m C) : Set (Literal (Fin (m+1)))) := by
  intro a ha b hb h
  obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp hb
  simpa only [project_old] using congrArg (litLift m) h

private theorem project_lift_image (m : Nat) (l : Literal (Fin m)) (C : Clause (Fin m)) :
    (clLift m C).image (Replay210.litMap (project m l)) = C := by
  ext x
  constructor
  · intro hx
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    rw [project_old] at he
    exact he ▸ hq
  · intro hx
    exact Finset.mem_image.mpr ⟨litLift m x, Finset.mem_map.mpr ⟨x,hx,rfl⟩, project_old m l x⟩

private theorem project_first (m : Nat) (l : Literal (Fin m)) (C : Clause (Fin m)) (hl : l ∈ C) :
    Set.InjOn (Replay210.litMap (project m l)) (↑(first m C l) : Set (Literal (Fin (m+1)))) ∧
      (first m C l).image (Replay210.litMap (project m l)) = C := by
  constructor
  · intro a ha b hb h
    have ha' := Finset.mem_insert.mp ha
    have hb' := Finset.mem_insert.mp hb
    rcases ha' with rfl | ha'
    · rcases hb' with rfl | hb'
      · rfl
      · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hb'
        rw [project_fresh,project_old] at h
        exact ((Finset.mem_erase.mp hq).1 h.symm).elim
    · rcases hb' with rfl | hb'
      · obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp ha'
        rw [project_fresh,project_old] at h
        exact ((Finset.mem_erase.mp hq).1 h).elim
      · exact project_lift_inj m l (C.erase l) ha' hb' h
  · rw [first, Finset.image_insert, project_fresh, project_lift_image, Finset.insert_erase hl]

private theorem project_second (m : Nat) (l : Literal (Fin m)) :
    Set.InjOn (Replay210.litMap (project m l)) (↑(second m l) : Set (Literal (Fin (m+1)))) ∧
      ∃ x : Fin m, (second m l).image (Replay210.litMap (project m l)) = {(x,true),(x,false)} := by
  have hxy : project m l (Fin.last m) = project m l l.1.castSucc := by simp [project]
  have h := Replay210.link_image (project m l) (Fin.last m) l.1.castSucc (!l.2) hxy
  dsimp only at h
  rw [Bool.not_not] at h
  exact ⟨h.1,_,h.2⟩

theorem pad_one (bound m : Nat) (h₂ : 2 ≤ bound) (H : Finset (Clause (Fin m))) (hH : Good bound H) :
    ∃ K : Finset (Clause (Fin (m+1))), Good bound K ∧ ∃ f : Fin (m+1) → Fin m,
      ∀ A ∈ K, Set.InjOn (Replay210.litMap f) (↑A : Set (Literal (Fin (m+1)))) ∧
        (A.image (Replay210.litMap f) ∈ H ∨ ∃ x : Fin m,
          A.image (Replay210.litMap f) = {(x,true),(x,false)}) := by
  classical
  have hn : H.Nonempty := by
    by_contra h
    apply hH.2.2.1
    exact ⟨fun _ => false, fun C hC => (h ⟨C,hC⟩).elim⟩
  obtain ⟨C,hC⟩ := hn
  obtain ⟨l,hl⟩ := (hH.1 C hC).1
  refine ⟨padded m H C l, padded_good bound m h₂ H hH C hC l hl, project m l, ?_⟩
  intro A hA
  rcases (mem_padded m H C l A).mp hA with rfl | rfl | ⟨B,hB,rfl⟩
  · have hh := project_first m l C hl
    exact ⟨hh.1,Or.inl (hh.2.symm ▸ hC)⟩
  · have hh := project_second m l
    exact ⟨hh.1,Or.inr hh.2⟩
  · exact ⟨project_lift_inj m l B,Or.inl (by rw [project_lift_image]; exact (Finset.mem_erase.mp hB).2)⟩

theorem pad_to (bound m n : Nat) (h₂ : 2 ≤ bound) (hn : m ≤ n)
    (H : Finset (Clause (Fin m))) (hH : Good bound H) :
    ∃ K : Finset (Clause (Fin n)), Good bound K ∧
      ∀ D : Nat, PCRefutable (cnfSystem (↑K : Set (Clause (Fin n)))) D →
        PCRefutable (cnfSystem (↑H : Set (Clause (Fin m)))) D := by
  obtain ⟨q,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction q with
  | zero => exact ⟨H,hH,fun _ h => h⟩
  | succ q ih =>
    obtain ⟨L,hL,transfer⟩ := ih (Nat.le_add_right _ _)
    obtain ⟨K,hK,f,image⟩ := pad_one bound (m+q) h₂ L hL
    exact ⟨K,hK,fun D h => transfer D (Replay210.refutable f _ _ image h)⟩

end Pad

namespace Exact210

open PEqualNP.ProofComplexity

theorem result :
∀ (v w : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin v))),
  (∀ C ∈ F, C.Nonempty ∧ C.card ≤ w) →
  ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin v))) →
  ∀ n : ℕ, F.sum (fun A₀ => A₀.card) ≤ n →
    ∃ H : Finset (PEqualNP.ProofComplexity.Clause (Fin n)),
      (∀ C ∈ H, C.Nonempty ∧ C.card ≤ max 2 w) ∧
      (∀ x : Fin n,
        let pos := (H.filter (fun A => (x, true) ∈ A)).card
        let neg := (H.filter (fun E => (x, false) ∈ E)).card
        1 ≤ pos ∧ 1 ≤ neg ∧ pos + neg ≤ 3) ∧
      ¬ PEqualNP.ProofComplexity.Satisfiable (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧
      (∀ C ∈ H, PEqualNP.ProofComplexity.Satisfiable
        (↑(H.erase C) : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) ∧
      ∀ D : ℕ,
        PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) D →
        PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin v)))) D := by
  classical
  intro v w F small unsat n le_n
  let S := Split210.split F
  obtain ⟨m, hm, H, hw, ho, hu, hmin, core⟩ :=
    Core.reduce (Split210.Occ F) (max 2 w) S
      (Split210.width F small) (by
        intro x
        refine (le_of_eq ?_).trans (Split210.counts F x)
        apply congrArg₂ Nat.add <;> apply congrArg Finset.card <;> ext C <;>
          simp only [Finset.mem_filter, Split210.has, S]) (Split210.unsat F unsat)
  have hmn : m ≤ n := hm.trans ((Split210.card_occ F).symm ▸ le_n)
  have good : Pad.Good (max 2 w) H := ⟨hw, ho, hu, hmin⟩
  obtain ⟨K, hK, replay⟩ := Pad.pad_to (max 2 w) m n (le_max_left _ _) hmn H good
  exact ⟨K, hK.1, hK.2.1, hK.2.2.1, hK.2.2.2, fun d h => Split210.replay F (core d (replay d h))⟩

end Exact210

end PEqualNP.Outside.L_pcx_210

theorem PEqualNP.Outside.L_pcx_210 :
    ∀ (v w : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin v))),
  (∀ C ∈ F, C.Nonempty ∧ C.card ≤ w) →
  ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin v))) →
  ∀ n : ℕ, F.sum (fun A₀ => A₀.card) ≤ n →
    ∃ H : Finset (PEqualNP.ProofComplexity.Clause (Fin n)),
      (∀ C ∈ H, C.Nonempty ∧ C.card ≤ max 2 w) ∧
      (∀ x : Fin n,
        let pos := (H.filter (fun A => (x, true) ∈ A)).card
        let neg := (H.filter (fun E => (x, false) ∈ E)).card
        1 ≤ pos ∧ 1 ≤ neg ∧ pos + neg ≤ 3) ∧
      ¬ PEqualNP.ProofComplexity.Satisfiable (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n))) ∧
      (∀ C ∈ H, PEqualNP.ProofComplexity.Satisfiable
        (↑(H.erase C) : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) ∧
      ∀ D : ℕ,
        PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (↑H : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) D →
        PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin v)))) D :=
  PEqualNP.Outside.L_pcx_210.Exact210.result
