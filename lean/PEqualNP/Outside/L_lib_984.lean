import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_984_aux
abbrev Edge (n : ℕ) := Fin n × Fin n
def ends {n} (e : Edge n) : Finset (Fin n) := {e.1,e.2}
def left {n} (c : Fin n → Bool) (e : Edge n) := if c e.1 then e.2 else e.1
def right {n} (c : Fin n → Bool) (e : Edge n) := if c e.1 then e.1 else e.2

theorem sides {n} (c : Fin n → Bool) (e : Edge n) (h : c e.1 ≠ c e.2) :
    c (left c e) = false ∧ c (right c e) = true ∧ ends e = {left c e,right c e} := by
  cases h1 : c e.1 <;> cases h2 : c e.2 <;> simp_all [left,right,ends,Finset.pair_comm]

theorem pair_cases {n} (c : Fin n → Bool) (e f : Edge n)
    (he : c e.1 ≠ c e.2) (hf : c f.1 ≠ c f.2) (meet : ¬Disjoint (ends e) (ends f)) :
    left c e=left c f ∨ right c e=right c f := by
  obtain ⟨v,hv,hw⟩ := Finset.not_disjoint_iff.mp meet
  obtain ⟨el,er,ep⟩ := sides c e he
  obtain ⟨fl,fr,fp⟩ := sides c f hf
  rw [ep] at hv
  rw [fp] at hw
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv hw
  rcases hv with h|h <;> rcases hw with g|g
  · exact Or.inl (h.symm.trans g)
  · exact False.elim (Bool.false_ne_true (el.symm.trans ((congrArg c (h.symm.trans g)).trans fr)))
  · exact False.elim (Bool.false_ne_true (fl.symm.trans ((congrArg c (g.symm.trans h)).trans er)))
  · exact Or.inr (h.symm.trans g)

theorem common {n} (c : Fin n → Bool) (F : Finset (Edge n)) (nonempty : F.Nonempty)
    (crosses : ∀ e ∈ F, c e.1 ≠ c e.2) (meets : ∀ e ∈ F, ∀ f ∈ F, ¬Disjoint (ends e) (ends f)) :
    ∃ v, ∀ e ∈ F, v ∈ ends e := by
  classical
  obtain ⟨e,he⟩ := nonempty
  by_cases all : ∀ f ∈ F, left c e=left c f
  · refine ⟨left c e,fun f hf => ?_⟩
    rw [(sides c f (crosses f hf)).2.2,all f hf]
    simp
  · push_neg at all
    obtain ⟨f,hf,neq⟩ := all
    have ef := (pair_cases c e f (crosses e he) (crosses f hf) (meets e he f hf)).resolve_left neq
    refine ⟨right c e, fun g hg => ?_⟩
    have ge := pair_cases c e g (crosses e he) (crosses g hg) (meets e he g hg)
    have gf := pair_cases c f g (crosses f hf) (crosses g hg) (meets f hf g hg)
    have eq : right c e=right c g := by
      rcases ge with le|re
      · exact ef.trans (gf.resolve_left (fun lf => neq (le.trans lf.symm)))
      · exact re
    rw [(sides c g (crosses g hg)).2.2,eq]
    simp
end PEqualNP.Outside.L_lib_984_aux
namespace PEqualNP.Outside.L_lib_984_aux
theorem constraints : (∀ (n : Nat) (E : Finset (Fin n × Fin n)),
  (∀ e ∈ E, e.1 < e.2) →
  let ends := fun e : Fin n × Fin n => ({e.1,e.2} : Finset (Fin n))
  let matching := fun Q : Finset (Fin n × Fin n) =>
    ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f)
  ∀ tests : Finset (Finset (Fin n)),
    (∀ R ∈ tests, ∀ e ∈ E, ends e ⊆ R → ∀ f ∈ E, ends f ⊆ R →
      ¬Disjoint (ends e) (ends f)) →
    ∀ (X : Finset (Fin n)) (side : Fin n → Bool),
      (∀ e ∈ E, e.1 ∉ X → e.2 ∉ X → side e.1 ≠ side e.2) →
      let color := fun (Y : Finset (Fin n)) (i : Fin n) =>
        if i ∈ X then decide (i ∈ Y) else side i
      let cross := fun Y : Finset (Fin n) =>
        E.filter (fun e => color Y e.1 ≠ color Y e.2)
      let hits := fun Q : Finset (Fin n × Fin n) =>
        ∀ R ∈ tests, ∃ e ∈ Q, ends e ⊆ R
      (∀ Y ∈ X.powerset, ∃ (ok : Bool) (must : Finset (Fin n)) (keep : Finset (Fin n × Fin n)),
        keep ⊆ cross Y ∧ ∀ Q ⊆ E, matching Q →
          ((Q ⊆ cross Y ∧ hits Q) ↔ (ok = true ∧ Q ⊆ keep ∧ must ⊆ Q.biUnion ends)))) := by
  classical
  intro n E order ends matching tests meets X side side_ok color cross hits Y hY
  let F (R : Finset (Fin n)) := (cross Y).filter (fun e => ends e ⊆ R)
  by_cases good : ∀ R ∈ tests, (F R).Nonempty
  · have star (R : ↥tests) : ∃ v, ∀ e ∈ F R.val, v ∈ ends e := by
      apply common (color Y) (F R.val) (good _ R.property)
      · intro e he
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      · intro e he f hf
        obtain ⟨ce,se⟩ := Finset.mem_filter.mp he
        obtain ⟨cf,sf⟩ := Finset.mem_filter.mp hf
        exact meets _ R.property e (Finset.mem_filter.mp ce).1 se f (Finset.mem_filter.mp cf).1 sf
    let v (R : ↥tests) := (star R).choose
    let must := Finset.univ.image v
    let keep := (cross Y).filter (fun e => ∀ R : ↥tests, v R ∈ ends e → ends e ⊆ R.val)
    refine ⟨true,must,keep,Finset.filter_subset _ _,?_⟩
    intro Q hQ hm
    constructor
    · rintro ⟨hc,hh⟩
      refine ⟨rfl,?_,?_⟩
      · intro e he
        apply Finset.mem_filter.mpr
        refine ⟨hc he,?_⟩
        intro R ve
        obtain ⟨f,hf,sub⟩ := hh _ R.property
        have vf := (star R).choose_spec f (Finset.mem_filter.mpr ⟨hc hf,sub⟩)
        by_cases eq : e=f
        · exact eq ▸ sub
        · exact False.elim (Finset.disjoint_left.mp (hm e he f hf eq) ve vf)
      · intro z hz
        obtain ⟨R,_,rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨f,hf,sub⟩ := hh _ R.property
        exact Finset.mem_biUnion.mpr ⟨f,hf,(star R).choose_spec f (Finset.mem_filter.mpr ⟨hc hf,sub⟩)⟩
    · rintro ⟨_,hk,hmust⟩
      refine ⟨fun e he => (Finset.mem_filter.mp (hk he)).1,?_⟩
      intro R hR
      let t : ↥tests := ⟨R,hR⟩
      have hv := hmust (Finset.mem_image_of_mem v (Finset.mem_univ t))
      obtain ⟨e,he,ve⟩ := Finset.mem_biUnion.mp hv
      exact ⟨e,he,(Finset.mem_filter.mp (hk he)).2 t ve⟩
  · refine ⟨false,∅,∅,Finset.empty_subset _,?_⟩
    intro Q hQ hm
    constructor
    · rintro ⟨hc,hh⟩
      apply False.elim
      apply good
      intro R hR
      obtain ⟨e,he,sub⟩ := hh R hR
      exact ⟨e,Finset.mem_filter.mpr ⟨hc he,sub⟩⟩
    · rintro ⟨bad,_,_⟩
      contradiction
end PEqualNP.Outside.L_lib_984_aux
namespace PEqualNP.Outside.L_lib_984_aux
theorem half_count {α : Type*} [DecidableEq α] (W : Finset α) (P : α → Prop) [DecidablePred P]
    (f : α → α) (inv : Function.Involutive f) (stable : ∀ x, x ∈ W ↔ f x ∈ W)
    (flip : ∀ x, P (f x) ↔ ¬P x) : (W.filter P).card * 2 = W.card := by
  classical
  have im : (W.filter P).image f = W.filter (fun a => ¬P a) := by
    ext y
    constructor
    · intro hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨inW,px⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨(stable x).mp inW, fun h => (flip x).mp h px⟩
    · intro hy
      obtain ⟨inW,py⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_image.mpr ⟨f y,Finset.mem_filter.mpr ⟨(stable y).mp inW,(flip y).mpr py⟩,inv y⟩
  have eq := congrArg Finset.card im
  rw [Finset.card_image_of_injective _ inv.injective] at eq
  have full := Finset.card_filter_add_card_filter_not (s:=W) P
  omega

def toggle {n} (v : Fin n) (Y : Finset (Fin n)) := if v ∈ Y then Y.erase v else insert v Y

theorem mem_toggle {n} (v u : Fin n) (Y : Finset (Fin n)) :
    u ∈ toggle v Y ↔ if u=v then u ∉ Y else u ∈ Y := by
  by_cases eq : u=v <;> by_cases mem : v ∈ Y <;> simp_all [toggle]
theorem toggle_inv {n} (v : Fin n) : Function.Involutive (toggle v) := by
  intro Y
  ext u
  by_cases eq : u=v <;> simp [mem_toggle,eq]

def shade {n} (X : Finset (Fin n)) (side : Fin n → Bool) (Y : Finset (Fin n)) (v : Fin n) :=
  if v ∈ X then decide (v ∈ Y) else side v
def sat {n} (X : Finset (Fin n)) (side : Fin n → Bool) (Y : Finset (Fin n)) (e : Edge n) :=
  shade X side Y e.1 ≠ shade X side Y e.2
noncomputable def choices {n} (X : Finset (Fin n)) (side : Fin n → Bool) (T : Finset (Edge n)) := by
  classical
  exact X.powerset.filter (fun Y => ∀ e ∈ T, sat X side Y e)

theorem toggle_other {n} {X : Finset (Fin n)} (side : Fin n → Bool) {v w : Fin n}
    (ne : w ≠ v) (Y : Finset (Fin n)) : shade X side (toggle v Y) w = shade X side Y w := by
  simp [shade,mem_toggle,ne]
theorem toggle_at {n} {X : Finset (Fin n)} (side : Fin n → Bool) {v : Fin n}
    (hv : v ∈ X) (Y : Finset (Fin n)) : shade X side (toggle v Y) v = !shade X side Y v := by
  by_cases h : v ∈ Y <;> simp [shade,mem_toggle,hv,h]

theorem halve {n} {X : Finset (Fin n)} (side : Fin n → Bool) (T : Finset (Edge n)) (e : Edge n)
    (distinct : e.1 ≠ e.2) (touch : e.1 ∈ X ∨ e.2 ∈ X)
    (away : ∀ g ∈ T, Disjoint (ends e) (ends g)) :
    (choices X side (insert e T)).card * 2 = (choices X side T).card := by
  classical
  let v := if e.1 ∈ X then e.1 else e.2
  have hv : v ∈ X := by by_cases h : e.1 ∈ X <;> simp_all [v]
  have ve : v ∈ ends e := by by_cases h : e.1 ∈ X <;> simp_all [v,ends]
  have vs (g) (hg : g ∈ T) : v ∉ ends g := Finset.disjoint_left.mp (away g hg) ve
  have preserves (Y : Finset (Fin n)) : Y ∈ choices X side T → toggle v Y ∈ choices X side T := by
    intro h
    obtain ⟨sub,good⟩ := Finset.mem_filter.mp h
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro u hu
      by_cases eq : u=v
      · exact eq ▸ hv
      · apply Finset.mem_powerset.mp sub; simpa [mem_toggle,eq] using hu
    · intro g hg
      have notL : g.1 ≠ v := by intro eq; exact vs g hg (eq ▸ (by simp [ends] : g.1 ∈ ends g))
      have notR : g.2 ≠ v := by intro eq; exact vs g hg (eq ▸ (by simp [ends] : g.2 ∈ ends g))
      simpa only [sat,toggle_other side notL,toggle_other side notR] using good g hg
  have flip (Y : Finset (Fin n)) : sat X side (toggle v Y) e ↔ ¬sat X side Y e := by
    by_cases h : e.1 ∈ X
    · have eq : v=e.1 := by simp [v,h]
      rw [eq]; simp only [sat,toggle_at side h,toggle_other side distinct.symm]
      cases shade X side Y e.1 <;> cases shade X side Y e.2 <;> decide
    · have eq : v=e.2 := by simp [v,h]
      rw [eq]; simp only [sat,toggle_at side (touch.resolve_left h),toggle_other side distinct]
      cases shade X side Y e.1 <;> cases shade X side Y e.2 <;> decide
  have keep : choices X side (insert e T) = (choices X side T).filter (fun Y => sat X side Y e) := by
    ext Y
    simp [choices,and_assoc,and_comm,and_left_comm]
  rw [keep]
  apply half_count _ _ _ (toggle_inv v) _ flip
  intro Y
  exact ⟨preserves Y,fun h => (toggle_inv v Y) ▸ preserves _ h⟩
end PEqualNP.Outside.L_lib_984_aux
open PEqualNP.Outside.L_lib_984_aux in
theorem PEqualNP.Outside.L_lib_984 : (∀ (n : Nat) (E : Finset (Fin n × Fin n)),
  (∀ e ∈ E, e.1 < e.2) →
  let ends := fun e : Fin n × Fin n => ({e.1,e.2} : Finset (Fin n))
  let matching := fun Q : Finset (Fin n × Fin n) =>
    ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint (ends e) (ends f)
  ∀ tests : Finset (Finset (Fin n)),
    (∀ R ∈ tests, ∀ e ∈ E, ends e ⊆ R → ∀ f ∈ E, ends f ⊆ R →
      ¬Disjoint (ends e) (ends f)) →
    ∀ (X : Finset (Fin n)) (side : Fin n → Bool),
      (∀ e ∈ E, e.1 ∉ X → e.2 ∉ X → side e.1 ≠ side e.2) →
      let color := fun (Y : Finset (Fin n)) (i : Fin n) =>
        if i ∈ X then decide (i ∈ Y) else side i
      let cross := fun Y : Finset (Fin n) =>
        E.filter (fun e => color Y e.1 ≠ color Y e.2)
      let hits := fun Q : Finset (Fin n × Fin n) =>
        ∀ R ∈ tests, ∃ e ∈ Q, ends e ⊆ R
      (∀ Y ∈ X.powerset, ∃ (ok : Bool) (must : Finset (Fin n)) (keep : Finset (Fin n × Fin n)),
        keep ⊆ cross Y ∧ ∀ Q ⊆ E, matching Q →
          ((Q ⊆ cross Y ∧ hits Q) ↔ (ok = true ∧ Q ⊆ keep ∧ must ⊆ Q.biUnion ends))) ∧
      ∀ Q ⊆ E, matching Q →
        (X.powerset.filter (fun Y => Q ⊆ cross Y)).card *
          2^(Q.filter (fun e => e.1 ∈ X ∨ e.2 ∈ X)).card = 2^X.card) := by
  classical
  intro n E order ends matching tests meets X side outside color cross hits
  refine ⟨constraints n E order tests meets X side outside,?_⟩
  intro Q hQ hm
  let D := Q.filter (fun e => e.1 ∈ X ∨ e.2 ∈ X)
  have eq : X.powerset.filter (fun Y => Q ⊆ cross Y) = choices X side D := by
    ext Y
    simp only [choices,Finset.mem_filter]
    apply and_congr_right
    intro _
    constructor
    · intro up e he
      exact (Finset.mem_filter.mp (up (Finset.mem_filter.mp he).1)).2
    · intro ok e he
      apply Finset.mem_filter.mpr
      refine ⟨hQ he,?_⟩
      by_cases touch : e.1 ∈ X ∨ e.2 ∈ X
      · exact ok e (Finset.mem_filter.mpr ⟨he,touch⟩)
      · push_neg at touch
        simpa [color,touch.1,touch.2] using outside e (hQ he) touch.1 touch.2
  rw [eq]
  change (choices X side D).card * 2^D.card = 2^X.card
  have calcCount (T : Finset (Edge n)) (sub : T ⊆ D) : (choices X side T).card * 2^T.card = 2^X.card := by
    induction T using Finset.induction_on with
    | empty => simp [choices]
    | @insert e T ne ih =>
      have he := Finset.mem_filter.mp (sub (Finset.mem_insert_self e T))
      have st : T ⊆ D := fun g hg => sub (Finset.mem_insert_of_mem hg)
      have dis (g) (hg : g ∈ T) : Disjoint (PEqualNP.Outside.L_lib_984_aux.ends e) (PEqualNP.Outside.L_lib_984_aux.ends g) :=
        hm e he.1 g (Finset.mem_filter.mp (st hg)).1 (fun eq => ne (eq ▸ hg))
      have step := halve side T e (ne_of_lt (order e (hQ he.1))) he.2 dis
      rw [Finset.card_insert_of_notMem ne,pow_succ]
      calc
        _ = ((choices X side (insert e T)).card * 2) * 2^T.card := by ac_rfl
        _ = _ := by rw [step]; exact ih st
  exact calcCount D (Finset.Subset.refl _)
