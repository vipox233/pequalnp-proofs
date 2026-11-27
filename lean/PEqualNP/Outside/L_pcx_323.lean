import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_323_aux

abbrev Tape (n : ℕ) (w : Fin n → ℕ) := (i : Fin n) → Bool → Fin (w i) → Bool

noncomputable def preimageSubtype {α β : Type*} (e : α ≃ β) (P : β → Prop) :
    {a : α // P (e a)} ≃ {b : β // P b} where
  toFun a := ⟨e a.val,a.property⟩
  invFun b := ⟨e.symm b.val, by rw [e.apply_symm_apply]; exact b.property⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.val)
  right_inv b := Subtype.ext (e.apply_symm_apply b.val)

def filterSubtype {α : Type*} (S : Finset α) (P : α → Prop) [DecidablePred P] :
    {s : ↥S // P s.val} ≃ ↥(S.filter P) where
  toFun s := ⟨s.val.val, Finset.mem_filter.mpr ⟨s.val.property, s.property⟩⟩
  invFun s := ⟨⟨s.val, (Finset.mem_filter.mp s.property).1⟩,(Finset.mem_filter.mp s.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tape_count_transfer {Tape Word T R : Type*} [Fintype T] [Fintype R]
    [DecidableEq Word]
    (S : Finset Tape) (B A : Finset Word)
    (P : Tape → Prop) [DecidablePred P]
    (f : T ≃ ↥S) (g : R ≃ ↥B) (restrict : T → R)
    (agree : ∀ t, P (f t).val ↔ (g (restrict t)).val ∈ A)
    (uniform : Fintype.card R * Fintype.card {t : T // (g (restrict t)).val ∈ A} =
      Fintype.card T * Fintype.card {r : R // (g r).val ∈ A}) :
    B.card * (S.filter P).card = S.card * (A ∩ B).card := by
  classical
  have cr : Fintype.card R = B.card := (Fintype.card_congr g).trans (Fintype.card_coe B)
  have ct : Fintype.card T = S.card := (Fintype.card_congr f).trans (Fintype.card_coe S)
  let isoT : {t : T // (g (restrict t)).val ∈ A} ≃ {t : T // P (f t).val} :=
    Equiv.subtypeEquivRight (fun t => (agree t).symm)
  have cs : Fintype.card {t : T // (g (restrict t)).val ∈ A} = (S.filter P).card :=
    (Fintype.card_congr (isoT.trans ((preimageSubtype f (fun y => P y.val)).trans
      (filterSubtype S P)))).trans (Fintype.card_coe _)
  let isoR : {r : R // (g r).val ∈ A} ≃ ↥(B.filter (fun z => z ∈ A)) :=
    (preimageSubtype g (fun z => z.val ∈ A)).trans (filterSubtype B (fun z => z ∈ A))
  have filt : B.filter (fun z => z ∈ A) = A ∩ B := by
    ext z
    simp [and_comm]
  have ca : Fintype.card {r : R // (g r).val ∈ A} = (A ∩ B).card := by
    rw [← filt]
    exact (Fintype.card_congr isoR).trans (Fintype.card_coe _)
  rw [cr,ct,cs,ca] at uniform
  exact uniform

end PEqualNP.Outside.L_pcx_323_aux

namespace PEqualNP.Outside.L_pcx_323_aux

theorem count_restriction {I : Type*} [Fintype I] [DecidableEq I]
    (α : I → Type*) [∀ i, Fintype (α i)]
    (T : Finset I) (P : (∀ i : T, α i) → Prop) [DecidablePred P] :
    Fintype.card (∀ i : T, α i) * Fintype.card {x : (∀ i, α i) // P (fun i => x i)} =
      Fintype.card (∀ i, α i) * Fintype.card {y : (∀ i : T, α i) // P y} := by
  let e : (∀ i, α i) ≃ (∀ i : T, α i) × (∀ i : {i // i ∉ T}, α i) :=
    Equiv.piEquivPiSubtypeProd (· ∈ T) α
  have hfull : Fintype.card (∀ i, α i) =
      Fintype.card (∀ i : T, α i) * Fintype.card (∀ i : {i // i ∉ T}, α i) := by
    rw [Fintype.card_congr e, Fintype.card_prod]
  let eP : {x : (∀ i, α i) // P (fun i => x i)} ≃
      {y : (∀ i : T, α i) // P y} × (∀ i : {i // i ∉ T}, α i) :=
    (Equiv.subtypeEquivOfSubtype (p := fun z => P z.1) e).trans
      Equiv.prodSubtypeFstEquivSubtypeProd
  have hevent : Fintype.card {x : (∀ i, α i) // P (fun i => x i)} =
      Fintype.card {y : (∀ i : T, α i) // P y} * Fintype.card (∀ i : {i // i ∉ T}, α i) := by
    rw [Fintype.card_congr eP, Fintype.card_prod]
  rw [hfull, hevent]
  ac_rfl

end PEqualNP.Outside.L_pcx_323_aux

namespace PEqualNP.Outside.L_pcx_323_aux

open PEqualNP.ProofComplexity

abbrev RawWire {n : ℕ} (w : Fin n → ℕ) := (i : Fin n) × Fin (w i)

def falsifyingBit {n : ℕ} (C : Clause (Fin n)) (i : Fin n) := decide ((i,false) ∈ C)

def selectedSlots {n : ℕ} (C : Clause (Fin n)) : Finset (Fin n × Bool) :=
  Finset.univ.filter (fun ib => ib.1 ∈ C.image Prod.fst ∧ ib.2 = falsifyingBit C ib.1)

abbrev Fiber {n : ℕ} (w : Fin n → ℕ)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) (ib : Fin n × Bool) :=
  {x : Fin (w ib.1) → Bool // g ib.1 x = ib.2}

abbrev Selected {n : ℕ} (w : Fin n → ℕ)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) (C : Clause (Fin n)) :=
  ∀ ib : selectedSlots C, Fiber w g ib.val

def clauseBlock {n : ℕ} (w : Fin n → ℕ) (C : Clause (Fin n))
    (x : RawWire w → Bool) : Clause (RawWire w) :=
  ((Finset.univ : Finset (RawWire w)).filter (fun j => j.1 ∈ C.image Prod.fst)).image
    (fun j => (j, !x j))

def clauseCopies {n : ℕ} (w : Fin n → ℕ) (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (C : Clause (Fin n)) : Finset (Clause (RawWire w)) :=
  ((Finset.univ : Finset (RawWire w → Bool)).filter (fun x =>
     ∀ l ∈ C, g l.1 (fun j => x ⟨l.1,j⟩) ≠ l.2)).image (clauseBlock w C)

def selectSlot {n : ℕ} {C : Clause (Fin n)} {i : Fin n} (hi : i ∈ C.image Prod.fst) :
    selectedSlots C :=
  ⟨(i, falsifyingBit C i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, rfl⟩⟩

def chooseRaw {n : ℕ} {w : Fin n → ℕ} {g : (i : Fin n) → (Fin (w i) → Bool) → Bool}
    {C : Clause (Fin n)} (s : Selected w g C) (z : RawWire w) : Bool :=
  if hz : z.1 ∈ C.image Prod.fst then (s (selectSlot hz)).val z.2 else false

theorem chooseRaw_on {n : ℕ} {w : Fin n → ℕ} {g : (i : Fin n) → (Fin (w i) → Bool) → Bool}
    {C : Clause (Fin n)} (s : Selected w g C) (t : selectedSlots C) (j : Fin (w t.val.1)) :
    chooseRaw s ⟨t.val.1,j⟩ = (s t).val j := by
  rcases t with ⟨⟨i,b⟩,ht⟩
  have h : i ∈ C.image Prod.fst ∧ b = falsifyingBit C i := (Finset.mem_filter.mp ht).2
  rcases h with ⟨hi,rfl⟩
  rw [chooseRaw, dite_eq_left hi]
  rfl

theorem falsifyingBit_literal {n : ℕ} {C : Clause (Fin n)}
    (hC : ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C)) {i : Fin n} {b : Bool}
    (h : (i,b) ∈ C) : falsifyingBit C i = !b := by
  cases b
  · simp [falsifyingBit,h]
  · have hn : (i,false) ∉ C := fun hf => hC i ⟨h,hf⟩
    simp [falsifyingBit,hn]

theorem chosenBlock_mem {n : ℕ} {w : Fin n → ℕ} {g : (i : Fin n) → (Fin (w i) → Bool) → Bool}
    {C : Clause (Fin n)} (hC : ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C))
    (s : Selected w g C) : clauseBlock w C (chooseRaw s) ∈ clauseCopies w g C := by
  apply Finset.mem_image.mpr
  refine ⟨chooseRaw s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  rintro ⟨i,b⟩ h
  have hi : i ∈ C.image Prod.fst := Finset.mem_image.mpr ⟨(i,b),h,rfl⟩
  have eq : (fun j => chooseRaw s ⟨i,j⟩) = (s (selectSlot hi)).val :=
    funext (chooseRaw_on s (selectSlot hi))
  change g i (fun j => chooseRaw s ⟨i,j⟩) ≠ b
  have hv : g i (s (selectSlot hi)).val = falsifyingBit C i := (s (selectSlot hi)).property
  rw [eq,hv,falsifyingBit_literal hC h]
  cases b <;> decide

theorem block_eq_of_agree {n : ℕ} {w : Fin n → ℕ} {C : Clause (Fin n)} {x y : RawWire w → Bool}
    (h : ∀ z : RawWire w, z.1 ∈ C.image Prod.fst → x z = y z) :
    clauseBlock w C x = clauseBlock w C y := by
  unfold clauseBlock
  exact Finset.image_congr (fun z hz => by rw [h z (Finset.mem_filter.mp hz).2])

theorem block_agree_of_eq {n : ℕ} {w : Fin n → ℕ} {C : Clause (Fin n)} {x y : RawWire w → Bool}
    (h : clauseBlock w C x = clauseBlock w C y)
    (z : RawWire w) (hz : z.1 ∈ C.image Prod.fst) : x z = y z := by
  have hmem : (z,!x z) ∈ clauseBlock w C x :=
    Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,rfl⟩
  rw [h] at hmem
  obtain ⟨v, _, equiv⟩ := Finset.mem_image.mp hmem
  have v_eq : v = z := congrArg Prod.fst equiv
  subst v
  have bits : Bool.not (y z) = Bool.not (x z) := congrArg Prod.snd equiv
  simpa using (congrArg Bool.not bits).symm

theorem chosenBlock_injective {n : ℕ} {w : Fin n → ℕ}
    {g : (i : Fin n) → (Fin (w i) → Bool) → Bool} {C : Clause (Fin n)} :
    Function.Injective (fun s : Selected w g C => clauseBlock w C (chooseRaw s)) := by
  intro s t h
  funext slot
  apply Subtype.ext
  funext j
  rw [← chooseRaw_on s slot j, ← chooseRaw_on t slot j]
  exact block_agree_of_eq h _ (Finset.mem_filter.mp slot.property).2.1

theorem raw_forces_slot {n : ℕ} {w : Fin n → ℕ} {g : (i : Fin n) → (Fin (w i) → Bool) → Bool}
    {C : Clause (Fin n)} (hC : ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C)) {x : RawWire w → Bool}
    (hx : ∀ l ∈ C, g l.1 (fun j => x ⟨l.1,j⟩) ≠ l.2)
    (t : selectedSlots C) : g t.val.1 (fun j => x ⟨t.val.1,j⟩) = t.val.2 := by
  have ht : t.val.1 ∈ C.image Prod.fst ∧ t.val.2 = falsifyingBit C t.val.1 :=
    (Finset.mem_filter.mp t.property).2
  obtain ⟨⟨i,b⟩, hc, he⟩ := Finset.mem_image.mp ht.1
  change i = t.val.1 at he
  subst i
  have hn : g t.val.1 (fun j => x ⟨t.val.1,j⟩) ≠ b := hx (t.val.1,b) hc
  rw [ht.2, falsifyingBit_literal hC hc]
  cases b <;> cases hg : g t.val.1 (fun j => x ⟨t.val.1,j⟩) <;> simp_all

noncomputable def equivCopies {n : ℕ} (w : Fin n → ℕ)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) (C : Clause (Fin n))
    (hC : ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C)) :
    Selected w g C ≃ {D // D ∈ clauseCopies w g C} := by
  refine Equiv.ofBijective (fun s => ⟨clauseBlock w C (chooseRaw s), chosenBlock_mem hC s⟩) ⟨?_,?_⟩
  · exact fun _ _ h => chosenBlock_injective (congrArg Subtype.val h)
  · rintro ⟨D,hD⟩
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hD
    have hx' := (Finset.mem_filter.mp hx).2
    let s : Selected w g C := fun t => ⟨fun j => x ⟨t.val.1,j⟩, raw_forces_slot hC hx' t⟩
    refine ⟨s,Subtype.ext (block_eq_of_agree (fun z hz => ?_))⟩
    rw [chooseRaw,dite_eq_left hz]
    rfl

end PEqualNP.Outside.L_pcx_323_aux

namespace PEqualNP.Outside.L_pcx_323_aux

open PEqualNP.ProofComplexity

noncomputable def straightSectionTapeEq {n : ℕ} {w : Fin n → ℕ}
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) :
    ((k : Fin n × Bool) → Fiber w g k) ≃
      {s : Tape n w // s ∈ (Finset.univ : Finset (Tape n w)).filter (fun s => ∀ i b, g i (s i b) = b)}
    where
  toFun f := ⟨fun i b => (f (i,b)).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i b => (f (i,b)).property⟩⟩
  invFun s k := ⟨s.val k.1 k.2, (Finset.mem_filter.mp s.property).2 k.1 k.2⟩
  left_inv f := by
    funext k
    apply Subtype.ext
    rcases k with ⟨i,b⟩
    rfl
  right_inv s := Subtype.ext rfl

theorem PCX323Counts : ∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  ∀ g : (i : Fin n) → (Fin (w i) → Bool) → Bool, (∀ i b, ∃ x, g i x = b) →
  let B := PEqualNP.ProofComplexity.Clause (Fin n)
  let Raw := (i : Fin n) × Fin (w i)
  let Axiom := PEqualNP.ProofComplexity.Clause Raw
  let Tape := (i : Fin n) → Bool → Fin (w i) → Bool
  let sections := (Finset.univ : Finset Tape).filter (fun s => ∀ i b, g i (s i b) = b)
  let block := fun (C : B) (x : Raw → Bool) =>
    ((Finset.univ : Finset Raw).filter (fun j => j.1 ∈ C.image Prod.fst)).image (fun j => (j, !(x j)))
  let copies := fun (C : B) =>
    ((Finset.univ : Finset (Raw → Bool)).filter (fun x =>
      ∀ l ∈ C, g l.1 (fun j => x ⟨l.1,j⟩) ≠ l.2)).image (block C)
  ∀ F : Finset B, (∀ C ∈ F, ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C)) →
    let allAx := F.biUnion copies
    let project := fun (A : Finset Axiom) (s : Tape) => F.filter (fun C =>
      block C (fun z => s z.1 (decide ((z.1,false) ∈ C)) z.2) ∈ A)
    let bad := fun {V : Type} (K : Finset (PEqualNP.ProofComplexity.Clause V)) =>
      ¬ PEqualNP.ProofComplexity.Satisfiable (K : Set (PEqualNP.ProofComplexity.Clause V))
    ∀ A : Finset Axiom, A ⊆ allAx →
      ∀ C ∈ F, (copies C).card * (sections.filter (fun s => C ∈ project A s)).card =
        sections.card * (A ∩ copies C).card := by
  intro n w _ g _ B Raw Axiom Tape sections block copies F hF allAx project bad A _ C hCF
  let f := straightSectionTapeEq g
  let e := equivCopies w g C (hF C hCF)
  let restrict (t : (k : Fin n × Bool) → Fiber w g k) : Selected w g C := fun k => t k.val
  let P (s : Tape) := C ∈ project A s
  have equate (t : (k : Fin n × Bool) → Fiber w g k) : P (f t).val ↔ (e (restrict t)).val ∈ A := by
    change (C ∈ F.filter (fun D => clauseBlock w D
        (fun z => (f t).val z.1 (falsifyingBit D z.1) z.2) ∈ A)) ↔
      clauseBlock w C (chooseRaw (restrict t)) ∈ A
    rw [Finset.mem_filter, and_iff_right hCF]
    have hBlock : clauseBlock w C (fun z => (f t).val z.1 (falsifyingBit C z.1) z.2) =
        clauseBlock w C (chooseRaw (restrict t)) := by
      apply block_eq_of_agree
      intro z hz
      exact (chooseRaw_on (restrict t) (selectSlot hz) z.2).symm
    rw [hBlock]
  have hu := count_restriction (Fiber w g) (selectedSlots C) (fun a => (e a).val ∈ A)
  exact tape_count_transfer sections (copies C) A P f e restrict equate hu

end PEqualNP.Outside.L_pcx_323_aux

namespace PEqualNP.Outside.L_pcx_323_aux

open PEqualNP.ProofComplexity

theorem PCX323Semantics : ∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  ∀ g : (i : Fin n) → (Fin (w i) → Bool) → Bool, (∀ i b, ∃ x, g i x = b) →
  let B := PEqualNP.ProofComplexity.Clause (Fin n)
  let Raw := (i : Fin n) × Fin (w i)
  let Axiom := PEqualNP.ProofComplexity.Clause Raw
  let Tape := (i : Fin n) → Bool → Fin (w i) → Bool
  let sections := (Finset.univ : Finset Tape).filter (fun s => ∀ i b, g i (s i b) = b)
  let block := fun (C : B) (x : Raw → Bool) =>
    ((Finset.univ : Finset Raw).filter (fun j => j.1 ∈ C.image Prod.fst)).image (fun j => (j, !(x j)))
  let copies := fun (C : B) =>
    ((Finset.univ : Finset (Raw → Bool)).filter (fun x =>
      ∀ l ∈ C, g l.1 (fun j => x ⟨l.1,j⟩) ≠ l.2)).image (block C)
  ∀ F : Finset B, (∀ C ∈ F, ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C)) →
    let allAx := F.biUnion copies
    let project := fun (A : Finset Axiom) (s : Tape) => F.filter (fun C =>
      block C (fun z => s z.1 (decide ((z.1,false) ∈ C)) z.2) ∈ A)
    let bad := fun {V : Type} (K : Finset (PEqualNP.ProofComplexity.Clause V)) =>
      ¬ PEqualNP.ProofComplexity.Satisfiable (K : Set (PEqualNP.ProofComplexity.Clause V))
    ∀ A : Finset Axiom, A ⊆ allAx →
      (bad A ↔ ∀ s ∈ sections, bad (project A s)) := by
  classical
  intro n w hwidth g hg B Raw Axiom Tape sections block copies F hF allAx project bad A hSub
  have blockUnsat (C : B) (x y : Raw → Bool) :
      ¬ ClauseSat x (block C y) ↔ ∀ z : Raw, z.1 ∈ C.image Prod.fst → x z = y z := by
    constructor
    · intro h z hz
      have hm : (z, !y z) ∈ block C y := by
        apply Finset.mem_image.mpr
        exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩
      have hn : x z ≠ !y z := fun e => h ⟨(z, !y z), hm, e⟩
      cases hx : x z <;> cases hy : y z <;> simp_all
    · rintro h ⟨l, hl, he⟩
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hl
      have hz' := (Finset.mem_filter.mp hz).2
      have eq := h z hz'
      change x z = !y z at he
      cases hx : x z <;> cases hy : y z <;> simp_all
  have sameBlock (C : B) (x y : Raw → Bool)
      (h : ∀ z : Raw, z.1 ∈ C.image Prod.fst → x z = y z) : block C x = block C y := by
    apply Finset.image_congr
    intro z hz
    exact congrArg (fun b => (z, !b)) (h z (Finset.mem_filter.mp hz).2)
  have falseBit (C : B) (b : Fin n → Bool)
      (h : ∀ l ∈ C, b l.1 ≠ l.2) (i : Fin n) (hi : i ∈ C.image Prod.fst) :
      b i = decide ((i,false) ∈ C) := by
    by_cases hn : (i,false) ∈ C
    · have he : b i ≠ false := h (i,false) hn
      cases hb : b i <;> simp_all
    · obtain ⟨⟨j,d⟩, hd, he⟩ := Finset.mem_image.mp hi
      change j=i at he
      subst j
      cases d with
      | false => exact (hn hd).elim
      | true =>
        have he : b i ≠ true := h (i,true) hd
        cases hb : b i <;> simp_all
  have sectionProperty (s : Tape) (hs : s ∈ sections) : ∀ i b, g i (s i b) = b :=
    (Finset.mem_filter.mp hs).2
  constructor
  · intro hbad s hs hsSat
    obtain ⟨a, ha⟩ := hsSat
    let raw (z : Raw) := s z.1 (a z.1) z.2
    apply hbad
    refine ⟨raw, ?_⟩
    intro D hD
    by_contra hDfalse
    have hDa : D ∈ A := hD
    obtain ⟨C,hCF,hDC⟩ := Finset.mem_biUnion.mp (hSub hDa)
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hDC
    have xFalse := (Finset.mem_filter.mp hx).2
    have agree := (blockUnsat C raw x).mp hDfalse
    have aFalse : ∀ l ∈ C, a l.1 ≠ l.2 := by
      intro l hl he
      apply xFalse l hl
      have e : (fun j => x ⟨l.1,j⟩) = s l.1 (a l.1) := by
        funext j
        exact (agree ⟨l.1,j⟩ (Finset.mem_image.mpr ⟨l,hl,rfl⟩)).symm
      rw [e, sectionProperty s hs]
      exact he
    let test (z : Raw) := s z.1 (decide ((z.1,false) ∈ C)) z.2
    have same : block C test = block C x := by
      apply sameBlock
      intro z hz
      dsimp [test]
      rw [← falseBit C a aFalse z.1 hz]
      exact agree z hz
    have hc : C ∈ project A s := Finset.mem_filter.mpr ⟨hCF, same.symm ▸ hDa⟩
    obtain ⟨l,hl,ht⟩ := ha C hc
    exact aFalse l hl ht
  · intro hbad hxSat
    obtain ⟨raw,hraw⟩ := hxSat
    let a (i : Fin n) := g i (fun j => raw ⟨i,j⟩)
    let s : Tape := fun i b =>
      if b = a i then fun j => raw ⟨i,j⟩ else Classical.choose (hg i b)
    have hs : s ∈ sections := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro i b
      dsimp [s]
      split_ifs with h
      · exact h.symm
      · exact Classical.choose_spec (hg i b)
    apply hbad s hs
    refine ⟨a, ?_⟩
    intro C hC
    by_contra hCf
    have aFalse : ∀ l ∈ C, a l.1 ≠ l.2 := fun l hl he => hCf ⟨l,hl,he⟩
    have hc : C ∈ project A s := hC
    have hBlock := (Finset.mem_filter.mp hc).2
    let test (z : Raw) := s z.1 (decide ((z.1,false) ∈ C)) z.2
    have noBlock : ¬ ClauseSat raw (block C test) := by
      apply (blockUnsat C raw test).mpr
      intro z hz
      dsimp [test]
      rw [← falseBit C a aFalse z.1 hz]
      simp only [s, ite_eq_left rfl]
      cases z
      rfl
    exact noBlock (hraw _ hBlock)

end PEqualNP.Outside.L_pcx_323_aux

theorem PEqualNP.Outside.L_pcx_323 : (∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  ∀ g : (i : Fin n) → (Fin (w i) → Bool) → Bool, (∀ i b, ∃ x, g i x = b) →
  let B := PEqualNP.ProofComplexity.Clause (Fin n)
  let Raw := (i : Fin n) × Fin (w i)
  let Axiom := PEqualNP.ProofComplexity.Clause Raw
  let Tape := (i : Fin n) → Bool → Fin (w i) → Bool
  let sections := (Finset.univ : Finset Tape).filter (fun s => ∀ i b, g i (s i b) = b)
  let block := fun (C : B) (x : Raw → Bool) =>
    ((Finset.univ : Finset Raw).filter (fun j => j.1 ∈ C.image Prod.fst)).image (fun j => (j, !(x j)))
  let copies := fun (C : B) =>
    ((Finset.univ : Finset (Raw → Bool)).filter (fun x =>
      ∀ l ∈ C, g l.1 (fun j => x ⟨l.1,j⟩) ≠ l.2)).image (block C)
  ∀ F : Finset B, (∀ C ∈ F, ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C)) →
    let allAx := F.biUnion copies
    let project := fun (A : Finset Axiom) (s : Tape) => F.filter (fun C =>
      block C (fun z => s z.1 (decide ((z.1,false) ∈ C)) z.2) ∈ A)
    let bad := fun {V : Type} (K : Finset (PEqualNP.ProofComplexity.Clause V)) =>
      ¬ PEqualNP.ProofComplexity.Satisfiable (K : Set (PEqualNP.ProofComplexity.Clause V))
    ∀ A : Finset Axiom, A ⊆ allAx →
      (bad A ↔ ∀ s ∈ sections, bad (project A s)) ∧
      ∀ C ∈ F, (copies C).card * (sections.filter (fun s => C ∈ project A s)).card =
        sections.card * (A ∩ copies C).card) := by
  intro n w hw g hg B Raw Axiom Tape sections block copies F hF allAx project bad A hA
  exact ⟨PEqualNP.Outside.L_pcx_323_aux.PCX323Semantics n w hw g hg F hF A hA,
    PEqualNP.Outside.L_pcx_323_aux.PCX323Counts n w hw g hg F hF A hA⟩
