import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_324.Reference

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

end PEqualNP.Outside.L_pcx_324.Reference

namespace PEqualNP.Outside.L_pcx_324.Reference

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

end PEqualNP.Outside.L_pcx_324.Reference

namespace PEqualNP.Outside.L_pcx_324.Reference

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

end PEqualNP.Outside.L_pcx_324.Reference

namespace PEqualNP.Outside.L_pcx_324.Reference

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

end PEqualNP.Outside.L_pcx_324.Reference



namespace PEqualNP.Outside.L_pcx_324

open PEqualNP.ProofComplexity

abbrev Base (n : ℕ) := Clause (Fin n)
abbrev Raw {n : ℕ} (w : Fin n → ℕ) := (i : Fin n) × Fin (w i)
abbrev Ax {n : ℕ} (w : Fin n → ℕ) := Clause (Raw w)
abbrev Tape {n : ℕ} (w : Fin n → ℕ) := (i : Fin n) → Bool → Fin (w i) → Bool

variable {n : ℕ} {w : Fin n → ℕ}

def vars (C : Base n) := C.image Prod.fst
def pick (C : Base n) (i : Fin n) : Bool := decide ((i,false) ∈ C)
def decode (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) (x : Raw w → Bool) :=
  fun i => g i (fun j => x ⟨i,j⟩)
def Valid (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) (s : Tape w) :=
  ∀ i b, g i (s i b) = b
def sections (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) : Finset (Tape w) :=
  Finset.univ.filter (fun s => ∀ i b, g i (s i b) = b)
def block (C : Base n) (x : Raw w → Bool) : Ax w :=
  (Finset.univ.filter (fun j : Raw w => j.1 ∈ vars C)).image (fun j => (j, !(x j)))
def Falsifies (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (C : Base n) (x : Raw w → Bool) := ∀ l ∈ C, decode g x l.1 ≠ l.2
def copies (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) (C : Base n) : Finset (Ax w) :=
  (Finset.univ.filter (fun x => ∀ l ∈ C, decode g x l.1 ≠ l.2)).image (block C)
def choice (C : Base n) (s : Tape w) : Ax w := block C (fun z => s z.1 (pick C z.1) z.2)
def project (F : Finset (Base n)) (A : Finset (Ax w)) (s : Tape w) :=
  F.filter (fun C => choice C s ∈ A)
def bad {V : Type} (K : Finset (Clause V)) := ¬ Satisfiable (K : Set (Clause V))
def NonTaut (C : Base n) := ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C)

lemma pick_lit {C : Base n} (hc : NonTaut C) {i : Fin n} {b : Bool}
    (hl : (i,b) ∈ C) : pick C i = !b := by
  cases b
  · simp [pick, hl]
  · have hn : (i,false) ∉ C := fun h => hc i ⟨hl,h⟩
    simp [pick, hn]

lemma falsifies_iff (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (C : Base n) (hc : NonTaut C) (x : Raw w → Bool) :
    Falsifies g C x ↔ ∀ i ∈ vars C, decode g x i = pick C i := by
  constructor
  · intro h i hi
    obtain ⟨⟨j,b⟩, hl, he⟩ := Finset.mem_image.mp hi
    change j = i at he
    subst j
    rw [pick_lit hc hl]
    have hh := h (i,b) hl
    cases b <;> cases hd : decode g x i <;> simp_all
  · intro h l hl
    have hi : l.1 ∈ vars C := Finset.mem_image.mpr ⟨l,hl,rfl⟩
    rw [h l.1 hi, pick_lit hc hl]
    cases l.2 <;> decide

lemma block_mem (C : Base n) (x : Raw w → Bool) (j : Raw w) (b : Bool) :
    (j,b) ∈ block C x ↔ j.1 ∈ vars C ∧ b = !(x j) := by
  constructor
  · intro h
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
    have hj : k = j := congrArg Prod.fst he
    subst k
    exact ⟨(Finset.mem_filter.mp hk).2, (congrArg Prod.snd he).symm⟩
  · rintro ⟨hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩, rfl⟩

lemma block_false (C : Base n) (x y : Raw w → Bool) :
    ¬ ClauseSat y (block C x) ↔ ∀ j : Raw w, j.1 ∈ vars C → y j = x j := by
  constructor
  · intro h j hj
    have hn : y j ≠ !(x j) := fun he => h ⟨(j,!(x j)), (block_mem C x j _).mpr ⟨hj,rfl⟩, he⟩
    cases hx : x j <;> cases hy : y j <;> simp_all
  · intro h
    rintro ⟨⟨j,b⟩, hl, he⟩
    obtain ⟨hj, hb⟩ := (block_mem C x j b).mp hl
    rw [h j hj, hb] at he
    exact (by decide : ∀ b : Bool, b ≠ !b) (x j) he

lemma block_eq (C : Base n) {x y : Raw w → Bool}
    (h : ∀ j : Raw w, j.1 ∈ vars C → x j = y j) : block C x = block C y := by
  apply Finset.image_congr
  intro j hj
  change (j,!(x j)) = (j,!(y j))
  rw [h j (Finset.mem_filter.mp hj).2]

lemma block_eq_values {C D : Base n} {x y : Raw w → Bool}
    (h : block C x = block D y) : ∀ j : Raw w, j.1 ∈ vars C → y j = x j := by
  apply (block_false C x y).mp
  rw [h]
  exact (block_false D y y).mpr (fun _ _ => rfl)

lemma block_eq_vars (hw : ∀ i, 0 < w i) {C D : Base n} {x y : Raw w → Bool}
    (h : block C x = block D y) : vars C ⊆ vars D := by
  intro i hi
  let j : Raw w := ⟨i,⟨0,hw i⟩⟩
  have hm : (j,!(x j)) ∈ block C x := (block_mem C x j _).mpr ⟨hi,rfl⟩
  rw [h] at hm
  exact ((block_mem D y j _).mp hm).1

lemma clause_subset (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (hw : ∀ i, 0 < w i) {C D : Base n} {x y : Raw w → Bool}
    (hx : Falsifies g C x) (hy : Falsifies g D y) (h : block C x = block D y) : C ⊆ D := by
  intro l hl
  have hi : l.1 ∈ vars C := Finset.mem_image.mpr ⟨l,hl,rfl⟩
  have hd := block_eq_vars hw h hi
  obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp hd
  have eqbits : (fun j => y ⟨l.1,j⟩) = (fun j => x ⟨l.1,j⟩) := by
    funext j
    exact block_eq_values h ⟨l.1,j⟩ hi
  have hg : decode g y l.1 = decode g x l.1 := congrArg (g l.1) eqbits
  have h1 := hx l hl
  have h2 := hy k hk
  change k.1 = l.1 at hki
  rw [hki, hg] at h2
  have he : k.2 = l.2 := by
    cases hkb : k.2 <;> cases hlb : l.2 <;> cases hval : decode g x l.1 <;> simp_all
  have hkl : k = l := Prod.ext hki he
  simpa only [hkl] using hk

lemma copies_disjoint (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (hw : ∀ i, 0 < w i) {C D : Base n} (hcd : C ≠ D) : Disjoint (copies g C) (copies g D) := by
  classical
  rw [Finset.disjoint_left]
  intro A hA hB
  obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hA
  obtain ⟨y,hy,hf⟩ := Finset.mem_image.mp hB
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hb : block C x = block D y := he.trans hf.symm
  exact hcd (Finset.Subset.antisymm (clause_subset g hw hx' hy' hb)
    (clause_subset g hw hy' hx' hb.symm))

lemma sections_nonempty (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (hg : ∀ i b, ∃ x, g i x = b) : (sections g).Nonempty := by
  classical
  choose s hs using hg
  exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩

lemma choice_mem (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (C : Base n) (hc : NonTaut C) (s : Tape w) (hs : Valid g s) : choice C s ∈ copies g C := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨fun j => s j.1 (pick C j.1) j.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  apply (falsifies_iff g C hc _).mpr
  intro i hi
  exact hs i (pick C i)

lemma base_false_pick (C : Base n) (hc : NonTaut C) (a : Fin n → Bool)
    (h : ¬ ClauseSat a C) : ∀ i ∈ vars C, a i = pick C i := by
  intro i hi
  obtain ⟨⟨j,b⟩,hl,he⟩ := Finset.mem_image.mp hi
  change j = i at he
  subst j
  have hh : a i ≠ b := fun he => h ⟨(i,b),hl,he⟩
  rw [pick_lit hc hl]
  cases b <;> cases ha : a i <;> simp_all

def liftBase (s : Tape w) (a : Fin n → Bool) : Raw w → Bool := fun z => s z.1 (a z.1) z.2

lemma decode_lift (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (s : Tape w) (hs : Valid g s) (a : Fin n → Bool) : decode g (liftBase s a) = a := by
  funext i
  exact hs i (a i)

lemma choice_lift (C : Base n) (hc : NonTaut C) (s : Tape w) (a : Fin n → Bool)
    (h : ¬ ClauseSat a C) : choice C s = block C (liftBase s a) := by
  apply block_eq
  intro z hz
  change s z.1 (pick C z.1) z.2 = s z.1 (a z.1) z.2
  rw [base_false_pick C hc a h z.1 hz]

lemma copy_false_base (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (C : Base n) (A : Ax w) (hA : A ∈ copies g C) (x : Raw w → Bool)
    (hx : ¬ ClauseSat x A) : ¬ ClauseSat (decode g x) C := by
  classical
  obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hA
  have hf := (Finset.mem_filter.mp hy).2
  rw [← he] at hx
  have hv := (block_false C y x).mp hx
  rintro ⟨l,hl,heq⟩
  have hi : l.1 ∈ vars C := Finset.mem_image.mpr ⟨l,hl,rfl⟩
  have hg : decode g x l.1 = decode g y l.1 := by
    apply congrArg (g l.1)
    funext j
    exact hv ⟨l.1,j⟩ hi
  exact hf l hl (hg.symm.trans heq)

lemma section_through (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (hg : ∀ i b, ∃ x, g i x = b) (x : Raw w → Bool) :
    ∃ s : Tape w, Valid g s ∧ ∀ i, s i (decode g x i) = (fun j => x ⟨i,j⟩) := by
  classical
  choose r hr using hg
  let s : Tape w := fun i b => if b = decode g x i then (fun j => x ⟨i,j⟩) else r i b
  refine ⟨s, ?_, ?_⟩
  · intro i b
    by_cases h : b = decode g x i
    · simp only [s, if_pos h]
      exact h.symm
    · simpa only [s, if_neg h] using hr i b
  · intro i
    simp only [s, if_pos rfl]

lemma project_bad (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (hg : ∀ i b, ∃ x, g i x = b) (F : Finset (Base n))
    (hF : ∀ C ∈ F, NonTaut C) (A : Finset (Ax w)) (hA : A ⊆ F.biUnion (copies g)) :
    bad A ↔ ∀ s ∈ sections g, bad (project F A s) := by
  classical
  constructor
  · intro hbad s hs
    have hs' : Valid g s := (Finset.mem_filter.mp hs).2
    rintro ⟨a,ha⟩
    apply hbad
    refine ⟨liftBase s a, ?_⟩
    intro B hB
    change B ∈ A at hB
    by_contra hn
    obtain ⟨C,hC,hBC⟩ := Finset.mem_biUnion.mp (hA hB)
    have hfalse := copy_false_base g C B hBC (liftBase s a) hn
    rw [decode_lift g s hs' a] at hfalse
    have hEq : choice C s = B := by
      rw [choice_lift C (hF C hC) s a hfalse]
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hBC
      rw [← he] at hn ⊢
      exact block_eq C ((block_false C y (liftBase s a)).mp hn)
    have hp : C ∈ project F A s := Finset.mem_filter.mpr ⟨hC,hEq ▸ hB⟩
    exact hfalse (ha C hp)
  · intro hbad hsat
    obtain ⟨x,hx⟩ := hsat
    obtain ⟨s,hs,hthrough⟩ := section_through g hg x
    apply hbad s (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩)
    refine ⟨decode g x, ?_⟩
    intro C hC
    obtain ⟨hCF,hCA⟩ := Finset.mem_filter.mp hC
    by_contra hn
    have hp := base_false_pick C (hF C hCF) (decode g x) hn
    have hEq : choice C s = block C x := by
      apply block_eq
      intro z hz
      change s z.1 (pick C z.1) z.2 = x z
      rw [← hp z.1 hz, hthrough z.1]
    rw [hEq] at hCA
    exact ((block_false C x x).mpr (fun _ _ => rfl)) (hx _ hCA)

lemma lift_bad (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (K : Finset (Base n)) (hK : bad K) : bad (K.biUnion (copies g)) := by
  classical
  rintro ⟨x,hx⟩
  apply hK
  refine ⟨decode g x, ?_⟩
  intro C hC
  by_contra hn
  have hf : Falsifies g C x := by
    intro l hl he
    exact hn ⟨l,hl,he⟩
  have hb : block C x ∈ K.biUnion (copies g) := Finset.mem_biUnion.mpr
    ⟨C,hC,Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩,rfl⟩⟩
  exact ((block_false C x x).mpr (fun _ _ => rfl)) (hx _ hb)

lemma lift_cost (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (hw : ∀ i, 0 < w i) (F K : Finset (Base n)) (hK : K ⊆ F) (fee : Base n → ℕ) :
    F.sum (fun C => fee C * ((K.biUnion (copies g)) ∩ copies g C).card) =
      K.sum (fun C => fee C * (copies g C).card) := by
  classical
  have he (C : Base n) :
      (K.biUnion (copies g)) ∩ copies g C = if C ∈ K then copies g C else ∅ := by
    by_cases hc : C ∈ K
    · rw [if_pos hc, Finset.inter_eq_right]
      intro B hB
      exact Finset.mem_biUnion.mpr ⟨C,hc,hB⟩
    · rw [if_neg hc]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨hBK,hBC⟩ := Finset.mem_inter.mp hB
      obtain ⟨D,hD,hBD⟩ := Finset.mem_biUnion.mp hBK
      have hd : D ≠ C := fun h => hc (h ▸ hD)
      exact Finset.disjoint_left.mp (copies_disjoint g hw hd) hBD hBC
  simp_rw [he]
  have hi : (fun C : Base n => fee C * (if C ∈ K then copies g C else ∅).card) =
      (fun C => if C ∈ K then fee C * (copies g C).card else 0) := by
    funext C
    split_ifs <;> simp
  rw [hi, ← Finset.sum_filter]
  congr 1
  exact Finset.filter_mem_eq_inter |>.trans (Finset.inter_eq_right.mpr hK)

lemma average_exists {σ : Type*} (S : Finset σ) (hS : S.Nonempty)
    (v : σ → ℕ) (k : ℕ) (h : ∑ s ∈ S, v s = S.card * k) :
    ∃ s ∈ S, v s ≤ k := by
  classical
  by_contra! hn
  have hi := Finset.sum_le_sum (s := S) (f := fun _ => k+1) (g := v)
    (fun s hs => Nat.succ_le_iff.mpr (hn s hs))
  simp only [Finset.sum_const, nsmul_eq_mul] at hi
  rw [h] at hi
  have hp := Finset.card_pos.mpr hS
  nlinarith

lemma abstract_minima {O R σ : Type*} [DecidableEq O] [DecidableEq R]
    (F : Finset O) (T : Finset R) (S : Finset σ) (hS : S.Nonempty)
    (proj : Finset R → σ → Finset O) (lift : Finset O → Finset R)
    (outCost : Finset O → ℕ) (rawCost : Finset R → ℕ)
    (badO : Finset O → Prop) (badR : Finset R → Prop)
    (projSub : ∀ A s, proj A s ⊆ F)
    (projBad : ∀ A ⊆ T, badR A ↔ ∀ s ∈ S, badO (proj A s))
    (liftSub : ∀ K ⊆ F, lift K ⊆ T)
    (liftBad : ∀ K ⊆ F, badO K → badR (lift K))
    (liftCost : ∀ K ⊆ F, rawCost (lift K) = outCost K)
    (balance : ∀ A ⊆ T, (∑ s ∈ S, outCost (proj A s)) = S.card * rawCost A) :
    (∀ k : ℕ, (∃ A ⊆ T, badR A ∧ rawCost A ≤ k) ↔
      (∃ K ⊆ F, badO K ∧ outCost K ≤ k)) ∧
    ∀ A ⊆ T,
      ((A ⊆ T ∧ badR A ∧ ∀ Q ⊆ T, badR Q → rawCost A ≤ rawCost Q) ↔
       ∀ s ∈ S, proj A s ⊆ F ∧ badO (proj A s) ∧
         ∀ Q ⊆ F, badO Q → outCost (proj A s) ≤ outCost Q) := by
  classical
  constructor
  · intro k
    constructor
    · rintro ⟨A,hA,hbad,hcost⟩
      obtain ⟨s,hs,hsmall⟩ := average_exists S hS (fun s => outCost (proj A s))
        (rawCost A) (balance A hA)
      exact ⟨proj A s, projSub A s, (projBad A hA).mp hbad s hs, hsmall.trans hcost⟩
    · rintro ⟨K,hK,hbad,hcost⟩
      exact ⟨lift K, liftSub K hK, liftBad K hK hbad, (liftCost K hK).trans_le hcost⟩
  · intro A hA
    constructor
    · rintro ⟨_,hbad,hbest⟩ s hs
      have hbadP : ∀ s ∈ S, badO (proj A s) := (projBad A hA).mp hbad
      have lower : ∀ s ∈ S, rawCost A ≤ outCost (proj A s) := by
        intro t ht
        rw [← liftCost _ (projSub A t)]
        exact hbest _ (liftSub _ (projSub A t)) (liftBad _ (projSub A t) (hbadP t ht))
      have equal : outCost (proj A s) = rawCost A := by
        by_contra hne
        have hlt : rawCost A < outCost (proj A s) := by have := lower s hs; omega
        have hi := Finset.sum_lt_sum lower ⟨s,hs,hlt⟩
        simp only [Finset.sum_const, nsmul_eq_mul] at hi
        rw [balance A hA] at hi
        exact Nat.lt_irrefl _ hi
      refine ⟨projSub A s, hbadP s hs, ?_⟩
      intro Q hQ hbQ
      rw [equal, ← liftCost Q hQ]
      exact hbest _ (liftSub Q hQ) (liftBad Q hQ hbQ)
    · intro h
      refine ⟨hA, (projBad A hA).mpr (fun s hs => (h s hs).2.1), ?_⟩
      intro Q hQ hbQ
      have hbadQ := (projBad Q hQ).mp hbQ
      have hi := Finset.sum_le_sum (s := S) (f := fun s => outCost (proj A s))
        (g := fun s => outCost (proj Q s)) (fun s hs => (h s hs).2.2 _ (projSub Q s) (hbadQ s hs))
      rw [balance A hA, balance Q hQ] at hi
      exact Nat.le_of_mul_le_mul_left hi (Finset.card_pos.mpr hS)

set_option maxHeartbeats 3000000 in
lemma balance (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (hw : ∀ i, 0 < w i) (hg : ∀ i b, ∃ x, g i x = b)
    (F : Finset (Base n)) (hF : ∀ C ∈ F, NonTaut C) (fee : Base n → ℕ)
    (A : Finset (Ax w)) (hA : A ⊆ F.biUnion (copies g)) :
    (∑ s ∈ sections g, (project F A s).sum (fun C => fee C * (copies g C).card)) =
      (sections g).card * F.sum (fun C => fee C * (A ∩ copies g C).card) := by
  classical
  have hc := Reference.PCX323Counts n w hw g hg F hF A hA
  change ∀ C ∈ F, (copies g C).card *
    ((sections g).filter (fun s => C ∈ project F A s)).card =
    (sections g).card * (A ∩ copies g C).card at hc
  have inner (s : Tape w) :
      (project F A s).sum (fun C => fee C * (copies g C).card) =
      F.sum (fun C => if choice C s ∈ A then fee C * (copies g C).card else 0) := by
    rw [project, Finset.sum_filter]
  simp_rw [inner]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C hC
  have he : (sections g).filter (fun s => choice C s ∈ A) =
      (sections g).filter (fun s => C ∈ project F A s) := by
    ext s
    simp [project, hC]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, he]
  simp only [Nat.cast_id]
  calc _ = fee C * ((copies g C).card *
        ((sections g).filter (fun s => C ∈ project F A s)).card) := by ring
    _ = _ := by rw [hc C hC]; ring


end PEqualNP.Outside.L_pcx_324

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_pcx_324 : (∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
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
    ∀ fee : B → ℕ,
      let outer := fun (K : Finset B) => K.sum (fun C => fee C * (copies C).card)
      let raw := fun (A : Finset Axiom) => F.sum (fun C => fee C * (A ∩ copies C).card)
      let bestOuter := fun K => K ⊆ F ∧ bad K ∧ ∀ Q ⊆ F, bad Q → outer K ≤ outer Q
      let bestRaw := fun A => A ⊆ allAx ∧ bad A ∧ ∀ Q ⊆ allAx, bad Q → raw A ≤ raw Q
      (∀ k : ℕ, (∃ A ⊆ allAx, bad A ∧ raw A ≤ k) ↔ (∃ K ⊆ F, bad K ∧ outer K ≤ k)) ∧
      ∀ A ⊆ allAx, (bestRaw A ↔ ∀ s ∈ sections, bestOuter (project A s))) := by
  classical
  intro n w hw g hg B Raw Axiom Tape sections block copies F hF allAx project bad fee outer raw bestOuter bestRaw
  exact PEqualNP.Outside.L_pcx_324.abstract_minima F allAx sections
    (PEqualNP.Outside.L_pcx_324.sections_nonempty g hg)
    project (fun K => K.biUnion copies) outer raw (fun K : Finset B => bad K)
    (fun A : Finset Axiom => bad A)
    (by intro A s; exact Finset.filter_subset _ _)
    (by intro A hA; exact PEqualNP.Outside.L_pcx_324.project_bad g hg F hF A hA)
    (by intro K hK; exact Finset.biUnion_subset_biUnion_of_subset_left _ hK)
    (by intro K hK hb; exact PEqualNP.Outside.L_pcx_324.lift_bad g K hb)
    (by intro K hK; exact PEqualNP.Outside.L_pcx_324.lift_cost g hw F K hK fee)
    (by intro A hA; exact PEqualNP.Outside.L_pcx_324.balance g hw hg F hF fee A hA)
