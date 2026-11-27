import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_228

open PEqualNP.ProofComplexity PEqualNP.Search Finset

noncomputable section

variable {n : ℕ}

def fits (P : Finset (Literal (Fin n))) (a : Fin n → Bool) : Prop := ∀ l ∈ P, a l.1 = l.2

def IsCore (R : Finset (Fin n → Bool)) (P : Finset (Literal (Fin n))) : Prop :=
  (∃ a, fits P a) ∧ (¬∃ a ∈ R, fits P a) ∧ ∀ e ∈ P, ∃ a ∈ R, fits (P.erase e) a

def coresOf (R : Finset (Fin n → Bool)) : Finset (Finset (Literal (Fin n))) :=
  @Finset.filter _ (IsCore R) (Classical.decPred _) univ

def step {V : Type} (F : Finset (Clause V)) (S : Set (Literal V)) : Set (Literal V) :=
  S ∪ {l | ∃ D ∈ F, l ∈ D ∧ ∀ other ∈ D, other ≠ l → negLit other ∈ S}

def seed {m : ℕ} (P : Finset (Literal (Fin n))) : Set (Literal (Fin n ⊕ Fin m)) :=
  {l | ∃ e ∈ P, l = (Sum.inl e.1, e.2)}

def Enc (R : Finset (Fin n → Bool)) (d m : ℕ) (F : Finset (Clause (Fin n ⊕ Fin m))) : Prop :=
  (∀ D ∈ F, D.card ≤ 3) ∧
  (∀ a : Fin n → Bool, a ∈ R ↔ ∃ aux : Fin m → Bool, Satisfies (Sum.elim a aux) (↑F : Set _)) ∧
  ∀ P : Finset (Literal (Fin n)), (∃ a, fits P a) →
    ((¬∃ a ∈ R, fits P a) ↔ ∃ D ∈ F, ∀ l ∈ D, negLit l ∈ (step F)^[d] (seed P)) ∧
    ((∃ a ∈ R, fits P a) → ∀ v : Fin n, ∀ b : Bool,
      (∀ a ∈ R, fits P a → a v = b) ↔ (Sum.inl v, b) ∈ (step F)^[d] (seed P))

lemma negLit_negLit {V : Type} (l : Literal V) : negLit (negLit l) = l := by simp [negLit]

lemma negLit_true {V : Type} (w : V → Bool) (l : Literal V) :
    w (negLit l).1 = (negLit l).2 ↔ ¬w l.1 = l.2 := by
  obtain ⟨v, b⟩ := l
  cases h : w v <;> cases b <;> simp [negLit, h]

lemma fits_mono {P Q : Finset (Literal (Fin n))} {a : Fin n → Bool} (h : Q ⊆ P)
    (ha : fits P a) : fits Q a := fun l hl => ha l (h hl)

lemma mem_seed {m : ℕ} {P : Finset (Literal (Fin n))} {e : Literal (Fin n)} (he : e ∈ P) :
    ((Sum.inl e.1, e.2) : Literal (Fin n ⊕ Fin m)) ∈ seed P := ⟨e, he, rfl⟩

lemma seed_mono {m : ℕ} {P Q : Finset (Literal (Fin n))} (h : Q ⊆ P) :
    (seed Q : Set (Literal (Fin n ⊕ Fin m))) ⊆ seed P :=
  fun _ ⟨e, he, hl⟩ => ⟨e, h he, hl⟩

section Propagation
variable {V : Type} (F : Finset (Clause V))

lemma subset_step (S : Set (Literal V)) : S ⊆ step F S := Set.subset_union_left

lemma step_mono : Monotone (step F) := fun _ _ h =>
  Set.union_subset_union h fun _ ⟨D, hD, hl, ho⟩ => ⟨D, hD, hl, fun o hoD hne => h (ho o hoD hne)⟩

lemma iterate_subset (S : Set (Literal V)) {i j : ℕ} (h : i ≤ j) :
    (step F)^[i] S ⊆ (step F)^[j] S :=
  Function.monotone_iterate_of_id_le (fun S => subset_step F S) h S

lemma iterate_mono (k : ℕ) {S S' : Set (Literal V)} (h : S ⊆ S') :
    (step F)^[k] S ⊆ (step F)^[k] S' :=
  (step_mono F).iterate k h

lemma mem_iterate_of_pred {d : ℕ} (hd : 0 < d) {S : Set (Literal V)} {l : Literal V}
    (h : l ∈ step F ((step F)^[d - 1] S)) : l ∈ (step F)^[d] S := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hd.ne'
  simpa [Function.iterate_succ_apply'] using h

lemma sound {w : V → Bool} (hw : Satisfies w (↑F : Set (Clause V))) {S : Set (Literal V)}
    (hS : ∀ l ∈ S, w l.1 = l.2) (k : ℕ) : ∀ l ∈ (step F)^[k] S, w l.1 = l.2 := by
  induction k with
  | zero => exact hS
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    rintro l (hl | ⟨D, hD, hlD, ho⟩)
    · exact ih l hl
    obtain ⟨l', hl'D, hl'⟩ := hw D (mem_coe.2 hD)
    by_cases h : l' = l
    · exact h ▸ hl'
    · exact absurd hl' ((negLit_true w l').1 (ih _ (ho l' hl'D h)))

lemma not_all_neg {w : V → Bool} (hw : Satisfies w (↑F : Set (Clause V))) {S : Set (Literal V)}
    (hS : ∀ l ∈ S, w l.1 = l.2) (k : ℕ) {D : Clause V} (hD : D ∈ F)
    (hall : ∀ l ∈ D, negLit l ∈ (step F)^[k] S) : False := by
  obtain ⟨l, hl, hlw⟩ := hw D (mem_coe.2 hD)
  exact (negLit_true w l).1 (sound F hw hS k _ (hall l hl)) hlw

end Propagation

lemma mem_coresOf {R : Finset (Fin n → Bool)} {Q : Finset (Literal (Fin n))} :
    Q ∈ coresOf R ↔ IsCore R Q := by
  simp [coresOf]

lemma support {m : ℕ} {F : Finset (Clause (Fin n ⊕ Fin m))} (hF : ∀ D ∈ F, D.card ≤ 3)
    (P : Finset (Literal (Fin n))) (k : ℕ) :
    ∀ l ∈ (step F)^[k] (seed P), ∃ Q ⊆ P, Q.card ≤ 2 ^ k ∧ l ∈ (step F)^[k] (seed Q) := by
  induction k with
  | zero =>
    rintro l ⟨e, he, rfl⟩
    exact ⟨{e}, singleton_subset_iff.2 he, by simp, mem_seed (mem_singleton_self e)⟩
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rintro l (hl | ⟨D, hD, hlD, ho⟩)
    · obtain ⟨Q, hQP, hQ, hlQ⟩ := ih l hl
      exact ⟨Q, hQP, hQ.trans (Nat.pow_le_pow_right two_pos k.le_succ), subset_step F _ hlQ⟩
    have h' : ∀ o ∈ D.erase l, ∃ Q ⊆ P, Q.card ≤ 2 ^ k ∧ negLit o ∈ (step F)^[k] (seed Q) :=
      fun o ho' => ih _ (ho o (mem_of_mem_erase ho') (ne_of_mem_erase ho'))
    choose Q hQP hQ hoQ using h'
    have h2 : (D.erase l).card ≤ 2 := by rw [card_erase_of_mem hlD]; have := hF D hD; omega
    refine ⟨(D.erase l).attach.biUnion fun o => Q o.1 o.2,
      biUnion_subset.2 fun o _ => hQP o.1 o.2, ?_, Or.inr ⟨D, hD, hlD, fun o hoD hne => ?_⟩⟩
    · calc _ ≤ ∑ o ∈ (D.erase l).attach, (Q o.1 o.2).card := card_biUnion_le
        _ ≤ ∑ _o ∈ (D.erase l).attach, 2 ^ k := sum_le_sum fun o _ => hQ o.1 o.2
        _ = (D.erase l).card * 2 ^ k := by rw [sum_const, card_attach, smul_eq_mul]
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_right _ h2
        _ = 2 ^ (k + 1) := by ring
    · have ho' : o ∈ D.erase l := mem_erase.2 ⟨hne, hoD⟩
      have hsub : Q o ho' ⊆ (D.erase l).attach.biUnion fun o => Q o.1 o.2 :=
        subset_biUnion_of_mem (fun o => Q o.1 o.2) (mem_attach _ ⟨o, ho'⟩)
      exact iterate_mono F k (seed_mono hsub) (hoQ o ho')

lemma card_le_of_enc {R : Finset (Fin n → Bool)} {d m : ℕ} {F : Finset (Clause (Fin n ⊕ Fin m))}
    (hE : Enc R d m F) {P : Finset (Literal (Fin n))} (hP : IsCore R P) :
    P.card ≤ 2 ^ d + 1 := by
  obtain ⟨hF, -, hprop⟩ := hE
  obtain ⟨-, hbad, hmin⟩ := hP
  rcases P.eq_empty_or_nonempty with rfl | ⟨e, he⟩
  · simp
  obtain ⟨a₀, ha₀R, ha₀⟩ := hmin e he

  have hforced : ∀ a ∈ R, fits (P.erase e) a → a e.1 = !e.2 := by
    intro a haR haP
    by_contra h
    refine hbad ⟨a, haR, fun l hl => ?_⟩
    by_cases hle : l = e
    · subst hle; cases h' : a l.1 <;> cases hl2 : l.2 <;> simp_all
    · exact haP l (mem_erase.2 ⟨hle, hl⟩)
  have hmem := ((hprop _ ⟨a₀, ha₀⟩).2 ⟨a₀, ha₀R, ha₀⟩ e.1 (!e.2)).1 hforced
  obtain ⟨Q, hQP, hQ, hlQ⟩ := support hF _ d _ hmem
  have hQforced := ((hprop Q ⟨a₀, fits_mono hQP ha₀⟩).2
    ⟨a₀, ha₀R, fits_mono hQP ha₀⟩ e.1 (!e.2)).2 hlQ

  have hsub : P.erase e ⊆ Q := by
    intro f hf
    by_contra hfQ
    obtain ⟨a, haR, haf⟩ := hmin f (mem_of_mem_erase hf)
    have h1 := hQforced a haR fun l hl =>
      haf l (mem_erase.2 ⟨fun h => hfQ (h ▸ hl), mem_of_mem_erase (hQP hl)⟩)
    have h2 := haf e (mem_erase.2 ⟨(ne_of_mem_erase hf).symm, he⟩)
    rw [h1] at h2; cases h3 : e.2 <;> simp [h3] at h2
  have := card_le_card hsub
  have := card_erase_add_one he
  omega

lemma exists_core (R : Finset (Fin n → Bool)) (P : Finset (Literal (Fin n)))
    (hc : ∃ a, fits P a) (hbad : ¬∃ a ∈ R, fits P a) : ∃ Q ⊆ P, IsCore R Q := by
  induction P using Finset.strongInduction with
  | H P ih =>
    by_cases hmin : ∀ e ∈ P, ∃ a ∈ R, fits (P.erase e) a
    · exact ⟨P, subset_refl P, hc, hbad, hmin⟩
    push Not at hmin
    obtain ⟨e, he, hno⟩ := hmin
    obtain ⟨Q, hQ, hcore⟩ := ih (P.erase e) (erase_ssubset he)
      (hc.imp fun a => fits_mono (erase_subset e P)) fun ⟨a, haR, ha⟩ => hno a haR ha
    exact ⟨Q, hQ.trans (erase_subset e P), hcore⟩

lemma mem_of_no_core {R : Finset (Fin n → Bool)} {a : Fin n → Bool}
    (h : ∀ P, IsCore R P → ¬fits P a) : a ∈ R := by
  by_contra haR
  have hfit : fits (univ.image fun v => ((v, a v) : Literal (Fin n))) a := by
    intro l hl; obtain ⟨v, -, rfl⟩ := mem_image.1 hl; rfl
  obtain ⟨Q, hQP, hQ⟩ := exists_core R _ ⟨a, hfit⟩ fun ⟨b, hbR, hb⟩ => by
    have hba : b = a := funext fun v => hb (v, a v) (mem_image_of_mem _ (mem_univ v))
    exact haR (hba ▸ hbR)
  exact h Q hQ (fits_mono hQP hfit)

lemma enc_of_props {R : Finset (Fin n → Bool)} {d m : ℕ} {F : Finset (Clause (Fin n ⊕ Fin m))}
    (hwidth : ∀ D ∈ F, D.card ≤ 3)
    (hsat : ∀ a ∈ R, ∃ aux : Fin m → Bool, Satisfies (Sum.elim a aux) (↑F : Set _))
    (hconf : ∀ Q, IsCore R Q → ∀ P, Q ⊆ P →
      ∃ D ∈ F, ∀ l ∈ D, negLit l ∈ (step F)^[d] (seed P))
    (hforce : ∀ Q, IsCore R Q → ∀ e ∈ Q, ∀ P, Q.erase e ⊆ P →
      ((Sum.inl e.1, !e.2) : Literal (Fin n ⊕ Fin m)) ∈ (step F)^[d] (seed P)) :
    Enc R d m F := by

  have hseed : ∀ {P a} (aux : Fin m → Bool), fits P a →
      ∀ l ∈ (seed P : Set (Literal (Fin n ⊕ Fin m))), Sum.elim a aux l.1 = l.2 := by
    rintro P a aux ha l ⟨e, he, rfl⟩; exact ha e he
  refine ⟨hwidth, fun a => ⟨hsat a, fun ⟨aux, hw⟩ => mem_of_no_core fun Q hQ hfit => ?_⟩,
    fun P hc => ⟨⟨fun hbad => ?_, fun ⟨D, hD, hall⟩ ⟨a, haR, ha⟩ => ?_⟩, fun hext v b => ⟨?_, ?_⟩⟩⟩
  · obtain ⟨D, hD, hall⟩ := hconf Q hQ Q subset_rfl
    exact not_all_neg F hw (hseed aux hfit) d hD hall
  · obtain ⟨Q, hQP, hQ⟩ := exists_core R P hc hbad
    exact hconf Q hQ P hQP
  · obtain ⟨aux, hw⟩ := hsat a haR
    exact not_all_neg F hw (hseed aux ha) d hD hall
  · intro hforced
    obtain ⟨a₀, ha₀R, ha₀⟩ := hext
    by_cases hvb : (v, b) ∈ P
    · exact iterate_subset F _ (Nat.zero_le d) (mem_seed hvb)
    have hvnb : (v, !b) ∉ P := fun h => by
      have := hforced a₀ ha₀R ha₀; have := ha₀ _ h; simp_all
    have hv : ∀ l ∈ P, l.1 ≠ v := by
      rintro ⟨u, c⟩ hl rfl; cases c <;> cases b <;> simp_all

    obtain ⟨Q, hQP, hQ⟩ := exists_core R (insert (v, !b) P)
      ⟨Function.update a₀ v (!b), fun l hl => by
        rcases mem_insert.1 hl with rfl | hl
        · simp
        · rw [Function.update_of_ne (hv l hl)]; exact ha₀ l hl⟩
      fun ⟨a, haR, ha⟩ => by
        have h1 := hforced a haR fun l hl => ha l (mem_insert_of_mem hl)
        have h2 := ha (v, !b) (mem_insert_self _ _)
        simp_all
    have hmem : (v, !b) ∈ Q := by
      by_contra h
      exact hQ.2.1 ⟨a₀, ha₀R, fits_mono (fun l hl => (mem_insert.1 (hQP hl)).resolve_left
        fun h' => h (h' ▸ hl)) ha₀⟩
    simpa using hforce Q hQ _ hmem P fun l hl =>
      (mem_insert.1 (hQP (mem_of_mem_erase hl))).resolve_left (ne_of_mem_erase hl)
  · intro hl a haR ha
    obtain ⟨aux, hw⟩ := hsat a haR
    exact sound F hw (hseed aux ha) d _ hl

lemma sum_biUnion_le' {ι β : Type*} [DecidableEq β] (s : Finset ι) (t : ι → Finset β)
    (g : β → ℕ) : ∑ x ∈ s.biUnion t, g x ≤ ∑ i ∈ s, ∑ x ∈ t i, g x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [biUnion_insert, sum_insert hi]
    have := sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := g)
    omega

section Gadget
variable {m d : ℕ} {C : Type} (P : C → Finset (Literal (Fin n)))
  (ι : (Σ c, Fin d × Fin (P c).card) ≃ Fin m) (hd : 0 < d)

def lift (e : Literal (Fin n)) : Literal (Fin n ⊕ Fin m) := (Sum.inl e.1, e.2)

def pin (c : C) (s : Fin (P c).card) : Literal (Fin n) := ((P c).equivFin.symm s).1

def rot {k : ℕ} (s : Fin k) (t : ℕ) : Fin k := ⟨(s + t) % k, Nat.mod_lt _ s.pos⟩

def len (k j : ℕ) : ℕ := min (2 ^ j) (k - 1)

def sig (c : C) (j : ℕ) (s : Fin (P c).card) : Literal (Fin n ⊕ Fin m) :=
  if j = 0 then lift (pin P c s) else (Sum.inr (ι ⟨c, ⟨j % d, Nat.mod_lt _ hd⟩, s⟩), true)

def link (c : C) (j : ℕ) (s : Fin (P c).card) : Clause (Fin n ⊕ Fin m) :=
  {negLit (sig P ι hd c (j - 1) s),
    negLit (sig P ι hd c (j - 1) (rot s (len (P c).card j - len (P c).card (j - 1)))),
    sig P ι hd c j s}

def last (c : C) (s : Fin (P c).card) : Clause (Fin n ⊕ Fin m) :=
  {negLit (sig P ι hd c (d - 1) (rot s 1)),
    negLit (sig P ι hd c (d - 1) (rot s ((P c).card - len (P c).card (d - 1)))),
    negLit (lift (pin P c s))}

def gadget (c : C) : Finset (Clause (Fin n ⊕ Fin m)) :=
  if (P c).card ≤ 1 then {(P c).image fun e => negLit (lift e)}
  else univ.image fun js : Fin d × Fin (P c).card =>
    if js.1.val = 0 then last P ι hd c js.2 else link P ι hd c js.1 js.2

def cnf [Fintype C] : Finset (Clause (Fin n ⊕ Fin m)) := univ.biUnion (gadget P ι hd)

def val {P : C → Finset (Literal (Fin n))} (a : Fin n → Bool) (c : C) (j : ℕ)
    (s : Fin (P c).card) : Prop :=
  ∀ t < len (P c).card j, a (pin P c (rot s t)).1 = (pin P c (rot s t)).2

def auxOf (P : C → Finset (Literal (Fin n))) (ι : (Σ c, Fin d × Fin (P c).card) ≃ Fin m)
    (a : Fin n → Bool) : Fin m → Bool := fun z =>
  @decide (val a (ι.symm z).1 (ι.symm z).2.1 (ι.symm z).2.2) (Classical.dec _)

lemma pin_mem (c : C) (s : Fin (P c).card) : pin P c s ∈ P c := ((P c).equivFin.symm s).2

lemma pin_injective (c : C) : Function.Injective (pin P c) := fun _ _ h =>
  (P c).equivFin.symm.injective (Subtype.ext h)

lemma exists_pin {c : C} {e : Literal (Fin n)} (he : e ∈ P c) : ∃ s, pin P c s = e :=
  ⟨(P c).equivFin ⟨e, he⟩, by simp [pin]⟩

lemma rot_zero {k : ℕ} (s : Fin k) : rot s 0 = s := Fin.ext (by simp [rot, Nat.mod_eq_of_lt s.2])

lemma rot_rot {k : ℕ} (s : Fin k) (a b : ℕ) : rot (rot s a) b = rot s (a + b) :=
  Fin.ext (by simp only [rot]; rw [Nat.mod_add_mod, add_assoc])

lemma rot_ne {k : ℕ} (s : Fin k) {u : ℕ} (h0 : 0 < u) (hu : u < k) : rot s u ≠ s := by
  intro h
  have h' := congrArg Fin.val h
  simp only [rot] at h'
  by_cases hlt : s.val + u < k
  · rw [Nat.mod_eq_of_lt hlt] at h'; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h'; omega

lemma exists_rot {k : ℕ} (i s : Fin k) : ∃ u < k, rot i u = s :=
  ⟨(s + k - i) % k, Nat.mod_lt _ i.pos, Fin.ext (by
    simp only [rot]
    rw [Nat.add_mod_mod, show i.val + (s + k - i) = s + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt s.2])⟩

lemma len_zero {k : ℕ} (hk : 2 ≤ k) : len k 0 = 1 := by simp [len]; omega

lemma len_le_succ (k j : ℕ) : len k j ≤ len k (j + 1) := by
  have := pow_succ 2 j; unfold len; omega

lemma len_succ_le (k j : ℕ) : len k (j + 1) ≤ 2 * len k j := by
  have := pow_succ 2 j; unfold len; omega

variable {P ι hd}

lemma sig_true (a : Fin n → Bool) {c : C} (hk : 2 ≤ (P c).card) {j : ℕ} (hj : j < d)
    (s : Fin (P c).card) :
    Sum.elim a (auxOf P ι a) (sig P ι hd c j s).1 = (sig P ι hd c j s).2 ↔ val a c j s := by
  by_cases hj0 : j = 0
  · subst hj0; simp [sig, lift, val, len_zero hk, rot_zero]
  · simp only [sig, hj0, ite_false, Sum.elim_inr]
    unfold auxOf; rw [Equiv.symm_apply_apply]
    simp [Nat.mod_eq_of_lt hj]

variable [Fintype C]

lemma link_mem {c : C} (hk : 2 ≤ (P c).card) {j : ℕ} (hj0 : j ≠ 0) (hj : j < d)
    (s : Fin (P c).card) : link P ι hd c j s ∈ cnf P ι hd :=
  mem_biUnion.2 ⟨c, mem_univ c, by
    rw [gadget, ite_eq_right (by omega)]
    exact mem_image.2 ⟨(⟨j, hj⟩, s), mem_univ _, by simp [hj0]⟩⟩

lemma last_mem {c : C} (hk : 2 ≤ (P c).card) (s : Fin (P c).card) :
    last P ι hd c s ∈ cnf P ι hd :=
  mem_biUnion.2 ⟨c, mem_univ c, by
    rw [gadget, ite_eq_right (by omega)]; exact mem_image.2 ⟨(⟨0, hd⟩, s), mem_univ _, by simp⟩⟩

lemma image_mem {c : C} (hk : (P c).card ≤ 1) :
    (P c).image (fun e => negLit (lift e)) ∈ cnf P ι hd :=
  mem_biUnion.2 ⟨c, mem_univ c, by rw [gadget, ite_eq_left hk]; exact mem_singleton_self _⟩

lemma sig_mem {c : C} (hk : 2 ≤ (P c).card) (S0 : Set (Literal (Fin n ⊕ Fin m))) :
    ∀ j < d, ∀ s, (∀ t < len (P c).card j, lift (pin P c (rot s t)) ∈ S0) →
      sig P ι hd c j s ∈ (step (cnf P ι hd))^[j] S0 := by
  intro j
  induction j with
  | zero =>
    intro _ s hs
    simpa [sig, rot_zero] using hs 0 (by rw [len_zero hk]; omega)
  | succ j ih =>
    intro hj s hs
    have h1 := len_le_succ (P c).card j
    have h2 := len_succ_le (P c).card j
    have hA := ih (by omega) s fun t ht => hs t (by omega)
    have hB := ih (by omega) (rot s (len (P c).card (j + 1) - len (P c).card j)) fun t ht => by
      rw [rot_rot]; exact hs _ (by omega)
    rw [Function.iterate_succ_apply']
    refine Or.inr ⟨link P ι hd c (j + 1) s, link_mem hk (by omega) hj s, by simp [link],
      fun o ho hne => ?_⟩
    simp only [link, Nat.add_sub_cancel, mem_insert, mem_singleton] at ho
    rcases ho with rfl | rfl | rfl
    · rwa [negLit_negLit]
    · rwa [negLit_negLit]
    · exact absurd rfl hne

lemma last_ready {c : C} (hk : 2 ≤ (P c).card) (i : Fin (P c).card)
    (S0 : Set (Literal (Fin n ⊕ Fin m))) (hS : ∀ s, s ≠ i → lift (pin P c s) ∈ S0) :
    ∀ l ∈ last P ι hd c i, l ≠ negLit (lift (pin P c i)) →
      negLit l ∈ (step (cnf P ι hd))^[d - 1] S0 := by
  have hL : len (P c).card (d - 1) ≤ (P c).card - 1 := min_le_right _ _
  intro l hl hne
  simp only [last, mem_insert, mem_singleton] at hl
  rcases hl with rfl | rfl | rfl
  · rw [negLit_negLit]
    exact sig_mem hk S0 (d - 1) (by omega) _ fun t ht => by
      rw [rot_rot]; exact hS _ (rot_ne _ (by omega) (by omega))
  · rw [negLit_negLit]
    exact sig_mem hk S0 (d - 1) (by omega) _ fun t ht => by
      rw [rot_rot]; exact hS _ (rot_ne _ (by omega) (by omega))
  · exact absurd rfl hne

lemma force_mem {c : C} {e : Literal (Fin n)} (he : e ∈ P c) (S0 : Set (Literal (Fin n ⊕ Fin m)))
    (hS : ∀ e' ∈ (P c).erase e, lift e' ∈ S0) :
    negLit (lift e) ∈ (step (cnf P ι hd))^[d] S0 := by
  by_cases hk : (P c).card ≤ 1
  · refine iterate_subset _ _ (Nat.one_le_iff_ne_zero.2 hd.ne')
      (Or.inr ⟨_, image_mem hk, mem_image_of_mem _ he, fun o ho hne => ?_⟩)
    obtain ⟨e', he', rfl⟩ := mem_image.1 ho
    have : e' ≠ e := fun h => hne (h ▸ rfl)
    exact absurd (one_lt_card.2 ⟨e', he', e, he, this⟩) (by omega)
  obtain ⟨i, rfl⟩ := exists_pin P he
  refine mem_iterate_of_pred _ hd (Or.inr ⟨_, last_mem (by omega) i, by simp [last],
    last_ready (by omega) i S0 fun s hs => hS _ (mem_erase.2 ⟨?_, pin_mem P c s⟩)⟩)
  exact fun h => hs (pin_injective P c h)

lemma conflict (c : C) (S0 : Set (Literal (Fin n ⊕ Fin m))) (hS : ∀ e ∈ P c, lift e ∈ S0) :
    ∃ D ∈ cnf P ι hd, ∀ l ∈ D, negLit l ∈ (step (cnf P ι hd))^[d] S0 := by
  by_cases hk : (P c).card ≤ 1
  · refine ⟨_, image_mem hk, fun l hl => ?_⟩
    obtain ⟨e, he, rfl⟩ := mem_image.1 hl
    rw [negLit_negLit]; exact iterate_subset _ _ (Nat.zero_le d) (hS e he)
  have i : Fin (P c).card := ⟨0, by omega⟩
  refine ⟨_, last_mem (by omega) i, fun l hl => ?_⟩
  by_cases hli : l = negLit (lift (pin P c i))
  · subst hli; rw [negLit_negLit]
    exact iterate_subset _ _ (Nat.zero_le d) (hS _ (pin_mem P c i))
  · exact iterate_subset _ _ (Nat.sub_le d 1)
      (last_ready (by omega) i S0 (fun s _ => hS _ (pin_mem P c s)) l hl hli)

lemma cnf_sat {R : Finset (Fin n → Bool)} (hcore : ∀ c, ¬∃ a ∈ R, fits (P c) a)
    (hsmall : ∀ c, (P c).card ≤ 2 ^ d + 1) {a : Fin n → Bool} (ha : a ∈ R) :
    Satisfies (Sum.elim a (auxOf P ι a)) (↑(cnf P ι hd) : Set _) := by
  intro D hD
  obtain ⟨c, -, hDc⟩ := mem_biUnion.1 (mem_coe.1 hD)
  have hnot : ¬fits (P c) a := fun h => hcore c ⟨a, ha, h⟩
  unfold gadget at hDc
  split_ifs at hDc with hk
  · rw [mem_singleton] at hDc; subst hDc
    simp only [fits, not_forall] at hnot
    obtain ⟨e, he, hfalse⟩ := hnot
    exact ⟨_, mem_image_of_mem _ he, (negLit_true _ _).2 hfalse⟩
  push Not at hk
  obtain ⟨⟨j, s⟩, -, rfl⟩ := mem_image.1 hDc
  dsimp only
  have hL : len (P c).card (d - 1) ≤ (P c).card - 1 := min_le_right _ _
  split_ifs with hj0

  · by_cases hA : val a c (d - 1) (rot s 1)
    · by_cases hB : val a c (d - 1) (rot s ((P c).card - len (P c).card (d - 1)))
      · by_cases hpin : a (pin P c s).1 = (pin P c s).2
        · refine absurd (fun e he => ?_) hnot
          have hcov : (P c).card - 1 ≤ 2 * len (P c).card (d - 1) := by
            have := hsmall c
            have : 2 ^ d = 2 * 2 ^ (d - 1) := by
              rw [← pow_succ', Nat.sub_add_cancel hd]
            unfold len; omega
          obtain ⟨s', rfl⟩ := exists_pin P he
          obtain ⟨u, hu, rfl⟩ := exists_rot s s'
          rcases Nat.eq_zero_or_pos u with rfl | hu0
          · rwa [rot_zero]
          by_cases huL : u ≤ len (P c).card (d - 1)
          · have := hA (u - 1) (by omega)
            rwa [rot_rot, show 1 + (u - 1) = u by omega] at this
          · have := hB (u - ((P c).card - len (P c).card (d - 1))) (by omega)
            rwa [rot_rot, show (P c).card - len (P c).card (d - 1) +
              (u - ((P c).card - len (P c).card (d - 1))) = u by omega] at this
        · exact ⟨negLit (lift (pin P c s)), by simp [last], (negLit_true _ _).2 hpin⟩
      · exact ⟨negLit (sig P ι hd c (d - 1) (rot s ((P c).card - len (P c).card (d - 1)))),
          by simp [last], (negLit_true _ _).2 (mt (sig_true a hk (by omega) _).1 hB)⟩
    · exact ⟨negLit (sig P ι hd c (d - 1) (rot s 1)), by simp [last],
        (negLit_true _ _).2 (mt (sig_true a hk (by omega) _).1 hA)⟩

  · have hjd := j.2
    by_cases hA : val a c (j - 1) s
    · by_cases hB : val a c (j - 1) (rot s (len (P c).card j - len (P c).card (j - 1)))
      · refine ⟨sig P ι hd c j s, by simp [link], (sig_true a hk hjd s).2 fun t ht => ?_⟩
        have h1 := len_le_succ (P c).card (j - 1)
        have h2 := len_succ_le (P c).card (j - 1)
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0)] at h1 h2
        by_cases ht' : t < len (P c).card (j - 1)
        · exact hA t ht'
        · have := hB (t - (len (P c).card j - len (P c).card (j - 1))) (by omega)
          rwa [rot_rot, show len (P c).card j - len (P c).card (j - 1) +
            (t - (len (P c).card j - len (P c).card (j - 1))) = t by omega] at this
      · exact ⟨negLit (sig P ι hd c (j - 1) (rot s (len (P c).card j - len (P c).card (j - 1)))),
          by simp [link], (negLit_true _ _).2 (mt (sig_true a hk (by omega) _).1 hB)⟩
    · exact ⟨negLit (sig P ι hd c (j - 1) s), by simp [link],
        (negLit_true _ _).2 (mt (sig_true a hk (by omega) _).1 hA)⟩

lemma cnf_width : ∀ D ∈ cnf P ι hd, D.card ≤ 3 := by
  intro D hD
  obtain ⟨c, -, hDc⟩ := mem_biUnion.1 hD
  unfold gadget at hDc
  split_ifs at hDc with hk
  · rw [mem_singleton] at hDc; subst hDc; exact card_image_le.trans (by omega)
  obtain ⟨⟨j, s⟩, -, rfl⟩ := mem_image.1 hDc
  split_ifs <;> exact card_le_three

lemma cnf_cost : ∑ D ∈ cnf P ι hd, D.card ≤ 3 * d * ∑ c, (P c).card := by
  refine (sum_biUnion_le' _ _ _).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun c _ => ?_
  unfold gadget
  split_ifs with hk
  · rw [sum_singleton]; exact card_image_le.trans (by nlinarith)
  · refine (sum_image_le_of_nonneg fun _ _ => Nat.zero_le _).trans ?_
    calc _ ≤ ∑ _js : Fin d × Fin (P c).card, 3 := sum_le_sum fun js _ => by
          split_ifs <;> exact card_le_three
      _ = 3 * d * (P c).card := by simp; ring

end Gadget

lemma enc_of_small {d : ℕ} (hd : 0 < d) {R : Finset (Fin n → Bool)}
    (hs : ∀ P ∈ coresOf R, P.card ≤ 2 ^ d + 1) :
    ∃ m F, Enc R d m F ∧ m + ∑ D ∈ F, D.card ≤ 4 * d * ∑ P ∈ coresOf R, P.card := by
  have hmem : ∀ {Q}, IsCore R Q → Q ∈ coresOf R := mem_coresOf.2
  let Pc : {Q // Q ∈ coresOf R} → Finset (Literal (Fin n)) := Subtype.val
  obtain ⟨m, ⟨ι⟩⟩ : ∃ m, Nonempty ((Σ c, Fin d × Fin (Pc c).card) ≃ Fin m) :=
    ⟨_, ⟨Fintype.equivFin _⟩⟩
  refine ⟨m, cnf Pc ι hd, enc_of_props cnf_width ?_ ?_ ?_, ?_⟩
  · exact fun a ha => ⟨auxOf Pc ι a, cnf_sat (P := Pc) (ι := ι) (hd := hd)
      (fun c => (mem_coresOf.1 c.2).2.1) (fun c => hs c.1 c.2) ha⟩
  · exact fun Q hQ P hQP => conflict (P := Pc) (ι := ι) (hd := hd) ⟨Q, hmem hQ⟩ (seed P)
      fun e he => mem_seed (hQP he)
  · intro Q hQ e he P hsub
    have := force_mem (P := Pc) (ι := ι) (hd := hd) (c := ⟨Q, hmem hQ⟩) he (seed P)
      fun e' he' => mem_seed (hsub he')
    exact this
  have hcost := cnf_cost (P := Pc) (ι := ι) (hd := hd)
  have hsum : ∑ c, (Pc c).card = ∑ Q ∈ coresOf R, Q.card := sum_coe_sort _ _
  have hcard : m = d * ∑ c, (Pc c).card := by
    rw [← Fintype.card_fin m, ← Fintype.card_congr ι]
    simp [Fintype.card_sigma, mul_sum]
  rw [hsum] at hcost hcard
  linarith

end

end PEqualNP.Outside.L_pcx_228

open PEqualNP.Outside.L_pcx_228 Finset in
theorem PEqualNP.Outside.L_pcx_228 : ∀ (n d : ℕ), 0 < d → ∀ R : Finset (Fin n → Bool),
  let Pin := PEqualNP.ProofComplexity.Literal (Fin n)
  let fits := fun (pins : Finset Pin) (a : Fin n → Bool) =>
    ∀ l ∈ pins, a l.1 = l.2
  let isCore := fun (candidate : Finset Pin) =>
    (∃ a, fits candidate a) ∧ (¬ ∃ a ∈ R, fits candidate a) ∧
      ∀ e ∈ candidate, ∃ a ∈ R, fits (candidate.erase e) a
  let cores := @Finset.filter (Finset Pin) isCore (Classical.decPred isCore) Finset.univ
  let small := ∀ P ∈ cores, P.card ≤ 2 ^ d + 1
  let enc := fun (m : ℕ)
      (F : Finset (PEqualNP.ProofComplexity.Clause (Sum (Fin n) (Fin m)))) =>
    let step := fun S : Set (PEqualNP.ProofComplexity.Literal (Sum (Fin n) (Fin m))) =>
      S ∪ {l | ∃ D ∈ F, l ∈ D ∧ ∀ other ∈ D, other ≠ l →
        PEqualNP.Search.negLit other ∈ S}
    (∀ D ∈ F, D.card ≤ 3) ∧
    (∀ a : Fin n → Bool, a ∈ R ↔ ∃ aux : Fin m → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim a aux) (↑F : Set _)) ∧
    ∀ P : Finset Pin, (∃ a, fits P a) →
      let seed : Set (PEqualNP.ProofComplexity.Literal (Sum (Fin n) (Fin m))) :=
        {l | ∃ e ∈ P, l = (Sum.inl e.1, e.2)}
      let known := (step^[d]) seed
      ((¬ ∃ a ∈ R, fits P a) ↔
        ∃ D ∈ F, ∀ l ∈ D, PEqualNP.Search.negLit l ∈ known) ∧
      ((∃ a ∈ R, fits P a) → ∀ v : Fin n, ∀ b : Bool,
        (∀ a ∈ R, fits P a → a v = b) ↔ (Sum.inl v, b) ∈ known)
  ((∃ m F, enc m F) → small) ∧
    (small → ∃ m F, enc m F ∧
      m + (∑ D ∈ F, D.card) ≤ 4 * d * (∑ P ∈ cores, P.card)) := by
  intro n d hd R Pin fits isCore cores small enc
  exact ⟨fun ⟨m, F, h⟩ P hP => card_le_of_enc h (mem_coresOf.1 hP), fun hs => enc_of_small hd hs⟩
