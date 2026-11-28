import Mathlib
import PEqualNP.Defs

-- The input model, linear algebra and evaluator use PR 50857.
-- The weighted rectangular contraction uses PR 52618.
-- Inherited tape, packing and compiler conventions use PRs 43594, 40726 and 45233.

-- Adapted from L-meta-29751 (PR 50857) and L-lib-838 (PR 52618).

open Fintype (card card_fin card_prod card_sum card_bool card_unit card_empty card_fun card_subtype card_congr card_coe)
open Finset (sum_congr sum_eq_zero sum_eq_single sum_ite_eq' mem_univ sum_const_zero)
open Submodule (span span_le subset_span span_union span_mono finrank_mono mem_span_range_iff_exists_fun)
open Module (finrank)
open Sum (inl inr elim elim_inl elim_inr)
open Function (Injective Surjective LeftInverse RightInverse)

namespace PEqualNP.Outside.L_meta_29774_aux

section Helpers

-- The tape conventions follow L_meta_29930.lean at 04168edab39014e515fbb09f71ba0651b69367a8.
-- The recurrence and Fourier counting lemmas below are adapted to this statement.

abbrev F := ZMod 2
abbrev Word (k : ℕ) := Fin k → F
abbrev Tape (k r : ℕ) := Word k × (Bool → Fin (r + 1) → Word k)
abbrev Leaf (k r : ℕ) := Fin k ⊕ (Bool × Fin r × Fin k)

def ix {k : ℕ} (hk : 0 < k) (s : ℕ) : Fin k := ⟨s % k, Nat.mod_lt _ hk⟩

def rot {k : ℕ} (hk : 0 < k) (s : ℕ) (v : Word k) (j : Fin k) : F :=
  v (ix hk (j.val + k - s % k))

def start (b : Bool) : ℕ := if b then 3 else 1

def feed (b : Bool) (t : ℕ) : ℕ := if b then 3 * (t + 1) + 1 else 2 * t

def mix {k : ℕ} (hk : 0 < k) (b : Bool) (v : Word k) (j : Fin k) : F :=
  let d := if b then 2 else 1
  v j + v (ix hk (j.val + d)) + v (ix hk (j.val + k - d % k))

def pair {k r : ℕ} (v z : Tape k r) : F := dotProduct v.1 z.1 +
  ∑ s : Fin (r + 1), (dotProduct (v.2 false s) (z.2 false s) + dotProduct (v.2 true s) (z.2 true s))

def form {k r : ℕ} (hk : 0 < k) : Leaf k r → Fin 3 → Tape k r → F :=
  elim (fun j _ z => z.1 j) (fun g e z =>
    let b := g.1
    let t := g.2.1
    let j := g.2.2
    let y := mix hk b (z.2 b t.castSucc)
    if e.val = 0 then y (ix hk (j.val + 1)) else if e.val = 1 then y (ix hk (j.val + 2))
    else z.2 b t.succ j + y j + rot hk (feed b t.val) z.1 j)

def step {k r : ℕ} (hk : 0 < k) (c : Bool → Fin r → Word k)
    (key : Word k) (b : Bool) (prev : Word k) (t : Fin r) : Word k :=
  let y := mix hk b prev
  fun j : Fin k => y j + (1 + y (ix hk (j.val + 1))) * y (ix hk (j.val + 2)) +
    rot hk (feed b t.val) key j + c b t j

def actual {k r : ℕ} (hk : 0 < k) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (key : Word k) (b : Bool) (t : Fin (r + 1)) : Word k :=
  ((List.finRange r).take t.val).foldl (step hk c key b) (rot hk (start b) key + name b)

def localCheck {k r : ℕ} (hk : 0 < k) (c : Bool → Fin r → Word k)
    (pref : Fin k → Option F) (z : Tape k r) : Leaf k r → Prop :=
  elim (fun j => ∀ x, pref j = some x → form hk (.inl j) 0 z = x)
    (fun g => form hk (.inr g) 2 z = (1 + form hk (.inr g) 0 z) * form hk (.inr g) 1 z +
      c g.1 g.2.1 g.2.2)

lemma ffCases (x : F) : x = 0 ∨ x = 1 := by
  revert x
  decide

lemma moveTerms (a b d u c : F) : a + b + d = u + c ↔ a = b + u + d + c := by
  revert a b d u c
  decide

lemma localCheck_gate {k r : ℕ} (hk : 0 < k) (c : Bool → Fin r → Word k)
    (pref : Fin k → Option F) (z : Tape k r) (b : Bool) (t : Fin r) (j : Fin k) :
    localCheck hk c pref z (.inr (b, t, j)) ↔
      z.2 b t.succ j = step hk c z.1 b (z.2 b t.castSucc) t j := by
  change _ ↔ _
  simpa [localCheck, form, step] using
    moveTerms (z.2 b t.succ j) (mix hk b (z.2 b t.castSucc) j)
      (rot hk (feed b t.val) z.1 j)
      ((1 + mix hk b (z.2 b t.castSucc) (ix hk (j.val + 1))) *
        mix hk b (z.2 b t.castSucc) (ix hk (j.val + 2))) (c b t j)

lemma actual_zero {k r : ℕ} (hk : 0 < k) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (key : Word k) (b : Bool) : actual hk name c key b 0 = rot hk (start b) key + name b := rfl

lemma actual_succ {k r : ℕ} (hk : 0 < k) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (key : Word k) (b : Bool) (t : Fin r) :
    actual hk name c key b t.succ = step hk c key b (actual hk name c key b t.castSucc) t := by
  have ht : t.val < (List.finRange r).length := by simp
  have hi : (List.finRange r)[t.val] = t := by apply Fin.ext; simp
  simp only [actual, Fin.val_succ, Fin.val_castSucc, List.take_succ_eq_append_getElem ht,
    List.foldl_append, List.foldl_cons, List.foldl_nil, hi]

theorem trace_iff {k r : ℕ} (hk : 0 < k) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (pref : Fin k → Option F) (z : Tape k r) :
    ((∀ b, z.2 b 0 = rot hk (start b) z.1 + name b) ∧ ∀ j, localCheck hk c pref z j) ↔
      z.2 = actual hk name c z.1 ∧ ∀ j x, pref j = some x → z.1 j = x := by
  constructor
  · rintro ⟨h0, ht⟩
    refine ⟨?_, fun j => ht (.inl j)⟩
    funext b t
    induction t using Fin.induction with
    | zero => exact h0 b
    | succ t IH =>
      rw [actual_succ, ← IH]
      funext j
      exact (localCheck_gate hk c pref z b t j).mp (ht (.inr (b, t, j)))
  · rintro ⟨ht, hp⟩
    refine ⟨fun b => congrFun (congrFun ht b) 0, ?_⟩
    rintro (j | ⟨b, t, j⟩)
    · exact hp j
    · apply (localCheck_gate hk c pref z b t j).mpr
      rw [ht, actual_succ]

def TapeOK {k r q : ℕ} (hk : 0 < k) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (obs : Fin q → Tape k r) (rhs : Fin q → F) (pref : Fin k → Option F) (z : Tape k r) : Prop :=
  (∀ b, z.2 b 0 = rot hk (start b) z.1 + name b) ∧ (∀ j, localCheck hk c pref z j) ∧
    ∀ i, pair (obs i) z = rhs i

def KeyOK {k r q : ℕ} (hk : 0 < k) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (obs : Fin q → Tape k r) (rhs : Fin q → F) (pref : Fin k → Option F) (key : Word k) : Prop :=
  (∀ j x, pref j = some x → key j = x) ∧ ∀ i, pair (obs i) (key, actual hk name c key) = rhs i

def tapeKeyEquiv {k r q : ℕ} (hk : 0 < k) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (obs : Fin q → Tape k r) (rhs : Fin q → F) (pref : Fin k → Option F) :
    {z // TapeOK hk name c obs rhs pref z} ≃ {key // KeyOK hk name c obs rhs pref key} where
  toFun z := ⟨z.val.1, by
    obtain ⟨hactual, hp⟩ := (trace_iff hk name c pref z.val).mp ⟨z.prop.1, z.prop.2.1⟩
    refine ⟨hp, fun i => ?_⟩
    change pair (obs i) (z.val.1, actual hk name c z.val.1) = rhs i
    rw [← hactual, Prod.eta]
    exact z.prop.2.2 i⟩
  invFun key := ⟨(key.val, actual hk name c key.val), by
    obtain ⟨h0, ht⟩ := (trace_iff hk name c pref (key.val, actual hk name c key.val)).mpr
      ⟨rfl, key.prop.1⟩
    exact ⟨h0, ht, key.prop.2⟩⟩
  left_inv z := by
    apply Subtype.ext
    exact Prod.ext rfl ((trace_iff hk name c pref z.val).mp ⟨z.prop.1, z.prop.2.1⟩).1.symm
  right_inv _ := rfl

abbrev Dual (V : Type*) [AddCommGroup V] [Module F V] := Module.Dual F V

def restr {V : Type*} [AddCommGroup V] [Module F V] {S T : Submodule F V}
    (h : S ≤ T) (f : Dual T) : Dual S := f.comp (Submodule.inclusion h)

theorem extend_agree {V : Type*} [AddCommGroup V] [Module F V]
    (L H : Submodule F V) (f : Dual L) (g : Dual H)
    (agree : restr (S := L ⊓ H) inf_le_left f = restr inf_le_right g) :
    ∃ u : Dual V, u.comp L.subtype = f ∧ u.comp H.subtype = g := by
  let m : L × H →ₗ[F] V := L.subtype.coprod H.subtype
  have ht : f.coprod g ∈ (LinearMap.ker m).dualAnnihilator := by
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro z hz
    have h : (z.1 : V) + (z.2 : V) = 0 := hz
    have he : (z.1 : V) = -(z.2 : V) := eq_neg_of_add_eq_zero_left h
    let x : ↥(L ⊓ H) := ⟨z.1, z.1.prop, he ▸ H.neg_mem z.2.prop⟩
    have hl : Submodule.inclusion (p := L ⊓ H) inf_le_left x = z.1 := rfl
    have hr : Submodule.inclusion (p := L ⊓ H) inf_le_right x = -z.2 := Subtype.ext he
    have ha := LinearMap.congr_fun agree x
    change f (Submodule.inclusion inf_le_left x) = g (Submodule.inclusion inf_le_right x) at ha
    rw [hl, hr, map_neg] at ha
    change f z.1 + g z.2 = 0
    rw [ha, neg_add_cancel]
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at ht
  obtain ⟨u, hu⟩ := ht
  refine ⟨u, LinearMap.ext fun x => ?_, LinearMap.ext fun x => ?_⟩
  · have h := LinearMap.congr_fun hu (x, 0)
    change u ((x : V) + (0 : H).val) = f x + g 0 at h
    simpa using h
  · have h := LinearMap.congr_fun hu (0, x)
    change u ((0 : L).val + (x : V)) = f 0 + g x at h
    simpa using h

theorem restr_sup_injective {V : Type*} [AddCommGroup V] [Module F V]
    {L H : Submodule F V} {f g : Dual ↥(L ⊔ H)}
    (hl : restr le_sup_left f = restr le_sup_left g)
    (hh : restr le_sup_right f = restr le_sup_right g) : f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨l, hL, h, hH, he⟩ := Submodule.mem_sup.mp x.prop
  let l0 : L := ⟨l, hL⟩
  let h0 : H := ⟨h, hH⟩
  have hx : Submodule.inclusion le_sup_left l0 + Submodule.inclusion le_sup_right h0 = x :=
    Subtype.ext he
  rw [← hx, map_add, map_add]
  exact congrArg₂ (· + ·) (LinearMap.congr_fun hl l0) (LinearMap.congr_fun hh h0)

theorem parentBoundary_le {V : Type*} [AddCommGroup V] [Module F V]
    (L H E : Submodule F V) : (L ⊔ H) ⊓ E ≤ L ⊓ (H ⊔ E) ⊔ H ⊓ (L ⊔ E) := by
  intro p hp
  obtain ⟨l, hl, h, hh, rfl⟩ := Submodule.mem_sup.mp hp.1
  have h₁ : l ∈ H ⊔ E := by
    have hs := Submodule.sub_mem_sup hp.2 hh
    simpa [sup_comm, sub_add_cancel] using hs
  have h₂ : h ∈ L ⊔ E := by
    have hs := Submodule.sub_mem_sup hp.2 hl
    simpa [sup_comm, add_comm l h, sub_add_cancel] using hs
  exact Submodule.add_mem_sup ⟨hl, h₁⟩ ⟨hh, h₂⟩

def LeftBoundary {V : Type*} [AddCommGroup V] [Module F V]
    (L H E : Submodule F V) : Submodule F V := L ⊓ (H ⊔ E)

def RightBoundary {V : Type*} [AddCommGroup V] [Module F V]
    (L H E : Submodule F V) : Submodule F V := H ⊓ (L ⊔ E)

def ParentBoundary {V : Type*} [AddCommGroup V] [Module F V]
    (L H E : Submodule F V) : Submodule F V := (L ⊔ H) ⊓ E

theorem split_glue {V : Type*} [AddCommGroup V] [Module F V]
    (L H E : Submodule F V) (f : Dual L) (g : Dual H) (p : Dual (ParentBoundary L H E)) :
    (∃ u : Dual V, u.comp (LeftBoundary L H E).subtype = restr inf_le_left f ∧
      u.comp (RightBoundary L H E).subtype = restr inf_le_left g ∧
      u.comp (ParentBoundary L H E).subtype = p) ↔
    (∃! u : Dual ↥(L ⊔ H), restr le_sup_left u = f ∧ restr le_sup_right u = g ∧
      restr inf_le_left u = p) := by
  constructor
  · rintro ⟨v, ha, hb, hp⟩
    have hagree : restr (S := L ⊓ H) inf_le_left f = restr inf_le_right g := by
      apply LinearMap.ext
      intro x
      let a : LeftBoundary L H E := ⟨x, x.prop.1, Submodule.mem_sup_left x.prop.2⟩
      let b : RightBoundary L H E := ⟨x, x.prop.2, Submodule.mem_sup_left x.prop.1⟩
      exact (LinearMap.congr_fun ha a).symm.trans (LinearMap.congr_fun hb b)
    obtain ⟨u, hul, hur⟩ := extend_agree L H f g hagree
    have hA (a : LeftBoundary L H E) : u (a : V) = v (a : V) :=
      (LinearMap.congr_fun hul ⟨a, a.prop.1⟩).trans (LinearMap.congr_fun ha a).symm
    have hB (b : RightBoundary L H E) : u (b : V) = v (b : V) :=
      (LinearMap.congr_fun hur ⟨b, b.prop.1⟩).trans (LinearMap.congr_fun hb b).symm
    let u' := u.comp (L ⊔ H).subtype
    refine ⟨u', ⟨hul, hur, ?_⟩, ?_⟩
    · apply LinearMap.ext
      intro x
      change u (x : V) = p x
      have hx := parentBoundary_le L H E x.prop
      obtain ⟨a, ha', b, hb', he⟩ := Submodule.mem_sup.mp hx
      have hval := LinearMap.congr_fun hp x
      change v (x : V) = p x at hval
      rw [← hval, ← he, map_add, map_add, hA ⟨a, ha'⟩, hB ⟨b, hb'⟩]
    · intro y hy
      exact restr_sup_injective (hy.1.trans hul.symm) (hy.2.1.trans hur.symm)
  · rintro ⟨u, hu, _⟩
    obtain ⟨v, hv⟩ := LinearMap.dualMap_surjective_of_injective (L ⊔ H).injective_subtype u
    refine ⟨v, LinearMap.ext fun a => ?_, LinearMap.ext fun b => ?_, LinearMap.ext fun x => ?_⟩
    · let y : L := ⟨a, a.prop.1⟩
      exact (LinearMap.congr_fun hv (Submodule.inclusion le_sup_left y)).trans
        (LinearMap.congr_fun hu.1 y)
    · let y : H := ⟨b, b.prop.1⟩
      exact (LinearMap.congr_fun hv (Submodule.inclusion le_sup_right y)).trans
        (LinearMap.congr_fun hu.2.1 y)
    · exact (LinearMap.congr_fun hv (Submodule.inclusion inf_le_left x)).trans
        (LinearMap.congr_fun hu.2.2 x)

abbrev Coord (k r : ℕ) := Fin k ⊕ (Bool × Fin (r + 1) × Fin k)
abbrev EqRow (k q : ℕ) := (Bool × Fin k) ⊕ Fin q

def flatten {k r : ℕ} : Tape k r ≃ₗ[F] (Coord k r → F) where
  toFun z := elim z.1 (fun p => z.2 p.1 p.2.1 p.2.2)
  invFun u := (fun j => u (.inl j), fun b t j => u (.inr (b,t,j)))
  left_inv _ := rfl
  right_inv x := by funext j; cases j <;> rfl
  map_add' _ _ := by funext j; cases j <;> rfl
  map_smul' _ _ := by funext j; cases j <;> rfl

def row {k r q : ℕ} (hk : 0 < k) (obs : Fin q → Tape k r) : EqRow k q → Coord k r → F :=
  elim (fun (p : Bool × Fin k) => Pi.single (.inr (p.1, 0, p.2)) 1 +
    Pi.single (.inl (ix hk (p.2.val + k - start p.1 % k))) 1)
    (fun i => flatten (obs i))

def rowTarget {k q : ℕ} (name : Bool → Word k) (rhs : Fin q → F) : EqRow k q → F :=
  elim (fun p => name p.1 p.2) rhs

lemma pair_flatten {k r : ℕ} (u v : Tape k r) :
    dotProduct (flatten u) (flatten v) = pair u v := by
  change (∑ j : Coord k r, flatten u j * flatten v j) =
    (∑ j : Fin k, u.1 j * v.1 j) +
      ∑ s : Fin (r + 1), ((∑ j : Fin k, u.2 false s j * v.2 false s j) +
        ∑ j : Fin k, u.2 true s j * v.2 true s j)
  rw [Fintype.sum_sum_type]
  congr 1
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  change (∑ b : Bool, ∑ s : Fin (r + 1), ∑ j : Fin k, u.2 b s j * v.2 b s j) = _
  rw [Finset.sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [Fintype.univ_bool]
  simp [add_comm]

lemma rowEquations {k r q : ℕ} (hk : 0 < k) (name : Bool → Word k)
    (obs : Fin q → Tape k r) (rhs : Fin q → F) (z : Tape k r) :
    (∀ i, dotProduct (row hk obs i) (flatten z) = rowTarget name rhs i) ↔
    (∀ b, z.2 b 0 = rot hk (start b) z.1 + name b) ∧ ∀ i, pair (obs i) z = rhs i := by
  have hinit (b : Bool) (j : Fin k) :
      dotProduct (row hk obs (.inl (b,j))) (flatten z) = z.2 b 0 j + rot hk (start b) z.1 j := by
    change dotProduct (Pi.single (.inr (b, 0, j)) 1 +
      Pi.single (.inl (ix hk (j.val + k - start b % k))) 1) (flatten z) = _
    rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct]
    rfl
  have hadd (a b c : F) : a + b = c ↔ a = b + c := by
    revert a b c
    decide
  constructor
  · intro h
    exact ⟨fun b => funext fun j => (hadd _ _ _).mp ((hinit b j).symm.trans (h (.inl (b,j)))),
      fun i => (pair_flatten (obs i) z).symm.trans (h (.inr i))⟩
  · rintro ⟨h0, hq⟩ (⟨b,j⟩ | i)
    · exact (hinit b j).trans ((hadd _ _ _).mpr (congrFun (h0 b) j))
    · exact (pair_flatten (obs i) z).trans (hq i)

def formLinear {k r : ℕ} (hk : 0 < k) (i : Leaf k r) (e : Fin 3) : Dual (Tape k r) where
  toFun := form hk i e
  map_add' u v := by
    rcases i with j | ⟨b,t,j⟩
    · rfl
    · by_cases h0 : e.val = 0
      · simp only [form, elim_inr, h0, ite_true, mix, Pi.add_apply, Prod.snd_add]
        abel
      · by_cases h1 : e.val = 1 <;>
          simp only [form, elim_inr, h0, h1, Nat.one_ne_zero, ite_true, ite_false, mix, rot,
            Pi.add_apply, Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' c v := by
    rcases i with j | ⟨b,t,j⟩
    · rfl
    · have hfst : (c • v).1 = fun j => c * v.1 j := rfl
      have hsnd : (c • v).2 = fun b t j => c * v.2 b t j := rfl
      by_cases h0 : e.val = 0
      · simp only [form, elim_inr, h0, ite_true, mix, hsnd, RingHom.id_apply, smul_eq_mul]
        ring
      · by_cases h1 : e.val = 1 <;>
          simp only [form, elim_inr, h0, h1, Nat.one_ne_zero, ite_true, ite_false, mix, rot,
            hfst, hsnd, RingHom.id_apply, smul_eq_mul] <;> ring

lemma allForms_separate {k r : ℕ} (hk : 0 < k) (name : Bool → Word k) {u v : Tape k r}
    (hu : ∀ b, u.2 b 0 = rot hk (start b) u.1 + name b)
    (hv : ∀ b, v.2 b 0 = rot hk (start b) v.1 + name b)
    (h : ∀ i e, form hk i e u = form hk i e v) : u = v := by
  have hk' : u.1 = v.1 := funext fun j => h (.inl j) 0
  refine Prod.ext hk' ?_
  funext b t
  induction t using Fin.induction with
  | zero => rw [hu, hv, hk']
  | succ t IH =>
    funext j
    have h2 := h (.inr (b,t,j)) 2
    change u.2 b t.succ j + mix hk b (u.2 b t.castSucc) j + rot hk (feed b t.val) u.1 j =
      v.2 b t.succ j + mix hk b (v.2 b t.castSucc) j + rot hk (feed b t.val) v.1 j at h2
    rw [IH, hk'] at h2
    exact add_right_cancel (add_right_cancel h2)

def selectedSpan {J V : Type*} [AddCommGroup V] [Module F V]
    (rows : J → V) (bag : J → Bool) : Submodule F V :=
  span F {v | ∃ j, bag j = true ∧ v = rows j}

lemma maskedSpan {J V : Type*} [AddCommGroup V] [Module F V]
    (rows : J → V) (bag : J → Bool) :
    span F (Set.range fun j => if bag j then rows j else 0) = selectedSpan rows bag := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨j, rfl⟩
    change (if bag j then rows j else 0) ∈ selectedSpan rows bag
    by_cases hj : bag j = true
    · rw [ite_eq_left hj]
      exact subset_span ⟨j, hj, rfl⟩
    · simp [hj]
  · apply span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    exact subset_span ⟨j, ite_eq_left hj⟩

lemma evalRange {J V : Type*} [Fintype J] [DecidableEq J] [AddCommGroup V] [Module F V]
    (rows : J → V) (x : J → F) :
    (∃ u : Dual V, ∀ j, u (rows j) = x j) ↔
      ∀ a : J → F, (∑ j, a j • rows j) = 0 → dotProduct x a = 0 := by
  let A : (J → F) →ₗ[F] V := Fintype.linearCombination F rows
  let ℓ := dotProductEquiv F J x
  have hsum (a : J → F) : A a = ∑ j, a j • rows j := by
    simp [A, Fintype.linearCombination_apply]
  have hunit (j : J) : A (Pi.single j 1) = rows j := by
    rw [hsum, sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_smul]
    · simp
  constructor
  · rintro ⟨u, hu⟩ a ha
    have h := congrArg u ha
    rw [map_sum, map_zero] at h
    simpa only [map_smul, hu, smul_eq_mul, dotProduct, mul_comm] using h
  · intro hx
    have hmem : ℓ ∈ (LinearMap.ker A).dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator _).mpr
      intro a ha
      exact hx a ((hsum a).symm.trans ha)
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
    obtain ⟨u, hu⟩ := hmem
    refine ⟨u, fun j => ?_⟩
    have h := LinearMap.congr_fun hu (Pi.single j 1)
    change u (A (Pi.single j 1)) = dotProduct x (Pi.single j 1) at h
    simpa [hunit, dotProduct_single] using h

end Helpers

-- Circuit, signed join, and projected-system helpers adapted from Zaz Brown.
-- Source: lean/PEqualNP/Outside/L_meta_33648.lean at 04168edab39014e515fbb09f71ba0651b69367a8.
-- Accepted in 2405e8184772d046cf97bcd918d1ca98d549a9ee, Apache-2.0.
-- Join wrapper chooses u = floor of half the total boundary dimension.

namespace Donor

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def val (gs : List Gate) (x : List Bool) (w : ℕ) : Bool := (run gs x).getD w false

def Good (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

def Cmp (ι κ : Type) (S : ℕ) (F : (ι → Bool) → κ → Bool) : Prop :=
  ∀ (n : ℕ) (gs : List Gate), Good n gs → 0 < n + gs.length →
    ∀ ws : ι → ℕ, (∀ j, ws j < n + gs.length) →
    ∃ (more : List Gate) (outs : κ → ℕ), Good n (gs ++ more) ∧ more.length ≤ S ∧
      (∀ k, outs k < n + gs.length + more.length) ∧
      ∀ x : List Bool, x.length = n → ∀ k,
        val (gs ++ more) x (outs k) = F (fun j => val gs x (ws j)) k

def Cb (ι : Type) (S : ℕ) (φ : (ι → Bool) → Bool) : Prop := Cmp ι Unit S (fun v _ => φ v)

def Cw (ι : Type) (W S : ℕ) (φ : (ι → Bool) → BitVec W) : Prop :=
  Cmp ι (Fin W) S (fun v i => (φ v).getLsbD i.val)

abbrev V (d : ℕ) := Fin d → ZMod 2

def bv {W : ℕ} (w : Fin W → Bool) : BitVec W := BitVec.ofFnLE w

def tab {α : Type} {W : ℕ} (v : α × Fin W → Bool) : α → BitVec W := fun x => bv (fun i => v (x, i))

def untab {α : Type} {W : ℕ} (T : α → BitVec W) : α × Fin W → Bool := fun p => (T p.1).getLsbD p.2.val

def mat {r c : ℕ} (v : Fin r × Fin c → Bool) : Matrix (Fin r) (Fin c) (ZMod 2) :=
  fun i j => if v (i, j) then 1 else 0

def sgn {W : ℕ} (b : ZMod 2) : BitVec W := if b = 0 then 1 else -1

def tmat {D : ℕ} (t s : Fin D) (c : Bool) : Matrix (Fin D) (Fin D) (ZMod 2) :=
  Matrix.transvection t s (if c then 1 else 0)

def zmat {D : ℕ} (q : Fin D) (c : Bool) : Matrix (Fin D) (Fin D) (ZMod 2) :=
  Matrix.diagonal (fun i => if i = q ∧ c = true then 0 else 1)

def rowAdd {D : ℕ} (t s : Fin D) (c : Bool) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  fun p => if p.1 = t then xor (M p) (c && M (s, p.2)) else M p

def gjCtl {D : ℕ} (e : Bool × Fin D × Fin D) (M : Fin D × Fin D → Bool) : Bool :=
  if e.1 then M (e.2.2, e.2.1) && M (e.2.1, e.2.1)
  else (decide (e.2.1 < e.2.2) || !M (e.2.2, e.2.2)) && M (e.2.2, e.2.1) && !M (e.2.1, e.2.1)

def gjT {D : ℕ} (e : Bool × Fin D × Fin D) : Fin D := if e.1 then e.2.2 else e.2.1
def gjS {D : ℕ} (e : Bool × Fin D × Fin D) : Fin D := if e.1 then e.2.1 else e.2.2

def gjStep {D : ℕ} (e : Bool × Fin D × Fin D) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  rowAdd (gjT e) (gjS e) (gjCtl e M) M

def sched (D : ℕ) : List (Bool × Fin D × Fin D) :=
  (List.finRange D).flatMap fun p =>
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (false, p, i)) ++
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (true, p, i))

def gj (D : ℕ) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  (sched D).foldl (fun M e => gjStep e M) M

def offdiag (D : ℕ) : List (Fin D × Fin D) :=
  ((List.finRange D).flatMap fun p => (List.finRange D).map fun q => (p, q)).filter
    (fun e => e.1 ≠ e.2)

def join3 {a b c : ℕ} (h : V a × V b × V c) : V (a + b + c) := fun j =>
  if h1 : j.val < a then h.1 ⟨j.val, h1⟩
  else if h2 : j.val < a + b then h.2.1 ⟨j.val - a, by omega⟩
  else h.2.2 ⟨j.val - (a + b), by omega⟩

def sysBits {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) :
    Fin (m + N + 1) × Fin (m + N + 1) → Bool := fun p =>
  if hi : p.1.val < m then
    (if hj : p.2.val < N then decide (Hf ⟨p.1.val, hi⟩ ⟨p.2.val, hj⟩ ≠ 0)
     else if p.2.val = N then decide (rhs ⟨p.1.val, hi⟩ ≠ 0) else false)
  else false

def cl (m : ℕ) {N : ℕ} (p : Fin N) : Fin (m + N + 1) := ⟨p.val, by omega⟩
def rc (m N : ℕ) : Fin (m + N + 1) := ⟨N, by omega⟩

def pv {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) : Bool :=
  R (cl m p, cl m p)

def nx {a b c : ℕ} (j : Fin a) : Fin (a + b + c) := ⟨j.val, by omega⟩
def ny {a b c : ℕ} (j : Fin b) : Fin (a + b + c) := ⟨a + j.val, by omega⟩
def nz {a b c : ℕ} (j : Fin c) : Fin (a + b + c) := ⟨a + b + j.val, by omega⟩

theorem fa_run_append (gs more : List Gate) (x : List Bool) :
    run (gs ++ more) x = run more (run gs x) := by
  simp [run, List.foldl_append]

theorem fa_run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    have : run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl
    rw [this, ih]
    simp
    omega

theorem fa_run_getD (more : List Gate) (l : List Bool) (w : ℕ) (hw : w < l.length) :
    (run more l).getD w false = l.getD w false := by
  induction more generalizing l with
  | nil => simp [run]
  | cons g more ih =>
    have : run (g :: more) l =
        run more (l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) := rfl
    rw [this, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hw]

theorem fa_val_append (n : ℕ) (gs more : List Gate) (x : List Bool) (w : ℕ)
    (hx : x.length = n) (hw : w < n + gs.length) :
    val (gs ++ more) x w = val gs x w := by
  unfold val
  rw [fa_run_append]
  exact fa_run_getD _ _ _ (by rw [fa_run_length]; omega)

theorem fa_good_snoc (n : ℕ) (gs : List Gate) (g : Gate) (hg : Good n gs)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hin : ∀ i ∈ g.inputs, i < n + gs.length) :
    Good n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.1 hg' with h | h
    · exact hg.1 g' h
    · rw [List.mem_singleton.1 h]; exact ⟨hop, hl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [this] at hi
      exact hg.2 j hlt i hi
    · have hj' : j = gs.length := by omega
      subst hj'
      have : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [this] at hi
      exact hin i hi

theorem fa_val_snoc (n : ℕ) (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = n) :
    val (gs ++ [g]) x (n + gs.length) = g.op.eval (g.inputs.map fun i => val gs x i) := by
  unfold val
  rw [fa_run_append]
  have h1 : run [g] (run gs x) =
      run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := rfl
  rw [h1]
  have h2 : n + gs.length = (run gs x).length := by rw [fa_run_length]; omega
  rw [h2]
  simp [List.getD_eq_getElem?_getD]

theorem fa_gate {ι : Type} (op : GateOp)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (js : List ι)
    (hl : js.length ≤ 2) : Cmp ι Unit 1 (fun v _ => op.eval (js.map v)) := by
  intro n gs hg hpos ws hws
  refine ⟨[⟨op, js.map ws⟩], fun _ => n + gs.length, ?_, by simp, ?_, ?_⟩
  · refine fa_good_snoc n gs _ hg hop (by simpa using hl) ?_
    intro i hi
    simp only [List.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact hws j
  · intro _; simp
  · intro x hx _
    rw [fa_val_snoc n gs _ x hx]
    simp [List.map_map, Function.comp_def]

theorem Cmp.mono {ι κ : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    (h : Cmp ι κ S F) (hS : S ≤ S') : Cmp ι κ S' F := by
  intro n gs hg hpos ws hws
  obtain ⟨more, outs, h1, h2, h3, h4⟩ := h n gs hg hpos ws hws
  exact ⟨more, outs, h1, le_trans h2 hS, h3, h4⟩

theorem Cmp.congr {ι κ : Type} {S : ℕ} {F F' : (ι → Bool) → κ → Bool}
    (h : Cmp ι κ S F) (hF : ∀ v k, F v k = F' v k) : Cmp ι κ S F' := by
  have : F = F' := by funext v k; exact hF v k
  exact this ▸ h

theorem Cmp.wire {ι κ : Type} (σ : κ → ι) : Cmp ι κ 0 (fun v k => v (σ k)) := by
  intro n gs hg hpos ws hws
  refine ⟨[], fun k => ws (σ k), by simpa using hg, by simp, ?_, ?_⟩
  · intro k; simpa using hws (σ k)
  · intro x hx k; simp

theorem Cmp.comp {ι κ μ : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    {G : (κ → Bool) → μ → Bool} (h1 : Cmp ι κ S F) (h2 : Cmp κ μ S' G) :
    Cmp ι μ (S + S') (fun v => G (F v)) := by
  intro n gs hg hpos ws hws
  obtain ⟨m1, o1, g1, l1, b1, v1⟩ := h1 n gs hg hpos ws hws
  obtain ⟨m2, o2, g2, l2, b2, v2⟩ := h2 n (gs ++ m1) g1 (by simp; omega) o1
    (by intro j; simpa [Nat.add_assoc] using b1 j)
  refine ⟨m1 ++ m2, o2, by simpa [List.append_assoc] using g2, by simp; omega, ?_, ?_⟩
  · intro k; have := b2 k; simp at this ⊢; omega
  · intro x hx k
    rw [← List.append_assoc, v2 x hx k]
    congr 1
    funext j
    exact v1 x hx j

theorem Cmp.pair {ι κ κ' : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    {F' : (ι → Bool) → κ' → Bool} (h1 : Cmp ι κ S F) (h2 : Cmp ι κ' S' F') :
    Cmp ι (κ ⊕ κ') (S + S') (fun v => elim (F v) (F' v)) := by
  intro n gs hg hpos ws hws
  obtain ⟨m1, o1, g1, l1, b1, v1⟩ := h1 n gs hg hpos ws hws
  obtain ⟨m2, o2, g2, l2, b2, v2⟩ := h2 n (gs ++ m1) g1 (by simp; omega) ws
    (by intro j; have := hws j; simp; omega)
  refine ⟨m1 ++ m2, elim o1 o2, by simpa [List.append_assoc] using g2, by simp; omega, ?_, ?_⟩
  · intro k
    cases k with
    | inl k => have := b1 k; simp; omega
    | inr k => have := b2 k; simp at this ⊢; omega
  · intro x hx k
    cases k with
    | inl k =>
      simp only [elim_inl]
      rw [← List.append_assoc, fa_val_append n (gs ++ m1) m2 x _ hx (by
        have := b1 k; simp; omega)]
      exact v1 x hx k
    | inr k =>
      simp only [elim_inr]
      rw [← List.append_assoc, v2 x hx k]
      congr 1
      funext j
      exact fa_val_append n gs m1 x _ hx (hws j)

theorem Cmp.keep {ι κ : Type} {S : ℕ} {F : (ι → Bool) → κ → Bool} (h : Cmp ι κ S F) :
    Cmp ι (ι ⊕ κ) S (fun v => elim v (F v)) := by
  have := Cmp.pair (Cmp.wire (ι := ι) (fun k : ι => k)) h
  rw [Nat.zero_add] at this
  exact this

theorem Cmp.sel {ι ι' κ : Type} {S : ℕ} {F : (ι' → Bool) → κ → Bool} (σ : ι' → ι)
    (h : Cmp ι' κ S F) : Cmp ι κ S (fun v => F (fun j => v (σ j))) := by
  intro n gs hg hpos ws hws
  exact h n gs hg hpos (fun j => ws (σ j)) (fun j => hws (σ j))

theorem fa_pi_list {ι κ I : Type} {S : I → ℕ} {F : I → (ι → Bool) → κ → Bool}
    (h : ∀ i, Cmp ι κ (S i) (F i)) (L : List I) :
    ∀ (n : ℕ) (gs : List Gate), Good n gs → 0 < n + gs.length →
    ∀ ws : ι → ℕ, (∀ j, ws j < n + gs.length) →
    ∃ (more : List Gate) (outs : I × κ → ℕ), Good n (gs ++ more) ∧
      more.length ≤ (L.map S).sum ∧
      (∀ k, outs k < n + gs.length + more.length) ∧
      ∀ x : List Bool, x.length = n → ∀ p : I × κ, p.1 ∈ L →
        val (gs ++ more) x (outs p) = F p.1 (fun j => val gs x (ws j)) p.2 := by
  classical
  induction L with
  | nil =>
    intro n gs hg hpos ws hws
    refine ⟨[], fun _ => 0, by simpa using hg, by simp, ?_, ?_⟩
    · intro _; simpa using hpos
    · intro x hx p hp; simp at hp
  | cons i L ih =>
    intro n gs hg hpos ws hws
    obtain ⟨m1, o1, g1, l1, b1, v1⟩ := ih n gs hg hpos ws hws
    obtain ⟨m2, o2, g2, l2, b2, v2⟩ := h i n (gs ++ m1) g1 (by simp; omega) ws
      (by intro j; have := hws j; simp; omega)
    refine ⟨m1 ++ m2, fun p => if p.1 = i then o2 p.2 else o1 p,
      by simpa [List.append_assoc] using g2, by simp; omega, ?_, ?_⟩
    · intro k
      by_cases hk : k.1 = i
      · have := b2 k.2; simp [hk] at this ⊢; omega
      · have := b1 k; simp [hk]; omega
    · intro x hx p hp
      by_cases hk : p.1 = i
      · simp only [hk, ite_true]
        rw [← List.append_assoc, v2 x hx p.2]
        congr 1
        funext j
        exact fa_val_append n gs m1 x _ hx (hws j)
      · simp only [hk, ite_false]
        have hp' : p.1 ∈ L := by
          rcases List.mem_cons.1 hp with h' | h'
          · exact absurd h' hk
          · exact h'
        rw [← List.append_assoc, fa_val_append n (gs ++ m1) m2 x _ hx (by
          have := b1 p; simp; omega)]
        exact v1 x hx p hp'

theorem Cmp.pi {ι κ I : Type} [Fintype I] {S : I → ℕ} {F : I → (ι → Bool) → κ → Bool}
    (h : ∀ i, Cmp ι κ (S i) (F i)) : Cmp ι (I × κ) (∑ i, S i) (fun v p => F p.1 v p.2) := by
  intro n gs hg hpos ws hws
  obtain ⟨more, outs, g1, l1, b1, v1⟩ :=
    fa_pi_list h (Finset.univ : Finset I).toList n gs hg hpos ws hws
  rw [Finset.sum_map_toList] at l1
  exact ⟨more, outs, g1, l1, b1, fun x hx p => v1 x hx p (by simp)⟩

theorem Cmp.piU {ι κ I : Type} [Fintype I] {s : ℕ} {F : I → (ι → Bool) → κ → Bool}
    (h : ∀ i, Cmp ι κ s (F i)) : Cmp ι (I × κ) (card I * s) (fun v p => F p.1 v p.2) := by
  have := Cmp.pi h
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at this
  exact this

theorem Cmp.foldl {ι α : Type} {s : ℕ} (L : List α) (F : α → (ι → Bool) → ι → Bool)
    (h : ∀ e ∈ L, Cmp ι ι s (F e)) :
    Cmp ι ι (L.length * s) (fun v => L.foldl (fun acc e => F e acc) v) := by
  induction L with
  | nil =>
    have := Cmp.wire (ι := ι) (fun k : ι => k)
    simpa using this
  | cons e L ih =>
    have h1 := h e (by simp)
    have h2 := ih (fun e' he' => h e' (by simp [he']))
    have := Cmp.comp h1 h2
    refine Cmp.mono this ?_
    simp [Nat.succ_mul]
    omega

theorem Cmp.chain {ι σ : Type} (n s : ℕ) (c : ℕ → (ι → Bool) → σ → Bool)
    (G : ℕ → (ι ⊕ σ → Bool) → σ → Bool)
    (h0 : Cmp ι σ s (c 0))
    (hG : ∀ i < n, Cmp (ι ⊕ σ) σ s (G i))
    (hc : ∀ i < n, ∀ v, c (i + 1) v = G i (elim v (c i v))) :
    Cmp ι (Fin (n + 1) × σ) ((n + 1) * s) (fun v p => c p.1.val v p.2) := by
  induction n with
  | zero =>
    have := Cmp.comp h0 (Cmp.wire (fun p : Fin 1 × σ => p.2))
    refine Cmp.congr (Cmp.mono this (by omega)) ?_
    intro v p
    have : p.1.val = 0 := by omega
    rw [this]
  | succ n ih =>
    have A := ih (fun i hi => hG i (by omega)) (fun i hi => hc i (by omega))
    have B := Cmp.sel (ι := ι ⊕ (Fin (n + 1) × σ))
      (fun j : ι ⊕ σ => Sum.map (fun k : ι => k) (fun k : σ => (Fin.last n, k)) j)
      (hG n (by omega))
    have C := Cmp.comp (Cmp.comp A.keep B.keep)
      (Cmp.wire (fun p : Fin (n + 2) × σ =>
        if hp : p.1.val < n + 1 then
          (inl (inr (⟨p.1.val, hp⟩, p.2)) : (ι ⊕ (Fin (n + 1) × σ)) ⊕ σ)
        else inr p.2))
    refine Cmp.congr (Cmp.mono C (by simp [Nat.succ_mul])) ?_
    intro v p
    by_cases hp : p.1.val < n + 1
    · simp [hp]
    · have hp' : p.1.val = n + 1 := by omega
      simp only [hp, ↓reduceDIte, elim_inr]
      rw [hp', hc n (by omega) v]
      congr 1
      funext j
      cases j with
      | inl j => simp
      | inr j => simp

theorem Cb.mono {ι : Type} {S S' : ℕ} {φ : (ι → Bool) → Bool} (h : Cb ι S φ) (hS : S ≤ S') :
    Cb ι S' φ := Cmp.mono h hS

theorem Cb.congr {ι : Type} {S : ℕ} {φ φ' : (ι → Bool) → Bool} (h : Cb ι S φ)
    (hF : ∀ v, φ v = φ' v) : Cb ι S φ' := Cmp.congr h (fun v _ => hF v)

theorem Cb.var {ι : Type} (i : ι) : Cb ι 0 (fun v => v i) := Cmp.wire (fun _ => i)

theorem Cb.const {ι : Type} (b : Bool) : Cb ι 1 (fun _ => b) := by
  cases b with
  | false =>
    have := fa_gate (ι := ι) GateOp.or (by simp) [] (by simp)
    exact Cmp.congr this (fun v k => by simp [GateOp.eval])
  | true =>
    have := fa_gate (ι := ι) GateOp.and (by simp) [] (by simp)
    exact Cmp.congr this (fun v k => by simp [GateOp.eval])

theorem Cb.not {ι : Type} {S : ℕ} {φ : (ι → Bool) → Bool} (h : Cb ι S φ) :
    Cb ι (S + 1) (fun v => !φ v) := by
  have g := fa_gate (ι := Unit) GateOp.not (by simp) [()] (by simp)
  have := Cmp.comp h g
  exact Cmp.congr this (fun v k => by simp [GateOp.eval])

theorem Cb.and {ι : Type} {S S' : ℕ} {φ ψ : (ι → Bool) → Bool} (h : Cb ι S φ) (h' : Cb ι S' ψ) :
    Cb ι (S + S' + 1) (fun v => φ v && ψ v) := by
  have g := fa_gate (ι := Unit ⊕ Unit) GateOp.and (by simp) [inl (), inr ()] (by simp)
  have := Cmp.comp (Cmp.pair h h') g
  exact Cmp.congr this (fun v k => by simp [GateOp.eval])

theorem Cb.or {ι : Type} {S S' : ℕ} {φ ψ : (ι → Bool) → Bool} (h : Cb ι S φ) (h' : Cb ι S' ψ) :
    Cb ι (S + S' + 1) (fun v => φ v || ψ v) := by
  have g := fa_gate (ι := Unit ⊕ Unit) GateOp.or (by simp) [inl (), inr ()] (by simp)
  have := Cmp.comp (Cmp.pair h h') g
  exact Cmp.congr this (fun v k => by simp [GateOp.eval])

theorem Cb.xor {ι : Type} {S S' : ℕ} {φ ψ : (ι → Bool) → Bool} (h : Cb ι S φ) (h' : Cb ι S' ψ) :
    Cb ι (S + S' + 4) (fun v => xor (φ v) (ψ v)) := by
  have l : Cb (Unit ⊕ Unit) 0 (fun v => v (inl ())) := Cb.var _
  have r : Cb (Unit ⊕ Unit) 0 (fun v => v (inr ())) := Cb.var _
  have g := Cb.and (Cb.or l r) (Cb.not (Cb.and l r))
  have := Cmp.comp (Cmp.pair h h') g
  refine Cmp.congr (Cmp.mono this (by omega)) ?_
  intro v k
  simp only [elim_inl, elim_inr]
  cases φ v <;> cases ψ v <;> rfl

theorem Cb.mux {ι : Type} {S S' S'' : ℕ} {χ φ ψ : (ι → Bool) → Bool} (hc : Cb ι S χ)
    (h : Cb ι S' φ) (h' : Cb ι S'' ψ) :
    Cb ι (S + S' + S'' + 4) (fun v => if χ v then φ v else ψ v) := by
  have c : Cb ((Unit ⊕ Unit) ⊕ Unit) 0 (fun v => v (inl (inl ()))) := Cb.var _
  have l : Cb ((Unit ⊕ Unit) ⊕ Unit) 0 (fun v => v (inl (inr ()))) := Cb.var _
  have r : Cb ((Unit ⊕ Unit) ⊕ Unit) 0 (fun v => v (inr ())) := Cb.var _
  have g := Cb.or (Cb.and c l) (Cb.and (Cb.not c) r)
  have := Cmp.comp (Cmp.pair (Cmp.pair hc h) h') g
  refine Cmp.congr (Cmp.mono this (by omega)) ?_
  intro v k
  simp only [elim_inl, elim_inr]
  cases χ v <;> cases φ v <;> cases ψ v <;> rfl

theorem Cb.comp {ι κ : Type} {S S' : ℕ} {F : (ι → Bool) → κ → Bool} {φ : (κ → Bool) → Bool}
    (h : Cmp ι κ S F) (h' : Cb κ S' φ) : Cb ι (S + S') (fun v => φ (F v)) := Cmp.comp h h'

theorem fa_listOr {ι I : Type} {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) (L : List I) :
    Cb ι (L.length * (s + 1) + 1) (fun v => L.any (fun i => φ i v)) := by
  induction L with
  | nil => simpa using Cb.const (ι := ι) false
  | cons i L ih =>
    refine Cb.congr (Cb.mono (Cb.or (h i) ih) ?_) (fun v => by simp)
    simp [Nat.succ_mul]
    omega

theorem fa_listAnd {ι I : Type} {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) (L : List I) :
    Cb ι (L.length * (s + 1) + 1) (fun v => L.all (fun i => φ i v)) := by
  induction L with
  | nil => simpa using Cb.const (ι := ι) true
  | cons i L ih =>
    refine Cb.congr (Cb.mono (Cb.and (h i) ih) ?_) (fun v => by simp)
    simp [Nat.succ_mul]
    omega

theorem fa_listXor {ι I : Type} {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) (L : List I) :
    Cb ι (L.length * (s + 4) + 1)
      (fun v => L.foldr (fun i acc => xor (φ i v) acc) false) := by
  induction L with
  | nil => simpa using Cb.const (ι := ι) false
  | cons i L ih =>
    refine Cb.congr (Cb.mono (Cb.xor (h i) ih) ?_) (fun v => by simp)
    simp [Nat.succ_mul]
    omega

theorem fa_xor_sum {I : Type} (p : I → Bool) (L : List I) :
    L.foldr (fun i acc => xor (p i) acc) false =
      decide ((L.map (fun i => if p i = true then 1 else 0)).sum % 2 = 1) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]
    cases hp : p i
    · simp
    · simp only [ite_true, Bool.true_xor]
      by_cases hq : (L.map (fun i => if p i = true then 1 else 0)).sum % 2 = 1
      · have : (1 + (L.map (fun i => if p i = true then 1 else 0)).sum) % 2 ≠ 1 := by omega
        simp [hq, this]
      · have : (1 + (L.map (fun i => if p i = true then 1 else 0)).sum) % 2 = 1 := by omega
        simp [hq, this]

theorem Cb.bigOr {ι I : Type} [Fintype I] {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (card I * (s + 1) + 1) (fun v => decide (∃ i, φ i v = true)) := by
  have := fa_listOr h (Finset.univ : Finset I).toList
  rw [Finset.length_toList, Finset.card_univ] at this
  refine Cb.congr this (fun v => ?_)
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true]

theorem Cb.bigAnd {ι I : Type} [Fintype I] {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (card I * (s + 1) + 1) (fun v => decide (∀ i, φ i v = true)) := by
  have := fa_listAnd h (Finset.univ : Finset I).toList
  rw [Finset.length_toList, Finset.card_univ] at this
  refine Cb.congr this (fun v => ?_)
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true]

theorem Cb.bigXor {ι I : Type} [Fintype I] {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (card I * (s + 4) + 1)
      (fun v => decide ((Finset.univ.filter (fun i => φ i v = true)).card % 2 = 1)) := by
  have := fa_listXor h (Finset.univ : Finset I).toList
  rw [Finset.length_toList, Finset.card_univ] at this
  refine Cb.congr this (fun v => ?_)
  rw [fa_xor_sum (fun i => φ i v), Finset.sum_map_toList, Finset.card_filter]

theorem Cmp.ofBits {ι κ : Type} [Fintype κ] {s : ℕ} {F : (ι → Bool) → κ → Bool}
    (h : ∀ k, Cb ι s (fun v => F v k)) : Cmp ι κ (card κ * s) F := by
  have := Cmp.comp (Cmp.piU (I := κ) (κ := Unit) (F := fun k v _ => F v k) h)
    (Cmp.wire (fun k : κ => (k, ())))
  exact this

theorem getLsbD_bv {W : ℕ} (w : Fin W → Bool) (i : Fin W) : (bv w).getLsbD i.val = w i := by
  simp [bv]

theorem bv_getLsbD {W : ℕ} (x : BitVec W) : bv (fun i : Fin W => x.getLsbD i.val) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [bv, hi]

theorem tab_untab {α : Type} {W : ℕ} (T : α → BitVec W) : tab (untab T) = T := by
  funext x
  show bv (fun i : Fin W => (T x).getLsbD i.val) = T x
  exact bv_getLsbD _

theorem untab_tab {α : Type} {W : ℕ} (v : α × Fin W → Bool) : untab (tab v) = v := by
  funext p
  show (bv (fun i => v (p.1, i))).getLsbD p.2.val = v p
  exact getLsbD_bv _ _

theorem Cw.mono {ι : Type} {W S S' : ℕ} {φ : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (hS : S ≤ S') : Cw ι W S' φ := Cmp.mono h hS

theorem Cw.congr {ι : Type} {W S : ℕ} {φ φ' : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (hF : ∀ v, φ v = φ' v) : Cw ι W S φ' := Cmp.congr h (fun v _ => by rw [hF v])

theorem Cw.var {ι : Type} {W : ℕ} (σ : Fin W → ι) : Cw ι W 0 (fun v => bv (fun i => v (σ i))) :=
  Cmp.congr (Cmp.wire σ) (fun v k => (getLsbD_bv (fun i => v (σ i)) k).symm)

theorem Cw.comp {ι κ : Type} {W S S' : ℕ} {F : (ι → Bool) → κ → Bool}
    {φ : (κ → Bool) → BitVec W} (h : Cmp ι κ S F) (h' : Cw κ W S' φ) :
    Cw ι W (S + S') (fun v => φ (F v)) := Cmp.comp h h'

theorem Cw.ofBits {ι : Type} {W s : ℕ} {φ : (ι → Bool) → BitVec W}
    (h : ∀ i : Fin W, Cb ι s (fun v => (φ v).getLsbD i.val)) : Cw ι W (W * s) φ := by
  have := Cmp.ofBits (F := fun v (i : Fin W) => (φ v).getLsbD i.val) h
  rw [card_fin] at this
  exact this

theorem Cw.const {ι : Type} {W : ℕ} (c : BitVec W) : Cw ι W W (fun _ => c) := by
  have := Cw.ofBits (ι := ι) (φ := fun _ => c) (s := 1) (fun i => Cb.const _)
  rw [Nat.mul_one] at this
  exact this

theorem fb_addcore (W : ℕ) (c0 : Bool) :
    Cmp (Fin W ⊕ Fin W) (Fin W) (13 * (W + 1))
      (fun u i => (bv (fun j => u (inl j)) + bv (fun j => u (inr j)) +
        BitVec.setWidth W (BitVec.ofBool c0)).getLsbD i.val) := by
  have hch := Cmp.chain (ι := Fin W ⊕ Fin W) (σ := Unit) W 5
    (fun i u _ => BitVec.carry i (bv (fun j => u (inl j))) (bv (fun j => u (inr j))) c0)
    (fun i w _ => if h : i < W then
      ((w (inl (inl ⟨i, h⟩)) && w (inl (inr ⟨i, h⟩)) ||
        w (inl (inl ⟨i, h⟩)) && w (inr ())) ||
        w (inl (inr ⟨i, h⟩)) && w (inr ())) else false)
    (by
      refine Cmp.mono (Cmp.congr (Cb.const c0) ?_) (by omega)
      intro v k
      cases c0 <;> simp [BitVec.carry, Nat.mod_one])
    (by
      intro i hi
      have h := Cb.or (Cb.or (Cb.and (Cb.var (ι := (Fin W ⊕ Fin W) ⊕ Unit) (inl (inl ⟨i, hi⟩)))
          (Cb.var (inl (inr ⟨i, hi⟩))))
        (Cb.and (Cb.var (inl (inl ⟨i, hi⟩))) (Cb.var (inr ()))))
        (Cb.and (Cb.var (inl (inr ⟨i, hi⟩))) (Cb.var (inr ())))
      refine Cmp.mono (Cmp.congr h ?_) (by omega)
      intro v k
      simp [hi])
    (by
      intro i hi u
      funext k
      have hx : (bv (fun j => u (inl j))).getLsbD i = u (inl ⟨i, hi⟩) :=
        getLsbD_bv (fun j => u (inl j)) ⟨i, hi⟩
      have hy : (bv (fun j => u (inr j))).getLsbD i = u (inr ⟨i, hi⟩) :=
        getLsbD_bv (fun j => u (inr j)) ⟨i, hi⟩
      rw [BitVec.carry_succ, hx, hy]
      simp only [dite_true, hi, elim_inl, elim_inr, Bool.atLeastTwo])
  have hk := Cmp.keep hch
  have hb : Cmp ((Fin W ⊕ Fin W) ⊕ Fin (W + 1) × Unit) (Fin W) (card (Fin W) * 8)
      (fun w i => xor (w (inl (inl i)))
        (xor (w (inl (inr i))) (w (inr ((⟨i.val, by omega⟩ : Fin (W + 1)), ()))))) := by
    apply Cmp.ofBits
    intro i
    exact Cb.mono (Cb.xor (Cb.var (inl (inl i)))
      (Cb.xor (Cb.var (inl (inr i))) (Cb.var (inr ((⟨i.val, by omega⟩ : Fin (W + 1)), ()))))) (by omega)
  refine Cmp.mono (Cmp.congr (Cmp.comp hk hb) ?_) (by rw [card_fin]; omega)
  intro v i
  rw [BitVec.getLsbD_add_add_bool i.isLt]
  have hx : (bv (fun j => v (inl j))).getLsbD i.val = v (inl i) :=
    getLsbD_bv (fun j => v (inl j)) i
  have hy : (bv (fun j => v (inr j))).getLsbD i.val = v (inr i) :=
    getLsbD_bv (fun j => v (inr j)) i
  rw [hx, hy]
  rfl

theorem fb_adc {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (c0 : Bool)
    (h : Cw ι W S φ) (h' : Cw ι W S' ψ) :
    Cw ι W (S + S' + 13 * (W + 1))
      (fun v => φ v + ψ v + BitVec.setWidth W (BitVec.ofBool c0)) := by
  refine Cmp.congr (Cmp.comp (Cmp.pair h h') (fb_addcore W c0)) ?_
  intro v i
  simp only [elim_inl, elim_inr]
  rw [bv_getLsbD, bv_getLsbD]

theorem fb_not {ι : Type} {W S : ℕ} {φ : (ι → Bool) → BitVec W} (h : Cw ι W S φ) :
    Cw ι W (S + W) (fun v => ~~~ φ v) := by
  have hb : Cmp (Fin W) (Fin W) (card (Fin W) * 1) (fun u i => !u i) := by
    apply Cmp.ofBits
    intro i
    exact Cb.mono (Cb.not (Cb.var i)) (by omega)
  refine Cmp.mono (Cmp.congr (Cmp.comp h hb) ?_) (by rw [card_fin]; omega)
  intro v i
  simp

theorem Cw.add {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (h' : Cw ι W S' ψ) : Cw ι W (S + S' + 20 * (W + 1)) (fun v => φ v + ψ v) := by
  refine Cw.mono (Cw.congr (fb_adc false h h') ?_) (by omega)
  intro v
  simp

theorem fb_add13 {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (h' : Cw ι W S' ψ) : Cw ι W (S + S' + 13 * (W + 1)) (fun v => φ v + ψ v) := by
  refine Cw.congr (fb_adc false h h') ?_
  intro v
  simp

theorem fb_sub_eq {W : ℕ} (x y : BitVec W) :
    x + ~~~ y + BitVec.setWidth W (BitVec.ofBool true) = x - y := by
  rw [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp

theorem Cw.sub {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (h' : Cw ι W S' ψ) : Cw ι W (S + S' + 20 * (W + 1)) (fun v => φ v - ψ v) := by
  refine Cw.mono (Cw.congr (fb_adc true h (fb_not h')) ?_) (by omega)
  intro v
  exact fb_sub_eq _ _

theorem fb_term (W k : ℕ) :
    Cw (Fin W ⊕ Fin W) W W
      (fun u => if (bv (fun j => u (inr j))).getLsbD k = true
        then bv (fun j => u (inl j)) <<< k else 0) := by
  have hb := Cw.ofBits (ι := Fin W ⊕ Fin W) (W := W) (s := 1)
    (φ := fun u => if (bv (fun j => u (inr j))).getLsbD k = true
        then bv (fun j => u (inl j)) <<< k else 0)
    (by
      intro i
      by_cases hk : k ≤ i.val
      · have hkW : k < W := lt_of_le_of_lt hk i.isLt
        refine Cb.congr (Cb.and (Cb.var (inr ⟨k, hkW⟩))
          (Cb.var (inl ⟨i.val - k, by omega⟩))) ?_
        intro v
        have hy : (bv (fun j => v (inr j))).getLsbD k = v (inr ⟨k, hkW⟩) :=
          getLsbD_bv (fun j => v (inr j)) ⟨k, hkW⟩
        have hx : (bv (fun j => v (inl j))).getLsbD (i.val - k)
            = v (inl ⟨i.val - k, by omega⟩) :=
          getLsbD_bv (fun j => v (inl j)) ⟨i.val - k, by omega⟩
        rw [hy]
        cases hv : v (inr ⟨k, hkW⟩)
        · simp
        · simp [i.isLt, Nat.not_lt.mpr hk]
          rw [← hx, BitVec.getLsbD_eq_getElem]
      · refine Cb.congr (Cb.const false) ?_
        intro v
        have hlt : i.val < k := Nat.lt_of_not_le hk
        split_ifs <;> simp [hlt])
  rw [Nat.mul_one] at hb
  exact hb

theorem fb_mulrec (W s : ℕ) :
    Cw (Fin W ⊕ Fin W) W (W + s * (W + 13 * (W + 1)))
      (fun u => (bv (fun j => u (inl j))).mulRec (bv (fun j => u (inr j))) s) := by
  induction s with
  | zero =>
    refine Cw.mono (Cw.congr (fb_term W 0) ?_) (by omega)
    intro v
    rw [BitVec.mulRec_zero_eq]
    simp
  | succ s ih =>
    refine Cw.mono (Cw.congr (fb_add13 ih (fb_term W (s + 1))) ?_) (by
      have := Nat.add_one_mul s (W + 13 * (W + 1)); omega)
    intro v
    rw [BitVec.mulRec_succ_eq]

theorem Cw.mul {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (h : Cw ι W S φ)
    (h' : Cw ι W S' ψ) : Cw ι W (S + S' + 30 * (W + 1) ^ 2) (fun v => φ v * ψ v) := by
  refine Cmp.mono (Cmp.congr (Cmp.comp (Cmp.pair h h') (fb_mulrec W W)) ?_) (by nlinarith)
  intro v i
  simp only [elim_inl, elim_inr]
  rw [bv_getLsbD, bv_getLsbD, BitVec.getLsbD_mul]

theorem Cw.mux {ι : Type} {W S S' S'' : ℕ} {χ : (ι → Bool) → Bool} {φ ψ : (ι → Bool) → BitVec W}
    (hc : Cb ι S χ) (h : Cw ι W S' φ) (h' : Cw ι W S'' ψ) :
    Cw ι W (S + S' + S'' + 4 * W) (fun v => if χ v then φ v else ψ v) := by
  have hb : Cmp (Unit ⊕ (Fin W ⊕ Fin W)) (Fin W) (card (Fin W) * 4)
      (fun w i => if w (inl ()) then w (inr (inl i)) else w (inr (inr i))) := by
    apply Cmp.ofBits
    intro i
    exact Cb.mono (Cb.mux (Cb.var (inl ())) (Cb.var (inr (inl i)))
      (Cb.var (inr (inr i)))) (by omega)
  refine Cmp.mono (Cmp.congr (Cmp.comp (Cmp.pair hc (Cmp.pair h h')) hb) ?_)
    (by rw [card_fin]; omega)
  intro v i
  simp only [elim_inl, elim_inr]
  cases χ v <;> simp

theorem Cmp.ofWords {ι α : Type} [Fintype α] {W s : ℕ} {G : (ι → Bool) → α → BitVec W}
    (h : ∀ x : α, Cw ι W s (fun v => G v x)) :
    Cmp ι (α × Fin W) (card α * s) (fun v => untab (G v)) := by
  exact Cmp.piU (κ := Fin W) (F := fun x v i => (G v x).getLsbD i.val) h

theorem fc_rowAdd_false {D : ℕ} (t s : Fin D) (M : Fin D × Fin D → Bool) :
    rowAdd t s false M = M := by
  funext p
  simp [rowAdd]

theorem fc_rowAdd_mat {D : ℕ} (t s : Fin D) (hts : t ≠ s) (c : Bool)
    (M : Fin D × Fin D → Bool) :
    mat M = tmat t s c * mat (rowAdd t s c M) := by
  ext i j
  by_cases hi : i = t
  · subst hi
    rw [tmat, Matrix.transvection_mul_apply_same]
    simp only [mat, rowAdd, if_true, if_neg (Ne.symm hts)]
    cases M (i, j) <;> cases c <;> cases M (s, j) <;> decide
  · rw [tmat, Matrix.transvection_mul_apply_of_ne _ _ _ _ hi]
    simp [mat, rowAdd, hi]

theorem fc_tmat_sq {D : ℕ} (t s : Fin D) (hts : t ≠ s) (c : Bool) :
    tmat t s c * tmat t s c = 1 := by
  rw [tmat, Matrix.transvection_mul_transvection_same _ _ hts]
  have : ((if c = true then (1 : ZMod 2) else 0) + (if c = true then (1 : ZMod 2) else 0)) = 0 := by
    cases c <;> decide
  rw [this, Matrix.transvection_zero]

theorem fc_gjTS {D : ℕ} (e : Bool × Fin D × Fin D) (he : e.2.1 ≠ e.2.2) : gjT e ≠ gjS e := by
  unfold gjT gjS
  split
  · exact he.symm
  · exact he

theorem gjStep_mat {D : ℕ} (e : Bool × Fin D × Fin D) (he : e.2.1 ≠ e.2.2)
    (M : Fin D × Fin D → Bool) :
    mat M = tmat (gjT e) (gjS e) (gjCtl e M) * mat (gjStep e M) :=
  fc_rowAdd_mat _ _ (fc_gjTS e he) _ M

theorem sched_ne {D : ℕ} (e : Bool × Fin D × Fin D) (he : e ∈ sched D) : e.2.1 ≠ e.2.2 := by
  unfold sched at he
  rw [List.mem_flatMap] at he
  obtain ⟨p, _, hp⟩ := he
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · rw [List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [List.mem_filter] at hi
    have := hi.2
    simp at this
    exact fun h => this h.symm
  · rw [List.mem_map] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [List.mem_filter] at hi
    have := hi.2
    simp at this
    exact fun h => this h.symm

theorem fc_equiv_list {D : ℕ} (l : List (Bool × Fin D × Fin D))
    (hl : ∀ e ∈ l, e.2.1 ≠ e.2.2) (M : Fin D × Fin D → Bool) :
    ∃ U U' : Matrix (Fin D) (Fin D) (ZMod 2),
      mat (l.foldl (fun M e => gjStep e M) M) = U * mat M ∧
      mat M = U' * mat (l.foldl (fun M e => gjStep e M) M) := by
  induction l generalizing M with
  | nil => exact ⟨1, 1, by simp, by simp⟩
  | cons e l ih =>
    have he := hl e (List.mem_cons_self)
    obtain ⟨U, U', h1, h2⟩ := ih (fun e' h' => hl e' (List.mem_cons_of_mem _ h')) (gjStep e M)
    have hs := gjStep_mat e he M
    have hs' : mat (gjStep e M) = tmat (gjT e) (gjS e) (gjCtl e M) * mat M := by
      rw [hs, ← mul_assoc, fc_tmat_sq _ _ (fc_gjTS e he), one_mul]
    refine ⟨U * tmat (gjT e) (gjS e) (gjCtl e M), tmat (gjT e) (gjS e) (gjCtl e M) * U', ?_, ?_⟩
    · rw [List.foldl_cons, h1, hs', mul_assoc]
    · rw [List.foldl_cons, mul_assoc, ← h2]
      exact hs

theorem gj_equiv {D : ℕ} (M : Fin D × Fin D → Bool) :
    ∃ U U' : Matrix (Fin D) (Fin D) (ZMod 2),
      mat (gj D M) = U * mat M ∧ mat M = U' * mat (gj D M) :=
  fc_equiv_list (sched D) (fun e he => sched_ne e he) M

def fc_Inv {D : ℕ} (k : ℕ) (M : Fin D × Fin D → Bool) : Prop :=
  (∀ q : Fin D, q.val < k → M (q, q) = true → ∀ i, M (i, q) = decide (i = q)) ∧
  (∀ i q : Fin D, q.val < k → (k ≤ i.val ∨ M (i, i) = false) → M (i, q) = false) ∧
  (∀ p q : Fin D, q < p → p.val < k → M (p, p) = true → M (p, q) = false)

theorem fc_Inv_congr {D : ℕ} (k : ℕ) (M M' : Fin D × Fin D → Bool)
    (h : ∀ i q : Fin D, q.val < k → M' (i, q) = M (i, q)) (hI : fc_Inv k M) : fc_Inv k M' := by
  obtain ⟨ha, hb, hc⟩ := hI
  refine ⟨?_, ?_, ?_⟩
  · intro q hq hqq i
    rw [h _ _ hq] at hqq ⊢
    exact ha q hq hqq i
  · intro i q hq hfree
    rw [h _ _ hq]
    apply hb i q hq
    by_cases hi : i.val < k
    · rcases hfree with hf | hf
      · omega
      · right
        rw [← h _ _ hi]
        exact hf
    · left
      omega
  · intro p q hqp hp hpp
    have hq : q.val < k := by
      have : q.val < p.val := hqp
      omega
    rw [h _ _ hq]
    rw [h _ _ hp] at hpp
    exact hc p q hqp hp hpp

private theorem foldIdle {α β : Type*} (step : α → β → α) (l : List β) (s : α)
    (h : ∀ x, step s x = s) : l.foldl step s = s := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, h, ih]

theorem fc_A_id {D : ℕ} (p : Fin D) (l : List (Fin D)) (M : Fin D × Fin D → Bool)
    (hp : M (p,p) = true) : l.foldl (fun M i => gjStep (false,p,i) M) M = M := by
  apply foldIdle
  intro i
  simp [gjStep,gjCtl,hp,fc_rowAdd_false]

theorem fc_B_id {D : ℕ} (p : Fin D) (l : List (Fin D)) (M : Fin D × Fin D → Bool)
    (hp : M (p,p) = false) : l.foldl (fun M i => gjStep (true,p,i) M) M = M := by
  apply foldIdle
  intro i
  simp [gjStep,gjCtl,hp,fc_rowAdd_false]

theorem fc_A {D : ℕ} (p : Fin D) (k : ℕ) (hk : p.val = k) (l : List (Fin D))
    (hl : ∀ i ∈ l, i ≠ p) (M : Fin D × Fin D → Bool) (hI : fc_Inv k M) :
    fc_Inv k (l.foldl (fun M i => gjStep (false, p, i) M) M) ∧
    ((l.foldl (fun M i => gjStep (false, p, i) M) M) (p, p) = false →
      l.foldl (fun M i => gjStep (false, p, i) M) M = M ∧
      ∀ i ∈ l, (p < i ∨ M (i, i) = false) → M (i, p) = false) := by
  induction l with
  | nil => simp [hI]
  | cons i l ih =>
    rw [List.foldl_cons]
    cases h : gjCtl (false,p,i) M
    · have idle : gjStep (false,p,i) M = M := by rw [gjStep,h,fc_rowAdd_false]
      rw [idle]
      obtain ⟨inv,no⟩ := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
      refine ⟨inv,fun hp => ⟨(no hp).1,?_⟩⟩
      intro j hj free
      rcases List.mem_cons.mp hj with rfl | hj
      · have hd : M (p,p) = false := by simpa only [(no hp).1] using hp
        rcases free with hg|hg <;> simpa [gjCtl,hg,hd] using h
      · exact (no hp).2 j hj free
    · have hh : (p < i ∨ M (i,i) = false) ∧ M (i,p) = true ∧ M (p,p) = false := by
        simpa only [gjCtl,Bool.false_eq_true,ite_false,Bool.and_eq_true,Bool.or_eq_true,
          decide_eq_true_eq,Bool.not_eq_true',and_assoc] using h
      have pivot : gjStep (false,p,i) M (p,p) = true := by
        simp [gjStep,gjT,gjS,rowAdd,h,hh.2.1,hh.2.2]
      rw [fc_A_id _ _ _ pivot]
      refine ⟨fc_Inv_congr k M _ ?_ hI,by simp [pivot]⟩
      intro j q hq
      have zero : M (i,q) = false := hI.2.1 i q hq
        (hh.1.imp (fun h => by have : p.val < i.val := h; omega) id)
      simp [gjStep,gjT,gjS,rowAdd,h,zero]

theorem fc_B {D : ℕ} (p : Fin D) (k : ℕ) (l : List (Fin D))
    (hl : ∀ i ∈ l, i ≠ p) (M : Fin D × Fin D → Bool) (hpp : M (p, p) = true)
    (hrow : ∀ q : Fin D, q.val < k → M (p, q) = false) :
    (∀ i q : Fin D, q.val < k →
      (l.foldl (fun M i => gjStep (true, p, i) M) M) (i, q) = M (i, q)) ∧
    (∀ j, (l.foldl (fun M i => gjStep (true, p, i) M) M) (p, j) = M (p, j)) ∧
    (∀ i, i ≠ p → (i ∈ l ∨ M (i, p) = false) →
      (l.foldl (fun M i => gjStep (true, p, i) M) M) (i, p) = false) := by
  induction l generalizing M with
  | nil => simp
  | cons i l ih =>
    have ne := hl i List.mem_cons_self
    let A := gjStep (true,p,i) M
    have stay (j) : A (p,j) = M (p,j) := by simp [A,gjStep,gjT,gjS,rowAdd,Ne.symm ne]
    have past (j q) (hq : q.val < k) : A (j,q) = M (j,q) := by
      simp [A,gjStep,gjT,gjS,rowAdd,hrow q hq]
    have col (j) : A (j,p) = if j = i then false else M (j,p) := by
      by_cases h : j = i <;> simp [A,gjStep,gjT,gjS,rowAdd,gjCtl,h,hpp]
    rw [List.foldl_cons]
    obtain ⟨a,b,c⟩ := ih (fun j h => hl j (List.mem_cons_of_mem _ h)) A
      ((stay p).trans hpp) (fun q hq => (stay q).trans (hrow q hq))
    refine ⟨fun j q hq => (a j q hq).trans (past j q hq),
      fun j => (b j).trans (stay j),fun j hj h => c j hj ?_⟩
    by_cases e : j = i
    · simp [col,e]
    · simpa [col,e] using h

def fc_col {D : ℕ} (p : Fin D) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  ((List.finRange D).filter (fun i => i ≠ p)).foldl (fun M i => gjStep (true, p, i) M)
    (((List.finRange D).filter (fun i => i ≠ p)).foldl (fun M i => gjStep (false, p, i) M) M)

theorem fc_gj_eq {D : ℕ} (M : Fin D × Fin D → Bool) :
    gj D M = (List.finRange D).foldl (fun M p => fc_col p M) M := by
  unfold gj sched
  rw [List.foldl_flatMap]
  simp only [List.foldl_append, List.foldl_map, fc_col]

theorem columnInvariantStep {D : Nat} (p : Fin D) (M : Fin D × Fin D → Bool)
    (old : fc_Inv p.val M)
    (pivot : M (p,p) = true → ∀ i, M (i,p) = decide (i = p))
    (free : ∀ i : Fin D, (p.val + 1 ≤ i.val ∨ M (i,i) = false) → M (i,p) = false) :
    fc_Inv (p.val+1) M := by
  have earlier (i : Fin D) (h : i.val < p.val+1) (ne : i ≠ p) : i.val < p.val := by
    have hv : i.val ≠ p.val := fun he => ne (Fin.ext he)
    omega
  refine ⟨?_,?_ ,?_⟩
  · intro q hq hd i
    by_cases e : q = p
    · subst q
      exact pivot hd i
    · exact old.1 q (earlier q hq e) hd i
  · intro i q hq hf
    by_cases e : q = p
    · subst q
      exact free i hf
    · apply old.2.1 i q (earlier q hq e)
      exact hf.imp (fun hi => by omega) id
  · intro i q hqi hi hdiag
    by_cases e : i = p
    · subst i
      exact old.2.1 p q hqi (Or.inl le_rfl)
    · exact old.2.2 i q hqi (earlier i hi e) hdiag

theorem fc_colInv {D : Nat} (p : Fin D) (M : Fin D × Fin D → Bool)
    (hI : fc_Inv p.val M) : fc_Inv (p.val+1) (fc_col p M) := by
  let rows := (List.finRange D).filter (fun i => i ≠ p)
  have member (i : Fin D) : i ∈ rows ↔ i ≠ p := by simp [rows]
  let A := rows.foldl (fun x i => gjStep (false,p,i) x) M
  obtain ⟨invA,noPivot⟩ := fc_A p p.val rfl rows (fun i h => (member i).mp h) M hI
  change fc_Inv p.val A at invA
  change fc_Inv (p.val+1) (rows.foldl (fun x i => gjStep (true,p,i) x) A)
  cases hp : A (p,p)
  · rw [fc_B_id p rows A hp]
    obtain ⟨unchanged,allZero⟩ := noPivot hp
    apply columnInvariantStep p A invA
    · simp [hp]
    · intro i hi
      by_cases e : i = p
      · rwa [e]
      · rw [show A = M from unchanged] at hi ⊢
        exact allZero i ((member i).mpr e) hi
  · obtain ⟨past,stay,clear⟩ := fc_B p p.val rows (fun i h => (member i).mp h) A hp
      (fun q hq => invA.2.1 p q hq (Or.inl le_rfl))
    let B := rows.foldl (fun x i => gjStep (true,p,i) x) A
    have hb : B (p,p) = true := (stay p).trans hp
    have cleared (i : Fin D) (ne : i ≠ p) : B (i,p) = false :=
      clear i ne (Or.inl ((member i).mpr ne))
    apply columnInvariantStep p B (fc_Inv_congr p.val A B past invA)
    · intro _ i
      by_cases e : i = p
      · subst i
        simpa using hb
      · simpa [e] using cleared i e
    · intro i h
      apply cleared
      intro e
      subst i
      simp [hb] at h

theorem fc_fold {D : ℕ} (l : List (Fin D)) :
    ∀ (k : ℕ), (∀ i (h : i < l.length), (l[i]).val = k + i) →
    ∀ M : Fin D × Fin D → Bool, fc_Inv k M →
      fc_Inv (k + l.length) (l.foldl (fun M p => fc_col p M) M) := by
  induction l with
  | nil => intro k _ M hI; exact hI
  | cons p l ih =>
    intro k hidx M hI
    have hp : p.val = k := by
      have := hidx 0 (by simp)
      simpa using this
    rw [List.foldl_cons]
    have h1 : fc_Inv (k + 1) (fc_col p M) := by
      have := fc_colInv p M (hp ▸ hI)
      rw [hp] at this
      exact this
    have h2 := ih (k + 1) (fun i h => by
      have := hidx (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      omega) (fc_col p M) h1
    have e : k + (p :: l).length = k + 1 + l.length := by simp; omega
    rw [e]
    exact h2

theorem fc_gjInv {D : ℕ} (M : Fin D × Fin D → Bool) : fc_Inv D (gj D M) := by
  rw [fc_gj_eq]
  have h0 : fc_Inv 0 M := by
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      omega
    · intro i q hq
      omega
    · intro p q _ hp
      omega
  have := fc_fold (List.finRange D) 0 (fun i h => by simp) M h0
  simpa using this

theorem gj_pivcol {D : ℕ} (M : Fin D × Fin D → Bool) (p : Fin D) (hp : gj D M (p, p) = true)
    (i : Fin D) : gj D M (i, p) = decide (i = p) :=
  (fc_gjInv M).1 p p.isLt hp i

theorem gj_zerorow {D : ℕ} (M : Fin D × Fin D → Bool) (q : Fin D) (hq : gj D M (q, q) = false)
    (j : Fin D) : gj D M (q, j) = false :=
  (fc_gjInv M).2.1 q j j.isLt (Or.inr hq)

theorem gj_upper {D : ℕ} (M : Fin D × Fin D → Bool) (p q : Fin D) (h : q < p) :
    gj D M (p, q) = false := by
  by_cases hp : gj D M (p, p) = true
  · exact (fc_gjInv M).2.2 p q h p.isLt hp
  · exact gj_zerorow M p (by simpa using hp) q

theorem fc_zprod {D : ℕ} (c : Fin D → Bool) (l : List (Fin D)) :
    (l.map (fun q => zmat q (c q))).prod =
      Matrix.diagonal (fun i => if i ∈ l ∧ c i = true then (0 : ZMod 2) else 1) := by
  induction l with
  | nil => simp
  | cons q l ih =>
    rw [List.map_cons, List.prod_cons, ih, zmat, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hiq : i = q
    · subst hiq
      by_cases hc : c i = true
      · simp [hc]
      · simp [hc]
    · simp [hiq]

theorem fc_cols {D : Nat} (R : Fin D × Fin D → Bool)
    (hpiv : ∀ p, R (p,p) = true → ∀ i, R (i,p) = decide (i = p))
    (hzero : ∀ q, R (q,q) = false → ∀ j, R (q,j) = false)
    (l : List (Fin D × Fin D)) (hnd : l.Nodup) (hne : ∀ e ∈ l, e.1 ≠ e.2) :
    ∀ A : Matrix (Fin D) (Fin D) (ZMod 2),
      (∀ i j, A i j = if i = j then (if R (i,i) then 1 else 0)
        else if (i,j) ∈ l then 0 else if R (i,j) then 1 else 0) →
      A * (l.map (fun e => tmat e.1 e.2 (R e))).prod = mat R := by
  induction l with
  | nil =>
    intro A hA
    simp only [List.map_nil,List.prod_nil,mul_one]
    ext i j
    by_cases eq : i = j
    · subst j
      simp [hA,mat]
    · simp [hA,mat,eq]
  | cons e l ih =>
    rcases e with ⟨p,q⟩
    intro A hA
    have hpq := hne (p,q) List.mem_cons_self
    obtain ⟨fresh,distinct⟩ := List.nodup_cons.mp hnd
    have diag (on : R (p,q) = true) : R (p,p) = true := by
      cases h : R (p,p)
      · rw [hzero p h q] at on
        contradiction
      · rfl
    rw [List.map_cons,List.prod_cons,← mul_assoc]
    apply ih distinct (fun e he => hne e (List.mem_cons_of_mem _ he))
    intro i j
    by_cases ej : j = q
    · subst j
      rw [tmat,Matrix.mul_transvection_apply_same]
      by_cases ei : i = p
      · subst i
        by_cases on : R (p,q) = true
        · simp [hA,hpq,fresh,on,diag on]
        · simp [hA,hpq,fresh,on]
      · have zero : (if R (p,q) then (1 : ZMod 2) else 0) * A i p = 0 := by
          by_cases on : R (p,q) = true
          · simp [on,hA,ei,hpiv p (diag on) i]
          · simp [on]
        rw [zero,add_zero]
        simp [hA,Prod.ext_iff,ei]
    · rw [tmat,Matrix.mul_transvection_apply_of_ne _ _ _ _ ej]
      simp [hA,Prod.ext_iff,ej]

theorem fc_offdiag_nodup (D : ℕ) : (offdiag D).Nodup := by
  unfold offdiag
  apply List.Nodup.filter
  exact (List.nodup_finRange D).product (List.nodup_finRange D)

theorem fc_mem_offdiag {D : ℕ} (e : Fin D × Fin D) : e ∈ offdiag D ↔ e.1 ≠ e.2 := by
  unfold offdiag
  rw [List.mem_filter]
  constructor
  · intro h
    simpa using h.2
  · intro h
    refine ⟨?_, by simpa using h⟩
    rw [List.mem_flatMap]
    exact ⟨e.1, List.mem_finRange _, List.mem_map.2 ⟨e.2, List.mem_finRange _, rfl⟩⟩

theorem gj_final {D : ℕ} (M : Fin D × Fin D → Bool) :
    mat (gj D M) =
      ((List.finRange D).map (fun q => zmat q (!(gj D M) (q, q)))).prod *
      ((offdiag D).map (fun e => tmat e.1 e.2 ((gj D M) e))).prod := by
  rw [fc_zprod (fun q => !(gj D M) (q, q))]
  symm
  apply fc_cols (gj D M) (gj_pivcol M) (gj_zerorow M) (offdiag D) (fc_offdiag_nodup D)
    (fun e he => (fc_mem_offdiag e).1 he)
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, if_pos rfl]
    cases gj D M (i, i) <;> simp
  · rw [Matrix.diagonal_apply_ne _ hij, if_neg hij, if_pos ((fc_mem_offdiag (i, j)).2 hij)]

def phiCost (D sE sZ : ℕ) : ℕ := 4 * (D + 1) ^ 2 * (sE + sZ + 16 * (D + 1) ^ 2)

def fd_step {D : ℕ} {τ : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (e : Bool × Fin D × Fin D) (v : (Fin D × Fin D) ⊕ τ → Bool) : (Fin D × Fin D) ⊕ τ → Bool :=
  elim (gjStep e (fun p => v (inl p)))
    (Φ (tmat (gjT e) (gjS e) (gjCtl e (fun p => v (inl p)))) (fun k => v (inr k)))

def fd_stepG {D : ℕ} {τ α : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (g : α → (Fin D × Fin D → Bool) → Matrix (Fin D) (Fin D) (ZMod 2))
    (x : α) (v : (Fin D × Fin D) ⊕ τ → Bool) : (Fin D × Fin D) ⊕ τ → Bool :=
  elim (fun p => v (inl p))
    (Φ (g x (fun p => v (inl p))) (fun k => v (inr k)))

theorem fd_fold1 {D : ℕ} {τ : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (hmul : ∀ A B T, Φ (A * B) T = Φ B (Φ A T)) :
    ∀ (L : List (Bool × Fin D × Fin D)), (∀ e ∈ L, e.2.1 ≠ e.2.2) →
    ∀ v : (Fin D × Fin D) ⊕ τ → Bool,
      (fun p => (L.foldl (fun acc e => fd_step Φ e acc) v) (inl p)) =
        L.foldl (fun M e => gjStep e M) (fun p => v (inl p)) ∧
      Φ (mat (fun p => v (inl p))) (fun k => v (inr k)) =
        Φ (mat (fun p => (L.foldl (fun acc e => fd_step Φ e acc) v) (inl p)))
          (fun k => (L.foldl (fun acc e => fd_step Φ e acc) v) (inr k)) := by
  intro L
  induction L with
  | nil => intro _ v; exact ⟨rfl, rfl⟩
  | cons e L ih =>
    intro hL v
    have he := hL e (List.mem_cons_self)
    obtain ⟨h1, h2⟩ := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) (fd_step Φ e v)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, ← h2]
    rw [gjStep_mat e he (fun p => v (inl p)), hmul]
    rfl

theorem fd_foldG {D : ℕ} {τ α : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (h1 : ∀ T, Φ 1 T = T) (hmul : ∀ A B T, Φ (A * B) T = Φ B (Φ A T))
    (g : α → (Fin D × Fin D → Bool) → Matrix (Fin D) (Fin D) (ZMod 2)) :
    ∀ (L : List α) (v : (Fin D × Fin D) ⊕ τ → Bool),
      (fun p => (L.foldl (fun acc x => fd_stepG Φ g x acc) v) (inl p)) =
        (fun p => v (inl p)) ∧
      (fun k => (L.foldl (fun acc x => fd_stepG Φ g x acc) v) (inr k)) =
        Φ ((L.map (fun x => g x (fun p => v (inl p)))).prod) (fun k => v (inr k)) := by
  intro L
  induction L with
  | nil => intro v; exact ⟨rfl, by simp [h1]⟩
  | cons x L ih =>
    intro v
    obtain ⟨h2, h3⟩ := ih (fd_stepG Φ g x v)
    refine ⟨h2, ?_⟩
    rw [List.foldl_cons, h3, List.map_cons, List.prod_cons, hmul]
    rfl

theorem fd_ctl {D : ℕ} {τ : Type} (e : Bool × Fin D × Fin D) :
    Cb ((Fin D × Fin D) ⊕ τ) 6 (fun v => gjCtl e (fun p => v (inl p))) := by
  rcases e with ⟨k, p, i⟩
  cases k
  · have h := Cb.and (Cb.and (Cb.or (Cb.const (ι := (Fin D × Fin D) ⊕ τ) (decide (p < i)))
        (Cb.not (Cb.var (inl (i, i))))) (Cb.var (inl (i, p))))
        (Cb.not (Cb.var (inl (p, p))))
    refine Cb.mono (Cb.congr h ?_) (by norm_num)
    intro v
    simp [gjCtl]
  · have h := Cb.and (Cb.var (ι := (Fin D × Fin D) ⊕ τ) (inl (i, p)))
        (Cb.var (inl (p, p)))
    refine Cb.mono (Cb.congr h ?_) (by norm_num)
    intro v
    simp [gjCtl]

theorem fd_bit {D : ℕ} {τ : Type} (e : Bool × Fin D × Fin D) (p : Fin D × Fin D) :
    Cb ((Fin D × Fin D) ⊕ τ) 11 (fun v => gjStep e (fun p => v (inl p)) p) := by
  by_cases h : p.1 = gjT e
  · have hh := Cb.xor (Cb.var (ι := (Fin D × Fin D) ⊕ τ) (inl p))
        (Cb.and (fd_ctl (τ := τ) e) (Cb.var (inl (gjS e, p.2))))
    refine Cb.mono (Cb.congr hh ?_) (by norm_num)
    intro v
    simp [gjStep, rowAdd, h]
  · refine Cb.mono (Cb.congr (Cb.var (inl p)) ?_) (by norm_num)
    intro v
    simp [gjStep, rowAdd, h]



theorem fd_cost_le (D sE sZ : ℕ) :
    card (Fin D × Fin D) * 11 + (6 + 0 + sE) ≤ sE + sZ + 16 * (D + 1) ^ 2 := by
  have h : card (Fin D × Fin D) = D * D := by simp
  rw [h]
  nlinarith [Nat.zero_le D, Nat.zero_le sZ]

theorem fd_cmp_step {D : ℕ} {τ : Type} [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool)) (sE sZ : ℕ)
    (hE : ∀ t s : Fin D, t ≠ s →
      Cmp (Unit ⊕ τ) τ sE (fun v => Φ (tmat t s (v (inl ()))) (fun k => v (inr k))))
    (e : Bool × Fin D × Fin D) (he : e.2.1 ≠ e.2.2) :
    Cmp ((Fin D × Fin D) ⊕ τ) ((Fin D × Fin D) ⊕ τ) (sE + sZ + 16 * (D + 1) ^ 2)
      (fd_step Φ e) := by
  have hm : Cmp ((Fin D × Fin D) ⊕ τ) (Fin D × Fin D) (card (Fin D × Fin D) * 11)
      (fun v => gjStep e (fun p => v (inl p))) :=
    Cmp.ofBits (fun p => fd_bit e p)
  have hc : Cmp ((Fin D × Fin D) ⊕ τ) Unit 6
      (fun v _ => gjCtl e (fun p => v (inl p))) := fd_ctl e
  have ht := Cmp.comp (Cmp.pair hc (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) inr))
    (hE (gjT e) (gjS e) (fc_gjTS e he))
  have h := Cmp.pair hm ht
  refine Cmp.mono (Cmp.congr h ?_) (fd_cost_le D sE sZ)
  intro v k
  rfl

theorem fd_cmp_stepZ {D : ℕ} {τ : Type} [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool)) (sE sZ : ℕ)
    (hZ : ∀ q : Fin D,
      Cmp (Unit ⊕ τ) τ sZ (fun v => Φ (zmat q (v (inl ()))) (fun k => v (inr k))))
    (q : Fin D) :
    Cmp ((Fin D × Fin D) ⊕ τ) ((Fin D × Fin D) ⊕ τ) (sE + sZ + 16 * (D + 1) ^ 2)
      (fd_stepG Φ (fun (q : Fin D) M => zmat q (!M (q, q))) q) := by
  have hc : Cmp ((Fin D × Fin D) ⊕ τ) Unit (0 + 1)
      (fun v _ => !v (inl (q, q))) := Cb.not (Cb.var (inl (q, q)))
  have ht := Cmp.comp (Cmp.pair hc (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) inr))
    (hZ q)
  have h := Cmp.pair (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := Fin D × Fin D) inl) ht
  refine Cmp.mono (Cmp.congr h ?_) (by nlinarith [Nat.zero_le D, Nat.zero_le sE])
  intro v k
  rfl

theorem fd_cmp_stepT {D : ℕ} {τ : Type} [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool)) (sE sZ : ℕ)
    (hE : ∀ t s : Fin D, t ≠ s →
      Cmp (Unit ⊕ τ) τ sE (fun v => Φ (tmat t s (v (inl ()))) (fun k => v (inr k))))
    (e : Fin D × Fin D) (he : e.1 ≠ e.2) :
    Cmp ((Fin D × Fin D) ⊕ τ) ((Fin D × Fin D) ⊕ τ) (sE + sZ + 16 * (D + 1) ^ 2)
      (fd_stepG Φ (fun (e : Fin D × Fin D) M => tmat e.1 e.2 (M e)) e) := by
  have hc : Cmp ((Fin D × Fin D) ⊕ τ) Unit 0
      (fun v _ => v (inl e)) := Cb.var (inl e)
  have ht := Cmp.comp (Cmp.pair hc (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) inr))
    (hE e.1 e.2 he)
  have h := Cmp.pair (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := Fin D × Fin D) inl) ht
  refine Cmp.mono (Cmp.congr h ?_) (by nlinarith [Nat.zero_le D, Nat.zero_le sZ])
  intro v k
  rfl

theorem fd_flatMap_len {α β : Type} (c : ℕ) (f : α → List β) (hf : ∀ x, (f x).length ≤ c) :
    ∀ L : List α, (L.flatMap f).length ≤ L.length * c := by
  intro L
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := hf x
    omega

theorem fd_sched_len (D : ℕ) : (sched D).length ≤ 2 * (D * D) := by
  have h := fd_flatMap_len (2 * D) (fun p : Fin D =>
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (false, p, i)) ++
    ((List.finRange D).filter (fun i => i ≠ p)).map (fun i => (true, p, i))) (by
      intro p
      have h1 : ((List.finRange D).filter (fun i => decide (i ≠ p))).length ≤ D := by
        have := List.length_filter_le (fun i => decide (i ≠ p)) (List.finRange D)
        simpa using this
      simp only [List.length_append, List.length_map]
      omega) (List.finRange D)
  have h2 : (List.finRange D).length = D := List.length_finRange
  rw [h2] at h
  have h3 : D * (2 * D) = 2 * (D * D) := by ring
  rw [h3] at h
  exact h

theorem fd_offdiag_len (D : ℕ) : (offdiag D).length ≤ D * D := by
  have h := fd_flatMap_len D (fun p : Fin D => (List.finRange D).map fun q => (p, q)) (by
      intro p
      simp) (List.finRange D)
  have h2 : (List.finRange D).length = D := List.length_finRange
  rw [h2] at h
  exact le_trans (List.length_filter_le _ _) h

theorem fd_offdiag_ne {D : ℕ} (e : Fin D × Fin D) (he : e ∈ offdiag D) : e.1 ≠ e.2 := by
  unfold offdiag at he
  have := (List.mem_filter.mp he).2
  simpa using this

theorem cmp_phi (D : ℕ) (τ : Type) [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (h1 : ∀ T, Φ 1 T = T) (hmul : ∀ A B T, Φ (A * B) T = Φ B (Φ A T))
    (sE sZ : ℕ)
    (hE : ∀ t s : Fin D, t ≠ s →
      Cmp (Unit ⊕ τ) τ sE (fun v => Φ (tmat t s (v (inl ()))) (fun k => v (inr k))))
    (hZ : ∀ q : Fin D,
      Cmp (Unit ⊕ τ) τ sZ (fun v => Φ (zmat q (v (inl ()))) (fun k => v (inr k)))) :
    Cmp ((Fin D × Fin D) ⊕ τ) τ (phiCost D sE sZ)
      (fun v => Φ (mat (fun p => v (inl p))) (fun k => v (inr k))) := by
  have c1 := Cmp.foldl (sched D) (fd_step Φ)
    (fun e he => fd_cmp_step Φ sE sZ hE e (sched_ne e he))
  have c2 := Cmp.foldl (List.finRange D)
    (fd_stepG Φ (fun (q : Fin D) M => zmat q (!M (q, q))))
    (fun q _ => fd_cmp_stepZ Φ sE sZ hZ q)
  have c3 := Cmp.foldl (offdiag D)
    (fd_stepG Φ (fun (e : Fin D × Fin D) M => tmat e.1 e.2 (M e)))
    (fun e he => fd_cmp_stepT Φ sE sZ hE e (fd_offdiag_ne e he))
  have c := Cmp.comp (Cmp.comp (Cmp.comp c1 c2) c3)
    (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) inr)
  refine Cmp.mono (Cmp.congr c ?_) ?_
  · intro v k
    obtain ⟨hM1, hT1⟩ := fd_fold1 Φ hmul (sched D) (fun e he => sched_ne e he) v
    obtain ⟨hM2, hT2⟩ := fd_foldG Φ h1 hmul (fun (q : Fin D) M => zmat q (!M (q, q)))
      (List.finRange D) ((sched D).foldl (fun acc e => fd_step Φ e acc) v)
    obtain ⟨_, hT3⟩ := fd_foldG Φ h1 hmul (fun (e : Fin D × Fin D) M => tmat e.1 e.2 (M e))
      (offdiag D) ((List.finRange D).foldl
        (fun acc x => fd_stepG Φ (fun (q : Fin D) M => zmat q (!M (q, q))) x acc)
        ((sched D).foldl (fun acc e => fd_step Φ e acc) v))
    refine (congrFun hT3 k).trans ?_
    rw [hM2, hT2, ← hmul, hT1, hM1]
    have hg : (sched D).foldl (fun M e => gjStep e M) (fun p => v (inl p)) =
        gj D (fun p => v (inl p)) := rfl
    rw [hg, ← gj_final]
  · have a1 := fd_sched_len D
    have a2 := fd_offdiag_len D
    have a3 : (List.finRange D).length = D := List.length_finRange
    rw [a3]
    unfold phiCost
    generalize sE + sZ + 16 * (D + 1) ^ 2 = s
    have : (sched D).length + D + (offdiag D).length ≤ 4 * (D + 1) ^ 2 := by nlinarith
    calc (sched D).length * s + D * s + (offdiag D).length * s + 0
        = ((sched D).length + D + (offdiag D).length) * s := by ring
      _ ≤ 4 * (D + 1) ^ 2 * s := Nat.mul_le_mul_right s this

def tcost (d k W : ℕ) : ℕ := 2 ^ 9 * (d + k + 2) ^ 4 * (W + 1) * 2 ^ (max d k)

def fp_ext (n : ℕ) {k : ℕ} (x : V k) : V n := fun j => if h : j.val < k then x ⟨j.val, h⟩ else 0

def fp_res {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : V n) : V k := fun j => x ⟨j.val, by omega⟩

def fp_pad (n : ℕ) {d k : ℕ} (B : Fin d × Fin k → Bool) : Fin n × Fin n → Bool := fun p =>
  if h : p.1.val < d ∧ p.2.val < k then B (⟨p.1.val, h.1⟩, ⟨p.2.val, h.2⟩) else false

theorem fp_res_ext {n k : ℕ} (hk : k ≤ n) (x : V k) : fp_res k hk (fp_ext n x) = x := by
  funext j
  simp [fp_res, fp_ext]

theorem fp_ext_inj (n : ℕ) {k : ℕ} (hk : k ≤ n) : Injective (fp_ext n (k := k)) := by
  intro x y h
  have := congrArg (fp_res k hk) h
  rwa [fp_res_ext, fp_res_ext] at this

theorem fp_pad_mulVec {n d k : ℕ} (hk : k ≤ n) (B : Fin d × Fin k → Bool)
    (lam : V k) :
    (mat (fp_pad n B)).mulVec (fp_ext n lam) = fp_ext n ((mat B).mulVec lam) := by
  funext a
  by_cases ha : a.val < d
  · have e1 : fp_ext n ((mat B).mulVec lam) a = (mat B).mulVec lam ⟨a.val, ha⟩ := by
      simp [fp_ext, ha]
    rw [e1]
    unfold Matrix.mulVec dotProduct
    symm
    apply Fintype.sum_of_injective (fun j : Fin k => (⟨j.val, by omega⟩ : Fin n))
    · intro x y h
      apply Fin.ext
      simpa using congrArg Fin.val h
    · intro b hb
      have hb' : ¬ b.val < k := by
        intro h
        exact hb ⟨⟨b.val, h⟩, rfl⟩
      simp [fp_ext, hb']
    · intro j
      simp [mat, fp_pad, fp_ext, ha]
  · have e1 : fp_ext n ((mat B).mulVec lam) a = 0 := by
      simp [fp_ext, ha]
    rw [e1]
    unfold Matrix.mulVec dotProduct
    apply sum_eq_zero
    intro b _
    simp [mat, fp_pad, ha]

theorem fp_cardV (n : ℕ) : card (V n) = 2 ^ n := by
  simp [V, ZMod.card]

theorem fp_arith (Q X A B Cc Y : ℕ) (hA : A ≤ Q) (hB : B ≤ X) (hC : Cc ≤ Q) (hY : Y ≤ 29 * X)
    (hQ : 1 ≤ Q) (hX : 1 ≤ X) : A + B + 4 * Cc * (Y + 16 * Cc) ≤ 512 * (Q * Q) * X := by
  have h1 : 4 * Cc * (Y + 16 * Cc) ≤ 4 * Q * (29 * X + 16 * Q) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : Q ≤ Q * X := Nat.le_mul_of_pos_right _ hX
  have h3 : Q * X ≤ Q * Q * X := by
    have : Q ≤ Q * Q := Nat.le_mul_of_pos_right _ hQ
    exact Nat.mul_le_mul_right _ this
  have h4 : X ≤ Q * X := Nat.le_mul_of_pos_left _ hQ
  have h5 : Q * Q ≤ Q * Q * X := Nat.le_mul_of_pos_right _ hX
  nlinarith [h1, h2, h3, h4, h5]



theorem fp_sum_eq {n W : ℕ} (f : V n → BitVec W) (z : V n) :
    (∑ x : V n, if x = z then f x else 0) = f z := by
  rw [sum_ite_eq' Finset.univ z f]
  simp

def fp_pullPhi (n W : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2)) (T : V n × Fin W → Bool) :
    V n × Fin W → Bool :=
  untab (fun x : V n => tab T (M.mulVec x))

def fp_pushPhi (n W : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2)) (T : V n × Fin W → Bool) :
    V n × Fin W → Bool :=
  untab (fun z : V n => ∑ x : V n, if M.transpose.mulVec x = z then tab T x else 0)

theorem fp_pull_one (n W : ℕ) (T : V n × Fin W → Bool) : fp_pullPhi n W 1 T = T := by
  unfold fp_pullPhi
  simp only [Matrix.one_mulVec]
  exact untab_tab T

theorem fp_pull_mul (n W : ℕ) (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (T : V n × Fin W → Bool) :
    fp_pullPhi n W (A * B) T = fp_pullPhi n W B (fp_pullPhi n W A T) := by
  unfold fp_pullPhi
  rw [tab_untab]
  simp only [Matrix.mulVec_mulVec]

theorem fp_pull_cw (n W : ℕ) (A : Bool → Matrix (Fin n) (Fin n) (ZMod 2)) (x : V n) :
    Cw (Unit ⊕ (V n × Fin W)) W (4 * W)
      (fun v => tab (fun k => v (inr k)) ((A (v (inl ()))).mulVec x)) := by
  have h := Cw.mux (Cb.var (inl () : Unit ⊕ (V n × Fin W)))
    (Cw.var (fun i : Fin W => (inr ((A true).mulVec x, i) : Unit ⊕ (V n × Fin W))))
    (Cw.var (fun i : Fin W => (inr ((A false).mulVec x, i) : Unit ⊕ (V n × Fin W))))
  refine (h.mono (by omega)).congr ?_
  intro v
  cases hv : v (inl ()) <;> simp [tab]

theorem fp_pull_step (n W : ℕ) (A : Bool → Matrix (Fin n) (Fin n) (ZMod 2)) :
    Cmp (Unit ⊕ (V n × Fin W)) (V n × Fin W) (card (V n) * (4 * W))
      (fun v => fp_pullPhi n W (A (v (inl ()))) (fun k => v (inr k))) := by
  unfold fp_pullPhi
  exact Cmp.ofWords (fun x => fp_pull_cw n W A x)

theorem fp_push_one (n W : ℕ) (T : V n × Fin W → Bool) : fp_pushPhi n W 1 T = T := by
  unfold fp_pushPhi
  simp only [Matrix.transpose_one, Matrix.one_mulVec]
  have : (fun z : V n => ∑ x : V n, if x = z then tab T x else 0) = tab T := by
    funext z
    exact fp_sum_eq _ z
  rw [this]
  exact untab_tab T

theorem fp_push_mul (n W : ℕ) (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (T : V n × Fin W → Bool) :
    fp_pushPhi n W (A * B) T = fp_pushPhi n W B (fp_pushPhi n W A T) := by
  unfold fp_pushPhi
  rw [tab_untab]
  congr 1
  funext z
  have e : ∀ y : V n, (if B.transpose.mulVec y = z then
      (∑ x : V n, if A.transpose.mulVec x = y then tab T x else 0) else 0) =
      ∑ x : V n, if A.transpose.mulVec x = y then
        (if B.transpose.mulVec y = z then tab T x else 0) else 0 := by
    intro y
    by_cases h : B.transpose.mulVec y = z
    · simp [h]
    · simp [h]
  simp only [e]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro x _
  rw [Finset.sum_ite_eq]
  simp [Matrix.transpose_mul, Matrix.mulVec_mulVec]

theorem fp_invol_sum {n W : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) (hA : A * A = 1)
    (f : V n → BitVec W) (z : V n) :
    (∑ x : V n, if A.mulVec x = z then f x else 0) = f (A.mulVec z) := by
  have key : ∀ x : V n, (A.mulVec x = z) ↔ (x = A.mulVec z) := by
    intro x
    constructor
    · intro h
      rw [← h, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
    · intro h
      rw [h, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
  simp only [key]
  exact fp_sum_eq _ _

theorem fp_tmat_sq {n : ℕ} (t s : Fin n) (hts : t ≠ s) (c : Bool) :
    (tmat t s c).transpose * (tmat t s c).transpose = 1 := by
  rw [← Matrix.transpose_mul]
  unfold tmat
  rw [Matrix.transvection_mul_transvection_same (h := hts)]
  have : ((if c = true then (1 : ZMod 2) else 0) + (if c = true then 1 else 0)) = 0 := by
    cases c
    · simp
    · exact (by decide : (1 : ZMod 2) + 1 = 0)
  rw [this, Matrix.transvection_zero, Matrix.transpose_one]

theorem fp_push_tmat (n W : ℕ) (t s : Fin n) (hts : t ≠ s) (c : Bool) (T : V n × Fin W → Bool) :
    fp_pushPhi n W (tmat t s c) T = fp_pullPhi n W ((tmat t s c).transpose) T := by
  unfold fp_pushPhi fp_pullPhi
  congr 1
  funext z
  exact fp_invol_sum _ (fp_tmat_sq t s hts c) _ z

theorem fp_zmat_false {n : ℕ} (q : Fin n) : zmat q false = 1 := by
  unfold zmat
  simp

theorem fp_zmat_true_mulVec {n : ℕ} (q : Fin n) (x : V n) :
    (zmat q true).transpose.mulVec x = Function.update x q 0 := by
  unfold zmat
  rw [Matrix.diagonal_transpose]
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : i = q
  · subst h
    simp
  · simp [h]

private theorem eraseCoord_iff {n : ℕ} (q : Fin n) (x z : V n) (hz : z q = 0) :
    Function.update x q 0 = z ↔ x = z ∨ x = Function.update z q 1 := by
  constructor
  · intro h
    have restore : Function.update z q (x q) = x := by
      rw [← h,Function.update_idem,Function.update_eq_self]
    rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) (x q) with h0|h1
    · exact Or.inl (by rw [← restore,h0,← hz,Function.update_eq_self])
    · exact Or.inr (by simpa only [h1] using restore.symm)
  · rintro (rfl | rfl)
    · rw [← hz,Function.update_eq_self]
    · rw [Function.update_idem,← hz,Function.update_eq_self]

theorem fp_zsum {n W : ℕ} (q : Fin n) (f : V n → BitVec W) (z : V n) :
    (∑ x : V n, if Function.update x q 0 = z then f x else 0) =
      if z q = 0 then f z + f (Function.update z q 1) else 0 := by
  by_cases hz : z q = 0
  · have ne : z ≠ Function.update z q 1 := by
      intro e
      have := congrFun e q
      simp [hz] at this
    rw [ite_eq_left hz,← fp_sum_eq f z, ← fp_sum_eq f (Function.update z q 1), ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro x _
    simp only [eraseCoord_iff q x z hz]
    by_cases h : x = z
    · subst h; simp [ne]
    · by_cases h' : x = Function.update z q 1 <;> simp [h,h',hz]
  · rw [ite_eq_right hz]
    apply sum_eq_zero
    intro x _
    apply ite_eq_right
    intro e
    exact False.elim (hz (by rw [← e,Function.update_self]))

theorem fp_push_z_cw (n W : ℕ) (q : Fin n) (z : V n) :
    Cw (Unit ⊕ (V n × Fin W)) W (25 * (W + 1))
      (fun v => ∑ x : V n, if (zmat q (v (inl ()))).transpose.mulVec x = z
        then tab (fun k => v (inr k)) x else 0) := by
  let get (x : V n) (i : Fin W) : Unit ⊕ (V n × Fin W) := inr (x,i)
  let dat (v : Unit ⊕ (V n × Fin W) → Bool) (x : V n) := tab (fun k => v (inr k)) x
  have fetch (x) : Cw _ W 0 (fun v => dat v x) := Cw.var (get x)
  have erase : Cw _ W (21 * (W+1)) (fun v => if z q = 0 then dat v z + dat v (Function.update z q 1) else 0) := by
    by_cases h : z q = 0
    · simpa only [ite_eq_left h] using ((fetch z).add (fetch (Function.update z q 1))).mono (by omega)
    · simpa only [ite_eq_right h] using (Cw.const (0 : BitVec W)).mono (by omega)
  refine ((Cw.mux (Cb.var (.inl ())) erase (fetch z)).mono (by omega)).congr ?_
  intro v
  cases e : v (.inl ()) <;> simp only [Bool.false_eq_true,ite_false,ite_true,fp_zmat_false,
    fp_zmat_true_mulVec,Matrix.transpose_one,Matrix.one_mulVec,fp_sum_eq,fp_zsum,dat]

theorem fp_push_z_step (n W : ℕ) (q : Fin n) :
    Cmp (Unit ⊕ (V n × Fin W)) (V n × Fin W) (card (V n) * (25 * (W + 1)))
      (fun v => fp_pushPhi n W (zmat q (v (inl ()))) (fun k => v (inr k))) := by
  unfold fp_pushPhi
  exact Cmp.ofWords (fun z => fp_push_z_cw n W q z)

theorem fp_push_t_step (n W : ℕ) (t s : Fin n) (hts : t ≠ s) :
    Cmp (Unit ⊕ (V n × Fin W)) (V n × Fin W) (card (V n) * (4 * W))
      (fun v => fp_pushPhi n W (tmat t s (v (inl ()))) (fun k => v (inr k))) := by
  have h := fp_pull_step n W (fun c => (tmat t s c).transpose)
  refine h.congr ?_
  intro v k
  rw [fp_push_tmat n W t s hts]

theorem ccOption {I J : Type} (s : J → Option I) :
    Cmp I J 1 (fun v j => (s j).elim false v) := by
  let f (j : J) : I ⊕ Unit := (s j).elim (.inr ()) inl
  have h := (Cmp.keep (Cb.const (ι := I) false)).comp (Cmp.wire f)
  refine (h.mono (by omega)).congr ?_
  intro v j
  cases e : s j <;> simp [f,e]

private theorem tableBound (d k W s t : ℕ) (h : s+t ≤ 29*((W+1)*2^(max d k))) :
    1 + phiCost (max d k) s t ≤ tcost d k W := by
  let Q := (d+k+2)^2
  let X := (W+1)*2^(max d k)
  have hQ : 1 ≤ Q := Nat.one_le_pow _ _ (by omega)
  have hX : 1 ≤ X := Nat.mul_pos (by omega) Nat.one_le_two_pow
  have hc : (max d k + 1)^2 ≤ Q := Nat.pow_le_pow_left (by omega) 2
  have b := fp_arith Q X 1 0 ((max d k + 1)^2) (s+t) hQ (Nat.zero_le _) hc h hQ hX
  simpa only [phiCost,tcost,Q,X,Nat.reducePow,Nat.add_zero, mul_assoc,← pow_add] using b

private abbrev TableBits (D W : ℕ) := V D × Fin W
private abbrev TableIn (D W : ℕ) := (Fin D × Fin D) ⊕ TableBits D W

private theorem tableRoute {I O : Type} (d k W s t : ℕ)
    (route : TableIn (max d k) W → Option I) (out : O → TableBits (max d k) W)
    {G : (TableIn (max d k) W → Bool) → TableBits (max d k) W → Bool}
    (hC : Cmp _ _ (phiCost (max d k) s t) G) (h : s+t ≤ 29*((W+1)*2^(max d k))) :
    Cmp I O (tcost d k W) (fun v p => G (fun j => (route j).elim false v) (out p)) := by
  have hc := (((ccOption route).comp hC).comp (Cmp.wire out))
  exact hc.mono (by simpa only [Nat.add_zero] using tableBound d k W s t h)

private def matrixRoute {n d k : ℕ} (p : Fin n × Fin n) : Option (Fin d × Fin k) :=
  if h : p.1.val < d ∧ p.2.val < k then some (⟨p.1.val,h.1⟩,⟨p.2.val,h.2⟩) else none

private theorem matrixRoute_eval {n d k : ℕ} (B : Fin d × Fin k → Bool) (p : Fin n × Fin n) :
    (matrixRoute p).elim false B = fp_pad n B p := by
  by_cases h : p.1.val < d ∧ p.2.val < k <;> simp [matrixRoute,fp_pad,h]

theorem cmp_pull (d k W : ℕ) :
    Cmp ((Fin d × Fin k) ⊕ (V d × Fin W)) (V k × Fin W) (tcost d k W)
      (fun v => untab (fun lam : V k =>
        tab (fun p => v (inr p)) ((mat (fun p => v (inl p))).mulVec lam))) := by
  let D := max d k
  let route : TableIn D W → Option ((Fin d × Fin k) ⊕ TableBits d W) :=
    elim (fun p => (matrixRoute p).map inl)
      (fun p => some (.inr (fp_res d (le_max_left d k) p.1,p.2)))
  let out (p : TableBits k W) : TableBits D W := (fp_ext D p.1,p.2)
  let S := card (V D) * (4*W)
  have mid := cmp_phi D (TableBits D W) (fp_pullPhi D W) (fp_pull_one _ _) (fp_pull_mul _ _)
    S S (fun t s _ => fp_pull_step _ _ (fun c => tmat t s c))
    (fun q => fp_pull_step _ _ (fun c => zmat q c))
  refine (tableRoute d k W S S route out mid ?_).congr ?_
  · simp only [S,fp_cardV,D]
    rw [← Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (29 * _) _]
    exact Nat.mul_le_mul_left _ (by omega)
  · intro v p
    have hM : (fun j => (route (.inl j)).elim false v) = fp_pad D (v ∘ inl) := by
      funext j
      change ((matrixRoute j).map inl).elim false v = _
      rw [← matrixRoute_eval]
      cases matrixRoute j <;> rfl
    simp only [fp_pullPhi, hM,out,untab,tab,getLsbD_bv,route,elim_inr,Option.elim_some]
    rw [fp_pad_mulVec (le_max_right d k),fp_res_ext]
    rfl

theorem fp_bv_false (W : ℕ) : bv (fun _ : Fin W => false) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bv, BitVec.getLsbD_ofFnLE]
  simp

theorem cmp_push (d k W : ℕ) :
    Cmp ((Fin d × Fin k) ⊕ (V k × Fin W)) (V d × Fin W) (tcost d k W)
      (fun v => untab (fun z : V d =>
        ∑ lam : V k, if (mat (fun p => v (inl p))).mulVec lam = z
          then tab (fun p => v (inr p)) lam else 0)) := by
  classical
  let D := max d k
  let R := Set.range (fp_ext D (k:=k))
  let route : TableIn D W → Option ((Fin d × Fin k) ⊕ TableBits k W) :=
    elim (fun p => (matrixRoute (p.2,p.1)).map inl)
      (fun p => if p.1 ∈ R then some (.inr (fp_res k (le_max_right d k) p.1,p.2)) else none)
  let out (p : TableBits d W) : TableBits D W := (fp_ext D p.1,p.2)
  let S := card (V D) * (4*W)
  let T := card (V D) * (25*(W+1))
  have mid := cmp_phi D (TableBits D W) (fp_pushPhi D W) (fp_push_one _ _) (fp_push_mul _ _)
    S T (fp_push_t_step _ _) (fp_push_z_step _ _)
  refine (tableRoute d k W S T route out mid ?_).congr ?_
  · simp only [S,T,fp_cardV,D]
    rw [← Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (29 * _) _]
    exact Nat.mul_le_mul_left _ (by omega)
  · intro v p
    have hM : (mat (fun j => (route (.inl j)).elim false v)).transpose =
        mat (fp_pad D (v ∘ inl)) := by
      ext i j
      rw [Matrix.transpose_apply,mat,mat,← matrixRoute_eval]
      change (if ((matrixRoute (i,j)).map inl).elim false v then 1 else 0) = _
      cases matrixRoute (i,j) <;> rfl
    simp only [fp_pushPhi, hM, out, untab]
    congr 1
    symm
    apply Fintype.sum_of_injective (fp_ext D) (fp_ext_inj _ (le_max_right d k))
    · intro x hx
      have hn : x ∉ R := hx
      simp only [route,elim_inr,ite_eq_right hn,Option.elim_none,tab,fp_bv_false,ite_self]
    · intro x
      have hx : fp_ext D x ∈ R := ⟨x,rfl⟩
      rw [fp_pad_mulVec (n:=D) (le_max_right d k)]
      simp only [(fp_ext_inj D (le_max_left d k)).eq_iff,route,tab,elim_inr,
        ite_eq_left hx,Option.elim_some]
      rw [fp_res_ext (le_max_right d k) x]
      first
      | rfl
      | by_cases e : (mat (v ∘ inl)).mulVec x = p.1
        · have e' : (mat (fun j => v (inl j))).mulVec x = p.1 := e
          simp [e,e']
        · have e' : ¬ (mat (fun j => v (inl j))).mulVec x = p.1 := e
          simp [e,e']

def whtCost (d W : ℕ) : ℕ := 2 ^ 7 * (d + 1) * (W + 1) * 2 ^ d

def fe_layer {d W : ℕ} (i : Fin d) (T : V d → BitVec W) : V d → BitVec W :=
  fun xi => T (Function.update xi i 0) + sgn (xi i) * T (Function.update xi i 1)

def fe_k {d : ℕ} (W : ℕ) (L : List (Fin d)) (xi x : V d) : BitVec W :=
  ∏ i : Fin d, (if i ∈ L then sgn (xi i * x i) else if x i = xi i then 1 else 0)

theorem fe_z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem fe_sgn_add {W : ℕ} (u v : ZMod 2) : (sgn (u + v) : BitVec W) = sgn u * sgn v := by
  rcases fe_z2 u with rfl | rfl <;> rcases fe_z2 v with rfl | rfl
  · simp [sgn]
  · simp [sgn]
  · simp [sgn]
  · have h : (1 + 1 : ZMod 2) = 0 := by decide
    rw [h]; simp [sgn]

theorem fe_sgn_sum {W : ℕ} {ι : Type} (s : Finset ι) (f : ι → ZMod 2) :
    (sgn (∑ i ∈ s, f i) : BitVec W) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, fe_sgn_add, ih]

theorem fe_k_step {d : ℕ} (W : ℕ) (L : List (Fin d)) (e : Fin d) (he : e ∉ L) (xi x : V d) :
    fe_k W L (Function.update xi e 0) x + sgn (xi e) * fe_k W L (Function.update xi e 1) x
      = fe_k W (L ++ [e]) xi x := by
  unfold fe_k
  rw [← Finset.mul_prod_erase Finset.univ _ (mem_univ e),
    ← Finset.mul_prod_erase Finset.univ _ (mem_univ e),
    ← Finset.mul_prod_erase Finset.univ _ (mem_univ e)]
  have h0 : ∀ b : ZMod 2, ∏ i ∈ Finset.univ.erase e,
      (if i ∈ L then (sgn (Function.update xi e b i * x i) : BitVec W)
        else if x i = Function.update xi e b i then 1 else 0)
      = ∏ i ∈ Finset.univ.erase e,
      (if i ∈ L ++ [e] then (sgn (xi i * x i) : BitVec W) else if x i = xi i then 1 else 0) := by
    intro b
    apply Finset.prod_congr rfl
    intro i hi
    have hne : i ≠ e := Finset.ne_of_mem_erase hi
    rw [Function.update_of_ne hne]
    simp [hne]
  rw [h0 0, h0 1]
  simp only [he, ite_false, Function.update_self, List.mem_append, List.mem_singleton, or_true,
    ite_true]
  rcases fe_z2 (x e) with h | h <;> rcases fe_z2 (xi e) with h' | h' <;>
    simp [h, h', sgn]

theorem fe_fold_sem {d W : ℕ} (T : V d → BitVec W) (L : List (Fin d)) (hL : L.Nodup) :
    ∀ xi, L.foldl (fun T e => fe_layer e T) T xi = ∑ x : V d, fe_k W L xi x * T x := by
  induction L using List.reverseRecOn with
  | nil =>
    intro xi
    have : ∀ x : V d, fe_k W [] xi x = if x = xi then 1 else 0 := by
      intro x
      unfold fe_k
      simp only [List.not_mem_nil, ite_false]
      rw [Finset.prod_ite_zero]
      simp only [Finset.prod_const_one, mem_univ, forall_true_left]
      congr 1
      exact propext funext_iff.symm
    simp only [this, ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq']
    simp
  | append_singleton L e ih =>
    intro xi
    have hn := List.nodup_append.1 hL
    have he : e ∉ L := fun h => hn.2.2 e h e (by simp) rfl
    rw [List.foldl_append]
    change List.foldl (fun T e => fe_layer e T) T L (Function.update xi e 0) +
      sgn (xi e) * List.foldl (fun T e => fe_layer e T) T L (Function.update xi e 1) = _
    rw [ih hn.1, ih hn.1, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro x _
    rw [← fe_k_step W L e he xi x]
    ring

theorem fe_k_full {d : ℕ} (W : ℕ) (xi x : V d) :
    fe_k W (List.finRange d) xi x = sgn (xi ⬝ᵥ x) := by
  unfold fe_k dotProduct
  rw [fe_sgn_sum]
  apply Finset.prod_congr rfl
  intro i _
  simp

theorem fe_fold_tab {d W : ℕ} (L : List (Fin d)) :
    ∀ v : V d × Fin W → Bool,
      L.foldl (fun acc e => untab (fe_layer e (tab acc))) v
        = untab (L.foldl (fun T e => fe_layer e T) (tab v)) := by
  induction L with
  | nil => intro v; exact (untab_tab v).symm
  | cons e L ih =>
    intro v
    rw [List.foldl_cons, List.foldl_cons, ih, tab_untab]

theorem fe_layer_cmp {d W : ℕ} (i : Fin d) :
    Cmp (V d × Fin W) (V d × Fin W) (2 ^ d * (20 * (W + 1)))
      (fun v => untab (fe_layer i (tab v))) := by
  have hc : card (V d) = 2 ^ d := by simp [V]
  have := Cmp.ofWords (ι := V d × Fin W) (α := V d) (W := W) (s := 20 * (W + 1))
    (G := fun v => fe_layer i (tab v)) (fun x => ?_)
  · rw [hc] at this; exact this
  · by_cases h : x i = 0
    · have hx : Function.update x i 0 = x := by rw [← h, Function.update_eq_self]
      refine Cw.congr (Cw.mono (Cw.add (Cw.var (fun k => (x, k)))
        (Cw.var (fun k => (Function.update x i 1, k)))) (by omega)) ?_
      intro v
      show tab v x + tab v (Function.update x i 1) = fe_layer i (tab v) x
      unfold fe_layer
      rw [hx, h]
      simp [sgn]
    · have h1 : x i = 1 := (fe_z2 (x i)).resolve_left h
      have hx : Function.update x i 1 = x := by rw [← h1, Function.update_eq_self]
      refine Cw.congr (Cw.mono (Cw.sub (Cw.var (fun k => (Function.update x i 0, k)))
        (Cw.var (fun k => (x, k)))) (by omega)) ?_
      intro v
      show tab v (Function.update x i 0) - tab v x = fe_layer i (tab v) x
      unfold fe_layer
      rw [hx, h1]
      have : (sgn (1 : ZMod 2) : BitVec W) = -1 := by simp [sgn]
      rw [this]
      ring

theorem cmp_wht (d W : ℕ) :
    Cmp (V d × Fin W) (V d × Fin W) (whtCost d W)
      (fun v => untab (fun xi : V d => ∑ x : V d, sgn (xi ⬝ᵥ x) * tab v x)) := by
  have h := Cmp.foldl (ι := V d × Fin W) (s := 2 ^ d * (20 * (W + 1))) (List.finRange d)
    (fun i v => untab (fe_layer i (tab v))) (fun e _ => fe_layer_cmp e)
  refine Cmp.congr (Cmp.mono h ?_) ?_
  · rw [List.length_finRange]
    unfold whtCost
    have h1 := Nat.zero_le (d * (2 ^ d * (W + 1)))
    have h2 := Nat.zero_le (2 ^ d * (W + 1))
    nlinarith
  · intro v k
    show (List.foldl (fun acc e => untab (fe_layer e (tab acc))) v (List.finRange d)) k = _
    rw [fe_fold_tab]
    congr 1
    funext xi
    rw [fe_fold_sem _ _ (List.nodup_finRange d)]
    apply sum_congr rfl
    intro x _
    rw [fe_k_full]

theorem fg_z2 (u : ZMod 2) : u = 0 ∨ u = 1 := by
  revert u; decide

theorem fg_sgn_add {W : ℕ} (u v : ZMod 2) : (sgn (u + v) : BitVec W) = sgn u * sgn v := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases fg_z2 u with rfl | rfl <;> rcases fg_z2 v with rfl | rfl <;> simp [sgn, h11]

theorem fg_char {W : ℕ} (K : ℕ) (w : Fin K → ZMod 2) :
    (∑ lam : V K, (sgn (∑ s, lam s * w s) : BitVec W)) = if w = 0 then 2 ^ K else 0 := by
  split_ifs with h
  · subst h
    simp [sgn]
  · obtain ⟨s, hs⟩ : ∃ s, w s ≠ 0 := by
      by_contra hh
      exact h (funext fun s => by_contra fun hs => hh ⟨s, hs⟩)
    have hs1 : w s = 1 := by
      rcases fg_z2 (w s) with h0 | h1
      · exact absurd h0 hs
      · exact h1
    have key : ∀ lam : V K, (∑ s', (lam + (Pi.single s 1 : V K)) s' * w s') = (∑ s', lam s' * w s') + 1 := by
      intro lam
      simp [add_mul, Finset.sum_add_distrib, Pi.single_apply, hs1]
    refine Finset.sum_involution (fun lam _ => lam + (Pi.single s 1 : V K)) ?_ ?_ ?_ ?_
    · intro lam _
      rw [key, fg_sgn_add]
      simp [sgn]
    · intro lam _ _ heq
      have := congrFun heq s
      simp at this
    · intro lam _
      simp
    · intro lam _
      funext i
      have h11 : (1 : ZMod 2) + 1 = 0 := by decide
      by_cases hi : i = s
      · subst hi
        simp [add_assoc, h11]
      · simp [Pi.single_apply, hi]

theorem vecEquiv_exists (a : ℕ) :
    ∃ e : Fin (2 ^ a) ≃ V a, ∀ ix j, e ix j = if ix.val.testBit j.val then 1 else 0 := by
  let e0 : Fin (2 ^ a) → V a := fun ix j => if ix.val.testBit j.val then 1 else 0
  have hinj : Injective e0 := by
    intro x y hxy
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < a
    · have := congrFun hxy ⟨i, hi⟩
      simp only [e0] at this
      by_cases hx : x.val.testBit i <;> by_cases hy : y.val.testBit i <;> simp_all
    · have hx : x.val < 2 ^ i := lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hy : y.val < 2 ^ i := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
  have hbij : Function.Bijective e0 := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [V]
  exact ⟨Equiv.ofBijective e0 hbij, fun ix j => rfl⟩

private theorem fhMove (a b c : ZMod 2) : a + b + c = 0 ↔ a = c + b := by
  revert a b c
  decide

def fh_w {m N : ℕ} (v : V N) : V (m+N+1) :=
  Fin.append (Fin.snoc v 1) 0 ∘ (finCongr (by omega : N+1+m = m+N+1)).symm

theorem fh_mulVec_w {m N : ℕ} (X : Matrix (Fin (m + N + 1)) (Fin (m + N + 1)) (ZMod 2))
    (v : V N) (i : Fin (m + N + 1)) :
    X.mulVec (fh_w v) i = ∑ p : Fin N, X i (cl m p) * v p + X i (rc m N) := by
  simp only [Matrix.mulVec,dotProduct]
  rw [← Equiv.sum_comp (finCongr (by omega : N+1+m = m+N+1)),Fin.sum_univ_add]
  simp only [fh_w,Function.comp_apply,Equiv.symm_apply_apply,Fin.append_left,Fin.append_right,
    Pi.zero_apply,mul_zero,sum_const_zero,add_zero]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last,mul_one]
  rfl

theorem fh_bit (x : ZMod 2) : (if decide (x ≠ 0) = true then (1 : ZMod 2) else 0) = x := by
  revert x; decide

theorem fh_sys_cl {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (i : Fin (m + N + 1))
    (p : Fin N) :
    mat (sysBits Hf rhs) i (cl m p) = if hi : i.val < m then Hf ⟨i.val, hi⟩ p else 0 := by
  by_cases h : i.val < m
  · have hp : (cl m p).val < N := p.isLt
    simp only [mat,sysBits,dite_eq_left h,dite_eq_left hp]
    exact fh_bit _
  · simp [mat,sysBits,h]

theorem fh_sys_rc {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (i : Fin (m + N + 1)) :
    mat (sysBits Hf rhs) i (rc m N) = if hi : i.val < m then rhs ⟨i.val, hi⟩ else 0 := by
  by_cases h : i.val < m
  · have hp : ¬ (rc m N).val < N := Nat.lt_irrefl N
    have hv : (rc m N).val = N := rfl
    simp only [mat,sysBits,dite_eq_left h,dite_eq_right hp,ite_eq_left hv]
    exact fh_bit _
  · simp [mat,sysBits,h]

theorem fh_sys_hi {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (i j : Fin (m + N + 1)) (hj : N < j.val) : mat (sysBits Hf rhs) i j = 0 := by
  by_cases h : i.val < m <;> simp [mat,sysBits,h,show ¬ j.val < N by omega,show j.val ≠ N by omega]

theorem fh_sys_iff {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (v : V N) :
    (∀ i, Hf i ⬝ᵥ v = rhs i) ↔ (mat (sysBits Hf rhs)).mulVec (fh_w v) = 0 := by
  have move (a b : ZMod 2) : a + b = 0 ↔ a = b := by simpa using fhMove a b 0
  rw [funext_iff]
  simp only [fh_mulVec_w,fh_sys_cl,fh_sys_rc,Pi.zero_apply]
  constructor
  · intro h i
    by_cases hi : i.val < m
    · simpa [hi,move,dotProduct] using h ⟨i.val,hi⟩
    · simp [hi]
  · intro h i
    simpa [move,dotProduct,i.isLt] using h ⟨i.val,by omega⟩

theorem fh_R_iff {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (v : V N) :
    (mat (sysBits Hf rhs)).mulVec (fh_w v) = 0 ↔
      (mat (gj _ (sysBits Hf rhs))).mulVec (fh_w v) = 0 := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv (sysBits Hf rhs)
  constructor
  · intro h
    rw [h1, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  · intro h
    rw [h2, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

theorem fh_mat_zero {r c : ℕ} (R : Fin r × Fin c → Bool) (i : Fin r) (j : Fin c)
    (h : mat R i j = 0) : R (i, j) = false := by
  unfold mat at h
  by_contra hc
  rw [if_pos (by simpa using hc)] at h
  exact one_ne_zero h

theorem fh_mat_false {r c : ℕ} (R : Fin r × Fin c → Bool) (i : Fin r) (j : Fin c)
    (h : R (i, j) = false) : mat R i j = 0 := by
  unfold mat; rw [h]; rfl

theorem fh_mat_true {r c : ℕ} (R : Fin r × Fin c → Bool) (i : Fin r) (j : Fin c)
    (h : R (i, j) = true) : mat R i j = 1 := by
  unfold mat; rw [h]; rfl

theorem fh_hicol {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (i j : Fin (m + N + 1)) (hj : N < j.val) : gj _ (sysBits Hf rhs) (i, j) = false := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv (sysBits Hf rhs)
  apply fh_mat_zero
  rw [h1, Matrix.mul_apply]
  apply sum_eq_zero
  intro k _
  rw [fh_sys_hi Hf rhs k j hj, mul_zero]

theorem fh_row_split {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (hpc : ∀ p, R (p, p) = true → ∀ i, R (i, p) = decide (i = p))
    (p : Fin N) (hp : pv R p = true) (u : V N) :
    ∑ q, mat R (cl m p) (cl m q) * u q =
      u p + ∑ q, if pv R q = false then mat R (cl m p) (cl m q) * u q else 0 := by
  have hpt : ∀ q : Fin N, mat R (cl m p) (cl m q) * u q =
      (if q = p then u p else 0) +
        (if pv R q = false then mat R (cl m p) (cl m q) * u q else 0) := by
    intro q
    by_cases hq : q = p
    · subst hq
      rw [if_pos rfl, if_neg (by rw [hp]; simp), add_zero, fh_mat_true R _ _ hp, one_mul]
    · rw [if_neg hq, zero_add]
      by_cases hv : pv R q = false
      · rw [if_pos hv]
      · rw [if_neg hv]
        have hv' : R (cl m q, cl m q) = true := by simpa [pv] using hv
        have := hpc (cl m q) hv' (cl m p)
        have hne : cl m p ≠ cl m q := by
          intro h
          apply hq
          apply Fin.ext
          exact (congrArg Fin.val h).symm
        rw [decide_eq_false hne] at this
        rw [fh_mat_false R _ _ this, zero_mul]
  rw [sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib, sum_ite_eq']
  rw [if_pos (mem_univ p)]

theorem fh_Rsol {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (hpc : ∀ p, R (p, p) = true → ∀ i, R (i, p) = decide (i = p))
    (hzr : ∀ q, R (q, q) = false → ∀ j, R (q, j) = false)
    (hhi : ∀ i j : Fin (m + N + 1), N < j.val → R (i, j) = false)
    (hcons : R (rc m N, rc m N) = false) (v : V N) :
    (mat R).mulVec (fh_w v) = 0 ↔
      ∀ p : Fin N, pv R p = true → v p = mat R (cl m p) (rc m N) +
        ∑ q, if pv R q = false then mat R (cl m p) (cl m q) * v q else 0 := by
  have eval (p : Fin N) (hp : pv R p = true) : (mat R).mulVec (fh_w v) (cl m p) = 0 ↔
      v p = mat R (cl m p) (rc m N) +
        ∑ q, if pv R q = false then mat R (cl m p) (cl m q) * v q else 0 := by
    rw [fh_mulVec_w,fh_row_split R hpc p hp,fhMove]
  constructor
  · exact fun h p hp => (eval p hp).mp (congrFun h _)
  · intro h
    funext i
    cases hi : R (i,i)
    · simp [fh_mulVec_w,mat,hzr i hi]
    · have hn : i.val < N := by
        by_contra! hle
        obtain e|lt := eq_or_lt_of_le hle
        · have ei : i = rc m N := Fin.ext e.symm
          simp [ei,hcons] at hi
        · simp [hhi i i lt] at hi
      let p : Fin N := ⟨i.val,hn⟩
      have he : cl m p = i := Fin.ext rfl
      have hp : pv R p = true := by simpa [pv,he] using hi
      rw [← he]
      exact (eval p hp).mpr (h p hp)

theorem fh_main_iff {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (hcons : gj _ (sysBits Hf rhs) (rc m N, rc m N) = false) (v : V N) :
    (∀ i, Hf i ⬝ᵥ v = rhs i) ↔
      ∀ p : Fin N, pv (gj _ (sysBits Hf rhs)) p = true →
        v p = mat (gj _ (sysBits Hf rhs)) (cl m p) (rc m N) +
          ∑ q, if pv (gj _ (sysBits Hf rhs)) q = false then
            mat (gj _ (sysBits Hf rhs)) (cl m p) (cl m q) * v q else 0 := by
  rw [fh_sys_iff, fh_R_iff]
  exact fh_Rsol _ (fun p hp i => gj_pivcol _ p hp i) (fun q hq j => gj_zerorow _ q hq j)
    (fun i j hj => fh_hicol Hf rhs i j hj) hcons v

theorem fh_cnt_lt {N : ℕ} (P : Fin N → Prop) [DecidablePred P] (p p' : Fin N) (h : p < p')
    (hp : P p) :
    (Finset.univ.filter (fun q : Fin N => q < p ∧ P q)).card <
      (Finset.univ.filter (fun q : Fin N => q < p' ∧ P q)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨p, by simp [h, hp], by simp⟩
  · intro q
    simp only [Finset.mem_filter, mem_univ, true_and]
    rintro ⟨h1, h2⟩
    exact ⟨h1.trans h, h2⟩

theorem fh_cnt_inj {N : ℕ} (P : Fin N → Prop) [DecidablePred P] (p p' : Fin N)
    (hp : P p) (hp' : P p')
    (h : (Finset.univ.filter (fun q : Fin N => q < p ∧ P q)).card =
      (Finset.univ.filter (fun q : Fin N => q < p' ∧ P q)).card) : p = p' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have := fh_cnt_lt P p p' h1 hp; omega
  · have := fh_cnt_lt P p' p h1 hp'; omega

theorem la_incons {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits Hf rhs) (rc m N, rc m N) = true) (v : V N) :
    ¬ ∀ i, Hf i ⬝ᵥ v = rhs i := by
  rw [fh_sys_iff, fh_R_iff]
  intro h0
  have := congrFun h0 (rc m N)
  rw [fh_mulVec_w, fh_mat_true _ _ _ h] at this
  rw [sum_eq_zero] at this
  · rw [zero_add] at this
    exact one_ne_zero this
  · intro q _
    have : gj _ (sysBits Hf rhs) (rc m N, cl m q) = false := by
      apply gj_upper
      show q.val < N
      exact q.isLt
    rw [fh_mat_false _ _ _ this, zero_mul]

theorem ft_join_nx {a b c : ℕ} (h : V a × V b × V c) (j : Fin a) :
    join3 h (nx j) = h.1 j := by
  simp [join3, nx]

theorem ft_join_ny {a b c : ℕ} (h : V a × V b × V c) (j : Fin b) :
    join3 h (ny j) = h.2.1 j := by
  simp [join3, ny]

theorem ft_join_nz {a b c : ℕ} (h : V a × V b × V c) (j : Fin c) :
    join3 h (nz j) = h.2.2 j := by
  have h1 : ¬ (a + b + j.val < a) := by omega
  have h2 : ¬ (a + b + j.val < a + b) := by omega
  simp [join3, nz, h1, h2]

def cnt {N : ℕ} (fl : Fin N → Bool) (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun q : Fin N => q.val < i ∧ fl q = true)).card

theorem cnt_zero {N : ℕ} (fl : Fin N → Bool) : cnt fl 0 = 0 := by simp [cnt]

theorem cnt_succ {N : ℕ} (fl : Fin N → Bool) (i : ℕ) (h : i < N) :
    cnt fl (i + 1) = cnt fl i + (if fl ⟨i, h⟩ = true then 1 else 0) := by
  unfold cnt
  by_cases hf : fl ⟨i, h⟩ = true
  · have : (Finset.univ.filter (fun q : Fin N => q.val < i + 1 ∧ fl q = true)) =
        insert ⟨i, h⟩ (Finset.univ.filter (fun q : Fin N => q.val < i ∧ fl q = true)) := by
      ext q
      simp only [Finset.mem_filter, mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hq : q.val = i
        · left; exact Fin.ext hq
        · right; exact ⟨by omega, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Nat.lt_succ_self i, hf⟩
        · exact ⟨by omega, h2⟩
    rw [this, Finset.card_insert_of_notMem (by simp), if_pos hf]
  · have : (Finset.univ.filter (fun q : Fin N => q.val < i + 1 ∧ fl q = true)) =
        (Finset.univ.filter (fun q : Fin N => q.val < i ∧ fl q = true)) := by
      ext q
      simp only [Finset.mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_contra hc
        have : q = ⟨i, h⟩ := Fin.ext (show q.val = i by omega)
        exact hf (this ▸ h2)
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h2⟩
    rw [this, if_neg hf, Nat.add_zero]

def cntG (N K : ℕ) (i : ℕ) (v : Fin N ⊕ Fin (K + 1) → Bool) (s : Fin (K + 1)) : Bool :=
  if hi : i < N then
    (if v (inl ⟨i, hi⟩) = true then
      (if hs : 0 < s.val then v (inr ⟨s.val - 1, by omega⟩) else false)
     else v (inr s))
  else v (inr s)

theorem cntG_cb (N K i : ℕ) (s : Fin (K + 1)) :
    Cb (Fin N ⊕ Fin (K + 1)) 6 (fun v => cntG N K i v s) := by
  by_cases hi : i < N
  · by_cases hs : 0 < s.val
    · refine ((Cb.mux (Cb.var (inl ⟨i, hi⟩)) (Cb.var (inr ⟨s.val - 1, by omega⟩))
        (Cb.var (inr s))).mono (by norm_num)).congr ?_
      intro v; simp [cntG, hi, hs]
    · refine ((Cb.mux (Cb.var (inl ⟨i, hi⟩)) (Cb.const false)
        (Cb.var (inr s))).mono (by norm_num)).congr ?_
      intro v; simp [cntG, hi, hs]
  · refine ((Cb.var (inr s)).mono (by norm_num)).congr ?_
    intro v; simp [cntG, hi]

theorem cmp_counter (N K : ℕ) :
    Cmp (Fin N) (Fin (N + 1) × Fin (K + 1)) ((N + 1) * ((K + 1) * 6))
      (fun fl p => decide (cnt fl p.1.val = p.2.val)) := by
  refine Cmp.chain N ((K + 1) * 6) (fun i fl s => decide (cnt fl i = s.val)) (cntG N K) ?_ ?_ ?_
  · have := Cmp.ofBits (ι := Fin N) (κ := Fin (K + 1)) (s := 6)
      (F := fun fl s => decide (cnt fl 0 = s.val)) (fun s => by
        refine ((Cb.const (decide (0 = s.val))).mono (by norm_num)).congr ?_
        intro v; simp [cnt_zero])
    rw [card_fin] at this
    exact this
  · intro i _
    have := Cmp.ofBits (ι := Fin N ⊕ Fin (K + 1)) (κ := Fin (K + 1)) (s := 6)
      (F := cntG N K i) (fun s => cntG_cb N K i s)
    rw [card_fin] at this
    exact this
  · intro i hi v
    funext s
    simp only [cntG, dif_pos hi, elim_inl, elim_inr, cnt_succ v i hi]
    by_cases hv : v ⟨i, hi⟩ = true
    · by_cases hs : 0 < s.val
      · simp [hv, hs]; omega
      · simp [hv, hs]; omega
    · simp [hv]

def gjCost (D : ℕ) : ℕ := 32 * (D + 1) ^ 4

theorem fz2_gjbit {D : ℕ} (e : Bool × Fin D × Fin D) (p : Fin D × Fin D) :
    Cb (Fin D × Fin D) 11 (fun M => gjStep e M p) := by
  have h := Cmp.sel (ι := Fin D × Fin D)
    (fun j : (Fin D × Fin D) ⊕ Empty => elim id (fun x => x.elim) j)
    (fd_bit (τ := Empty) e p)
  exact h

theorem cmp_gj (D : ℕ) : Cmp (Fin D × Fin D) (Fin D × Fin D) (gjCost D) (gj D) := by
  have h := Cmp.foldl (ι := Fin D × Fin D) (s := card (Fin D × Fin D) * 11) (sched D)
    (fun e M => gjStep e M) (fun e _ => Cmp.ofBits (fun p => fz2_gjbit e p))
  refine Cmp.mono h ?_
  have h1 := fd_sched_len D
  have h2 : card (Fin D × Fin D) = D * D := by simp
  rw [h2]
  unfold gjCost
  have h3 : D ^ 4 ≤ (D + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h4 : 2 * (D * D) * (D * D * 11) = 22 * D ^ 4 := by ring
  calc (sched D).length * (D * D * 11) ≤ 2 * (D * D) * (D * D * 11) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ 32 * (D + 1) ^ 4 := by omega

theorem fz2_zsum (K : ℕ) (x : Fin K → ZMod 2) (b : Fin K → Bool) :
    (∑ s, x s * (if b s = true then (1 : ZMod 2) else 0)) ≠ 0 ↔
      (Finset.univ.filter (fun s => (decide (x s ≠ 0) && b s) = true)).card % 2 = 1 := by
  have key : ∀ s, x s * (if b s = true then (1 : ZMod 2) else 0) =
      if (decide (x s ≠ 0) && b s) = true then 1 else 0 := by
    intro s
    have hall : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
    have hx : x s = 0 ∨ x s = 1 := hall (x s)
    rcases hx with hx | hx <;> cases b s <;> simp [hx]
  simp_rw [key]
  rw [Finset.sum_boole, Ne, ZMod.natCast_eq_zero_iff]
  omega

abbrev In0 (a b c m t : ℕ) : Type :=
  (Fin m × Fin (a + b + c + 1)) ⊕ ((Fin (2 ^ a) × Fin t) ⊕ (Fin (2 ^ b) × Fin t))

def fTab (a b c m t W : ℕ) (ea : Fin (2 ^ a) ≃ V a) (v : In0 a b c m t → Bool) :
    V a × Fin W → Bool := fun p =>
  if h : p.2.val < t then v (inr (inl (ea.symm p.1, ⟨p.2.val, h⟩))) else false

def gTab (a b c m t W : ℕ) (eb : Fin (2 ^ b) ≃ V b) (v : In0 a b c m t → Bool) :
    V b × Fin W → Bool := fun p =>
  if h : p.2.val < t then v (inr (inr (eb.symm p.1, ⟨p.2.val, h⟩))) else false

def inpOf {a b c m t : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) : In0 a b c m t → Bool :=
  elim (fun p => if h : p.2.val < a + b + c then decide (join3 (H p.1) ⟨p.2.val, h⟩ ≠ 0)
      else decide (rhs p.1 ≠ 0))
    (elim (fun p => (f p.1).val.testBit p.2.val) (fun p => (g p.1).val.testBit p.2.val))

theorem fz4_fTab (a b c m t W : ℕ) (ea : Fin (2 ^ a) ≃ V a) :
    Cmp (In0 a b c m t) (V a × Fin W) (2 ^ a * W) (fTab a b c m t W ea) := by
  refine (Cmp.ofBits (s := 1) (F := fTab a b c m t W ea) (fun p => ?_)).mono
    (by simp)
  by_cases h : p.2.val < t
  · refine ((Cb.var (inr (inl (ea.symm p.1, ⟨p.2.val, h⟩)))).mono (by norm_num)).congr ?_
    intro v; simp [fTab, h]
  · refine (Cb.const false).congr ?_
    intro v; simp [fTab, h]

theorem fz4_gTab (a b c m t W : ℕ) (eb : Fin (2 ^ b) ≃ V b) :
    Cmp (In0 a b c m t) (V b × Fin W) (2 ^ b * W) (gTab a b c m t W eb) := by
  refine (Cmp.ofBits (s := 1) (F := gTab a b c m t W eb) (fun p => ?_)).mono
    (by simp)
  by_cases h : p.2.val < t
  · refine ((Cb.var (inr (inr (eb.symm p.1, ⟨p.2.val, h⟩)))).mono (by norm_num)).congr ?_
    intro v; simp [gTab, h]
  · refine (Cb.const false).congr ?_
    intro v; simp [gTab, h]

theorem fz5_tabf {a b c m t : ℕ} (W : ℕ) (ea : Fin (2 ^ a) ≃ V a)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (x : V a) :
    tab (fTab a b c m t W ea (inpOf H rhs f g)) x = BitVec.ofNat W (f (ea.symm x)).val := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 := getLsbD_bv (fun k : Fin W => fTab a b c m t W ea (inpOf H rhs f g) (x, k)) ⟨i, hi⟩
  have h2 : (tab (fTab a b c m t W ea (inpOf H rhs f g)) x).getLsbD i =
      fTab a b c m t W ea (inpOf H rhs f g) (x, ⟨i, hi⟩) := h1
  rw [h2, BitVec.getLsbD_ofNat]
  unfold fTab inpOf
  by_cases h : i < t
  · simp [h, hi]
  · have hlt : (f (ea.symm x)).val < 2 ^ i :=
      lt_of_lt_of_le (f (ea.symm x)).isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [h, hi, Nat.testBit_lt_two_pow hlt]

theorem fz5_tabg {a b c m t : ℕ} (W : ℕ) (eb : Fin (2 ^ b) ≃ V b)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (y : V b) :
    tab (gTab a b c m t W eb (inpOf H rhs f g)) y = BitVec.ofNat W (g (eb.symm y)).val := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 := getLsbD_bv (fun k : Fin W => gTab a b c m t W eb (inpOf H rhs f g) (y, k)) ⟨i, hi⟩
  have h2 : (tab (gTab a b c m t W eb (inpOf H rhs f g)) y).getLsbD i =
      gTab a b c m t W eb (inpOf H rhs f g) (y, ⟨i, hi⟩) := h1
  rw [h2, BitVec.getLsbD_ofNat]
  unfold gTab inpOf
  by_cases h : i < t
  · simp [h, hi]
  · have hlt : (g (eb.symm y)).val < 2 ^ i :=
      lt_of_lt_of_le (g (eb.symm y)).isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [h, hi, Nat.testBit_lt_two_pow hlt]

def Phi (w : ℕ) : ℕ := 2 ^ (w % 2) * 7 ^ (w / 2)

theorem two_pow_le_Phi (w : ℕ) : 2 ^ w ≤ Phi w := by
  unfold Phi
  have e : 2 ^ w = 2 ^ (w % 2) * 4 ^ (w / 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
    congr 1
    omega
  rw [e]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) _)

def co {w : ℕ} (u : V w) (i : ℕ) : ZMod 2 := if h : i < w then u ⟨i, h⟩ else 0

def Std (w q d r1 r2 r3 : ℕ) (u v t : V w) : Prop :=
  (∀ i < q, co u i + co v i = co t i) ∧
  (∀ i < d, co u (q + i) = co t (q + i) ∧ co v (q + i) = co t (q + i)) ∧
  (∀ i < r2, co u (q + d + i) = co t (q + d + i)) ∧
  (∀ i < r1, co u (q + d + r2 + i) = co v (q + d + i)) ∧
  (∀ i < r3, co v (q + d + r1 + i) = co t (q + d + r2 + i)) ∧
  (∀ i : Fin w, q + d + r2 + r1 ≤ i.val → u i = 0) ∧
  (∀ i : Fin w, q + d + r1 + r3 ≤ i.val → v i = 0) ∧
  (∀ i : Fin w, q + d + r2 + r3 ≤ i.val → t i = 0)

instance (w q d r1 r2 r3 : ℕ) (u v t : V w) : Decidable (Std w q d r1 r2 r3 u v t) := by
  unfold Std; infer_instance

def ShapeSpec (w W B q d r1 r2 r3 : ℕ) : Prop :=
  ∃ S, S ≤ 2 ^ 30 * (W + w + 1) ^ 3 * Phi w ∧
    Cmp ((V w × Fin W) ⊕ (V w × Fin W)) (V w × Fin B) S
      (fun v p => (∑ x : V w, ∑ y : V w, if Std w q d r1 r2 r3 x y p.1 then
        tab (fun e => v (inl e)) x * tab (fun e => v (inr e)) y else 0 : BitVec W).getLsbD
          p.2.val)

def wOf (a b c : ℕ) : ℕ := max a (max b c)

def WOf (a b c t : ℕ) : ℕ := a + b + 2 * t + 1 + wOf a b c

def fitsW (w : ℕ) (s : Fin 5 → ℕ) : Prop :=
  s 0 + s 1 + s 2 + s 3 ≤ w ∧ s 0 + s 1 + s 2 + s 4 ≤ w ∧ s 0 + s 1 + s 3 + s 4 ≤ w

end Donor

namespace Donor

def ctrlB (u : ZMod 2) : Bool := decide (u ≠ 0)

def ctrlF (b : Bool) : ZMod 2 := if b then 1 else 0

theorem ctrlB_F (b : Bool) : ctrlB (ctrlF b) = b := by cases b <;> decide

theorem ctrlF_B (u : ZMod 2) : ctrlF (ctrlB u) = u := by revert u; decide

theorem ctrlB_mul (x y : ZMod 2) : ctrlB (x*y) = (ctrlB x && ctrlB y) := by
  revert x y; decide

theorem ctrl_mul {ι : Type} {S T : ℕ} {f g : (ι → Bool) → ZMod 2}
    (hf : Cb ι S (fun v => ctrlB (f v))) (hg : Cb ι T (fun v => ctrlB (g v))) :
    Cb ι (S + T + 1) (fun v => ctrlB (f v * g v)) :=
  (Cb.and hf hg).congr fun _ => (ctrlB_mul _ _).symm

theorem ctrl_sum {ι I : Type} [Fintype I] {S : ℕ} {f : I → (ι → Bool) → ZMod 2}
    (hf : ∀ i, Cb ι S (fun v => ctrlB (f i v))) :
    Cb ι (card I * (S + 4) + 1) (fun v => ctrlB (∑ i, f i v)) := by
  apply (Cb.bigXor hf).congr
  intro v
  have he : ∀ i, f i v = if ctrlB (f i v) then 1 else 0 :=
    fun i => (ctrlF_B (f i v)).symm
  unfold ctrlB
  apply decide_eq_decide.mpr
  conv_rhs => rw [sum_congr rfl fun i _ => he i, Finset.sum_boole]
  rw [Ne, ZMod.natCast_eq_zero_iff]
  simp only [ctrlB, decide_eq_true_eq]
  apply Iff.trans (b := ¬ 2 ∣ (Finset.univ.filter fun i => f i v ≠ 0).card) (by omega)
  apply not_congr
  apply iff_of_eq
  exact congrArg (fun s : Finset I => 2 ∣ s.card) (by ext; simp)

theorem ctrl_rewire {ι κ μ : Type} {S : ℕ} {F : (ι → Bool) → κ → Bool}
    (h : Cmp ι κ S F) (e : μ → κ) : Cmp ι μ S (fun v j => F v (e j)) :=
  Cmp.comp h (Cmp.wire e)

def ctrlPacked {N : ℕ} {J : Type} (K : ℕ) (fl : Fin N → Bool)
    (payload : Fin N × J → Bool) (p : Fin K × J) : Bool :=
  decide (∃ i, fl i = true ∧ cnt fl i.val = p.1.val ∧ payload (i,p.2) = true)

theorem ctrl_rank_lt {N : ℕ} (fl : Fin N → Bool) (i : Fin N) (hi : fl i = true) :
    cnt fl i.val < cnt fl N := by
  unfold cnt
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, by simp [hi], by simp⟩
  · intro j hj
    simpa using (Finset.mem_filter.mp hj).2.2

theorem ctrl_rank_surj {N : ℕ} (fl : Fin N → Bool) (s : ℕ) (hs : s < cnt fl N) :
    ∃ i : Fin N, fl i = true ∧ cnt fl i.val = s := by
  suffices h : ∀ n ≤ N, s < cnt fl n → ∃ i : Fin N, fl i = true ∧ cnt fl i.val = s from
    h N le_rfl hs
  intro n
  induction n with
  | zero => simp [cnt_zero]
  | succ n ih =>
    intro hn he
    have hn' : n < N := by omega
    rw [cnt_succ fl n hn'] at he
    by_cases h : s < cnt fl n
    · exact ih (by omega) h
    · split_ifs at he with hj
      · exact ⟨⟨n,hn'⟩, hj, by change cnt fl n = s; omega⟩
      · omega

theorem ctrlPacked_hit {N K : ℕ} {J : Type} (fl : Fin N → Bool) (payload : Fin N × J → Bool)
    (i : Fin N) (s : Fin K) (j : J) (hi : fl i = true) (hs : cnt fl i.val = s.val) :
    ctrlPacked K fl payload (s,j) = payload (i,j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [ctrlPacked, decide_eq_true_eq]
  constructor
  · rintro ⟨q,hq,hqs,hv⟩
    have he : q = i := fh_cnt_inj (fun p => fl p = true) q i hq hi (hqs.trans hs.symm)
    simpa only [he] using hv
  · exact fun h => ⟨i, hi, hs, h⟩

theorem ctrlPacked_tail {N K : ℕ} {J : Type} (fl : Fin N → Bool) (payload : Fin N × J → Bool)
    (s : Fin K) (j : J) (hs : cnt fl N ≤ s.val) :
    ctrlPacked K fl payload (s,j) = false := by
  unfold ctrlPacked
  apply decide_eq_false
  rintro ⟨i,hi,his,_⟩
  have := ctrl_rank_lt fl i hi
  change cnt fl i.val = s.val at his
  omega

theorem ctrl_pack {ι J : Type} [Fintype J] {S T N K : ℕ}
    {fl : (ι → Bool) → Fin N → Bool} {dat : (ι → Bool) → Fin N × J → Bool}
    (hf : Cmp ι (Fin N) S fl) (hd : Cmp ι (Fin N × J) T dat) :
    Cmp ι (Fin K × J)
      (S + ((N+1)*((K+1)*6)) + T + ((K * card J) * (N*3+1)))
      (fun v => ctrlPacked K (fl v) (dat v)) := by
  let B := (Fin N ⊕ (Fin (N+1) × Fin (K+1))) ⊕ (Fin N × J)
  let step (p : Fin K × J) (v : B → Bool) (i : Fin N) : Bool :=
    v (.inl (.inl i)) && v (.inl (.inr (i.castSucc, p.1.castSucc))) && v (.inr (i,p.2))
  have cb (p : Fin K × J) : Cb B (N*3+1) (fun v => decide (∃ i, step p v i = true)) := by
    have hh := Cb.bigOr (I := Fin N) (ι := B) (s := 2) (φ := fun i v => step p v i)
      (fun i => (Cb.and (Cb.and (Cb.var _) (Cb.var _)) (Cb.var _)))
    rw [card_fin] at hh
    exact hh.congr fun _ => decide_eq_decide.mpr Iff.rfl
  have hc := Cmp.ofBits (F := fun v (p : Fin K × J) => decide (∃ i, step p v i = true)) cb
  simp only [card_prod, card_fin] at hc
  refine (Cmp.comp (Cmp.pair (hf.comp (cmp_counter N K).keep) hd) hc).congr ?_
  intro v p
  simp [step, ctrlPacked, and_assoc]

def ctrlAffine {d k : ℕ} (L : Fin d × Fin (k+1) → Bool) (x : V k) : V d :=
  (mat L).mulVec (@Fin.snoc k (fun _ => ZMod 2) x 1)

def ctrlPushed {d k W : ℕ} (L : Fin d × Fin (k+1) → Bool)
    (mask : V k → Bool) (T : V k × Fin W → Bool) : V d × Fin W → Bool :=
  untab (fun z => ∑ x : V k, if ctrlAffine L x = z ∧ mask x = true then tab T x else 0)

theorem ctrl_split {R : Type} [AddCommMonoid R] (k : ℕ) (h : V (k+1) → R) :
    (∑ l : V (k+1), h l) =
      (∑ x : V k, h (@Fin.snoc k (fun _ => ZMod 2) x 0)) +
      (∑ x : V k, h (@Fin.snoc k (fun _ => ZMod 2) x 1)) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (k+1) => ZMod 2)).sum_comp, Fintype.sum_prod_type]
  have h2 : ∀ F : ZMod 2 → R, ∑ x, F x = F 0 + F 1 := fun F => Fin.sum_univ_two F
  rw [h2]
  rfl

theorem ctrl_push {ι : Type} {S T U d k W : ℕ}
    {L : (ι → Bool) → Fin d × Fin (k+1) → Bool} {msk : (ι → Bool) → V k → Bool}
    {tabB : (ι → Bool) → V k × Fin W → Bool}
    (hL : Cmp ι (Fin d × Fin (k+1)) S L) (hm : Cmp ι (V k) T msk)
    (ht : Cmp ι (V k × Fin W) U tabB) :
    Cmp ι (V d × Fin W) (S + ((T + U) + 2^(k+1)*W) + tcost d (k+1) W)
      (fun v => ctrlPushed (L v) (msk v) (tabB v)) := by
  let B := V k ⊕ (V k × Fin W)
  let pad (v : B → Bool) (p : V (k+1) × Fin W) : Bool :=
    if p.1 (Fin.last k) = 1 then
      v (.inl (Fin.init p.1)) && v (.inr (Fin.init p.1, p.2))
    else false
  have hp (p : V (k+1) × Fin W) : Cb B 1 (fun v => pad v p) := by
    by_cases h : p.1 (Fin.last k) = 1
    · simpa [pad,h] using Cb.and (Cb.var (ι := B) (.inl (Fin.init p.1)))
        (Cb.var (ι := B) (.inr (Fin.init p.1,p.2)))
    · simpa [pad,h] using Cb.const (ι := B) false
  have hb := Cmp.ofBits (F := pad) hp
  simp only [card_prod, fp_cardV, card_fin, Nat.mul_one] at hb
  have hc := hL.pair ((hm.pair ht).comp hb)
  refine (hc.comp (cmp_push d (k+1) W)).congr ?_
  intro v p
  unfold ctrlPushed untab
  apply congrArg (fun u : BitVec W => u.getLsbD p.2.val)
  simp only [elim_inl, elim_inr]
  rw [ctrl_split k]
  simp only [elim_inl, elim_inr, tab, pad, Fin.snoc_last, zero_ne_one,
    ite_false, fp_bv_false, ite_self, sum_const_zero, zero_add, ite_true, Fin.init_snoc]
  apply sum_congr rfl
  intro x _
  by_cases h : msk v x = true
  · simp [ctrlAffine, h]
  · simp [ctrlAffine, Bool.eq_false_iff.mpr h, fp_bv_false]

def ctrlSat {I : Type} [Fintype I] {k : ℕ} (R : I × Fin (k+1) → Bool) (x : V k) : Bool :=
  decide (∀ i, (∑ j : Fin k, ctrlF (R (i,j.castSucc)) * x j) = ctrlF (R (i,Fin.last k)))

theorem ctrl_pin {ι I : Type} [Fintype I] {k S : ℕ}
    {R : (ι → Bool) → I × Fin (k+1) → Bool} (hr : Cmp ι (I × Fin (k+1)) S R) :
    Cmp ι (V k) (S + 2^k * (card I * (k*6+7) + 1))
      (fun v => ctrlSat (R v)) := by
  let B := I × Fin (k+1)
  have mit (x : V k) (i : I) (j : Fin k) :
      Cb B 2 (fun r => ctrlB (ctrlF (r (i,j.castSucc)) * x j)) := by
    have hb : Cb B 0 (fun r => ctrlB (ctrlF (r (i,j.castSucc)))) :=
      (Cb.var (i,j.castSucc)).congr fun _ => (ctrlB_F _).symm
    exact ctrl_mul hb (Cb.const (ctrlB (x j)))
  have lit (x : V k) (i : I) :
      Cb B (k*6+6) (fun r => decide
        ((∑ j : Fin k, ctrlF (r (i,j.castSucc)) * x j) = ctrlF (r (i,Fin.last k)))) := by
    let A (r : B → Bool) := ∑ j : Fin k, ctrlF (r (i,j.castSucc)) * x j
    have ha : Cb B (k*6+1) (fun r => ctrlB (A r)) := by
      simpa [A] using ctrl_sum (mit x i)
    have hb : Cb B 0 (fun r => r (i,Fin.last k)) := Cb.var _
    have hh : ∀ u b, (!(xor (ctrlB u) b)) = decide (u = ctrlF b) := by decide
    exact (Cb.not (ha.xor hb)).congr fun r => hh (A r) (r (i,Fin.last k))
  have bit (x : V k) : Cb B (card I * (k*6+7) + 1) (fun r => ctrlSat r x) := by
    apply (Cb.bigAnd (fun i => lit x i)).congr
    intro r
    apply decide_eq_decide.mpr
    simp
  have h := Cmp.ofBits (F := fun r (x : V k) => ctrlSat r x) bit
  rw [fp_cardV] at h
  exact hr.comp h

def ctrlPushExtra (w k W : ℕ) := (2^k*W + 2^(k+1)*W) + tcost w (k+1) W

theorem ctrl_push_extra {w k W P : ℕ} (hk : k ≤ w) (hw : w+2 ≤ P)
    (hW : W+1 ≤ 4*P) : ctrlPushExtra w k W ≤ 2^18 * P^5 * 2^w := by
  have hP : 1 ≤ P := by omega
  have hp : 2^k ≤ 2^w := Nat.pow_le_pow_right (by norm_num) hk
  have hq : 2^(max w (k+1)) ≤ 2^(w+1) :=
    Nat.pow_le_pow_right (by norm_num) (max_le (by omega) (by omega))
  have hs : w + (k+1) + 2 ≤ 2*P := by omega
  have hW' : W ≤ 4*P := by omega
  have hpow : P ≤ P^5 := by simpa using Nat.pow_le_pow_right hP (show 1 ≤ 5 by decide)
  unfold ctrlPushExtra tcost
  calc
    _ ≤ (2^w*(4*P) + 2^(w+1)*(4*P)) + 2^9*(2*P)^4*(4*P)*2^(w+1) := by
      gcongr
    _ = 12 * P * 2^w + 65536 * P^5 * 2^w := by rw [pow_succ]; ring
    _ ≤ 12 * P^5 * 2^w + 65536 * P^5 * 2^w := by gcongr
    _ = (12+65536) * P^5 * 2^w := by ring
    _ ≤ _ := by gcongr; norm_num

theorem ctrl_bundle {a b c m t w W S : ℕ} (ea : Fin (2^a) ≃ V a) (eb : Fin (2^b) ≃ V b)
    {D : (In0 a b c m t → Bool) → Fin 5 × Fin (w+1) → Bool}
    {L : (In0 a b c m t → Bool) → Fin w × Fin (a+1) → Bool}
    {M : (In0 a b c m t → Bool) → Fin w × Fin (b+1) → Bool}
    {E : (In0 a b c m t → Bool) → Fin w × Fin c → Bool}
    {X : (In0 a b c m t → Bool) → V a → Bool}
    {Y : (In0 a b c m t → Bool) → V b → Bool}
    {Z : (In0 a b c m t → Bool) → V c → Bool}
    (hD : Cmp _ _ S D) (hL : Cmp _ _ S L) (hM : Cmp _ _ S M)
    (hE : Cmp _ _ S E) (hX : Cmp _ _ S X) (hY : Cmp _ _ S Y) (hZ : Cmp _ _ S Z) :
    Cmp (In0 a b c m t)
      ((Fin 5 × Fin (w+1)) ⊕ ((V w × Fin W) ⊕ ((V w × Fin W) ⊕ ((Fin w × Fin c) ⊕ V c))))
      (7*S + ctrlPushExtra w a W + ctrlPushExtra w b W)
      (fun v => elim (D v) (elim (ctrlPushed (L v) (X v) (fTab a b c m t W ea v))
        (elim (ctrlPushed (M v) (Y v) (gTab a b c m t W eb v)) (elim (E v) (Z v))))) := by
  have hf := ctrl_push hL hX (fz4_fTab a b c m t W ea)
  have hg := ctrl_push hM hY (fz4_gTab a b c m t W eb)
  exact (hD.pair (hf.pair (hg.pair (hE.pair hZ)))).mono (by unfold ctrlPushExtra; omega)

theorem ctrl_eval_fiber {I J R : Type} [Fintype I] [Fintype J] [DecidableEq J] [Semiring R]
    (L : I → J) (m : I → Bool) (F : I → R) (K : J → R) :
    (∑ j, (∑ i, if L i = j ∧ m i = true then F i else 0) * K j) =
      ∑ i, if m i then F i * K (L i) else 0 := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  cases m i <;> simp [ite_mul]

theorem ctrl_regroup {a b w W : ℕ}
    (L : Fin w × Fin (a+1) → Bool) (M : Fin w × Fin (b+1) → Bool)
    (mx : V a → Bool) (my : V b → Bool) (F : V a × Fin W → Bool) (G : V b × Fin W → Bool)
    (R : V w → V w → Prop) [DecidableRel R] :
    (∑ u, ∑ v, if R u v then tab (ctrlPushed L mx F) u * tab (ctrlPushed M my G) v else 0) =
      ∑ x, ∑ y, if mx x = true ∧ my y = true ∧ R (ctrlAffine L x) (ctrlAffine M y) then
        tab F x * tab G y else 0 := by
  classical
  let h (u v : V w) : BitVec W := if R u v then 1 else 0
  let ff := tab (ctrlPushed L mx F)
  let gg := tab (ctrlPushed M my G)
  have t (u v : V w) : (if R u v then ff u * gg v else 0) = ff u * (gg v * h u v) := by
    by_cases hr : R u v <;> simp [h,hr]
  change (∑ u, ∑ v, if R u v then ff u * gg v else 0) = _
  simp_rw [t, ← Finset.mul_sum]
  dsimp only [ff, gg, ctrlPushed]
  rw [tab_untab, tab_untab, ctrl_eval_fiber]
  apply sum_congr rfl
  intro x _
  cases mx x with
  | false => simp
  | true =>
    simp only [ite_true, true_and, ctrl_eval_fiber, Finset.mul_sum]
    apply sum_congr rfl
    intro y _
    by_cases hr : R (ctrlAffine L x) (ctrlAffine M y) <;> cases my y <;> simp [hr,h]

def ceCat {α : Type} {b c : ℕ} (f0 f1 f2 : Fin c → α) (f3 : Fin b → α) (f4 : Fin c → α) :
    Fin (c + c + c + b + c) → α :=
  Fin.append (Fin.append (Fin.append (Fin.append f0 f1) f2) f3) f4

theorem swCntFalse {n : Nat} (j : Nat) : cnt (fun _ : Fin n => false) j = 0 := by
  simp [cnt]

theorem swCntAppendLeft {m n : Nat} (f : Fin m → Bool) (g : Fin n → Bool) (j : Nat) (h : j ≤ m) :
    cnt (Fin.append f g) j = cnt f j := by
  induction j with
  | zero => simp [cnt_zero]
  | succ j ih =>
    have hj : j < m := by omega
    rw [cnt_succ _ _ (by omega), cnt_succ _ _ hj, ih (by omega)]
    exact congrArg (fun x : Bool => cnt f j + if x = true then 1 else 0)
      (Fin.append_left f g (⟨j,hj⟩ : Fin m))

theorem swCntAppendRight {m n : Nat} (f : Fin m → Bool) (g : Fin n → Bool)
    (j : Nat) (h : j ≤ n) :
    cnt (Fin.append f g) (m+j) = cnt f m + cnt g j := by
  induction j with
  | zero => simp [swCntAppendLeft, cnt_zero]
  | succ j ih =>
    have hj : j < n := by omega
    rw [Nat.add_succ, cnt_succ _ _ (by omega), cnt_succ _ _ hj, ih (by omega), Nat.add_assoc]
    have e := Fin.append_right f g (⟨j,hj⟩ : Fin n)
    simpa only [Fin.natAdd_mk] using congrArg
      (fun x : Bool => cnt f m + (cnt g j + if x = true then 1 else 0)) e

theorem swCntAppendAll {m n : Nat} (f : Fin m → Bool) (g : Fin n → Bool) :
    cnt (Fin.append f g) (m+n) = cnt f m + cnt g n :=
  swCntAppendRight f g n le_rfl

abbrev ceSeg (b c : ℕ) := Fin c ⊕ Fin c ⊕ Fin c ⊕ Fin b ⊕ Fin c

def cePos {b c : ℕ} : ceSeg b c → Fin (c+c+c+b+c)
  | .inl k => (((k.castAdd c).castAdd c).castAdd b).castAdd c
  | .inr (.inl k) => (((k.natAdd c).castAdd c).castAdd b).castAdd c
  | .inr (.inr (.inl k)) => ((k.natAdd (c+c)).castAdd b).castAdd c
  | .inr (.inr (.inr (.inl j))) => (j.natAdd (c+c+c)).castAdd c
  | .inr (.inr (.inr (.inr k))) => k.natAdd (c+c+c+b)

def ceChoose {b c : ℕ} {A : Type} (f g h : Fin c → A) (l : Fin b → A) (r : Fin c → A) :
    ceSeg b c → A := elim f (elim g (elim h (elim l r)))

theorem ceCat_pos {b c : ℕ} {A : Type} (f g h : Fin c → A) (l : Fin b → A) (r : Fin c → A)
    (p : ceSeg b c) : ceCat f g h l r (cePos p) = ceChoose f g h l r p := by
  rcases p with p|p|p|p|p <;> simp only [cePos,ceCat,ceChoose,
    Fin.append_left,Fin.append_right,elim_inl,elim_inr]

def ceRank {b c : ℕ} (f g h : Fin c → Bool) (l : Fin b → Bool) (r : Fin c → Bool) :
    ceSeg b c → ℕ :=
  ceChoose (fun k => cnt f k.val) (fun k => cnt f c + cnt g k.val)
    (fun k => cnt f c + cnt g c + cnt h k.val)
    (fun j => cnt f c + cnt g c + cnt h c + cnt l j.val)
    (fun k => cnt f c + cnt g c + cnt h c + cnt l b + cnt r k.val)

theorem ceApL {n k : ℕ} (f : Fin n → Bool) (g : Fin k → Bool) (i : Fin n) :
    cnt (Fin.append f g) (i.castAdd k).val = cnt f i.val :=
  swCntAppendLeft f g i.val (Nat.le_of_lt i.isLt)

theorem ceApR {n k : ℕ} (f : Fin n → Bool) (g : Fin k → Bool) (i : Fin k) :
    cnt (Fin.append f g) (i.natAdd n).val = cnt f n + cnt g i.val :=
  swCntAppendRight f g i.val (Nat.le_of_lt i.isLt)

theorem ceCat_cnt {b c : ℕ} (f g h : Fin c → Bool) (l : Fin b → Bool) (r : Fin c → Bool)
    (p : ceSeg b c) : cnt (ceCat f g h l r) (cePos p).val = ceRank f g h l r p := by
  rcases p with p|p|p|p|p <;> simp only [cePos,ceCat,ceRank,ceChoose,elim_inl,elim_inr,
    ceApL,ceApR,swCntAppendAll]

theorem ceHit {N n w : ℕ} (fl : Fin N → Bool) (pay : Fin N × Fin n → Bool)
    (x : V n) (fit : cnt fl N ≤ w) (i : Fin N) (hi : fl i = true) :
    co ((mat (ctrlPacked w fl pay)).mulVec x) (cnt fl i.val) =
      ∑ j, ctrlF (pay (i,j))*x j := by
  have hlt := (ctrl_rank_lt fl i hi).trans_le fit
  simp only [co,dif_pos hlt,Matrix.mulVec,dotProduct,mat,
    ctrlPacked_hit fl pay i (⟨_,hlt⟩ : Fin w) _ hi rfl,ctrlF]

theorem ceTail {N n w : ℕ} (fl : Fin N → Bool) (pay : Fin N × Fin n → Bool)
    (x : V n) (i : Fin w) (hi : cnt fl N ≤ i.val) :
    (mat (ctrlPacked w fl pay)).mulVec x i = 0 := by
  simp [Matrix.mulVec,dotProduct,mat,ctrlPacked_tail fl pay i _ hi]

theorem swRankQuant {n : Nat} (f : Fin n → Bool) (P : Nat → Prop) (Q : Fin n → Prop)
    (h : ∀ i, f i = true → (P (cnt f i.val) ↔ Q i)) :
    (∀ j < cnt f n, P j) ↔ ∀ i, f i = true → Q i := by
  constructor
  · intro hh i hi
    exact (h i hi).mp (hh _ (ctrl_rank_lt f i hi))
  · intro hh j hj
    obtain ⟨i,hi,rfl⟩ := ctrl_rank_surj f j hj
    exact (h i hi).mpr (hh i hi)

theorem ctrl_parts_cost (a b c m t : ℕ) :
    let P := a+b+c+m+t+4
    let w := wOf a b c
    let W := WOf a b c t
    7*(2^40*P^18*Phi w) + ctrlPushExtra w a W + ctrlPushExtra w b W ≤
      2^50*P^20*Phi w := by
  let P := a+b+c+m+t+4
  let w := wOf a b c
  let W := WOf a b c t
  have ha : a ≤ w := le_max_left _ _
  have hb : b ≤ w := le_trans (le_max_left _ _) (le_max_right _ _)
  have hP : 1 ≤ P := by dsimp [P]; omega
  have hw : w+2 ≤ P := by dsimp [w,wOf,P]; omega
  have hW : W+1 ≤ 4*P := by dsimp [W,WOf,wOf,P]; omega
  have e {n : ℕ} (hn : n ≤ 20) : P^n ≤ P^20 := Nat.pow_le_pow_right hP hn
  have ex (k : ℕ) (hk : k ≤ w) : ctrlPushExtra w k W ≤ 2^18 * (P^20*Phi w) := calc
    _ ≤ 2^18*P^5*2^w := ctrl_push_extra hk hw hW
    _ ≤ 2^18*P^20*Phi w :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (e (show 5 ≤ 20 by decide))) (two_pow_le_Phi _)
    _ = _ := Nat.mul_assoc _ _ _
  have hmain : 2^40 * P^18 * Phi w ≤ 2^40 * (P^20 * Phi w) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (e (show 18 ≤ 20 by decide)))
  change 7*(2^40*P^18*Phi w) + ctrlPushExtra w a W + ctrlPushExtra w b W ≤ 2^50*P^20*Phi w
  rw [Nat.mul_assoc (2^50)]
  exact le_trans (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hmain) (ex a ha)) (ex b hb))
    ((show ∀ n : ℕ, 7*(2^40*n) + 2^18*n + 2^18*n ≤ 2^50*n from fun n => by omega) _)

def swPartSize (a b c m t : Nat) := 2^40 * (a+b+c+m+t+4)^18 * Phi (wOf a b c)

end Donor

namespace Donor

private def rcRead {ι : Type} {W : ℕ} (v : ι → Bool) (f : Fin W → ι) : BitVec W :=
  bv (fun i => v (f i))

private def rcProblem (X Y Z : Type) [Fintype Y] (W C : ℕ) : Prop :=
  ∀ {ι : Type} (A : X → Y → Fin W → ι) (B : Y → Z → Fin W → ι),
  Cmp ι ((X × Z) × Fin W) C (fun v => untab (fun p =>
    ∑ j, rcRead v (A p.1 j) * rcRead v (B j p.2)))

private theorem rcSum {ι T : Type} {W C : ℕ} (f : T → (ι → Bool) → BitVec W)
    (h : ∀ j, Cw ι W C (f j)) (s : Finset T) :
    Cw ι W (W + s.card * (C + 20 * (W + 1))) (fun v => ∑ j ∈ s, f j v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cw.const (ι := ι) (0 : BitVec W)
  | @insert j s hj ih =>
    simpa [hj, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Cw.add (h j) ih)

private theorem rcNaive {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (W D : ℕ) (hXZ : card (X × Z) ≤ D)
    (hXYZ : card (X × Z) * card Y ≤ D) :
    rcProblem X Y Z W (D * (64 * (W+1)^2)) := by
  intro ι A B
  have h (p : X × Z) (j : Y) :
      Cw ι W (30 * (W+1)^2) (fun v => rcRead v (A p.1 j) * rcRead v (B j p.2)) :=
    by simpa only [Nat.zero_add, rcRead] using (Cw.mul (Cw.var (A p.1 j)) (Cw.var (B j p.2)))
  have hs (p : X × Z) := rcSum _ (h p) Finset.univ
  simp only [Finset.card_univ] at hs
  refine (Cmp.ofWords hs).mono ?_
  have hw : W+1 ≤ (W+1)^2 := by nlinarith
  calc
    _ = card (X × Z) * W +
        (card (X × Z) * card Y) * (30*(W+1)^2 + 20*(W+1)) := by ring
    _ ≤ D * W + D * (30*(W+1)^2 + 20*(W+1)) := by gcongr
    _ ≤ _ := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)

private def rcL {R : Type} [Add R] [Sub R] (a b c d : R) (i : Fin 7) : R :=
  match i.val with
  | 0 => a+d
  | 1 => c+d
  | 2 => a
  | 3 => d
  | 4 => a+b
  | 5 => c-a
  | _ => b-d

private def rcR {R : Type} [Add R] [Sub R] (e f g h : R) (i : Fin 7) : R :=
  match i.val with
  | 0 => e+h
  | 1 => e
  | 2 => f-h
  | 3 => g-e
  | 4 => h
  | 5 => e+f
  | _ => g+h

private def rcOut {R : Type} [Add R] [Sub R] (p : Fin 7 → R) : Bool → Bool → R
  | false, false => (p 0 + p 3) + (p 6 - p 4)
  | false, true => p 2 + p 4
  | true, false => p 1 + p 3
  | true, true => (p 0 - p 1) + (p 2 + p 5)

private theorem rcLCw {ι : Type} {W : ℕ} (a b c d : Fin W → ι) (i : Fin 7) :
    Cw ι W (20*(W+1)) (fun v => rcL (rcRead v a) (rcRead v b) (rcRead v c) (rcRead v d) i) := by
  have H (u : Fin W → ι) : Cw ι W 0 (fun v => rcRead v u) := Cw.var _
  fin_cases i <;> dsimp [rcL]
  · simpa only [Nat.zero_add] using Cw.add (H a) (H d)
  · simpa only [Nat.zero_add] using Cw.add (H c) (H d)
  · exact (H a).mono (Nat.zero_le _)
  · exact (H d).mono (Nat.zero_le _)
  · simpa only [Nat.zero_add] using Cw.add (H a) (H b)
  · simpa only [Nat.zero_add] using Cw.sub (H c) (H a)
  · simpa only [Nat.zero_add] using Cw.sub (H b) (H d)

private theorem rcRCw {ι : Type} {W : ℕ} (a b c d : Fin W → ι) (i : Fin 7) :
    Cw ι W (20*(W+1)) (fun v => rcR (rcRead v a) (rcRead v b) (rcRead v c) (rcRead v d) i) := by
  have H (u : Fin W → ι) : Cw ι W 0 (fun v => rcRead v u) := Cw.var _
  fin_cases i <;> dsimp [rcR]
  · simpa only [Nat.zero_add] using Cw.add (H a) (H d)
  · exact (H a).mono (Nat.zero_le _)
  · simpa only [Nat.zero_add] using Cw.sub (H b) (H d)
  · simpa only [Nat.zero_add] using Cw.sub (H c) (H a)
  · exact (H d).mono (Nat.zero_le _)
  · simpa only [Nat.zero_add] using Cw.add (H a) (H b)
  · simpa only [Nat.zero_add] using Cw.add (H c) (H d)

private theorem rcOutCw {ι : Type} {W : ℕ} (f : Fin 7 → Fin W → ι) (a b : Bool) :
    Cw ι W (60*(W+1)) (fun v => rcOut (fun k => rcRead v (f k)) a b) := by
  have H (k : Fin 7) : Cw ι W 0 (fun v => rcRead v (f k)) := Cw.var _
  cases a <;> cases b
  · exact (Cw.add (Cw.add (H 0) (H 3)) (Cw.sub (H 6) (H 4))).mono (by omega)
  · exact (Cw.add (H 2) (H 4)).mono (by omega)
  · exact (Cw.add (H 1) (H 3)).mono (by omega)
  · exact (Cw.add (Cw.sub (H 0) (H 1)) (Cw.add (H 2) (H 5))).mono (by omega)

private theorem rcLaw {R T : Type} [CommRing R] [Fintype T]
    (A B : Bool → Bool → T → R) (x z : Bool) :
    rcOut (fun k => ∑ j, rcL (A false false j) (A false true j) (A true false j) (A true true j) k *
      rcR (B false false j) (B false true j) (B true false j) (B true true j) k) x z =
    ∑ j : Bool × T, A x j.1 j.2 * B j.1 z j.2 := by
  cases x <;> cases z <;>
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, rcOut, rcL, rcR,
      show (0 : Fin 7).val = 0 by rfl, show (1 : Fin 7).val = 1 by rfl,
      show (2 : Fin 7).val = 2 by rfl, show (3 : Fin 7).val = 3 by rfl,
      show (4 : Fin 7).val = 4 by rfl, show (5 : Fin 7).val = 5 by rfl,
      show (6 : Fin 7).val = 6 by rfl,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib] <;>
    apply sum_congr rfl <;> intro j _ <;> ring

private theorem rcStep {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    {W C M : ℕ} (hP : rcProblem X Y Z W C)
    (hXY : card (X × Y) ≤ M) (hYZ : card (Y × Z) ≤ M)
    (hXZ : card (X × Z) ≤ M) :
    rcProblem (Bool × X) (Bool × Y) (Bool × Z) W (7*C + 520*(W+1)*M) := by
  intro ι A B
  let L (i : Fin 7) (v : ι → Bool) (p : X × Y) := rcL
    (rcRead v (A (false,p.1) (false,p.2))) (rcRead v (A (false,p.1) (true,p.2)))
    (rcRead v (A (true,p.1) (false,p.2))) (rcRead v (A (true,p.1) (true,p.2))) i
  let R (i : Fin 7) (v : ι → Bool) (p : Y × Z) := rcR
    (rcRead v (B (false,p.1) (false,p.2))) (rcRead v (B (false,p.1) (true,p.2)))
    (rcRead v (B (true,p.1) (false,p.2))) (rcRead v (B (true,p.1) (true,p.2))) i
  let P (i : Fin 7) (v : ι → Bool) (p : X × Z) := ∑ j, L i v (p.1,j) * R i v (j,p.2)
  have hp (i : Fin 7) : Cmp ι ((X × Z) × Fin W) (M*(20*(W+1)) + M*(20*(W+1)) + C)
      (fun v => untab (P i v)) := by
    have l : Cmp ι ((X × Y) × Fin W) (M*(20*(W+1))) (fun v => untab (L i v)) :=
      (Cmp.ofWords (G := L i) (fun p => rcLCw _ _ _ _ i)).mono (Nat.mul_le_mul_right _ hXY)
    have r : Cmp ι ((Y × Z) × Fin W) (M*(20*(W+1))) (fun v => untab (R i v)) :=
      (Cmp.ofWords (G := R i) (fun p => rcRCw _ _ _ _ i)).mono (Nat.mul_le_mul_right _ hYZ)
    refine ((l.pair r).comp (hP (fun x y t => inl ((x,y),t))
      (fun y z t => inr ((y,z),t)))).congr ?_
    intro v p
    simp only [rcRead, elim_inl, elim_inr, untab, bv_getLsbD, P]
  let G (w : Fin 7 × ((X × Z) × Fin W) → Bool) (p : (Bool × X) × (Bool × Z)) :=
    rcOut (fun i => rcRead w (fun t => (i,((p.1.2,p.2.2),t)))) p.1.1 p.2.1
  have hG := Cmp.ofWords (G := G) (fun p => rcOutCw _ p.1.1 p.2.1)
  refine ((Cmp.piU hp).comp hG).congr ?_ |>.mono ?_
  · intro v p
    rcases p with ⟨⟨⟨x,u⟩,⟨z,w⟩⟩,t⟩
    simp only [untab, G, rcRead, bv_getLsbD]
    exact congrArg (fun q : BitVec W => q.getLsbD t.val)
      (rcLaw (fun x y j => rcRead v (A (x,u) (y,j))) (fun y z j => rcRead v (B (y,j) (z,w))) x z)
  · have hh : card ((Bool × X) × (Bool × Z)) ≤ 4*M := by
      simp only [card_prod, card_bool] at hXZ ⊢
      nlinarith
    rw [card_fin]
    calc
      _ ≤ 7*(M*(20*(W+1)) + M*(20*(W+1)) + C) + (4*M)*(60*(W+1)) := by gcongr
      _ = _ := by ring

private def rcIx (a : ℕ) : ℕ → Type
  | 0 => Fin (2^a)
  | s+1 => Bool × rcIx a s

private def rcFintype (a : ℕ) : (s : ℕ) → Fintype (rcIx a s)
  | 0 => inferInstanceAs (Fintype (Fin (2^a)))
  | s+1 => @instFintypeProd _ _ inferInstance (rcFintype a s)

private theorem rcCard (a s : ℕ) : @card (rcIx a s) (rcFintype a s) = 2^a * 2^s := by
  induction s with
  | zero =>
    change card (Fin (2^a)) = _
    simp
  | succ s ih =>
    letI := rcFintype a s
    change card (Bool × rcIx a s) = _
    rw [card_prod, card_bool, ih, pow_succ]; ring

private def rcCost (W : ℕ) : ℕ → ℕ
  | 0 => 64*(W+1)^2
  | s+1 => 7*rcCost W s + 520*(W+1)*4^s

private theorem rcCostBound (W s : ℕ) :
    rcCost W s + 200*(W+1)^2*4^s ≤ 2048*(W+1)^2*7^s := by
  have hw : W+1 ≤ (W+1)^2 := by nlinarith
  induction s with
  | zero => simp only [rcCost, pow_zero, mul_one]; omega
  | succ s ih =>
    have h : 520*(W+1)*4^s ≤ 600*(W+1)^2*4^s :=
      Nat.mul_le_mul_right _ (by omega)
    simp only [rcCost, pow_succ (4:ℕ) s, pow_succ (7:ℕ) s]
    nlinarith only [h, ih]

private theorem rcPairCard (a b s D : ℕ) (h : 2^a * 2^b ≤ D) :
    letI := rcFintype a s
    letI := rcFintype b s
    card (rcIx a s × rcIx b s) ≤ D * 4^s := by
  letI := rcFintype a s
  letI := rcFintype b s
  change card (rcIx a s × rcIx b s) ≤ _
  rw [card_prod, rcCard, rcCard, show (4:ℕ) = 2*2 by decide, mul_pow]
  calc
    _ = (2^a * 2^b) * (2^s * 2^s) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ h

private theorem rcBuilt (W a b c s : ℕ) :
    @rcProblem (rcIx a s) (rcIx b s) (rcIx c s) (rcFintype b s) W
      (2^(a+b+c)*rcCost W s) := by
  let D := 2^(a+b+c)
  have cab : 2^a * 2^b ≤ D := by
    dsimp [D]; rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have cbc : 2^b * 2^c ≤ D := by
    dsimp [D]; rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have cac : 2^a * 2^c ≤ D := by
    dsimp [D]; rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  change @rcProblem (rcIx a s) (rcIx b s) (rcIx c s) (rcFintype b s) W (D * rcCost W s)
  induction s with
  | zero =>
    letI := rcFintype a 0
    letI := rcFintype b 0
    letI := rcFintype c 0
    apply rcNaive
    · simpa using rcPairCard a c 0 D cac
    · simp [card_prod, rcCard, D, pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  | succ s ih =>
    letI := rcFintype a s
    letI := rcFintype b s
    letI := rcFintype c s
    rw [show D*rcCost W (s+1) = 7*(D*rcCost W s) + 520*(W+1)*(D*4^s) by
      dsimp [rcCost]; ring]
    intro ι A B
    exact rcStep ih (rcPairCard a b s D cab) (rcPairCard b c s D cbc) (rcPairCard a c s D cac) A B

private theorem rcTransport {X Y Z X₁ Y₁ Z₁ : Type} [Fintype Y] [Fintype Y₁]
    {W C : ℕ} (ex : X ≃ X₁) (ey : Y ≃ Y₁) (ez : Z ≃ Z₁)
    (h : rcProblem X Y Z W C) : rcProblem X₁ Y₁ Z₁ W C := by
  intro ι A B
  have h₁ := h (fun x y => A (ex x) (ey y)) (fun y z => B (ey y) (ez z))
  have h₂ := h₁.comp (Cmp.wire (fun p : (X₁ × Z₁) × Fin W =>
    ((ex.symm p.1.1,ez.symm p.1.2),p.2)))
  rw [Nat.add_zero] at h₂
  apply h₂.congr
  rintro v ⟨⟨x,z⟩,t⟩
  simp only [untab, Equiv.apply_symm_apply]
  exact congrArg (fun q : BitVec W => q.getLsbD t.val)
    (ey.sum_comp (fun j => rcRead v (A x j) * rcRead v (B j z)))

private noncomputable def rcEquiv (a s : ℕ) (hs : s ≤ a) : rcIx (a-s) s ≃ V a := by
  letI := rcFintype (a-s) s
  exact Fintype.equivOfCardEq (by
    rw [rcCard, ← pow_add, Nat.sub_add_cancel hs]
    simp [V, ZMod.card])

theorem rectCore (W a b c s : ℕ) (ha : s ≤ a) (hb : s ≤ b) (hc : s ≤ c)
    {ι : Type} (A : V a → V b → Fin W → ι) (B : V b → V c → Fin W → ι) :
    Cmp ι ((V a × V c) × Fin W) (2048*(W+1)^2 * 2^(a+b+c-3*s) * 7^s)
      (fun v => untab (fun p => ∑ j, bv (fun t => v (A p.1 j t)) * bv (fun t => v (B j p.2 t)))) := by
  letI := rcFintype (b-s) s
  have h := rcTransport (rcEquiv a s ha) (rcEquiv b s hb) (rcEquiv c s hc)
    (rcBuilt W (a-s) (b-s) (c-s) s) A B
  apply h.mono
  rw [show a-s+(b-s)+(c-s) = a+b+c-3*s by omega]
  calc
    _ ≤ 2^(a+b+c-3*s)*(2048*(W+1)^2*7^s) :=
      Nat.mul_le_mul_left _ (le_trans (Nat.le_add_right _ _) (rcCostBound W s))
    _ = _ := by ring

private theorem rcBudget (w k m : ℕ) (h : k + 2*m ≤ w) :
    2^k * 7^m ≤ 2^(w%2) * 7^(w/2) := by
  have h₁ : k ≤ w%2 + 2*(w/2-m) := by omega
  have h₂ : 2^k ≤ 2^(w%2 + 2*(w/2-m)) := Nat.pow_le_pow_right (by decide) h₁
  calc
    _ ≤ 2^(w%2 + 2*(w/2-m))*7^m := Nat.mul_le_mul_right _ h₂
    _ = 2^(w%2)*4^(w/2-m)*7^m := by rw [pow_add, pow_mul]; norm_num
    _ ≤ 2^(w%2)*7^(w/2-m)*7^m := by gcongr; decide
    _ = _ := by rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]

theorem rcFinalCost (W w q d a b c : ℕ)
    (hx : q+d+a+b ≤ w) (hy : q+d+b+c ≤ w) (hz : q+d+a+c ≤ w) :
    let m := min a (min b c)
    (2^(d+a+b)+2^(d+b+c)+2^(d+a+c))*(2^7*(q+1)*(W+1)*2^q) +
      2^(q+d)*(2048*(W+1)^2*2^(a+b+c-3*m)*7^m) + (1 + 2^w) ≤
      2^30*(W+w+1)^3*(2^(w%2)*7^(w/2)) := by
  dsimp only
  let m := min a (min b c)
  let T := W+w+1
  let U := 2^(w%2)*7^(w/2)
  have hP : 2^w ≤ U := by simpa [U] using rcBudget w w 0 (by omega)
  have hbnd (e : ℕ) (he : q+e ≤ w) : 2^e * 2^q ≤ U := by
    rw [← pow_add]
    exact (Nat.pow_le_pow_right (by decide) (by omega : e+q ≤ w)).trans hP
  have h₁ := hbnd (d+a+b) (by omega)
  have h₂ := hbnd (d+b+c) (by omega)
  have h₃ := hbnd (d+a+c) (by omega)
  have h₄ : 2^(q+d)*2^(a+b+c-3*m)*7^m ≤ U := by
    rw [← pow_add]
    apply rcBudget
    dsimp [m]; omega
  have h₅ : (q+1)*(W+1) ≤ T^3 := by
    calc
      _ ≤ T*T := Nat.mul_le_mul (by dsimp [T]; omega) (by dsimp [T]; omega)
      _ ≤ _ := by dsimp [T]; nlinarith
  have h₆ : (W+1)^2 ≤ T^3 := by
    calc
      _ ≤ T^2 := Nat.pow_le_pow_left (by dsimp [T]; omega) _
      _ ≤ _ := Nat.pow_le_pow_right (by dsimp [T]; omega) (by decide)
  have h₇ : 1 ≤ U := by change 0 < U; dsimp [U]; positivity
  have h₈ : 1 ≤ T^3 := by change 0 < T^3; dsimp [T]; positivity
  have hs : (2^(d+a+b)+2^(d+b+c)+2^(d+a+c))*(2^7*(q+1)*(W+1)*2^q) ≤
      (3*128)*(T^3 * U) := by
    calc
      _ = 128*((q+1)*(W+1))*((2^(d+a+b)*2^q)+(2^(d+b+c)*2^q)+(2^(d+a+c)*2^q)) := by ring
      _ ≤ 128*T^3*(U+U+U) := by gcongr
      _ = _ := by ring
  have ht : 2^(q+d)*(2048*(W+1)^2*2^(a+b+c-3*m)*7^m) ≤ 2048*(T^3 * U) := by
    calc
      _ = 2048*(W+1)^2*(2^(q+d)*2^(a+b+c-3*m)*7^m) := by ring
      _ ≤ 2048*T^3*U := by gcongr
      _ = _ := by ring
  have hU : U ≤ T^3*U := by simpa only [one_mul] using Nat.mul_le_mul_right U h₈
  change _ + (2^(q+d)*(2048*(W+1)^2*2^(a+b+c-3*m)*7^m)) + _ ≤ 2^30*T^3*U
  rw [Nat.mul_assoc (2^30)]
  omega

end Donor

namespace Donor

def swTransform {q W : Nat} (F : V q → BitVec W) (z : V q) : BitVec W :=
  ∑ x, sgn (z ⬝ᵥ x) * F x

theorem swConv {q W : Nat} (F G : V q → BitVec W) (t : V q) :
    swTransform (fun z => swTransform F z * swTransform G z) t =
      2 ^ q * ∑ x, F x * G (t + x) := by
  classical
  have hterm (z : V q) :
      sgn (t ⬝ᵥ z) * (swTransform F z * swTransform G z) =
        ∑ x, ∑ y, sgn (z ⬝ᵥ (x + y + t)) * (F x * G y) := by
    unfold swTransform
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [dotProduct_add, dotProduct_add, fe_sgn_add, fe_sgn_add, dotProduct_comm t z]
    ring
  change (∑ z, sgn (t ⬝ᵥ z) * (swTransform F z * swTransform G z)) = _
  simp_rw [hterm]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  have hxy (y : V q) :
      (∑ z : V q, sgn (z ⬝ᵥ (x+y+t)) * (F x * G y)) =
        if y = t+x then 2^q * (F x * G y) else 0 := by
    rw [← Finset.sum_mul, show (∑ z : V q, (sgn (z ⬝ᵥ (x+y+t)) : BitVec W)) =
        (if x+y+t = 0 then 2^q else 0) from fg_char q (x+y+t)]
    have iff0 : x+y+t = 0 ↔ y = t+x := by
      have hh : ∀ a b c : ZMod 2, a+b+c = 0 ↔ b = c+a := by decide
      constructor
      · intro h
        exact funext fun j => (hh _ _ _).mp (congrFun h j)
      · intro h
        exact funext fun j => (hh _ _ _).mpr (congrFun h j)
    by_cases h : y = t+x
    · rw [if_pos (iff0.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (iff0.mp hh)), if_neg h, zero_mul]
  simp_rw [hxy]
  rw [sum_ite_eq']
  simp

theorem swContract {q W : Nat} {ι : Type} [Fintype ι]
    (F G : ι → V q → BitVec W) (t : V q) :
    swTransform (fun z => ∑ i, swTransform (F i) z * swTransform (G i) z) t =
      2^q * ∑ i, ∑ x, F i x * G i (t+x) := by
  unfold swTransform
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  simpa only [swTransform, Finset.mul_sum] using swConv (F i) (G i) t

theorem swBit {q W : Nat} (x : BitVec W) (i : Nat) (hi : q+i < W) :
    ((2^q : BitVec W) * x).getLsbD (q+i) = x.getLsbD i := by
  have hk : (2^q : BitVec W) = BitVec.twoPow W q := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_twoPow]
    exact (Nat.pow_mod ..).symm
  rw [hk, mul_comm, BitVec.mul_twoPow_eq_shiftLeft, BitVec.getLsbD_shiftLeft]
  simp [hi]

abbrev SWRect (W a b c cost : Nat) :=
  ∀ {ι : Type} (A : V a → V b → Fin W → ι) (B : V b → V c → Fin W → ι),
    Cmp ι ((V a × V c) × Fin W) cost (fun v => untab (fun p =>
      ∑ j, bv (fun t => v (A p.1 j t)) * bv (fun t => v (B j p.2 t))))

def swCost (q d a b c W R : Nat) : Nat :=
  (2^(d+a+b) + 2^(d+b+c) + 2^(d+a+c)) * whtCost q W + 2^(q+d) * R

theorem swPacked {q d a b c W R : Nat} (hm : SWRect W a b c R)
    {ι : Type} (F : V q → V d → V a → V b → Fin W → ι)
    (G : V q → V d → V b → V c → Fin W → ι) :
    Cmp ι ((V d × V a × V c) × V q × Fin W) (swCost q d a b c W R)
      (fun v p => ((2^q : BitVec W) * ∑ k, ∑ x,
        bv (fun j => v (F x p.1.1 p.1.2.1 k j)) *
        bv (fun j => v (G (p.2.1+x) p.1.1 k p.1.2.2 j))).getLsbD p.2.2.val) := by
  let U := ((V d × V a × V b) × V q × Fin W) ⊕ ((V d × V b × V c) × V q × Fin W)
  let T := (V q × V d) × (V a × V c) × Fin W
  let frontF := Cmp.piU (fun k : V d × V a × V b =>
    Cmp.sel (fun j : V q × Fin W => F j.1 k.1 k.2.1 k.2.2 j.2) (cmp_wht q W))
  let frontG := Cmp.piU (fun k : V d × V b × V c =>
    Cmp.sel (fun j : V q × Fin W => G j.1 k.1 k.2.1 k.2.2 j.2) (cmp_wht q W))
  let mult := Cmp.piU (fun p : V q × V d =>
    hm (ι := U) (fun i j t => inl ((p.2,i,j),p.1,t))
      (fun j k t => inr ((p.2,j,k),p.1,t)))
  let back := Cmp.piU (fun p : V d × V a × V c =>
    Cmp.sel (fun k : V q × Fin W => ((k.1,p.1),(p.2.1,p.2.2),k.2) : V q × Fin W → T)
      (cmp_wht q W))
  have H := Cmp.comp (Cmp.comp (Cmp.pair frontF frontG) mult) back
  refine Cmp.mono (Cmp.congr H ?_) ?_
  · rintro v ⟨⟨delta,i,l⟩,z,j⟩
    let A := fun k x => bv (fun j => v (F x delta i k j))
    let B := fun k x => bv (fun j => v (G x delta k l j))
    change (∑ t, sgn (z ⬝ᵥ t) * bv (fun e : Fin W =>
      (∑ k, bv (fun f : Fin W => (swTransform (A k) t).getLsbD f.val) *
        bv (fun f : Fin W => (swTransform (B k) t).getLsbD f.val) : BitVec W).getLsbD e.val)).getLsbD j.val =
      ((2^q : BitVec W) * ∑ k, ∑ x, A k x * B k (z+x)).getLsbD j.val
    simp only [bv_getLsbD]
    exact congrArg (fun x : BitVec W => x.getLsbD j.val) (swContract A B z)
  · simp only [card_prod, fp_cardV, swCost, pow_add]
    exact le_of_eq (by ring)

def swPre {k : Nat} (x : V k) (r : Nat → ZMod 2) (i : Nat) : ZMod 2 :=
  if h : i < k then x ⟨i,h⟩ else r (i-k)

def sw4 (w : Nat) {q d a b : Nat} (Q : V q) (D : V d) (A : V a) (B : V b) : V w :=
  fun i => swPre Q (swPre D (swPre A (swPre B (fun _ => 0)))) i.val

def swSl (off n : Nat) {w : Nat} (x : V w) : V n := fun i => co x (off+i.val)

def swTail (n : Nat) {w : Nat} (x : V w) : Prop := ∀ j : Fin w, n ≤ j.val → x j = 0

theorem swPre1 {k : Nat} (x : V k) (r : Nat → ZMod 2) (i : Fin k) :
    swPre x r i.val = x i := by simp [swPre]

theorem swPre2 {k : Nat} (x : V k) (r : Nat → ZMod 2) (i : Nat) :
    swPre x r (k+i) = r i := by simp [swPre]

theorem swRead4 {w q d a b : Nat} (hf : q+d+a+b ≤ w)
    (Q : V q) (D : V d) (A : V a) (B : V b) :
    swSl 0 q (sw4 w Q D A B) = Q ∧ swSl q d (sw4 w Q D A B) = D ∧
    swSl (q+d) a (sw4 w Q D A B) = A ∧ swSl (q+d+a) b (sw4 w Q D A B) = B ∧
    swTail (q+d+a+b) (sw4 w Q D A B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext i
    simp [swSl, co, show i.val < w by omega, sw4, swPre1]
  · funext i
    simp [swSl, co, show q+i.val < w by omega, sw4, swPre1, swPre2]
  · funext i
    simp [swSl, co, show q+(d+i.val) < w by omega, sw4, Nat.add_assoc, swPre1, swPre2]
  · funext i
    simp [swSl, co, show q+(d+(a+i.val)) < w by omega, sw4, Nat.add_assoc, swPre1, swPre2]
  · intro i hi
    have e : i.val = q+(d+(a+(b+(i.val-(q+d+a+b))))) := by omega
    unfold sw4
    rw [e]
    simp only [swPre2]

theorem swEta {w q d a b : Nat} (x : V w) (ht : swTail (q+d+a+b) x) :
    sw4 w (swSl 0 q x) (swSl q d x) (swSl (q+d) a x) (swSl (q+d+a) b x) = x := by
  funext i
  simp only [sw4, swPre]
  split_ifs with h1 h2 h3 h4
  · simp [swSl, co]
  · simp [swSl, co, show q+(i.val-q) = i.val by omega]
  · simp [swSl, co, show q+d+(i.val-q-d) = i.val by omega]
  · simp [swSl, co, show q+d+a+(i.val-q-d-a) = i.val by omega]
  · exact (ht i (by omega)).symm

theorem swStdSl {w q d k a b : Nat} (x y z : V w) :
    Std w q d k a b x y z ↔
      swSl 0 q y = swSl 0 q z + swSl 0 q x ∧
      swSl q d x = swSl q d z ∧ swSl q d y = swSl q d z ∧
      swSl (q+d) a x = swSl (q+d) a z ∧
      swSl (q+d+a) k x = swSl (q+d) k y ∧
      swSl (q+d+k) b y = swSl (q+d+a) b z ∧
      swTail (q+d+a+k) x ∧ swTail (q+d+k+b) y ∧ swTail (q+d+a+b) z := by
  have hh : ∀ i j k : ZMod 2, i+j = k ↔ j = k+i := by decide
  constructor
  · rintro ⟨hq,hd,ha,hk,hb,hx,hy,hz⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hx, hy, hz⟩
    · funext i; simpa [swSl] using (hh _ _ _).mp (hq i.val i.isLt)
    · funext i; exact (hd i.val i.isLt).1
    · funext i; exact (hd i.val i.isLt).2
    · funext i; exact ha i.val i.isLt
    · funext i; exact hk i.val i.isLt
    · funext i; exact hb i.val i.isLt
  · rintro ⟨hq,hdx,hdy,ha,hk,hb,hx,hy,hz⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, hx, hy, hz⟩
    · intro i hi; apply (hh _ _ _).mpr; simpa [swSl] using congrFun hq ⟨i,hi⟩
    · intro i hi; exact ⟨congrFun hdx ⟨i,hi⟩,congrFun hdy ⟨i,hi⟩⟩
    · intro i hi; exact congrFun ha ⟨i,hi⟩
    · intro i hi; exact congrFun hk ⟨i,hi⟩
    · intro i hi; exact congrFun hb ⟨i,hi⟩

theorem swSumGraph {α β γ M : Type} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (pick : α → β → Prop) [DecidableRel pick] (u : γ → α) (v : γ → β) (ex : α → γ)
    (left : LeftInverse ex u)
    (spec : ∀ x y, pick x y ↔ u (ex x) = x ∧ v (ex x) = y)
    (f : α → β → M) :
    (∑ x, ∑ y, if pick x y then f x y else 0) = ∑ p, f (u p) (v p) := by
  classical
  have step (x : α) : (∑ y, if pick x y then f x y else 0) =
      if u (ex x) = x then f x (v (ex x)) else 0 := by
    by_cases h : u (ex x) = x
    · simp only [spec, h, true_and, ite_true, Finset.sum_ite_eq, mem_univ]
    · simp [spec, h]
  simp_rw [step]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun x => u (ex x) = x) = Finset.univ.image u := by
    ext x
    simp only [Finset.mem_filter, mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨ex x, h⟩
    · rintro ⟨y,rfl⟩; rw [left y]
  rw [he, Finset.sum_image (fun _ _ _ _ h => left.injective h)]
  exact sum_congr rfl fun i _ => by rw [left i]

theorem swStdSum {w W q d k a b : Nat}
    (hx : q+d+a+k ≤ w) (hy : q+d+k+b ≤ w)
    (z : V w) (ht : swTail (q+d+a+b) z) (F G : V w → BitVec W) :
    (∑ x, ∑ y, if Std w q d k a b x y z then F x * G y else 0) =
      ∑ j : V k, ∑ s : V q,
        F (sw4 w s (swSl q d z) (swSl (q+d) a z) j) *
        G (sw4 w (swSl 0 q z+s) (swSl q d z) j (swSl (q+d+a) b z)) := by
  let K := V k × V q
  let U (p : K) := sw4 w p.2 (swSl q d z) (swSl (q+d) a z) p.1
  let Vv (p : K) := sw4 w (swSl 0 q z+p.2) (swSl q d z) p.1 (swSl (q+d+a) b z)
  let ex (x : V w) : K := (swSl (q+d+a) k x,swSl 0 q x)
  have L : LeftInverse ex U := by
    intro p
    have e := swRead4 hx p.2 (swSl q d z) (swSl (q+d) a z) p.1
    exact Prod.ext e.2.2.2.1 e.1
  have H (x y : V w) : Std w q d k a b x y z ↔ U (ex x) = x ∧ Vv (ex x) = y := by
    constructor
    · intro h
      obtain ⟨hQ,hD,hD',hA,hK,hB,hX,hY,_⟩ := (swStdSl x y z).mp h
      constructor
      · simpa only [U, ex, hD, hA] using swEta x hX
      · simpa only [Vv, ex, hQ, hD', ← hK, hB] using swEta y hY
    · rintro ⟨h1,h2⟩
      let p := ex x
      have ex1 := swRead4 hx p.2 (swSl q d z) (swSl (q+d) a z) p.1
      have ex2 := swRead4 hy (swSl 0 q z+p.2) (swSl q d z) p.1 (swSl (q+d+a) b z)
      change U p = x at h1
      change Vv p = y at h2
      rw [← h1, ← h2, swStdSl]
      exact ⟨ex2.1.trans (congrArg _ ex1.1.symm), ex1.2.1, ex2.2.1,
        ex1.2.2.1, ex1.2.2.2.1.trans ex2.2.2.1.symm, ex2.2.2.2.1,
        ex1.2.2.2.2, ex2.2.2.2.2, ht⟩
  rw [swSumGraph (fun x y => Std w q d k a b x y z) U Vv ex L H (fun x y => F x * G y)]
  exact Fintype.sum_prod_type _

theorem swShapeAt {w W B q d k a b R : Nat} (hm : SWRect W a k b R)
    (hx : q+d+a+k ≤ w) (hy : q+d+k+b ≤ w) (hB : q+B ≤ W)
    (hCost : swCost q d a k b W R + 1 ≤ 2^30*(W+w+1)^3*Phi w) :
    ShapeSpec w W B q d k a b := by
  classical
  let I := ((V w × Fin W) ⊕ (V w × Fin W))
  let L := ((V d × V a × V b) × V q × Fin W)
  let F (s : V q) (u : V d) (i : V a) (j : V k) (e : Fin W) : I :=
    inl (sw4 w s u i j, e)
  let G (s : V q) (u : V d) (j : V k) (l : V b) (e : Fin W) : I :=
    inr (sw4 w s u j l, e)
  let pick (p : V w × Fin B) : L ⊕ Unit :=
    if swTail (q+d+a+b) p.1 then
      inl ((swSl q d p.1,swSl (q+d) a p.1,swSl (q+d+a) b p.1),swSl 0 q p.1,
        ⟨q+p.2.val,by omega⟩)
    else inr ()
  have h := Cmp.comp (Cmp.pair (swPacked hm F G) (Cb.const (ι := I) false)) (Cmp.wire pick)
  refine ⟨_, by simpa only [Nat.add_zero] using hCost, Cmp.congr h ?_⟩
  rintro v ⟨z,j⟩
  by_cases ht : swTail (q+d+a+b) z
  · simp only [pick, ht, ite_true, elim_inl]
    rw [swStdSum hx hy z ht]
    exact swBit _ j.val (by omega)
  · simp only [pick, ht, ite_false, elim_inr]
    have he (x y : V w) : ¬Std w q d k a b x y z :=
      fun h => ht (swStdSl x y z |>.mp h).2.2.2.2.2.2.2.2
    simp [he]

theorem shape_solver (w W B q d r1 r2 r3 : ℕ) (h1 : q+d+r1+r2 ≤ w)
    (h2 : q+d+r1+r3 ≤ w) (h3 : q+d+r2+r3 ≤ w) (hB : q+B ≤ W) :
    ShapeSpec w W B q d r1 r2 r3 := by
  let s := min r2 (min r1 r3)
  have h1' : q+d+r2+r1 ≤ w := by omega
  refine swShapeAt (q := q) (d := d) (rectCore W r2 r1 r3 s
    (min_le_left ..) ((min_le_right ..).trans (min_le_left ..))
    ((min_le_right ..).trans (min_le_right ..)))
    h1' h2 hB ?_
  have h := rcFinalCost W w q d r2 r1 r3 h1' h2 h3
  change swCost q d r2 r1 r3 W
    (2048*(W+1)^2*2^(r2+r1+r3-3*s)*7^s) + 1 ≤ _
  exact (Nat.add_le_add_left (Nat.le_add_right 1 (2^w)) _).trans h

end Donor

namespace Donor
open PEqualNP.CircuitLowerBounds

instance (w : ℕ) (s : Fin 5 → ℕ) : Decidable (fitsW w s) := by
  unfold fitsW; infer_instance

def ShapeHyp : Prop := ∀ w W B q d r1 r2 r3 : ℕ, q + d + r1 + r2 ≤ w → q + d + r1 + r3 ≤ w →
  q + d + r2 + r3 ≤ w → q + B ≤ W → ShapeSpec w W B q d r1 r2 r3

abbrev dpK (w W c : ℕ) : Type :=
  (Fin 5 × Fin (w + 1)) ⊕ ((V w × Fin W) ⊕ ((V w × Fin W) ⊕ ((Fin w × Fin c) ⊕ V c)))

def dpSel {w W c : ℕ} (σ : Fin 5 → Fin (w + 1)) (u : dpK w W c → Bool) : Bool :=
  decide (∀ k, u (inl (k, σ k)) = true)

def dpOut (w W B : ℕ) (δ : Fin 5 → ℕ) (F G : V w × Fin W → Bool) (p : V w × Fin B) : Bool :=
  (∑ x : V w, ∑ y : V w, if Std w (δ 0) (δ 1) (δ 2) (δ 3) (δ 4) x y p.1 then
    tab F x * tab G y else 0 : BitVec W).getLsbD p.2.val

def dpGate (w W B c : ℕ) (σ : Fin 5 → Fin (w + 1)) (u : dpK w W c → Bool) (p : V w × Fin B) :
    Bool :=
  dpSel σ u && (if fitsW w (fun k => (σ k).val) then
    dpOut w W B (fun k => (σ k).val) (fun e => u (inr (inl e)))
      (fun e => u (inr (inr (inl e)))) p else false)

def dpCost (w W B : ℕ) : ℕ := 6 + 2 ^ 30 * (W + w + 1) ^ 3 * Phi w + 2 ^ w * B

theorem dp_gate_cmp (w W B c : ℕ) (hsh : ShapeHyp) (hB : w + B ≤ W) (σ : Fin 5 → Fin (w + 1)) :
    Cmp (dpK w W c) (V w × Fin B) (dpCost w W B) (dpGate w W B c σ) := by
  by_cases hf : fitsW w (fun k => (σ k).val)
  · obtain ⟨h1, h2, h3⟩ := hf
    have h0 : (σ 0).val + B ≤ W := by have := (σ 0).isLt; omega
    obtain ⟨S, hS, hc⟩ := hsh w W B (σ 0).val (σ 1).val (σ 2).val (σ 3).val (σ 4).val h1 h2 h3 h0
    have hc' := Cmp.sel (ι := dpK w W c)
      (fun e : (V w × Fin W) ⊕ (V w × Fin W) => elim (fun p => inr (inl p))
        (fun p => inr (inr (inl p))) e) hc
    have hs : Cb (dpK w W c) (card (Fin 5) * (0 + 1) + 1) (dpSel σ) :=
      (Cb.bigAnd (ι := dpK w W c) (fun k : Fin 5 => Cb.var (ι := dpK w W c)
        (inl (k, σ k)))).congr (fun u => by simp [dpSel])
    have hp := Cmp.comp (Cmp.pair hs hc')
      (Cmp.ofBits (fun p : V w × Fin B => Cb.and (Cb.var (inl ())) (Cb.var (inr p))))
    refine (hp.mono ?_).congr ?_
    · rw [card_fin, card_prod, fp_cardV, card_fin]
      unfold dpCost
      omega
    · intro u p
      have hf' : fitsW w (fun k => (σ k).val) := ⟨h1, h2, h3⟩
      simp only [dpGate, if_pos hf']
      rfl
  · refine ((Cmp.comp (Cb.const false) (Cmp.wire (fun _ : V w × Fin B => ()))).mono ?_).congr ?_
    · unfold dpCost; omega
    · intro u p
      simp only [dpGate, if_neg hf, Bool.and_false]

abbrev dpL (w c B : ℕ) : Type := ((Fin w × Fin c) ⊕ (V w × Fin B)) ⊕ V c

def dpMux (w W B c : ℕ) (u : dpK w W c ⊕ ((Fin 5 → Fin (w + 1)) × (V w × Fin B)) → Bool) :
    dpL w c B → Bool :=
  elim (elim (fun p => u (inl (inr (inr (inr (inl p))))))
    (fun p => decide (∃ σ, u (inr (σ, p)) = true)))
    (fun z => u (inl (inr (inr (inr (inr z))))))

theorem dp_mux_cmp (w W B c : ℕ) :
    Cmp (dpK w W c ⊕ ((Fin 5 → Fin (w + 1)) × (V w × Fin B))) (dpL w c B)
      (2 ^ w * B * ((w + 1) ^ 5 + 1)) (dpMux w W B c) := by
  have h := Cmp.pair (Cmp.pair
    (Cmp.wire (ι := dpK w W c ⊕ ((Fin 5 → Fin (w + 1)) × (V w × Fin B)))
      (fun p : Fin w × Fin c => inl (inr (inr (inr (inl p))))))
    (Cmp.ofBits (fun p : V w × Fin B =>
      Cb.bigOr (fun σ : Fin 5 → Fin (w + 1) => Cb.var (inr (σ, p))))))
    (Cmp.wire (ι := dpK w W c ⊕ ((Fin 5 → Fin (w + 1)) × (V w × Fin B)))
      (fun z : V c => inl (inr (inr (inr (inr z))))))
  refine (h.mono ?_).congr ?_
  · simp only [card_prod, card_fin, card_fun, ZMod.card, zero_add,
      mul_one]
    omega
  · intro u p
    rcases p with (p | p) | p <;> rfl

def dpPull (w c B : ℕ) (v : dpL w c B → Bool) : (V c × Fin B) ⊕ V c → Bool :=
  elim (untab (fun lam : V c => tab (fun p => v (inl (inr p)))
    ((mat (fun p => v (inl (inl p)))).mulVec lam))) (fun z => v (inr z))

theorem dp_pull_cmp (w c B : ℕ) :
    Cmp (dpL w c B) ((V c × Fin B) ⊕ V c) (tcost w c B) (dpPull w c B) := by
  have h := Cmp.pair (Cmp.sel (ι := dpL w c B) inl (cmp_pull w c B))
    (Cmp.wire (ι := dpL w c B) (fun z : V c => inr z))
  refine (h.mono (by omega)).congr ?_
  intro v p
  rcases p with p | p <;> rfl

theorem dp_pull_inl (w c B : ℕ) (X : dpL w c B → Bool) (z : V c) (j : Fin B) :
    dpPull w c B X (inl (z, j)) =
      X (inl (inr ((mat (fun p => X (inl (inl p)))).mulVec z, j))) :=
  getLsbD_bv _ j

def dpFin (c B : ℕ) (ec : Fin (2 ^ c) ≃ V c) (v : (V c × Fin B) ⊕ V c → Bool) :
    Fin (2 ^ c) × Fin B → Bool :=
  fun p => v (inr (ec p.1)) && v (inl (ec p.1, p.2))

theorem dp_fin_cmp (c B : ℕ) (ec : Fin (2 ^ c) ≃ V c) :
    Cmp ((V c × Fin B) ⊕ V c) (Fin (2 ^ c) × Fin B) (2 ^ c * B) (dpFin c B ec) := by
  have h := Cmp.ofBits (ι := (V c × Fin B) ⊕ V c) (F := dpFin c B ec)
    (fun p => Cb.and (Cb.var (inr (ec p.1))) (Cb.var (inl (ec p.1, p.2))))
  refine h.mono ?_
  simp only [card_prod, card_fin]
  omega

theorem dp_gate_eq (w W B c : ℕ) (δ : Fin 5 → ℕ) (hf : fitsW w δ) (u : dpK w W c → Bool)
    (hu : ∀ k (i : Fin (w + 1)), u (inl (k, i)) = decide (δ k = i.val)) (p : V w × Fin B) :
    decide (∃ σ, dpGate w W B c σ u p = true) =
      dpOut w W B δ (fun e => u (inr (inl e)))
        (fun e => u (inr (inr (inl e)))) p := by
  have hδ : ∀ k, δ k < w + 1 := by
    obtain ⟨h1, h2, h3⟩ := hf
    intro k; fin_cases k <;> simp <;> omega
  have hsel : ∀ σ : Fin 5 → Fin (w + 1), dpSel σ u = true ↔ (fun k => (σ k).val) = δ := by
    intro σ
    simp only [dpSel, hu, decide_eq_true_eq]
    constructor
    · intro h; funext k; exact (h k).symm
    · intro h k; rw [← h]
  have hfs : fitsW w (fun k => ((⟨δ k, hδ k⟩ : Fin (w + 1))).val) := hf
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    simp only [dpGate, Bool.and_eq_true] at hσ
    obtain ⟨h1, h2⟩ := hσ
    have e := (hsel σ).mp h1
    rw [e, if_pos hf] at h2
    exact h2
  · intro h
    refine ⟨fun k => ⟨δ k, hδ k⟩, ?_⟩
    have e1 : dpSel (fun k => (⟨δ k, hδ k⟩ : Fin (w + 1))) u = true := (hsel _).mpr rfl
    simp only [dpGate, e1, Bool.true_and]
    rw [if_pos hfs]
    exact h

def dpCtl {a b c m t : ℕ} (dims : (In0 a b c m t → Bool) → Fin 5 → ℕ)
    (FF GG : (In0 a b c m t → Bool) → V (wOf a b c) × Fin (WOf a b c t) → Bool)
    (EE : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin c → Bool)
    (CZ : (In0 a b c m t → Bool) → V c → Bool) (v : In0 a b c m t → Bool) :
    dpK (wOf a b c) (WOf a b c t) c → Bool :=
  elim (fun p => decide (dims v p.1 = p.2.val))
    (elim (FF v) (elim (GG v) (elim (EE v) (CZ v))))

def dpAll {a b c m t : ℕ} (ec : Fin (2 ^ c) ≃ V c) (dims : (In0 a b c m t → Bool) → Fin 5 → ℕ)
    (FF GG : (In0 a b c m t → Bool) → V (wOf a b c) × Fin (WOf a b c t) → Bool)
    (EE : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin c → Bool)
    (CZ : (In0 a b c m t → Bool) → V c → Bool) (v : In0 a b c m t → Bool) :
    Fin (2 ^ c) × Fin (a + b + 2 * t + 1) → Bool :=
  dpFin c (a + b + 2 * t + 1) ec (dpPull (wOf a b c) c (a + b + 2 * t + 1)
    (dpMux (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) c
      (elim (dpCtl dims FF GG EE CZ v)
        (fun q => dpGate (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) c q.1
          (dpCtl dims FF GG EE CZ v) q.2))))

theorem dp_all_eq {a b c m t : ℕ} (ec : Fin (2 ^ c) ≃ V c)
    (dims : (In0 a b c m t → Bool) → Fin 5 → ℕ)
    (FF GG : (In0 a b c m t → Bool) → V (wOf a b c) × Fin (WOf a b c t) → Bool)
    (EE : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin c → Bool)
    (CZ : (In0 a b c m t → Bool) → V c → Bool) (v : In0 a b c m t → Bool)
    (hf : fitsW (wOf a b c) (dims v)) (iz : Fin (2 ^ c)) (j : Fin (a + b + 2 * t + 1)) :
    dpAll ec dims FF GG EE CZ v (iz, j) = (CZ v (ec iz) &&
      dpOut (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) (dims v) (FF v) (GG v)
        ((mat (EE v)).mulVec (ec iz), j)) := by
  have hg := dp_gate_eq (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) c (dims v) hf
    (dpCtl dims FF GG EE CZ v) (fun k i => rfl) ((mat (EE v)).mulVec (ec iz), j)
  have e : dpAll ec dims FF GG EE CZ v (iz, j) = (CZ v (ec iz) &&
      decide (∃ σ, dpGate (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) c σ
        (dpCtl dims FF GG EE CZ v) ((mat (EE v)).mulVec (ec iz), j) = true)) := by
    show (dpPull _ _ _ _ (inr (ec iz)) && dpPull _ _ _ _ (inl (ec iz, j))) = _
    rw [dp_pull_inl]
    rfl
  rw [e, hg]
  rfl

theorem dp_out_val (W B : ℕ) (hB : B ≤ W) (w : ℕ) (δ : Fin 5 → ℕ) (F G : V w × Fin W → Bool)
    (t0 : V w) (j : Fin B) (cz : Bool) (n : ℕ)
    (h : BitVec.ofNat W n = if cz = true then (∑ x : V w, ∑ y : V w,
      if Std w (δ 0) (δ 1) (δ 2) (δ 3) (δ 4) x y t0 then tab F x * tab G y else 0) else 0) :
    (cz && dpOut w W B δ F G (t0, j)) = n.testBit j.val := by
  have hj : j.val < W := lt_of_lt_of_le j.isLt hB
  have e : n.testBit j.val = (BitVec.ofNat W n).getLsbD j.val := by
    rw [BitVec.getLsbD_ofNat]; simp [hj]
  rw [e, h]
  cases cz
  · simp
  · simp [dpOut]

theorem dp_cost (a b c m t S0 : ℕ)
    (hS0 : S0 ≤ 2 ^ 50 * (a + b + c + m + t + 4) ^ 20 * Phi (wOf a b c)) :
    S0 + (wOf a b c + 1) ^ 5 * dpCost (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) +
      2 ^ wOf a b c * (a + b + 2 * t + 1) * ((wOf a b c + 1) ^ 5 + 1) +
      tcost (wOf a b c) c (a + b + 2 * t + 1) + 2 ^ c * (a + b + 2 * t + 1) + 1 ≤
    2 ^ 60 * (a + b + c + m + t + 4) ^ 30 * Phi (wOf a b c) := by
  have hwd : wOf a b c = max a (max b c) := rfl
  have hw : wOf a b c ≤ a + b + c := by rw [hwd]; omega
  have hcw : c ≤ wOf a b c := by rw [hwd]; omega
  have hWd : WOf a b c t = a + b + 2 * t + 1 + wOf a b c := rfl
  have hmax : max (wOf a b c) c = wOf a b c := max_eq_left hcw
  have hΦ := two_pow_le_Phi (wOf a b c)
  have h2c : 2 ^ c ≤ 2 ^ wOf a b c := Nat.pow_le_pow_right (by norm_num) hcw
  have hQ1 : 1 ≤ 2 ^ wOf a b c := Nat.one_le_two_pow
  unfold dpCost tcost
  rw [hWd, hmax]
  generalize wOf a b c = w at *
  generalize Phi w = Φ at *
  generalize 2 ^ w = Q at *
  generalize hP : a + b + c + m + t + 4 = P at *
  have hP1 : 1 ≤ P := by omega
  have hw1 : w + 1 ≤ P := by omega
  have hK : a + b + 2 * t + 1 + w + w + 1 ≤ 3 * P := by omega
  have hB : a + b + 2 * t + 1 ≤ 2 * P := by omega
  have hB1 : a + b + 2 * t + 1 + 1 ≤ 2 * P := by omega
  have hwc : w + c + 2 ≤ 2 * P := by omega
  have hpow : ∀ i, i ≤ 30 → P ^ i * Φ ≤ P ^ 30 * Φ := fun i hi =>
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hP1 hi)
  have hΦ1 : 1 ≤ Φ := le_trans hQ1 hΦ
  have z0 := hpow 0 (by norm_num)
  have z1 := hpow 1 (by norm_num)
  have z5 := hpow 5 (by norm_num)
  have z6 := hpow 6 (by norm_num)
  have z8 := hpow 8 (by norm_num)
  have z20 := hpow 20 (by norm_num)
  have p5 : P ^ 5 ≤ P ^ 5 * Φ := Nat.le_mul_of_pos_right _ hΦ1
  have e2 : (w + 1) ^ 5 * (6 + 2 ^ 30 * (a + b + 2 * t + 1 + w + w + 1) ^ 3 * Φ +
      Q * (a + b + 2 * t + 1)) ≤ 6 * P ^ 5 + 2 ^ 30 * 27 * (P ^ 8 * Φ) + 2 * (P ^ 6 * Φ) := by
    calc _ ≤ P ^ 5 * (6 + 2 ^ 30 * (3 * P) ^ 3 * Φ + Φ * (2 * P)) := by gcongr
      _ = _ := by ring
  have e3 : Q * (a + b + 2 * t + 1) * ((w + 1) ^ 5 + 1) ≤ 4 * (P ^ 6 * Φ) := by
    calc _ ≤ Φ * (2 * P) * (P ^ 5 + P ^ 5) := by
          gcongr
          exact Nat.one_le_pow _ _ (by omega)
      _ = _ := by ring
  have e4 : 2 ^ 9 * (w + c + 2) ^ 4 * (a + b + 2 * t + 1 + 1) * Q ≤ 2 ^ 14 * (P ^ 5 * Φ) := by
    calc _ ≤ 2 ^ 9 * (2 * P) ^ 4 * (2 * P) * Φ := by gcongr
      _ = _ := by ring
  have e5 : 2 ^ c * (a + b + 2 * t + 1) ≤ 2 * (P ^ 1 * Φ) := by
    calc _ ≤ Φ * (2 * P) := Nat.mul_le_mul (le_trans h2c hΦ) hB
      _ = _ := by ring
  have e6 : 2 ^ 50 * P ^ 20 * Φ = 2 ^ 50 * (P ^ 20 * Φ) := by ring
  have e7 : 2 ^ 60 * P ^ 30 * Φ = 2 ^ 60 * (P ^ 30 * Φ) := by ring
  have e8 : P ^ 0 * Φ = Φ := by ring
  rw [e7]
  rw [e6] at hS0
  omega

def weightedJoinCost (a b c m t : ℕ) : ℕ :=
  2^60 * (a+b+c+m+t+4)^30 * Phi (wOf a b c)

end Donor

namespace Donor

set_option maxHeartbeats 120000 in
theorem fz5_totalRel {a b t : ℕ} (W : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (rel : V a → V b → Prop) [DecidableRel rel]
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) :
    (∑ x : V a, ∑ y : V b,
      if rel x y then
        BitVec.ofNat W (f (ea.symm x)).val * BitVec.ofNat W (g (eb.symm y)).val else 0) =
    BitVec.ofNat W (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
      if rel (ea ix) (eb iy) then
        (f ix).val * (g iy).val else 0) := by
  rw [← Equiv.sum_comp ea]
  have : ∀ ix : Fin (2 ^ a), (∑ y : V b,
      if rel (ea ix) y then
        BitVec.ofNat W (f (ea.symm (ea ix))).val * BitVec.ofNat W (g (eb.symm y)).val else 0) =
      ∑ iy : Fin (2 ^ b),
      if rel (ea ix) (eb iy) then
        ((f ix).val : BitVec W) * ((g iy).val : BitVec W) else 0 := by
    intro ix
    rw [← Equiv.sum_comp eb]
    apply sum_congr rfl
    intro iy _
    simp only [Equiv.symm_apply_apply, BitVec.natCast_eq_ofNat]
  rw [sum_congr rfl (fun ix _ => this ix)]
  rw [← BitVec.natCast_eq_ofNat]
  push_cast
  rfl

set_option maxHeartbeats 120000 in
theorem ctrl_totalRel {a b c w m t W : ℕ} (ea : Fin (2^a) ≃ V a) (eb : Fin (2^b) ≃ V b)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t))
    (L : Fin w × Fin (a+1) → Bool) (M : Fin w × Fin (b+1) → Bool)
    (X : V a → Bool) (Y : V b → Bool) (Z : Bool)
    (R : V w → V w → Prop) [DecidableRel R]
    (rel : V a → V b → Prop) [DecidableRel rel]
    (hs : ∀ x y, rel x y ↔
      X x = true ∧ Y y = true ∧ Z = true ∧ R (ctrlAffine L x) (ctrlAffine M y)) :
    BitVec.ofNat W (∑ ix : Fin (2^a), ∑ iy : Fin (2^b),
      if rel (ea ix) (eb iy) then
        (f ix).val * (g iy).val else 0) = if Z then
      ∑ x, ∑ y, if R x y then
        tab (ctrlPushed L X (fTab a b c m t W ea (inpOf H rhs f g))) x *
        tab (ctrlPushed M Y (gTab a b c m t W eb (inpOf H rhs f g))) y else 0
      else 0 := by
  rw [← fz5_totalRel W ea eb rel f g, ctrl_regroup]
  cases Z <;> simp [hs, fz5_tabf, fz5_tabg]

open Classical in
def CtlSpecRel (a b c m t : ℕ)
    (legal : (Fin m → V a × V b × V c) → Prop)
    (rel : (Fin m → V a × V b × V c) → V a → V b → V c → Prop)
    (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b) : Prop :=
  ∃ (S : ℕ) (dims : (In0 a b c m t → Bool) → Fin 5 → ℕ)
    (FF GG : (In0 a b c m t → Bool) → V (wOf a b c) × Fin (WOf a b c t) → Bool)
    (EE : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin c → Bool)
    (CZ : (In0 a b c m t → Bool) → V c → Bool),
    S ≤ 2 ^ 50 * (a + b + c + m + t + 4) ^ 20 * Phi (wOf a b c) ∧
    Cmp (In0 a b c m t) ((Fin 5 × Fin (wOf a b c + 1)) ⊕ ((V (wOf a b c) × Fin (WOf a b c t)) ⊕
      ((V (wOf a b c) × Fin (WOf a b c t)) ⊕ ((Fin (wOf a b c) × Fin c) ⊕ V c)))) S
      (fun v => elim (fun p => decide (dims v p.1 = p.2.val))
        (elim (FF v) (elim (GG v) (elim (EE v) (CZ v))))) ∧
    ∀ (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2) (f : Fin (2 ^ a) → Fin (2 ^ t))
      (g : Fin (2 ^ b) → Fin (2 ^ t)), legal H →
      fitsW (wOf a b c) (dims (inpOf H rhs f g)) ∧
      ∀ z : V c, BitVec.ofNat (WOf a b c t) (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
          if rel H (ea ix) (eb iy) z then
            (f ix).val * (g iy).val else 0) =
        if CZ (inpOf H rhs f g) z = true then
          ∑ x : V (wOf a b c), ∑ y : V (wOf a b c),
            if Std (wOf a b c) (dims (inpOf H rhs f g) 0) (dims (inpOf H rhs f g) 1)
              (dims (inpOf H rhs f g) 2) (dims (inpOf H rhs f g) 3) (dims (inpOf H rhs f g) 4) x y
              ((mat (EE (inpOf H rhs f g))).mulVec z)
            then tab (FF (inpOf H rhs f g)) x * tab (GG (inpOf H rhs f g)) y else 0
        else 0

set_option maxHeartbeats 150000 in
theorem swCtlSpecRel {a b c m t : ℕ}
    {legal : (Fin m → V a × V b × V c) → Prop}
    {rel : (Fin m → V a × V b × V c) → V a → V b → V c → Prop}
    (ea : Fin (2^a) ≃ V a) (eb : Fin (2^b) ≃ V b)
    {D : (In0 a b c m t → Bool) → Fin 5 → Nat}
    {L : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin (a+1) → Bool}
    {M : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin (b+1) → Bool}
    {E : (In0 a b c m t → Bool) → Fin (wOf a b c) × Fin c → Bool}
    {X : (In0 a b c m t → Bool) → V a → Bool}
    {Y : (In0 a b c m t → Bool) → V b → Bool}
    {Z : (In0 a b c m t → Bool) → V c → Bool}
    (hD : Cmp _ (Fin 5 × Fin (wOf a b c+1)) (swPartSize a b c m t)
      (fun v p => decide (D v p.1 = p.2.val)))
    (hL : Cmp _ _ (swPartSize a b c m t) L) (hM : Cmp _ _ (swPartSize a b c m t) M)
    (hE : Cmp _ _ (swPartSize a b c m t) E) (hX : Cmp _ _ (swPartSize a b c m t) X)
    (hY : Cmp _ _ (swPartSize a b c m t) Y) (hZ : Cmp _ _ (swPartSize a b c m t) Z)
    (hfit : ∀ (H : Fin m → V a × V b × V c) (r : Fin m → ZMod 2)
      (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t)), legal H →
      fitsW (wOf a b c) (D (inpOf H r f g)))
    (hsat : ∀ (H : Fin m → V a × V b × V c) (r : Fin m → ZMod 2)
      (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t))
      (x : V a) (y : V b) (z : V c), legal H →
      let u := inpOf H r f g
      rel H x y z ↔
      X u x = true ∧ Y u y = true ∧ Z u z = true ∧
      Std (wOf a b c) (D u 0) (D u 1) (D u 2) (D u 3) (D u 4)
        (ctrlAffine (L u) x) (ctrlAffine (M u) y) ((mat (E u)).mulVec z)) :
    CtlSpecRel a b c m t legal rel ea eb := by
  classical
  let W := WOf a b c t
  refine ⟨_, D, _, _, E, Z, ctrl_parts_cost a b c m t,
    ctrl_bundle (W := W) ea eb hD hL hM hE hX hY hZ, ?_⟩
  intro H r f g hleg
  refine ⟨hfit H r f g hleg, fun z => ?_⟩
  exact ctrl_totalRel ea eb H r f g _ _ _ _ _ _ (fun x y => rel H x y z)
    (fun x y => hsat H r f g x y z hleg)

open Classical in
set_option maxHeartbeats 200000 in
theorem weightedJoinRel (a b c m t : ℕ)
    {legal : (Fin m → V a × V b × V c) → Prop}
    {rel : (Fin m → V a × V b × V c) → V a → V b → V c → Prop}
    (hCtl : ∀ ea eb, CtlSpecRel a b c m t legal rel ea eb) :
    ∃ J : (In0 a b c m t → Bool) → Fin (2^c) × Fin (a + b + 2 * t + 1) → Bool,
      Cmp (In0 a b c m t) (Fin (2^c) × Fin (a + b + 2 * t + 1))
        (weightedJoinCost a b c m t) J ∧
      ∀ (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
        (f : Fin (2^a) → Fin (2^t)) (g : Fin (2^b) → Fin (2^t)) (iz) (j), legal H →
        J (inpOf H rhs f g) (iz,j) =
          (∑ ix : Fin (2^a), ∑ iy : Fin (2^b), if rel H
            (fun j => if ix.val.testBit j.val then 1 else 0)
            (fun j => if iy.val.testBit j.val then 1 else 0)
            (fun j => if iz.val.testBit j.val then 1 else 0)
            then (f ix).val * (g iy).val else 0).testBit j.val := by
  classical
  obtain ⟨ea, hea⟩ := vecEquiv_exists a
  obtain ⟨eb, heb⟩ := vecEquiv_exists b
  obtain ⟨ec, hec⟩ := vecEquiv_exists c
  obtain ⟨S0, dims, FF, GG, EE, CZ, hS0, hctl, hsem⟩ := hCtl ea eb
  have hBW : wOf a b c + (a + b + 2 * t + 1) ≤ WOf a b c t := by unfold WOf; omega
  have hB := Cmp.keep (Cmp.piU (fun σ => dp_gate_cmp (wOf a b c) (WOf a b c t)
    (a + b + 2 * t + 1) c (fun w W B q d r1 r2 r3 => shape_solver w W B q d r1 r2 r3) hBW σ))
  have htop0 := Cmp.comp (Cmp.comp (Cmp.comp (Cmp.comp hctl hB) (dp_mux_cmp _ _ _ _))
    (dp_pull_cmp _ _ _)) (dp_fin_cmp c (a + b + 2 * t + 1) ec)
  have htop : Cmp (In0 a b c m t) (Fin (2 ^ c) × Fin (a + b + 2 * t + 1))
      (S0 + (wOf a b c + 1) ^ 5 * dpCost (wOf a b c) (WOf a b c t) (a + b + 2 * t + 1) +
        2 ^ wOf a b c * (a + b + 2 * t + 1) * ((wOf a b c + 1) ^ 5 + 1) +
        tcost (wOf a b c) c (a + b + 2 * t + 1) + 2 ^ c * (a + b + 2 * t + 1))
      (dpAll ec dims FF GG EE CZ) := by
    refine (htop0.mono ?_).congr ?_
    · simp only [card_fun, card_fin]
      exact le_refl _
    · intro v p; rfl
  refine ⟨_, htop.mono ((Nat.le_succ _).trans (dp_cost a b c m t S0 hS0)), ?_⟩
  intro H rhs f g iz j hleg
  obtain ⟨hfit, hval⟩ := hsem H rhs f g hleg
  have hea' : ∀ ix, ea ix = (fun j : Fin a => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
    fun ix => funext (hea ix)
  have heb' : ∀ ix, eb ix = (fun j : Fin b => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
    fun ix => funext (heb ix)
  have hec' : ∀ ix, ec ix = (fun j : Fin c => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
    fun ix => funext (hec ix)
  rw [dp_all_eq ec dims FF GG EE CZ _ hfit iz j,
    dp_out_val (WOf a b c t) (a + b + 2 * t + 1) (by unfold WOf; omega) _ _ _ _ _ j _ _
      (hval (ec iz))]
  simp only [hea', heb', hec']

end Donor

namespace Donor

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

def vecN (m x : ℕ) : Fin m → ZMod 2 := fun i => if x.testBit i.val then 1 else 0

def glSol (M N1 N2 : ℕ) (Hb : Fin M × Fin (N1+N2+1) → Bool) (e : Fin N2 → ZMod 2) : Prop :=
  ∃ c : Fin N1 → ZMod 2, ∀ i : Fin M,
    (∑ j : Fin N1, b2z (Hb (i, ⟨j.val, by omega⟩)) * c j) +
    (∑ j : Fin N2, b2z (Hb (i, ⟨N1 + j.val, by omega⟩)) * e j) =
      b2z (Hb (i, ⟨N1 + N2, by omega⟩))

def glCost (M N1 N2 β : ℕ) : ℕ := 2^12 * (M + N1 + N2 + β + 2)^6

abbrev GlOut (N2 β : ℕ) : Type := (Fin N2 × Fin β) ⊕ (Fin N2 ⊕ (Fin β ⊕ Unit))

def glPt {N2 β : ℕ} (o : GlOut N2 β → Bool) (x : Fin β → ZMod 2) : Fin N2 → ZMod 2 :=
  fun j => b2z (o (inr (inl j))) + ∑ t : Fin β, b2z (o (inl (j, t))) * x t

def glOk {N2 β : ℕ} (o : GlOut N2 β → Bool) (x : Fin β → ZMod 2) : Prop :=
  ∀ t : Fin β, o (inr (inr (inl t))) = false → x t = 0

def GlSpec (M N1 N2 β : ℕ)
    (F : (Fin M × Fin (N1+N2+1) → Bool) → GlOut N2 β → Bool)
    (nf : (Fin M × Fin (N1+N2+1) → Bool) → ℕ) : Prop :=
  ∀ Hb : Fin M × Fin (N1+N2+1) → Bool,
    (F Hb (inr (inr (inr ()))) = false → ∀ e, ¬ glSol M N1 N2 Hb e) ∧
    (F Hb (inr (inr (inr ()))) = true →
      Nat.card {e : Fin N2 → ZMod 2 // glSol M N1 N2 Hb e} = 2^(nf Hb) ∧
      (∀ t : Fin β, F Hb (inr (inr (inl t))) = true ↔ t.val < nf Hb) ∧
      (nf Hb ≤ β →
        (∀ x, glOk (F Hb) x → glSol M N1 N2 Hb (glPt (F Hb) x)) ∧
        (∀ e, glSol M N1 N2 Hb e → ∃ x, glOk (F Hb) x ∧ glPt (F Hb) x = e) ∧
        (∀ x x', glOk (F Hb) x → glOk (F Hb) x' → glPt (F Hb) x = glPt (F Hb) x' → x = x')))

def gl_P {n : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (e : Fin n → ZMod 2) : Prop :=
  ∀ j, fl j = false → e j = b2z (a j) + ∑ q, if fl q = true then b2z (G (j, q)) * e q else 0

def gl_A {n : ℕ} (β : ℕ) (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool) :
    GlOut n β → Bool :=
  elim (fun p => decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = p.2.val ∧
      xor (decide (p.1 = q)) (G (p.1, q)) = true))
    (elim a (elim (fun t => decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = t.val))
      (fun _ => c)))

def gl_xs {n β : ℕ} (fl : Fin n → Bool) (x : Fin β → ZMod 2) (q : Fin n) : ZMod 2 :=
  if h : cnt fl q.val < β then x ⟨_, h⟩ else 0

noncomputable def glRank {n : ℕ} (fl : Fin n → Bool) : {q : Fin n // fl q = true} ≃ Fin (cnt fl n) :=
  Equiv.ofBijective (fun q => ⟨cnt fl q.val.val,ctrl_rank_lt fl q.val q.prop⟩)
    ⟨fun q r h => Subtype.ext (fh_cnt_inj (fun i => fl i = true) _ _ q.prop r.prop
      (congrArg Fin.val h)),
     fun t => by
      obtain ⟨q,hq,e⟩ := ctrl_rank_surj fl t.val t.isLt
      exact ⟨⟨q,hq⟩,Fin.ext e⟩⟩

theorem gl_pt {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) (j : Fin n) :
    glPt (gl_A β fl a G c) x j = b2z (a j) +
      ∑ q, if fl q = true then b2z (xor (decide (j = q)) (G (j, q))) * gl_xs fl x q else 0 := by
  let row (q : Fin n × Unit) := xor (decide (j = q.1)) (G (j,q.1))
  let f (t : Fin β) := b2z (ctrlPacked β fl row (t,())) * x t
  change b2z (a j) + (∑ t,f t) = _
  congr 1
  let d := (glRank fl).toEmbedding.trans (Fin.castLEEmb hβ)
  have truncate : ∑ t ∈ Finset.univ.map d, f t = ∑ t,f t := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have ht' : cnt fl n ≤ t.val := by
      by_contra! h
      apply ht
      obtain ⟨q,hq⟩ := (glRank fl).surjective ⟨t.val,h⟩
      exact Finset.mem_map.mpr ⟨q,mem_univ _,Fin.ext (congrArg (fun u : Fin (cnt fl n) => u.val) hq)⟩
    simp [f,ctrlPacked_tail fl row t () ht',b2z]
  rw [← truncate, Finset.sum_map]
  rw [← Finset.sum_filter (fun q => fl q = true)
    (fun q => b2z (xor (decide (j = q)) (G (j,q))) * gl_xs fl x q)]
  rw [Finset.sum_subtype (p := fun q : Fin n => fl q = true)
    (Finset.univ.filter (fun q => fl q = true)) (fun q => by simp)]
  apply sum_congr rfl
  intro q _
  have hq : cnt fl q.val.val < β := (ctrl_rank_lt fl q.val q.prop).trans_le hβ
  have hd : d q = (⟨cnt fl q.val.val,hq⟩ : Fin β) := rfl
  rw [show f (d q) = b2z (row (q.val,())) * x (d q) by
    unfold f
    rw [ctrlPacked_hit fl row q.val (d q) () q.prop rfl]]
  simp [hd,row,gl_xs,hq]

theorem gl_pt_free {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) (j : Fin n) (hj : fl j = true) :
    glPt (gl_A β fl a G c) x j = gl_xs fl x j := by
  rw [gl_pt fl a G c hβ x j, (hz j hj).1]
  rw [sum_eq_single j]
  · rw [if_pos hj, (hz j hj).2 j]
    simp [b2z]
  · intro q _ hq
    by_cases hf : fl q = true
    · rw [if_pos hf, (hz j hj).2 q]
      have : decide (j = q) = false := decide_eq_false (fun h => hq h.symm)
      simp [this, b2z]
    · rw [if_neg hf]
  · intro hh; exact absurd (mem_univ _) hh

theorem gl_pt_piv {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) (j : Fin n) (hj : fl j = false) :
    glPt (gl_A β fl a G c) x j = b2z (a j) +
      ∑ q, if fl q = true then b2z (G (j, q)) * gl_xs fl x q else 0 := by
  rw [gl_pt fl a G c hβ x j]
  congr 1
  apply sum_congr rfl
  intro q _
  by_cases hf : fl q = true
  · rw [if_pos hf, if_pos hf]
    have : decide (j = q) = false := decide_eq_false (fun h => by rw [h, hf] at hj; exact Bool.noConfusion hj)
    simp [this]
  · rw [if_neg hf, if_neg hf]

theorem gl_A_sol {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) : gl_P fl a G (glPt (gl_A β fl a G c) x) := by
  intro j hj
  rw [gl_pt_piv fl a G c hβ x j hj]
  congr 1
  apply sum_congr rfl
  intro q _
  by_cases hf : fl q = true
  · rw [if_pos hf, if_pos hf, gl_pt_free fl a G c hz hβ x q hf]
  · rw [if_neg hf, if_neg hf]

theorem gl_A_used {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (t : Fin β) : gl_A β fl a G c (inr (inr (inl t))) = true ↔ t.val < cnt fl n := by
  simp only [gl_A, elim_inr, elim_inl, decide_eq_true_eq]
  exact ⟨fun ⟨q,hq,e⟩ => e ▸ ctrl_rank_lt fl q hq,ctrl_rank_surj fl _⟩

theorem gl_A_inj {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (x x' : Fin β → ZMod 2)
    (hx : glOk (gl_A β fl a G c) x) (hx' : glOk (gl_A β fl a G c) x')
    (h : glPt (gl_A β fl a G c) x = glPt (gl_A β fl a G c) x') : x = x' := by
  funext t
  by_cases ht : t.val < cnt fl n
  · obtain ⟨q, hq, eq⟩ := ctrl_rank_surj fl _ ht
    have e := congrFun h q
    rw [gl_pt_free fl a G c hz hβ _ q hq,gl_pt_free fl a G c hz hβ _ q hq] at e
    simpa [gl_xs,eq,t.isLt] using e
  · have off := Bool.eq_false_iff.mpr (ht ∘ (gl_A_used fl a G c t).mp)
    rw [hx t off,hx' t off]

theorem gl_A_surj {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (e : Fin n → ZMod 2) (he : gl_P fl a G e) :
    ∃ x, glOk (gl_A β fl a G c) x ∧ glPt (gl_A β fl a G c) x = e := by
  let x (t : Fin β) := if h : t.val < cnt fl n then e ((glRank fl).symm ⟨t.val,h⟩).val else 0
  have hxs (q : Fin n) (hq : fl q = true) : gl_xs fl x q = e q := by
    have hq₀ := ctrl_rank_lt fl q hq
    rw [gl_xs,dite_eq_left (hq₀.trans_le hβ)]
    change (if h : cnt fl q.val < cnt fl n then e ((glRank fl).symm ⟨_,h⟩).val else 0) = e q
    rw [dite_eq_left hq₀]
    exact congrArg (fun j : {q : Fin n // fl q = true} => e j.val) ((glRank fl).symm_apply_apply ⟨q,hq⟩)
  refine ⟨x,?_,?_⟩
  · intro t ht
    change decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = t.val) = false at ht
    rw [decide_eq_false_iff_not] at ht
    exact dite_eq_right (fun h => ht (ctrl_rank_surj fl _ h))
  · funext j
    cases hj : fl j
    · rw [gl_pt_piv fl a G c hβ _ j hj, he j hj]
      congr 1
      exact sum_congr rfl (fun q _ => by by_cases h : fl q = true <;> simp [h,hxs])
    · rw [gl_pt_free fl a G c hz hβ _ j hj, hxs j hj]

theorem gl_P_card {n : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) :
    Nat.card {e : Fin n → ZMod 2 // gl_P fl a G e} = 2 ^ (cnt fl n) := by
  have hcard : card {q : Fin n // fl q = true} = cnt fl n := by
    rw [card_subtype]; unfold cnt; congr 1; ext q; simp
  have hext : ∀ g : {q : Fin n // fl q = true} → ZMod 2, gl_P fl a G (fun j =>
      if h : fl j = true then g ⟨j, h⟩ else b2z (a j) +
        ∑ q, if h : fl q = true then b2z (G (j, q)) * g ⟨q, h⟩ else 0) := by
    intro g j hj
    have hj' : ¬ fl j = true := by rw [hj]; exact Bool.false_ne_true
    simp only [dif_neg hj']
    congr 1
    apply sum_congr rfl
    intro q _
    by_cases hf : fl q = true
    · rw [if_pos hf, dif_pos hf, dif_pos hf]
    · rw [if_neg hf, dif_neg hf]
  have e : {e : Fin n → ZMod 2 // gl_P fl a G e} ≃ ({q : Fin n // fl q = true} → ZMod 2) :=
    { toFun := fun e q => e.1 q.1
      invFun := fun g => ⟨_, hext g⟩
      left_inv := by
        intro e
        apply Subtype.ext
        funext j
        by_cases hj : fl j = true
        · simp only [dif_pos hj]
        · have hj' : fl j = false := by simpa using hj
          simp only [dif_neg hj]
          rw [e.2 j hj']
          congr 1 <;> (
            apply sum_congr rfl
            intro q _
            by_cases hf : fl q = true
            · rw [if_pos hf, dif_pos hf]
            · rw [if_neg hf, dif_neg hf])
      right_inv := by
        intro g
        funext q
        simp only [dif_pos q.2] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, card_fun, ZMod.card, hcard]

def gl_Hf {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool) : Fin M → V (N1+N2) :=
  fun i j => b2z (Hb (i, ⟨j.val, by omega⟩))

def gl_rhs {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool) : Fin M → ZMod 2 :=
  fun i => b2z (Hb (i, ⟨N1+N2, by omega⟩))

def gl_mat {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool) :
    Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool := fun p =>
  if hi : p.1.val < M then
    (if hj : p.2.val < N1+N2+1 then Hb (⟨p.1.val, hi⟩, ⟨p.2.val, hj⟩) else false)
  else false

theorem gl_mat_eq {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool) :
    gl_mat Hb = sysBits (gl_Hf Hb) (gl_rhs Hb) := by
  have hb : ∀ x : Bool, x = decide (b2z x ≠ 0) := by intro x; cases x <;> simp [b2z]
  funext p
  unfold gl_mat sysBits
  by_cases hi : p.1.val < M
  · simp only [dif_pos hi]
    by_cases hj : p.2.val < N1 + N2
    · have hj' : p.2.val < N1 + N2 + 1 := by omega
      simp only [dif_pos hj, dif_pos hj', gl_Hf]
      exact hb _
    · simp only [dif_neg hj]
      by_cases hj2 : p.2.val = N1 + N2
      · have hj' : p.2.val < N1 + N2 + 1 := by omega
        simp only [dif_pos hj', if_pos hj2, gl_rhs]
        have : (⟨p.2.val, hj'⟩ : Fin (N1+N2+1)) = ⟨N1+N2, by omega⟩ := Fin.ext hj2
        rw [this]
        exact hb _
      · have hj' : ¬ p.2.val < N1 + N2 + 1 := by omega
        simp only [dif_neg hj', if_neg hj2]
  · simp only [dif_neg hi]

def gl_vc (M N1 : ℕ) {N2 : ℕ} (j : Fin N2) : Fin (M + (N1+N2) + 1) := cl M (Fin.natAdd N1 j)

def gl_fl {M N1 N2 : ℕ} (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool)
    (j : Fin N2) : Bool := !R (gl_vc M N1 j, gl_vc M N1 j)

def gl_O {M N1 N2 : ℕ} (β : ℕ) (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool) :
    GlOut N2 β → Bool :=
  gl_A β (gl_fl R) (fun j => R (gl_vc M N1 j, rc M (N1+N2)))
    (fun p => R (gl_vc M N1 p.1, gl_vc M N1 p.2)) (!R (rc M (N1+N2), rc M (N1+N2)))

theorem gl_dot {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool) (c : Fin N1 → ZMod 2)
    (e : Fin N2 → ZMod 2) (i : Fin M) :
    gl_Hf Hb i ⬝ᵥ Fin.append c e =
      (∑ j : Fin N1, b2z (Hb (i, ⟨j.val, by omega⟩)) * c j) +
      (∑ j : Fin N2, b2z (Hb (i, ⟨N1 + j.val, by omega⟩)) * e j) := by
  simp only [dotProduct]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rfl

theorem gl_split {M N1 N2 : ℕ} (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool)
    (c : Fin N1 → ZMod 2) (e : Fin N2 → ZMod 2) (p : Fin (N1+N2))
    (hc0 : ∀ q : Fin N1, pv R (Fin.castAdd N2 q) = false →
      (c q = 0 ∨ R (cl M p, cl M (Fin.castAdd N2 q)) = false)) :
    (∑ q : Fin (N1+N2), if pv R q = false then mat R (cl M p) (cl M q) * Fin.append c e q else 0) =
      ∑ q : Fin N2, if gl_fl R q = true then b2z (R (cl M p, gl_vc M N1 q)) * e q else 0 := by
  rw [Fin.sum_univ_add]
  have h1 : (∑ q : Fin N1, if pv R (Fin.castAdd N2 q) = false then
      mat R (cl M p) (cl M (Fin.castAdd N2 q)) * Fin.append c e (Fin.castAdd N2 q) else 0) = 0 := by
    apply sum_eq_zero
    intro q _
    by_cases h : pv R (Fin.castAdd N2 q) = false
    · rw [if_pos h, Fin.append_left]
      rcases hc0 q h with h0 | h0
      · rw [h0, mul_zero]
      · simp [mat, h0]
    · rw [if_neg h]
  rw [h1, zero_add]
  apply sum_congr rfl
  intro q _
  rw [Fin.append_right]
  have hiff : (pv R (Fin.natAdd N1 q) = false) ↔ (gl_fl R q = true) := by
    simp [gl_fl, pv, gl_vc]
  by_cases h : gl_fl R q = true
  · rw [if_pos h, if_pos (hiff.mpr h)]
    rfl
  · rw [if_neg h, if_neg (fun hh => h (hiff.mp hh))]

theorem gl_char {M N1 N2 : ℕ} (Hb : Fin M × Fin (N1+N2+1) → Bool)
    (hcons : gj _ (gl_mat Hb) (rc M (N1+N2), rc M (N1+N2)) = false) (e : Fin N2 → ZMod 2) :
    glSol M N1 N2 Hb e ↔ gl_P (gl_fl (gj _ (gl_mat Hb)))
      (fun j => gj _ (gl_mat Hb) (gl_vc M N1 j, rc M (N1+N2)))
      (fun p => gj _ (gl_mat Hb) (gl_vc M N1 p.1, gl_vc M N1 p.2)) e := by
  rw [gl_mat_eq] at hcons ⊢
  have hmain := fun v => fh_main_iff (gl_Hf Hb) (gl_rhs Hb) hcons v
  constructor
  · rintro ⟨c, hc⟩ j hj
    have h1 : ∀ i, gl_Hf Hb i ⬝ᵥ Fin.append c e = gl_rhs Hb i := by
      intro i; rw [gl_dot]; exact hc i
    have h2 := (hmain _).mp h1 (Fin.natAdd N1 j) (by simpa [gl_fl, pv, gl_vc] using hj)
    rw [Fin.append_right, gl_split _ c e (Fin.natAdd N1 j) (fun q _ => Or.inr
      (gj_upper _ _ _ (by
        show (cl M (Fin.castAdd N2 q)).val < (cl M (Fin.natAdd N1 j)).val
        simp [cl]; omega)))] at h2
    rw [h2]
    congr 1
  · intro hP
    have hcl : ∀ (x : Fin (M + (N1+N2) + 1)) (y : Fin (M + (N1+N2) + 1)),
        mat (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb))) x y =
          b2z (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb)) (x, y)) := fun x y => rfl
    refine ⟨fun q => if pv (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb))) (Fin.castAdd N2 q) = true then
      b2z (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb)) (cl M (Fin.castAdd N2 q), rc M (N1+N2))) +
        ∑ q' : Fin N2, (if gl_fl (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb))) q' = true then
          b2z (gj _ (sysBits (gl_Hf Hb) (gl_rhs Hb)) (cl M (Fin.castAdd N2 q), gl_vc M N1 q')) * e q'
          else 0) else 0, ?_⟩
    intro i
    rw [← gl_dot]
    revert i
    refine (hmain _).mpr ?_
    intro p hp
    rw [gl_split _ _ e p (fun q hq => Or.inl (by rw [if_neg (by rw [hq]; exact Bool.false_ne_true)])),
      hcl]
    revert hp
    refine Fin.addCases (fun q => ?_) (fun j => ?_) p
    · intro hp
      rw [Fin.append_left, if_pos hp]
    · intro hp
      rw [Fin.append_right]
      exact hP j (by simpa [gl_fl, pv, gl_vc] using hp)

abbrev gl_B (M N1 N2 β : ℕ) : Type :=
  (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) ⊕ (Fin (N2 + 1) × Fin (β + 1))

def gl_blk {M N1 N2 : ℕ} (β : ℕ) (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool) :
    gl_B M N1 N2 β → Bool :=
  elim R (fun p => decide (cnt (gl_fl R) p.1.val = p.2.val))

def gl_Psi {M N1 N2 : ℕ} (β : ℕ) (w : gl_B M N1 N2 β → Bool) : GlOut N2 β → Bool :=
  elim (fun p => decide (∃ q : Fin N2, ((!w (inl (gl_vc M N1 q, gl_vc M N1 q))) &&
      w (inr (⟨q.val, by omega⟩, ⟨p.2.val, by omega⟩)) &&
      xor (decide (p.1 = q)) (w (inl (gl_vc M N1 p.1, gl_vc M N1 q)))) = true))
    (elim (fun j => w (inl (gl_vc M N1 j, rc M (N1+N2))))
      (elim (fun t => decide (∃ q : Fin N2, ((!w (inl (gl_vc M N1 q, gl_vc M N1 q))) &&
        w (inr (⟨q.val, by omega⟩, ⟨t.val, by omega⟩))) = true))
      (fun _ => !w (inl (rc M (N1+N2), rc M (N1+N2))))))

theorem gl_Psi_eq {M N1 N2 : ℕ} (β : ℕ)
    (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool) :
    gl_Psi β (gl_blk β R) = gl_O β R := by
  funext k
  rcases k with p | j | t | u
  · simp only [gl_Psi, gl_blk, gl_O, gl_A, elim_inl, elim_inr]
    refine decide_eq_decide.mpr (exists_congr fun q => ?_)
    simp [gl_fl, and_assoc]
  · rfl
  · simp only [gl_Psi, gl_blk, gl_O, gl_A, elim_inl, elim_inr]
    refine decide_eq_decide.mpr (exists_congr fun q => ?_)
    simp [gl_fl]
  · rfl

theorem gl_xbit (M N1 N2 β : ℕ) (j q : Fin N2) :
    Cb (gl_B M N1 N2 β) 1
      (fun w => xor (decide (j = q)) (w (inl (gl_vc M N1 j, gl_vc M N1 q)))) := by
  by_cases h : j = q
  · refine ((Cb.not (Cb.var (inl (gl_vc M N1 j, gl_vc M N1 q)))).mono (by norm_num)).congr ?_
    intro w; simp [h]
  · refine ((Cb.var (inl (gl_vc M N1 j, gl_vc M N1 q))).mono (by norm_num)).congr ?_
    intro w; simp [h]

theorem gl_Psi_cb (M N1 N2 β : ℕ) (k : GlOut N2 β) :
    Cb (gl_B M N1 N2 β) (N2 * 5 + 1) (fun w => gl_Psi β w k) := by
  rcases k with p | j | t | u
  · have := Cb.bigOr (ι := gl_B M N1 N2 β) (I := Fin N2)
      (φ := fun q w => ((!w (inl (gl_vc M N1 q, gl_vc M N1 q))) &&
        w (inr (⟨q.val, by omega⟩, ⟨p.2.val, by omega⟩)) &&
        xor (decide (p.1 = q)) (w (inl (gl_vc M N1 p.1, gl_vc M N1 q)))))
      (fun q => (Cb.and (Cb.and (Cb.not (Cb.var _)) (Cb.var _)) (gl_xbit M N1 N2 β p.1 q)))
    rw [card_fin] at this
    exact (this.mono (by norm_num)).congr (fun w => decide_eq_decide.mpr Iff.rfl)
  · exact (Cb.var (inl (gl_vc M N1 j, rc M (N1+N2)))).mono (by omega)
  · have := Cb.bigOr (ι := gl_B M N1 N2 β) (I := Fin N2)
      (φ := fun q w => ((!w (inl (gl_vc M N1 q, gl_vc M N1 q))) &&
        w (inr (⟨q.val, by omega⟩, ⟨t.val, by omega⟩))))
      (fun q => (Cb.and (Cb.not (Cb.var _)) (Cb.var _)))
    rw [card_fin] at this
    exact (this.mono (by omega)).congr (fun w => decide_eq_decide.mpr Iff.rfl)
  · exact (Cb.not (Cb.var (inl (rc M (N1+N2), rc M (N1+N2))))).mono (by omega)

theorem gl_mat_cb (M N1 N2 : ℕ) (p : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) :
    Cb (Fin M × Fin (N1+N2+1)) 1 (fun Hb => gl_mat Hb p) := by
  by_cases hi : p.1.val < M
  · by_cases hj : p.2.val < N1+N2+1
    · refine ((Cb.var ((⟨p.1.val, hi⟩ : Fin M), (⟨p.2.val, hj⟩ : Fin (N1+N2+1)))).mono
        (by norm_num)).congr ?_
      intro v; simp [gl_mat, hi, hj]
    · refine (Cb.const false).congr ?_
      intro v; simp [gl_mat, hi, hj]
  · refine (Cb.const false).congr ?_
    intro v; simp [gl_mat, hi]

theorem gl_arith (d n b X : ℕ) (hd : d + 1 ≤ X) (hn : n + 1 ≤ X) (hb : b + 1 ≤ X) :
    d * d * 1 + 32 * (d + 1) ^ 4 + (0 + (n * (0 + 1) + (n + 1) * ((b + 1) * 6))) +
      (n * b + (n + (b + 1))) * (n * 5 + 1) ≤ 2 ^ 12 * X ^ 6 := by
  have hX : 1 ≤ X := by omega
  have a1 : d * d ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
  have a2 : (d + 1) ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left hd 4
  have a3 : (n + 1) * (b + 1) ≤ X * X := Nat.mul_le_mul hn hb
  have a4 : n * 5 + 1 ≤ 5 * X := by omega
  have a5 : (n * b + (n + (b + 1))) = (n + 1) * (b + 1) := by ring
  have a6 : ((n + 1) * (b + 1)) * (n * 5 + 1) ≤ (X * X) * (5 * X) := Nat.mul_le_mul a3 a4
  have p2 : X * X ≤ X ^ 6 := by
    calc X * X = X ^ 2 := by ring
      _ ≤ X ^ 6 := Nat.pow_le_pow_right hX (by norm_num)
  have p4 : X ^ 4 ≤ X ^ 6 := Nat.pow_le_pow_right hX (by norm_num)
  have p3 : (X * X) * (5 * X) ≤ 5 * X ^ 6 := by
    calc (X * X) * (5 * X) = 5 * X ^ 3 := by ring
      _ ≤ 5 * X ^ 6 := Nat.mul_le_mul_left 5 (Nat.pow_le_pow_right hX (by norm_num))
  have a7 : (n + 1) * ((b + 1) * 6) = 6 * ((n + 1) * (b + 1)) := by ring
  have a8 : n ≤ X ^ 6 := by
    have : n ≤ X * X := by nlinarith
    omega
  rw [a5, a7]
  generalize (n + 1) * (b + 1) * (n * 5 + 1) = T at a6 ⊢
  generalize (n + 1) * (b + 1) = U at a3 ⊢
  generalize (d + 1) ^ 4 = E at a2 ⊢
  generalize d * d = Q at a1 ⊢
  generalize X * X * (5 * X) = P3 at a6 p3
  generalize X * X = P2 at a1 a3 p2
  generalize X ^ 4 = P4 at a2 p4
  generalize X ^ 6 = Y at *
  omega

theorem gl_main (M N1 N2 β : ℕ) :
    ∃ (F : (Fin M × Fin (N1+N2+1) → Bool) → GlOut N2 β → Bool)
      (nf : (Fin M × Fin (N1+N2+1) → Bool) → ℕ),
      Cmp (Fin M × Fin (N1+N2+1)) (GlOut N2 β) (glCost M N1 N2 β) F ∧ GlSpec M N1 N2 β F nf := by
  refine ⟨fun Hb => gl_O β (gj _ (gl_mat Hb)), fun Hb => cnt (gl_fl (gj _ (gl_mat Hb))) N2, ?_, ?_⟩
  · have c1 : Cmp (Fin M × Fin (N1+N2+1))
        (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1))
        (card (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) * 1) gl_mat :=
      Cmp.ofBits (fun p => gl_mat_cb M N1 N2 p)
    have c2 := cmp_gj (M + (N1+N2) + 1)
    have hn : Cmp (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) (Fin N2)
        (card (Fin N2) * (0 + 1)) (fun R q => gl_fl R q) :=
      Cmp.ofBits (fun q => Cb.not (Cb.var (gl_vc M N1 q, gl_vc M N1 q)))
    have c3 := Cmp.pair (Cmp.wire (ι := Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) id)
      (Cmp.comp hn (cmp_counter N2 β))
    have c3' : Cmp (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) (gl_B M N1 N2 β) _
        (gl_blk β) := Cmp.congr c3 (by intro R k; rcases k with k | k <;> rfl)
    have c4 : Cmp (gl_B M N1 N2 β) (GlOut N2 β) (card (GlOut N2 β) * (N2 * 5 + 1))
        (gl_Psi β) := Cmp.ofBits (fun k => gl_Psi_cb M N1 N2 β k)
    have call := ((c1.comp c2).comp c3').comp c4
    refine Cmp.mono (Cmp.congr call ?_) ?_
    · intro Hb k
      show gl_Psi β (gl_blk β (gj _ (gl_mat Hb))) k = _
      rw [gl_Psi_eq]
    · simp only [card_prod, card_sum, card_fin, card_unit]
      unfold gjCost glCost
      exact gl_arith (M + (N1+N2) + 1) N2 β (M + N1 + N2 + β + 2) (by omega) (by omega) (by omega)
  · intro Hb
    have hz : ∀ q : Fin N2, gl_fl (gj _ (gl_mat Hb)) q = true →
        gj _ (gl_mat Hb) (gl_vc M N1 q, rc M (N1+N2)) = false ∧
        ∀ q' : Fin N2, gj _ (gl_mat Hb) (gl_vc M N1 q, gl_vc M N1 q') = false := by
      intro q hq
      have hq' : gj _ (gl_mat Hb) (gl_vc M N1 q, gl_vc M N1 q) = false := by
        simpa [gl_fl] using hq
      exact ⟨gj_zerorow _ _ hq' _, fun q' => gj_zerorow _ _ hq' _⟩
    refine ⟨?_, ?_⟩
    · intro hc e he
      have hc' : gj _ (gl_mat Hb) (rc M (N1+N2), rc M (N1+N2)) = true := by
        simpa [gl_O, gl_A] using hc
      obtain ⟨c, hce⟩ := he
      rw [gl_mat_eq] at hc'
      refine la_incons (gl_Hf Hb) (gl_rhs Hb) hc' (Fin.append c e) ?_
      intro i; rw [gl_dot]; exact hce i
    · intro hc
      have hc' : gj _ (gl_mat Hb) (rc M (N1+N2), rc M (N1+N2)) = false := by
        simpa [gl_O, gl_A] using hc
      refine ⟨?_, ?_, ?_⟩
      · rw [Nat.card_congr (Equiv.subtypeEquivRight (fun e => gl_char Hb hc' e))]
        exact gl_P_card _ _ _
      · intro t
        exact gl_A_used _ _ _ _ t
      · intro hβ
        refine ⟨?_, ?_, ?_⟩
        · intro x _
          exact (gl_char Hb hc' _).mpr (gl_A_sol _ _ _ _ hz hβ x)
        · intro e he
          exact gl_A_surj _ _ _ _ hz hβ e ((gl_char Hb hc' e).mp he)
        · intro x x' hx hx' h
          exact gl_A_inj _ _ _ _ hz hβ x x' hx hx' h

def solS {ρ ι1 ι2 : Type} [Fintype ι1] [Fintype ι2]
    (Hb : ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) (e : ι2 → ZMod 2) : Prop :=
  ∃ c : ι1 → ZMod 2, ∀ i : ρ,
    (∑ j : ι1, b2z (Hb (i, inl j)) * c j) +
    (∑ j : ι2, b2z (Hb (i, inr (inl j))) * e j) = b2z (Hb (i, inr (inr ())))

abbrev SOut (ι2 : Type) (β : ℕ) : Type := (ι2 × Fin β) ⊕ (ι2 ⊕ (Fin β ⊕ Unit))

def sPt {ι2 : Type} {β : ℕ} (o : SOut ι2 β → Bool) (x : Fin β → ZMod 2) : ι2 → ZMod 2 :=
  fun j => b2z (o (inr (inl j))) + ∑ t : Fin β, b2z (o (inl (j, t))) * x t

def sOk {ι2 : Type} {β : ℕ} (o : SOut ι2 β → Bool) (x : Fin β → ZMod 2) : Prop :=
  ∀ t : Fin β, o (inr (inr (inl t))) = false → x t = 0

def SSpec (ρ ι1 ι2 : Type) [Fintype ι1] [Fintype ι2] (β : ℕ)
    (F : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → SOut ι2 β → Bool)
    (nf : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → ℕ) : Prop :=
  ∀ Hb : ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool,
    (F Hb (inr (inr (inr ()))) = false → ∀ e, ¬ solS Hb e) ∧
    (F Hb (inr (inr (inr ()))) = true →
      Nat.card {e : ι2 → ZMod 2 // solS Hb e} = 2^(nf Hb) ∧
      (∀ t : Fin β, F Hb (inr (inr (inl t))) = true ↔ t.val < nf Hb) ∧
      (nf Hb ≤ β →
        (∀ x, sOk (F Hb) x → solS Hb (sPt (F Hb) x)) ∧
        (∀ e, solS Hb e → ∃ x, sOk (F Hb) x ∧ sPt (F Hb) x = e) ∧
        (∀ x x', sOk (F Hb) x → sOk (F Hb) x' → sPt (F Hb) x = sPt (F Hb) x' → x = x')))

def tabN {t : ℕ} (T : Fin t → Bool) : ℕ := ∑ j : Fin t, if T j then 2^j.val else 0

theorem st_tabN_succ {t : ℕ} (T : Fin (t+1) → Bool) :
    tabN T = tabN (fun j : Fin t => T j.castSucc) + (if T (Fin.last t) then 2^t else 0) := by
  unfold tabN
  rw [Fin.sum_univ_castSucc]
  simp

theorem st_tabN_lt : ∀ {t : ℕ} (T : Fin t → Bool), tabN T < 2^t := by
  intro t
  induction t with
  | zero => intro T; simp [tabN]
  | succ t ih =>
    intro T
    rw [st_tabN_succ]
    have := ih (fun j : Fin t => T j.castSucc)
    rw [pow_succ]
    split <;> omega

theorem st_tabN_testBit : ∀ {t : ℕ} (T : Fin t → Bool) (j : Fin t),
    (tabN T).testBit j.val = T j := by
  intro t
  induction t with
  | zero => intro T j; exact j.elim0
  | succ t ih =>
    intro T j
    rw [st_tabN_succ]
    have hlt := st_tabN_lt (fun j : Fin t => T j.castSucc)
    by_cases hj : j.val < t
    · have e : j = (⟨j.val, hj⟩ : Fin t).castSucc := Fin.ext rfl
      have := ih (fun j : Fin t => T j.castSucc) ⟨j.val, hj⟩
      by_cases hT : T (Fin.last t) = true
      · rw [if_pos hT, add_comm, Nat.testBit_two_pow_add_gt hj, this]
        exact congrArg T e.symm
      · rw [if_neg hT, add_zero, this]
        exact congrArg T e.symm
    · have e : j = Fin.last t := Fin.ext (by have := j.isLt; simp; omega)
      subst e
      by_cases hT : T (Fin.last t) = true
      · rw [if_pos hT, add_comm]
        simp only [Fin.val_last]
        rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt, hT]
        rfl
      · rw [if_neg hT, add_zero]
        simp only [Fin.val_last]
        rw [Nat.testBit_lt_two_pow hlt]
        simpa using hT

theorem st_dec_b2z (x : Bool) : decide (b2z x ≠ 0) = x := by
  cases x <;> simp [b2z]

theorem glS (ρ ι1 ι2 : Type) [Fintype ρ] [Fintype ι1] [Fintype ι2] (β : ℕ) :
    ∃ (F : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → SOut ι2 β → Bool)
      (nf : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → ℕ),
      Cmp (ρ × (ι1 ⊕ (ι2 ⊕ Unit))) (SOut ι2 β)
        (glCost (card ρ) (card ι1) (card ι2) β) F ∧
      SSpec ρ ι1 ι2 β F nf := by
  classical
  obtain ⟨F0, nf0, hC, hS⟩ :=
    gl_main (card ρ) (card ι1) (card ι2) β
  let eρ := Fintype.equivFin ρ
  let e1 := Fintype.equivFin ι1
  let e2 := Fintype.equivFin ι2
  let col : Fin (card ι1 + card ι2 + 1) → ι1 ⊕ (ι2 ⊕ Unit) := fun j =>
    if h : j.val < card ι1 then inl (e1.symm ⟨j.val, h⟩)
    else if h2 : j.val < card ι1 + card ι2 then
      inr (inl (e2.symm ⟨j.val - card ι1, by omega⟩))
    else inr (inr ())
  let σ : Fin (card ρ) × Fin (card ι1 + card ι2 + 1) →
      ρ × (ι1 ⊕ (ι2 ⊕ Unit)) := fun p => (eρ.symm p.1, col p.2)
  let om : SOut ι2 β → GlOut (card ι2) β :=
    elim (fun p => inl (e2 p.1, p.2))
      (elim (fun j => inr (inl (e2 j))) (fun x => inr (inr x)))
  have hcol1 : ∀ (j : Fin (card ι1)) (h : j.val < card ι1 + card ι2 + 1),
      col ⟨j.val, h⟩ = inl (e1.symm j) := by
    intro j h
    simp [col, j.isLt]
  have hcol2 : ∀ (j : Fin (card ι2))
      (h : card ι1 + j.val < card ι1 + card ι2 + 1),
      col ⟨card ι1 + j.val, h⟩ = inr (inl (e2.symm j)) := by
    intro j h
    simp [col, j.isLt]
  have hcol3 : ∀ (h : card ι1 + card ι2 < card ι1 + card ι2 + 1),
      col ⟨card ι1 + card ι2, h⟩ = inr (inr ()) := by
    intro h
    simp [col]
  refine ⟨fun Hb o => F0 (fun p => Hb (σ p)) (om o), fun Hb => nf0 (fun p => Hb (σ p)), ?_, ?_⟩
  · exact (Cmp.comp (Cmp.sel σ hC) (Cmp.wire om)).mono (by omega)
  · intro Hb
    let H := Hb ∘ σ
    let E := Equiv.arrowCongr e2 (Equiv.refl F)
    have key (e : ι2 → F) : solS Hb e ↔ glSol _ _ _ H (E e) := by
      unfold solS glSol
      refine Equiv.exists_congr (Equiv.arrowCongr e1 (Equiv.refl F)) (fun c => ?_)
      refine Equiv.forall_congr eρ (fun i => ?_)
      rw [← e1.sum_comp, ← e2.sum_comp]
      simp only [H, Function.comp_apply, σ, hcol1, hcol2, hcol3, E, Equiv.arrowCongr_apply,
        Equiv.symm_apply_apply, Equiv.refl_apply]
    let Fout := F0 H
    obtain ⟨no,yes⟩ := hS H
    refine ⟨fun h e he => no h (E e) ((key e).mp he),?_⟩
    intro h
    obtain ⟨card,flags,proj⟩ := yes h
    refine ⟨(Nat.card_congr (Equiv.subtypeEquiv E key)).trans card, flags, ?_⟩
    intro bound
    obtain ⟨sound,onto,inj⟩ := proj bound
    have point (x : Fin β → F) :
        E (sPt (Fout ∘ om) x) = glPt Fout x := by
      funext j
      change glPt Fout x (e2 (e2.symm j)) = _
      rw [Equiv.apply_symm_apply]
    refine ⟨?_,?_ ,?_⟩
    · intro x ok
      apply (key _).mpr
      change glSol _ _ _ H (E (sPt (Fout ∘ om) x))
      rw [point]
      exact sound x ok
    · intro e he
      obtain ⟨x,ok,eq⟩ := onto (E e) ((key e).mp he)
      exact ⟨x,ok,E.injective ((point x).trans eq)⟩
    · intro x y hx hy eq
      exact inj x y hx hy ((point x).symm.trans ((congrArg E eq).trans (point y)))

end Donor

section Helpers

open Donor

abbrev ProjIn (ρ α β : Type) := ρ × (α ⊕ (β ⊕ Unit))

def zbit (a : F) : Bool := decide (a ≠ 0)

lemma zbit_decode (a : F) : b2z (zbit a) = a := by
  rcases ffCases a with rfl | rfl <;> decide

def enabled {J : Type} {d : ℕ} (o : SOut J d → Bool) (t : Fin d) : Bool :=
  o (.inr (.inr (.inl t)))

def successful {J : Type} {d : ℕ} (o : SOut J d → Bool) : Bool :=
  o (.inr (.inr (.inr ())))

def offset {J : Type} {d : ℕ} (o : SOut J d → Bool) : J → F :=
  fun j => b2z (o (.inr (.inl j)))

def column {J : Type} {d : ℕ} (o : SOut J d → Bool) (t : Fin d) : J → F :=
  fun j => b2z (enabled o t && o (.inl (j,t)))

lemma project_zero {J : Type} {d : ℕ} (o : SOut J d → Bool) : sOk o 0 := by
  intro t _
  rfl

lemma project_point {J : Type} {d : ℕ} (o : SOut J d → Bool) (x : Fin d → F)
    (hx : sOk o x) : sPt o x = offset o + ∑ t : Fin d, x t • column o t := by
  funext j
  simp only [sPt, offset, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  cases h : enabled o t
  · rw [hx t h]
    simp
  · simp [column, h, mul_comm]

lemma project_point_zero {J : Type} {d : ℕ} (o : SOut J d → Bool) : sPt o 0 = offset o := by
  rw [project_point o 0 (project_zero o)]
  simp

lemma project_span {J : Type} {d : ℕ} (o : SOut J d → Bool)
    (K : Submodule F (J → F))
    (hproj : (∀ x, sOk o x → sPt o x ∈ K) ∧
      (∀ v ∈ K, ∃ x, sOk o x ∧ sPt o x = v)) :
    span F (Set.range (column o)) = K := by
  have h0 : offset o ∈ K := by simpa only [project_point_zero] using hproj.1 0 (project_zero o)
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨t, rfl⟩
    cases h : enabled o t
    · have hz : column o t = 0 := by funext j; simp [column, h, b2z]
      rw [hz]
      exact K.zero_mem
    · let x : Fin d → F := Pi.single t 1
      have hx : sOk o x := by
        intro u hu
        change enabled o u = false at hu
        have hne : u ≠ t := fun e => by subst u; rw [h] at hu; contradiction
        exact Pi.single_eq_of_ne hne 1
      have hval := hproj.1 x hx
      rw [project_point o x hx] at hval
      have hs : (∑ u : Fin d, x u • column o u) = column o t := by
        rw [sum_eq_single t]
        · simp [x]
        · intro j _ hj
          rw [show x j = 0 from Pi.single_eq_of_ne hj 1, zero_smul]
        · simp
      rw [hs] at hval
      exact (K.add_mem_iff_right h0).mp hval
  · intro a ha
    have hshift := K.add_mem h0 ha
    obtain ⟨x, hx, hxa⟩ := hproj.2 _ hshift
    rw [project_point o x hx] at hxa
    rw [← add_left_cancel hxa]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (subset_span ⟨t, rfl⟩)

lemma projected_submodule {ρ α J : Type} [Fintype α] [Fintype J]
    {β : ℕ} (o : (ProjIn ρ α J → Bool) → SOut J β → Bool) (nf : (ProjIn ρ α J → Bool) → ℕ)
    (h : SSpec ρ α J β o nf) (v : ProjIn ρ α J → Bool)
    (K : Submodule F (J → F)) (hk : ∀ x, solS v x ↔ x ∈ K) :
    successful (o v) = true ∧ finrank F K = nf v ∧
    (nf v ≤ β → span F (Set.range (column (o v))) = K) := by
  obtain ⟨hno, hyes⟩ := h v
  have hsuccess : successful (o v) = true := by
    cases hs : successful (o v)
    · exact False.elim (hno hs 0 ((hk 0).mpr K.zero_mem))
    · rfl
  obtain ⟨hcard, _, hproj⟩ := hyes hsuccess
  have hcard' : Nat.card K = 2^(nf v) := by
    let e : K ≃ {x // solS v x} :=
      { toFun := fun x => ⟨x, (hk x).mpr x.prop⟩
        invFun := fun x => ⟨x, (hk x).mp x.prop⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans hcard
  have hc : Nat.card F = 2 := by simp [Nat.card_eq_fintype_card, ZMod.card]
  have hp : 2 ^ finrank F K = 2 ^ (nf v) := by
    rwa [Module.natCard_eq_pow_finrank (K := F), hc] at hcard'
  refine ⟨hsuccess, le_antisymm ((Nat.pow_le_pow_iff_right (by decide)).mp hp.le)
    ((Nat.pow_le_pow_iff_right (by decide)).mp hp.ge), ?_⟩
  intro hcap
  obtain ⟨hin, hsurj, _⟩ := hproj hcap
  exact project_span (o v) K ⟨fun x hx => (hk _).mp (hin x hx), fun x hx => hsurj x ((hk _).mpr hx)⟩

def intersectSys {J U : Type} [DecidableEq U] (R : J → U → F) (p : J → Bool) :
    ProjIn (Bool × U) (Bool × J) U → Bool :=
  fun x => match x.2 with
  | .inl y => (x.1.1 == y.1) && (p y.2 == y.1) && zbit (R y.2 x.1.2)
  | .inr (.inl u) => decide (x.1.2 = u)
  | .inr (.inr ()) => false

lemma sum_mask {J U : Type} [Fintype J] (R : J → U → F) (p : J → Bool) (x : U → F) :
    (∃ a : J → F, (∑ j : J, a j • (if p j then R j else 0)) = x) ↔
      x ∈ selectedSpan R p := by
  rw [← maskedSpan]
  exact (mem_span_range_iff_exists_fun F).symm

lemma intersectionSys_spec {J U : Type} [Fintype J] [Fintype U] [DecidableEq U]
    (R : J → U → F) (p : J → Bool) (x : U → F) :
    solS (intersectSys R p) x ↔ x ∈ selectedSpan R p ⊓ selectedSpan R (fun j => !p j) := by
  have hd (a : Bool × J → F) (b : Bool) (u : U) :
      (∑ y : Bool × J, b2z (intersectSys R p ((b,u), .inl y)) * a y) =
        ∑ j : J, a (b,j) * (if p j == b then R j u else 0) := by
    rw [Fintype.sum_prod_type, sum_eq_single b]
    · refine sum_congr rfl fun j _ => ?_
      cases hb : (p j == b)
      · simp [intersectSys, hb, b2z]
      · simp only [intersectSys, beq_self_eq_true, Bool.true_and, hb, ite_true, zbit_decode]
        exact mul_comm _ _
    · intro b' _ hb'
      refine sum_eq_zero fun j _ => ?_
      cases b <;> cases b' <;> simp_all [intersectSys, b2z]
    · simp
  have hs (a : J → F) (b : Bool) (u : U) :
      (∑ j : J, a j • (if p j == b then R j else 0)) u =
        ∑ j : J, a j * (if p j == b then R j u else 0) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_congr rfl fun j _ => by cases h : (p j == b) <;> rfl
  have hu (b : Bool) (u : U) :
      (∑ v : U, b2z (intersectSys R p ((b,u), .inr (.inl v))) * x v) = x u := by
    classical
    simp [intersectSys, b2z]
  have hzero (a b : F) : a + b = 0 ↔ a = b := by revert a b; decide
  constructor
  · rintro ⟨a, ha⟩
    have he (b : Bool) : (∑ j : J, a (b,j) • (if p j == b then R j else 0)) = x := by
      funext u
      rw [hs]
      have h := ha (b,u)
      rw [hd, hu] at h
      exact (hzero _ _).mp h
    exact ⟨(sum_mask R p x).mp ⟨fun j => a (true,j), by simpa using he true⟩,
      (sum_mask R (fun j => !p j) x).mp ⟨fun j => a (false,j), by
        simpa using he false⟩⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨acTrue, ht⟩ := (sum_mask R p x).mpr ha
    obtain ⟨af, hf⟩ := (sum_mask R (fun j => !p j) x).mpr hb
    let a : Bool × J → F := fun y => if y.1 then acTrue y.2 else af y.2
    have he (b : Bool) : (∑ j : J, a (b,j) • (if p j == b then R j else 0)) = x := by
      cases b
      · simpa [a] using hf
      · simpa [a] using ht
    refine ⟨a, ?_⟩
    rintro ⟨b,u⟩
    rw [hd, hu]
    exact (hzero _ _).mpr (by simpa only [hs] using congrFun (he b) u)

def system {ρ U : Type} (M : ρ → U → F) (b : ρ → F) : ProjIn ρ Empty U → Bool :=
  fun v => match v.2 with
  | .inl a => nomatch a
  | .inr (.inl u) => zbit (M v.1 u)
  | .inr (.inr ()) => zbit (b v.1)

lemma system_iff {ρ U : Type} [Fintype U] (M : ρ → U → F) (b : ρ → F) (v : U → F) :
    solS (system M b) v ↔ ∀ i, dotProduct (M i) v = b i := by
  unfold solS
  simp only [Fintype.univ_empty, Finset.sum_empty, zero_add, system, zbit_decode, dotProduct]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Empty.elim, h⟩⟩

lemma null_iff {J U : Type} [Fintype J] (R : J → U → F) (a : J → F) :
    solS (system (fun u j => R j u) (fun _ => 0)) a ↔
      a ∈ LinearMap.ker (Fintype.linearCombination F R) := by
  rw [system_iff]
  change (∀ u, ∑ j, R j u * a j = 0) ↔ Fintype.linearCombination F R a = 0
  rw [Fintype.linearCombination_apply]
  change _ ↔ (∑ j, a j • R j) = 0
  constructor
  · intro h
    funext u
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using h u
  · intro h u
    have h' := congrFun h u
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_comm] using h'

end Helpers

namespace PackedTape

-- Enumeration, idxOf and map/ofFn bridge adapted from L_meta_25940.lean,
-- lines 6034–6088 at 04168edab39014e515fbb09f71ba0651b69367a8.

abbrev tapeSize (k r : ℕ) := (2 * r + 3) * k
abbrev inputs (k r q n : ℕ) :=
  (2 + 2 * r) * k + q * (tapeSize k r + 1) + n * ((2 * r + 1) * k)

abbrev ObsSlot (k r : ℕ) := Fin k ⊕ ((Bool × Fin (r + 1) × Fin k) ⊕ Unit)
abbrev InputSlot (k r q n : ℕ) :=
  (Bool × Fin k) ⊕ ((Bool × Fin r × Fin k) ⊕ ((Fin q × ObsSlot k r) ⊕ (Fin n × Leaf k r)))

variable {k r q n : ℕ}

def nameSlot (b : Bool) (j : Fin k) : InputSlot k r q n := .inl (b, j)
def cSlot (b : Bool) (t : Fin r) (j : Fin k) : InputSlot k r q n := .inr (.inl (b, t, j))
def obsKeySlot (i : Fin q) (j : Fin k) : InputSlot k r q n := .inr (.inr (.inl (i, .inl j)))
def obsTapeSlot (i : Fin q) (b : Bool) (t : Fin (r + 1)) (j : Fin k) : InputSlot k r q n :=
  .inr (.inr (.inl (i, .inr (.inl (b, t, j)))))
def rhsSlot (i : Fin q) : InputSlot k r q n := .inr (.inr (.inl (i, .inr (.inr ()))))
def bagSlot (v : Fin n) (l : Leaf k r) : InputSlot k r q n := .inr (.inr (.inr (v, l)))

theorem card_inputSlot (k r q n : ℕ) : card (InputSlot k r q n) = inputs k r q n := by
  simp only [InputSlot, ObsSlot, Leaf, card_sum, card_prod, card_bool,
    card_fin, card_unit, inputs, tapeSize]
  ring

def slotBit (name : Bool → Word k) (c : Bool → Fin r → Word k) (obs : Fin q → Tape k r)
    (rhs : Fin q → F) (bag : Fin n → Leaf k r → Bool) : InputSlot k r q n → Bool
  | .inl (b, j) => decide (name b j ≠ 0)
  | .inr (.inl (b, t, j)) => decide (c b t j ≠ 0)
  | .inr (.inr (.inl (i, .inl j))) => decide ((obs i).1 j ≠ 0)
  | .inr (.inr (.inl (i, .inr (.inl (b, t, j))))) => decide ((obs i).2 b t j ≠ 0)
  | .inr (.inr (.inl (i, .inr (.inr ())))) => decide (rhs i ≠ 0)
  | .inr (.inr (.inr (v, l))) => bag v l

end PackedTape

namespace Greedy

-- Descending initial segments from L_meta_33648.lean (04168edab39014e515fbb09f71ba0651b69367a8),
-- ta_arg–ta_top_sem. Uses only the transferred Donor Cmp/Cb combinators.
open Donor
open scoped BigOperators

abbrev Bits (k : ℕ) := Fin k → Bool
-- Input wires are data, mask, then values. A true mask bit fixes the corresponding key bit.
abbrev Input (ι : Type) (k : ℕ) := ι ⊕ (Fin k ⊕ Fin k)
abbrev Reply (k : ℕ) := Unit ⊕ Fin (k + 1)
abbrev Output (k : ℕ) := Reply k ⊕ Fin k

def input {ι : Type} {k : ℕ} (d : ι → Bool) (m p : Bits k) : Input ι k → Bool :=
  elim d (elim m p)

noncomputable def cardinal {k : ℕ} (P : Bits k → Prop) : ℕ := Nat.card {x // P x}

def matched {k : ℕ} (P : Bits k → Prop) (m p x : Bits k) : Prop :=
  P x ∧ ∀ j, m j = true → x j = p j

def OracleSpec {ι : Type} {k : ℕ} (F : (Input ι k → Bool) → Reply k → Bool)
    (ok : (ι → Bool) → Bool) (hit : (ι → Bool) → Bits k → Prop) : Prop :=
  ∀ d m p, F (input d m p) (.inl ()) = ok d ∧
    ∀ s : Fin (k + 1), F (input d m p) (.inr s) =
      (if ok d then cardinal (matched (hit d) m p) else 0).testBit s.val

def code {k : ℕ} (x : Bits k) : ℕ := ∑ j : Fin k, if x j then 2 ^ j.val else 0

private theorem code_split {n : ℕ} (x : Bits (n + 1)) :
    code x = code (fun i : Fin n => x i.castSucc) + (if x (Fin.last n) then 2 ^ n else 0) := by
  simp only [code, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

private theorem code_bound : ∀ {n : ℕ} (x : Bits n), code x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [code]
  | succ n ih =>
    intro x
    have h := ih (fun i : Fin n => x i.castSucc)
    rw [code_split, pow_succ]
    cases hb : x (Fin.last n) <;> simp [hb] <;> omega

private theorem code_less : ∀ {n : ℕ} (i : Fin n) (x y : Bits n),
    x i = false → y i = true → (∀ j : Fin n, i.val < j.val → x j = y j) → code x < code y := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i x y hx hy hhi
    by_cases hi : i.val = n
    · have hi' : i = Fin.last n := Fin.ext hi
      subst i
      have hb := code_bound (fun j : Fin n => x j.castSucc)
      simp [code_split, hx, hy]
      omega
    · let j : Fin n := ⟨i.val, by have := i.isLt; omega⟩
      have hj : j.castSucc = i := Fin.ext rfl
      have hh := hhi (Fin.last n) (by simp only [Fin.val_last]; have := i.isLt; omega)
      have hl := ih j (fun a => x a.castSucc) (fun a => y a.castSucc)
        (by simpa only [hj] using hx) (by simpa only [hj] using hy)
        (fun a ha => hhi a.castSucc ha)
      rw [code_split x, code_split y, hh]
      exact Nat.add_lt_add_right hl _

private theorem cardinal_pos {k : ℕ} (P : Bits k → Prop) :
    0 < cardinal P ↔ ∃ x, P x := by
  rw [cardinal, Nat.card_pos_iff]
  constructor
  · rintro ⟨⟨⟨x, hx⟩⟩, _⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨⟨x, hx⟩⟩, inferInstance⟩

private theorem cardinal_bound {k : ℕ} (P : Bits k → Prop) : cardinal P < 2 ^ (k + 1) := by
  have h := Nat.card_le_card_of_injective (Subtype.val : {x // P x} → Bits k) Subtype.val_injective
  have hc : Nat.card (Bits k) = 2 ^ k := by
    simp [Nat.card_eq_fintype_card, card_fun]
  rw [hc] at h
  have hp : 0 < 2 ^ k := by positivity
  rw [pow_succ]
  exact lt_of_le_of_lt h (by omega)

-- The word is nonempty, so its OR needs exactly n binary gates, not a fresh constant.
private def someBit : (n : ℕ) → Bits (n + 1) → Bool
  | 0, v => v 0
  | n + 1, v => someBit n (fun i => v i.castSucc) || v (Fin.last (n + 1))

private theorem someBit_true : ∀ (n : ℕ) (v : Bits (n + 1)),
    someBit n v = true ↔ ∃ i, v i = true := by
  intro n
  induction n with
  | zero =>
    intro v
    constructor
    · exact fun h => ⟨0, h⟩
    · rintro ⟨i, hi⟩
      have he : i = 0 := Fin.ext (by have := i.isLt; omega)
      simpa only [someBit, he] using hi
  | succ n ih =>
    intro v
    simp only [someBit, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi⟩ | h)
      · exact ⟨i.castSucc, hi⟩
      · exact ⟨Fin.last (n + 1), h⟩
    · rintro ⟨i, hi⟩
      revert hi
      exact Fin.lastCases (fun h => Or.inr h) (fun j h => Or.inl ⟨j, h⟩) i

private theorem someBit_cb {σ : Type} : ∀ (n : ℕ) (wire : Fin (n + 1) → σ),
    Cb σ n (fun v => someBit n (fun i => v (wire i))) := by
  intro n
  induction n with
  | zero => intro wire; exact Cb.var (wire 0)
  | succ n ih =>
    intro wire
    exact Cb.or (ih (fun i => wire i.castSucc)) (Cb.var (wire (Fin.last (n + 1))))

private theorem someBit_nat {k a : ℕ} (ha : a < 2 ^ (k + 1)) :
    someBit k (fun s => a.testBit s.val) = true ↔ 0 < a := by
  rw [someBit_true]
  constructor
  · rintro ⟨s, hs⟩
    by_contra hn
    have he : a = 0 := by omega
    simp [he] at hs
  · intro hp
    by_contra hn
    have he : a = 0 := Nat.zero_of_testBit_eq_false (fun i => by
      by_cases hi : i < k + 1
      · cases h : a.testBit i
        · rfl
        · exact False.elim (hn ⟨⟨i, hi⟩, h⟩)
      · exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))))
    omega

private abbrev Base (ι : Type) := ι ⊕ Bool
private abbrev State (ι : Type) (k : ℕ) := Base ι ⊕ (Reply k ⊕ Fin k)

private def base {ι : Type} (d : ι → Bool) : Base ι → Bool := elim d id
private def reply {ι : Type} {k : ℕ} (v : State ι k → Bool) (s : Reply k) : Bool := v (.inr (.inl s))
private def keys {ι : Type} {k : ℕ} (v : State ι k → Bool) (j : Fin k) : Bool := v (.inr (.inr j))
private def positive {k : ℕ} (v : Reply k → Bool) : Bool := someBit k (fun i => v (.inr i))

private def emptyRoute {ι : Type} {k : ℕ} : Input ι k → Base ι :=
  elim inl (elim (fun _ => .inr false) (fun _ => .inr false))

private def start {ι : Type} {k : ℕ} (F : (Input ι k → Bool) → Reply k → Bool)
    (v : Base ι → Bool) : State ι k → Bool :=
  elim v (elim (F (fun a => v (emptyRoute a))) (fun _ => v (.inr false)))

private def probeRoute {ι : Type} {k : ℕ} (i : Fin k) : Input ι k → State ι k
  | .inl a => .inl (.inl a)
  | .inr (.inl j) => .inl (.inr (decide (i.val ≤ j.val)))
  | .inr (.inr j) => if j = i then .inl (.inr false) else .inr (.inr j)

private def put {k : ℕ} (p : Bits k) (i : Fin k) (b : Bool) : Bits k :=
  fun j => if j = i then b else p j

private def advance {ι : Type} {k : ℕ} (F : (Input ι k → Bool) → Reply k → Bool)
    (i : Fin k) (v : State ι k → Bool) : State ι k → Bool :=
  elim (fun b => v (.inl b))
    (elim (reply v) (put (keys v) i (!positive (F (fun a => v (probeRoute i a))))))

private def loop {ι : Type} {k : ℕ} (F : (Input ι k → Bool) → Reply k → Bool) :
    ℕ → (State ι k → Bool) → State ι k → Bool
  | 0, v => v
  | q + 1, v => if hq : q < k then loop F q (advance F ⟨q, hq⟩ v) else v

private def finish {ι : Type} {k : ℕ} (v : State ι k → Bool) : Output k → Bool :=
  elim (reply v) (fun j => positive (reply v) && keys v j)

def wrap {ι : Type} {k : ℕ} (F : (Input ι k → Bool) → Reply k → Bool)
    (d : ι → Bool) : Output k → Bool := finish (loop F k (start F (base d)))

private theorem base_cmp (ι : Type) : Cmp ι (Base ι) 2 base := by
  let route : Base ι → ι ⊕ (Unit ⊕ Unit) :=
    elim inl (fun b => .inr (if b then .inr () else .inl ()))
  refine Cmp.congr (Cmp.comp (Cmp.keep (Cmp.pair (Cb.const false) (Cb.const true))) (Cmp.wire route)) ?_
  intro v a
  rcases a with a | b
  · rfl
  · cases b <;> rfl

private theorem start_cmp {ι : Type} {k S : ℕ} {F : (Input ι k → Bool) → Reply k → Bool}
    (hc : Cmp (Input ι k) (Reply k) S F) : Cmp (Base ι) (State ι k) S (start F) := by
  let route : State ι k → Base ι ⊕ Reply k :=
    elim inl (elim inr (fun _ => .inl (.inr false)))
  refine Cmp.congr (Cmp.comp (Cmp.keep (Cmp.sel emptyRoute hc)) (Cmp.wire route)) ?_
  intro v a
  rcases a with a | s | j <;> rfl

private theorem advance_cmp {ι : Type} {k S : ℕ} {F : (Input ι k → Bool) → Reply k → Bool}
    (hc : Cmp (Input ι k) (Reply k) S F) (i : Fin k) :
    Cmp (State ι k) (State ι k) (S + k + 1) (advance F i) := by
  have hpos : Cb (Reply k) k positive := someBit_cb k inr
  have hbit := Cb.comp (Cmp.sel (probeRoute i) hc) (Cb.not hpos)
  let route : State ι k → State ι k ⊕ Unit :=
    elim (fun b => .inl (.inl b)) (elim (fun s => .inl (.inr (.inl s)))
      (fun j => if j = i then .inr () else .inl (.inr (.inr j))))
  have hcomp := Cmp.comp (Cmp.keep hbit) (Cmp.wire route)
  simp only [Nat.add_zero, ← Nat.add_assoc] at hcomp
  refine Cmp.congr hcomp ?_
  intro v a
  rcases a with a | s | j
  · rfl
  · rfl
  · by_cases hj : j = i <;> simp [route, advance, put, keys, hj]

private theorem loop_cmp {ι : Type} {k S : ℕ} {F : (Input ι k → Bool) → Reply k → Bool}
    (hc : Cmp (Input ι k) (Reply k) S F) (q : ℕ) :
    Cmp (State ι k) (State ι k) (q * (S + k + 1)) (loop F q) := by
  induction q with
  | zero => simpa only [loop, Nat.zero_mul] using (Cmp.wire (fun a : State ι k => a))
  | succ q ih =>
    by_cases hq : q < k
    · have h := Cmp.comp (advance_cmp hc ⟨q, hq⟩) ih
      have ha : (S + k + 1) + q * (S + k + 1) = (q + 1) * (S + k + 1) := by
        rw [Nat.succ_mul]
        omega
      rw [ha] at h
      simpa only [loop, dif_pos hq] using h
    · simp only [loop, dif_neg hq]
      exact Cmp.mono (Cmp.wire (fun a : State ι k => a)) (Nat.zero_le _)

private theorem finish_cmp (ι : Type) (k : ℕ) :
    Cmp (State ι k) (Output k) (k + k) finish := by
  have ha : Cb (State ι k) k (fun v => positive (reply v)) :=
    someBit_cb (σ := State ι k) k (fun i => .inr (.inl (.inr i)))
  have hb : Cmp (State ι k ⊕ Unit) (Fin k) k
      (fun v j => v (.inr ()) && v (.inl (.inr (.inr j)))) := by
    have h := Cmp.ofBits (s := 1) (fun j : Fin k =>
      Cb.and (Cb.var (ι := State ι k ⊕ Unit) (.inr ())) (Cb.var (.inl (.inr (.inr j)))))
    simpa only [card_fin, Nat.mul_one] using h
  have hr := Cmp.wire (fun s : Reply k => (inl (.inr (.inl s)) : State ι k ⊕ Unit))
  have h := Cmp.comp (Cmp.keep ha) (Cmp.pair hr hb)
  rw [Nat.zero_add] at h
  refine Cmp.congr h ?_
  intro v a
  cases a <;> rfl

-- One unrestricted call and k calls on initial segments; all mask and unchanged key wires are shared.
theorem wrap_cmp {ι : Type} {k S : ℕ} {F : (Input ι k → Bool) → Reply k → Bool}
    (hc : Cmp (Input ι k) (Reply k) S F) :
    Cmp ι (Output k) ((k + 1) * S + k ^ 2 + 3 * k + 2) (wrap F) := by
  have h := Cmp.comp (Cmp.comp (Cmp.comp (base_cmp ι) (start_cmp hc)) (loop_cmp hc k)) (finish_cmp ι k)
  have hs : 2 + S + k * (S + k + 1) + (k + k) = (k + 1) * S + k ^ 2 + 3 * k + 2 := by ring
  rw [hs] at h
  exact h

private def agrees {k : ℕ} (q : ℕ) (p x : Bits k) : Prop := ∀ j, q ≤ j.val → x j = p j

private theorem agrees_put {k : ℕ} (i : Fin k) (p x : Bits k) (b : Bool) :
    agrees i.val (put p i b) x ↔ agrees (i.val + 1) p x ∧ x i = b := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, by simpa [put] using h i (Nat.le_refl _)⟩
    have hn : j ≠ i := fun he => by subst j; omega
    simpa [put, hn] using h j (by omega)
  · rintro ⟨ha, hi⟩ j hj
    by_cases he : j = i
    · subst j
      simpa [put] using hi
    · have hn : j.val ≠ i.val := fun h => he (Fin.ext h)
      simpa [put, he] using ha j (by omega)

private theorem probe_pos {ι : Type} {k : ℕ} {F : (Input ι k → Bool) → Reply k → Bool}
    {ok : (ι → Bool) → Bool} {hit : (ι → Bool) → Bits k → Prop} (hs : OracleSpec F ok hit)
    (d : ι → Bool) (hok : ok d = true) (v : State ι k → Bool)
    (hv : ∀ a, v (.inl a) = base d a) (i : Fin k) :
    positive (F (fun a => v (probeRoute i a))) = true ↔
      ∃ x, hit d x ∧ agrees (i.val + 1) (keys v) x ∧ x i = false := by
  let m : Bits k := fun j => decide (i.val ≤ j.val)
  let p := put (keys v) i false
  have hroute : (fun a => v (probeRoute i a)) = input d m p := by
    funext a
    rcases a with a | j | j
    · exact hv (.inl a)
    · exact hv (.inr (m j))
    · by_cases hj : j = i
      · simpa [probeRoute, input, p, put, hj, base] using hv (.inr false)
      · simp [probeRoute, input, p, put, keys, hj]
  let P := matched (hit d) m p
  have hbits : (fun s : Fin (k + 1) => F (input d m p) (.inr s)) =
      (fun s : Fin (k + 1) => (cardinal P).testBit s.val) := by
    funext s
    simpa only [if_pos hok] using (hs d m p).2 s
  rw [hroute, positive, hbits, someBit_nat (cardinal_bound P), cardinal_pos]
  apply exists_congr
  intro x
  have hm : matched (hit d) m p x ↔ hit d x ∧ agrees i.val p x := by
    simp only [matched, agrees, m, decide_eq_true_eq]
  change matched (hit d) m p x ↔ _
  rw [hm]
  change (hit d x ∧ agrees i.val (put (keys v) i false) x) ↔ _
  rw [agrees_put]

private theorem loop_spec {ι : Type} {k : ℕ} {F : (Input ι k → Bool) → Reply k → Bool}
    {ok : (ι → Bool) → Bool} {hit : (ι → Bool) → Bits k → Prop} (hs : OracleSpec F ok hit)
    (d : ι → Bool) (hok : ok d = true) : ∀ q ≤ k, ∀ v : State ι k → Bool,
    (∀ a, v (.inl a) = base d a) → (∃ w, hit d w ∧ agrees q (keys v) w) →
    let x := keys (loop F q v)
    hit d x ∧ agrees q (keys v) x ∧ ∀ y, hit d y → agrees q (keys v) y → code x ≤ code y := by
  intro q
  induction q with
  | zero =>
    rintro _ v _ ⟨w, hw, ha⟩
    have hEq : w = keys v := funext (fun j => ha j (Nat.zero_le _))
    subst w
    refine ⟨hw, fun _ _ => rfl, fun y _ hy => ?_⟩
    have hEq : y = keys v := funext (fun j => hy j (Nat.zero_le _))
    subst y
    exact le_rfl
  | succ q ih =>
    rintro hq v hv ⟨w, hw, haw⟩
    have hlt : q < k := by omega
    let i : Fin k := ⟨q, hlt⟩
    let t := positive (F (fun a => v (probeRoute i a)))
    let b := !t
    have ht : t = true ↔ ∃ z, hit d z ∧ agrees (q + 1) (keys v) z ∧ z i = false :=
      probe_pos hs d hok v hv i
    have chooseFalse : ∀ z, hit d z → agrees (q + 1) (keys v) z → z i = false → b = false := by
      intro z hz haz hzi
      change (!t) = false
      exact congrArg (fun a : Bool => !a) (ht.2 ⟨z, hz, haz, hzi⟩)
    let u := advance F i v
    have refinePrefix : ∀ z, agrees q (keys u) z ↔ agrees (q + 1) (keys v) z ∧ z i = b :=
      fun z => agrees_put i (keys v) z b
    have hnew : ∃ z, hit d z ∧ agrees q (keys u) z := by
      cases hb : t with
      | false =>
        have hwi : w i = true := by
          cases hwi : w i
          · have ht' := ht.2 ⟨w, hw, haw, hwi⟩
            rw [hb] at ht' <;> contradiction
          · rfl
        exact ⟨w, hw, (refinePrefix w).2 ⟨haw, by simpa [b, hb] using hwi⟩⟩
      | true =>
        obtain ⟨z, hz, haz, hzi⟩ := ht.1 hb
        exact ⟨z, hz, (refinePrefix z).2 ⟨haz, by simpa [b, hb] using hzi⟩⟩
    let x := keys (loop F q u)
    have hu : ∀ a, u (.inl a) = base d a := hv
    obtain ⟨hx, hax, hmin⟩ := ih (by omega) u hu hnew
    change agrees q (keys u) x at hax
    have hx' := (refinePrefix x).1 hax
    simp only [loop, dif_pos hlt]
    change hit d x ∧ agrees (q + 1) (keys v) x ∧ _
    refine ⟨hx, hx'.1, ?_⟩
    intro y hy hay
    by_cases hei : y i = b
    · exact hmin y hy ((refinePrefix y).2 ⟨hay, hei⟩)
    · have hyi : y i = true := by
        cases hyi : y i
        · exact False.elim (hei (hyi.trans (chooseFalse y hy hay hyi).symm))
        · rfl
      have hbi : b = false := by
        cases hb : b
        · rfl
        · exact False.elim (hei (hyi.trans hb.symm))
      exact Nat.le_of_lt (code_less i x y (hx'.2.trans hbi) hyi (fun j hj =>
        (hx'.1 j (by change q < j.val at hj; omega)).trans
          (hay j (by change q < j.val at hj; omega)).symm))

private theorem loop_reply {ι : Type} {k : ℕ} (F : (Input ι k → Bool) → Reply k → Bool)
    (q : ℕ) (v : State ι k → Bool) : reply (loop F q v) = reply v := by
  induction q generalizing v with
  | zero => rfl
  | succ q ih =>
    by_cases hq : q < k
    · rw [loop, dif_pos hq, ih] <;> rfl
    · rw [loop, dif_neg hq]

theorem wrap_spec {ι : Type} {k : ℕ} {F : (Input ι k → Bool) → Reply k → Bool}
    {ok : (ι → Bool) → Bool} {hit : (ι → Bool) → Bits k → Prop} (hs : OracleSpec F ok hit)
    (d : ι → Bool) :
    let out := wrap F d
    let cnt := cardinal (hit d)
    let x : Bits k := fun j => out (.inr j)
    out (.inl (.inl ())) = ok d ∧
    (∀ s : Fin (k + 1), out (.inl (.inr s)) = (if ok d then cnt else 0).testBit s.val) ∧
    (ok d = true → 0 < cnt → hit d x ∧ ∀ y, hit d y → code x ≤ code y) ∧
    ((ok d = false ∨ cnt = 0) → x = fun _ => false) := by
  let v := start F (base d)
  let u := loop F k v
  let cnt := cardinal (hit d)
  let z : Bits k := fun _ => false
  have hroute : (fun a : Input ι k => base d (emptyRoute a)) = input d z z := by
    funext a
    rcases a with a | j | j <;> rfl
  have hc : matched (hit d) z z = hit d := by
    funext x
    apply propext
    simp [matched, z]
  have hrv : reply v = F (input d z z) := by
    change F (fun a => base d (emptyRoute a)) = F (input d z z)
    rw [hroute]
  have hru : reply u = F (input d z z) := (loop_reply F k v).trans hrv
  have hb : (fun s : Fin (k + 1) => reply u (.inr s)) =
      (fun s : Fin (k + 1) => (if ok d then cnt else 0).testBit s.val) := by
    funext s
    rw [hru]
    simpa only [hc] using (hs d z z).2 s
  have hpos : positive (reply u) = true ↔ 0 < (if ok d then cnt else 0) := by
    rw [positive, hb]
    apply someBit_nat
    split
    · exact cardinal_bound (hit d)
    · positivity
  change reply u (.inl ()) = ok d ∧
    (∀ s : Fin (k + 1), reply u (.inr s) = (if ok d then cnt else 0).testBit s.val) ∧ _ ∧ _
  refine ⟨(congrFun hru (.inl ())).trans (hs d z z).1, congrFun hb, ?_, ?_⟩
  · intro hok hp
    have hactive : positive (reply u) = true := hpos.2 (by simpa only [if_pos hok] using hp)
    have vacuous : ∀ y, agrees k (keys v) y := fun _ j hj => by have := j.isLt; omega
    obtain ⟨w, hw⟩ := (cardinal_pos (hit d)).1 hp
    have hv : ∀ a, v (.inl a) = base d a := fun _ => rfl
    obtain ⟨hx, _, hmin⟩ := loop_spec hs d hok k (Nat.le_refl _) v hv ⟨w, hw, vacuous w⟩
    have he : (fun j => wrap F d (.inr j)) = keys u := by
      funext j
      change (positive (reply u) && keys u j) = keys u j
      simp [hactive]
    change hit d (fun j => wrap F d (.inr j)) ∧
      (∀ y, hit d y → code (fun j => wrap F d (.inr j)) ≤ code y)
    rw [he]
    exact ⟨hx, fun y hy => hmin y hy (vacuous y)⟩
  · intro hn
    have hzero : (if ok d then cnt else 0) = 0 := by
      rcases hn with h | h
      · simp [h]
      · change cnt = 0 at h
        simp [h]
    have hactive : positive (reply u) = false := by
      cases h : positive (reply u)
      · rfl
      · have hh := hpos.1 h
        omega
    funext j
    change (positive (reply u) && keys u j) = false
    simp [hactive]

end Greedy

namespace TreeSchedule

open Donor

abbrev State (D T : Type) (n : ℕ) := D ⊕ (Fin n × T)
abbrev Candidate (J : Type) (n : ℕ) := J ⊕ (Fin n × Fin n)

abbrev LeafFn (D J T : Type) := J → (D → Bool) → T → Bool
abbrev JoinFn (D T : Type) (n : ℕ) :=
  Fin n → Fin n → Fin n → (D ⊕ (T ⊕ T) → Bool) → T → Bool
abbrev GuardFn (D J : Type) (n : ℕ) := Fin n → Candidate J n → (D → Bool) → Bool

abbrev data {D T : Type} {n : ℕ} (s : State D T n → Bool) : D → Bool := s ∘ inl
abbrev table {D T : Type} {n : ℕ} (s : State D T n → Bool) (i : Fin n) : T → Bool :=
  fun t => s (.inr (i,t))

def joinInputs {D T : Type} {n : ℕ} (l h : Fin n) (s : State D T n → Bool) :
    D ⊕ (T ⊕ T) → Bool := elim (data s) (elim (table s l) (table s h))

def getCand {D J T : Type} {n : ℕ} (leaf : LeafFn D J T) (join : JoinFn D T n)
    (v : Fin n) (s : State D T n → Bool) (c : Candidate J n) : T → Bool :=
  c.elim (fun i => leaf i (data s)) (fun (l,h) => join v l h (joinInputs l h s))

def validCand {D J T : Type} {n : ℕ} (guard : GuardFn D J n) (v : Fin n)
    (s : State D T n → Bool) (c : Candidate J n) : Bool :=
  match c with
  | .inl _ => guard v c (data s)
  | .inr (l,h) => decide (l < v ∧ h < v) && guard v c (data s)

open Classical in
noncomputable def step {D J T : Type} {n : ℕ} (leaf : LeafFn D J T) (join : JoinFn D T n)
    (guard : GuardFn D J n) (v : Fin n) (s : State D T n → Bool) : State D T n → Bool :=
  fun o => match o with
  | .inl d => s (.inl d)
  | .inr (i,t) => if i = v then
      decide (∃ c, validCand guard v s c = true ∧ getCand leaf join v s c t = true)
    else table s i t

noncomputable def run {D J T : Type} {n : ℕ} (leaf : LeafFn D J T) (join : JoinFn D T n)
    (guard : GuardFn D J n) (x : D → Bool) : State D T n → Bool :=
  (List.finRange n).foldl (fun s i => step leaf join guard i s) (elim x (fun _ => false))

def stepCost (D J T : Type) [Fintype D] [Fintype J] [Fintype T] (n sTable sFlag : ℕ) : ℕ :=
  card (Candidate J n) * (sTable + sFlag + 2) +
    card (State D T n) * (2 * card (Candidate J n) + 1)

theorem decision_eq (p : Prop) (a b : Decidable p) : @decide p a = @decide p b :=
  congrArg (fun d => @decide p d) (Subsingleton.elim a b)

theorem step_cmp {D J T : Type} [Fintype D] [Fintype J] [Fintype T]
    {n sTable sFlag : ℕ} (leaf : LeafFn D J T) (join : JoinFn D T n)
    (guard : GuardFn D J n)
    (hLeaf : ∀ i, Cmp D T sTable (leaf i))
    (hJoin : ∀ i l h, Cmp (D ⊕ (T ⊕ T)) T sTable (join i l h))
    (hGuard : ∀ i c, Cb D sFlag (guard i c)) (v : Fin n) :
    Cmp (State D T n) (State D T n) (stepCost D J T n sTable sFlag) (step leaf join guard v) := by
  classical
  let C := Candidate J n
  let S := State D T n
  let stageA : (S → Bool) → Sum (C × T) (C × Unit) → Bool := fun s =>
    elim (fun ct => getCand leaf join v s ct.1 ct.2) (fun c => validCand guard v s c.1)
  have ha : Cmp S (C × T) (card C * sTable) (fun s p => getCand leaf join v s p.1 p.2) := by
    refine Cmp.piU (F := fun c s t => getCand leaf join v s c t) ?_
    rintro (i | ⟨l,h⟩)
    · exact Cmp.sel inl (hLeaf i)
    · refine Cmp.congr (Cmp.sel (elim inl (elim (fun t => .inr (l,t)) (fun t => .inr (h,t))))
        (hJoin v l h)) ?_
      intro s t
      change join v l h _ t = join v l h _ t
      congr 2
      funext j
      rcases j with d | u | u <;> rfl
  have hb : Cmp S (C × Unit) (card C * (sFlag + 2))
      (fun s p => validCand guard v s p.1) := by
    refine Cmp.piU (F := fun c s (_ : Unit) => validCand guard v s c) ?_
    intro p
    cases p with
    | inl i => exact (Cmp.sel inl (hGuard v (.inl i))).mono (by omega)
    | inr p =>
      rcases p with ⟨l,h⟩
      have hv : Cb S sFlag (fun s => guard v (.inr (l,h)) (data s)) :=
        Cmp.sel inl (hGuard v (.inr (l,h)))
      exact Cb.mono (Cb.and (Cb.const (decide (l < v ∧ h < v))) hv) (by omega)
  have hA : Cmp S (Sum (C × T) (C × Unit))
      (card C * (sTable + sFlag + 2)) stageA := by
    simpa [stageA, Nat.mul_add, Nat.add_assoc] using Cmp.pair ha hb
  let Z := S ⊕ Sum (C × T) (C × Unit)
  let stageB : (S ⊕ Sum (C × T) (C × Unit) → Bool) → S → Bool := fun z s =>
    match s with
    | .inl d => z (.inl (.inl d))
    | .inr (i,t) => if i = v then decide (∃ c : C, z (.inr (.inr (c, ()))) = true ∧
        z (.inr (.inl (c,t))) = true) else z (.inl (.inr (i,t)))
  have hB : Cmp (S ⊕ Sum (C × T) (C × Unit)) S
      (card S * (2 * card C + 1)) stageB := by
    apply Cmp.ofBits
    rintro (d | ⟨i,t⟩)
    · exact (Cb.var (ι := Z) (.inl (.inl d))).mono (Nat.zero_le _)
    · by_cases h : i = v
      · simpa [stageB, h, Bool.and_eq_true, Nat.mul_comm] using
          (Cb.bigOr (I := C) fun c => Cb.and (Cb.var (ι := Z) (.inr (.inr (c, ()))))
            (Cb.var (ι := Z) (.inr (.inl (c,t)))))
      · simpa only [stageB, ite_eq_right h] using
          (Cb.var (ι := S ⊕ Sum (C × T) (C × Unit)) (.inl (.inr (i,t)))).mono
            (Nat.zero_le (2 * card C + 1))
  have hF := Cmp.comp (Cmp.keep hA) hB
  refine Cmp.congr hF (fun z s => ?_)
  rcases s with d | ⟨i,t⟩
  · rfl
  · by_cases hi : i = v <;>
      simp only [step, stageA, stageB, table, elim_inl, elim_inr, hi, ite_true, ite_false]
    exact decision_eq _ _ _

theorem run_cmp {D J T : Type} [Fintype D] [Fintype J] [Fintype T]
    {n sTable sFlag : ℕ} (leaf : LeafFn D J T) (join : JoinFn D T n)
    (guard : GuardFn D J n)
    (hLeaf : ∀ i, Cmp D T sTable (leaf i))
    (hJoin : ∀ i l h, Cmp (D ⊕ (T ⊕ T)) T sTable (join i l h))
    (hGuard : ∀ i c, Cb D sFlag (guard i c)) :
    Cmp D (State D T n) (card (Fin n × T) + n * stepCost D J T n sTable sFlag)
      (run leaf join guard) := by
  have h0 : Cmp D (State D T n) (card (Fin n × T))
      (fun x => elim x (fun _ => false)) := by
    simpa using Cmp.pair (Cmp.wire (fun i : D => i))
      (Cmp.ofBits (κ := Fin n × T) fun _ => Cb.const (ι := D) false)
  have h1 := Cmp.foldl (List.finRange n) (step leaf join guard)
    (fun i _ => step_cmp leaf join guard hLeaf hJoin hGuard i)
  have h := Cmp.comp h0 h1
  rw [List.length_finRange] at h
  exact h

theorem run_sem {D J T : Type} {n : ℕ} (leaf : LeafFn D J T) (join : JoinFn D T n)
    (guard : GuardFn D J n) (x : D → Bool) (A : Fin n → T → Bool)
    (hAvail : ∀ v, ∃ c, validCand guard v (elim x (fun _ => false) : State D T n → Bool) c = true)
    (hLeaf : ∀ v i, guard v (.inl i) x = true → leaf i x = A v)
    (hJoin : ∀ v l h, l < v → h < v → guard v (.inr (l,h)) x = true →
      join v l h (elim x (elim (A l) (A h))) = A v) :
    ∀ v, table (run leaf join guard x) v = A v := by
  classical
  let S := State D T n
  let st (p : ℕ) : S → Bool := ((List.finRange n).take p).foldl
    (fun s i => step leaf join guard i s) (elim x (fun _ => false))
  have hrec : ∀ p ≤ n, data (st p) = x ∧ ∀ i : Fin n, i.val < p → table (st p) i = A i := by
    intro p
    induction p with
    | zero => exact fun _ => ⟨rfl, fun i hi => (Nat.not_lt_zero _ hi).elim⟩
    | succ p IH =>
      intro hp
      let v : Fin n := ⟨p, by omega⟩
      have h := IH (by omega)
      have hp' : p < (List.finRange n).length := by simp; omega
      have hv : (List.finRange n)[p] = v := by apply Fin.ext; simp [v]
      have hs : st (p+1) = step leaf join guard v (st p) := by
        simp only [st, List.take_succ_eq_append_getElem hp', hv, List.foldl_append, List.foldl_cons, List.foldl_nil]
      refine ⟨(show data (st (p+1)) = _ by rw [hs]; exact h.1), ?_⟩
      intro i hi
      by_cases e : i = v
      · subst i
        have hex : ∃ c, validCand guard v (st p) c = true := by
          obtain ⟨c,hc⟩ := hAvail v
          exact ⟨c, by cases c <;> simpa [validCand, h.1] using hc⟩
        have hgood : ∀ c, validCand guard v (st p) c = true → getCand leaf join v (st p) c = A v := by
          rintro (a | ⟨l,u⟩) hc
          · change leaf a (data (st p)) = A v
            rw [h.1]
            exact hLeaf v a (by simpa [validCand, h.1] using hc)
          · simp only [validCand, Bool.and_eq_true, decide_eq_true_eq, h.1] at hc
            have he : joinInputs l u (st p) = elim x (elim (A l) (A u)) := by
              simp [joinInputs, h.1, h.2 l hc.1.1, h.2 u hc.1.2]
            change join v l u (joinInputs l u (st p)) = A v
            rw [he]
            exact hJoin v l u hc.1.1 hc.1.2 hc.2
        funext t
        rw [hs]
        change (if v = v then decide (∃ c, validCand guard v (st p) c = true ∧
          getCand leaf join v (st p) c t = true) else table (st p) v t) = _
        rw [ite_eq_left rfl, Bool.eq_iff_iff, decide_eq_true_eq]
        exact ⟨fun ⟨c,hc,ht⟩ => congrFun (hgood c hc) t ▸ ht,
          fun ht => by obtain ⟨c,hc⟩ := hex; exact ⟨c,hc,congrFun (hgood c hc).symm t ▸ ht⟩⟩
      · have hi' : i.val < p := by
          have hn : i.val ≠ p := fun h => e (Fin.ext h)
          omega
        rw [hs]
        funext t
        simpa [table, step, e] using congrFun (h.2 i hi') t
  intro v
  have h := (hrec n le_rfl).2 v v.isLt
  have he : (List.finRange n).take n = List.finRange n := by simp
  simpa [run, st, he] using h

theorem run_data {D J T : Type} {n : ℕ} (leaf : LeafFn D J T) (join : JoinFn D T n)
    (guard : GuardFn D J n) (x : D → Bool) : data (run leaf join guard x) = x := by
  have h (l : List (Fin n)) (s : State D T n → Bool) :
      data (l.foldl (fun a i => step leaf join guard i a) s) = data s := by
    induction l generalizing s with
    | nil => rfl
    | cons i l ih => change data (l.foldl _ (step leaf join guard i s)) = data s; rw [ih]; rfl
  exact h _ _

end TreeSchedule

section Helpers

lemma selectedSpan_map {J V U : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup U] [Module F U] (T : V →ₗ[F] U) (rows : J → V) (bag : J → Bool) :
    (selectedSpan rows bag).map T = selectedSpan (fun j => T (rows j)) bag := by
  unfold selectedSpan
  rw [Submodule.map_span]
  congr 1
  ext u
  constructor
  · rintro ⟨v, ⟨j,hj,rfl⟩, rfl⟩
    exact ⟨j,hj,rfl⟩
  · rintro ⟨j,hj,rfl⟩
    exact ⟨rows j, ⟨j,hj,rfl⟩, rfl⟩

lemma width_map {J V U : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup U] [Module F U] (T : V →ₗ[F] U) (ht : Injective T)
    (rows : J → V) (bag : J → Bool) :
    finrank F (selectedSpan (fun j => T (rows j)) bag ⊓
      selectedSpan (fun j => T (rows j)) (fun j => !bag j) : Submodule F U) =
    finrank F (selectedSpan rows bag ⊓ selectedSpan rows (fun j => !bag j) : Submodule F V) := by
  let C : Submodule F V := selectedSpan rows bag ⊓ selectedSpan rows (fun j => !bag j)
  rw [← selectedSpan_map, ← selectedSpan_map, ← Submodule.map_inf T ht]
  exact (Submodule.equivMapOfInjective T ht C).finrank_eq.symm

def precompose {A B : Type*} (f : A → B) : (B → F) →ₗ[F] (A → F) where
  toFun g := g ∘ f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma precompose_injective {A B : Type*} (f : A → B) (hf : Surjective f) :
    Injective (precompose f) := by
  intro a b h
  funext y
  obtain ⟨x,rfl⟩ := hf y
  exact congrFun h x

def dotFunctions (A : Type*) [Fintype A] : (A → F) →ₗ[F] ((A → F) → F) where
  toFun a := dotProduct a
  map_add' _ _ := funext fun b => add_dotProduct _ _ _
  map_smul' c a := funext fun b => smul_dotProduct c a b

lemma dotFunctions_injective (A : Type*) [Fintype A] [DecidableEq A] :
    Injective (dotFunctions A) := by
  intro a b h
  funext i
  simpa [dotFunctions] using congrFun h (Pi.single i 1)

lemma width_coordinates {J A B : Type*} [Fintype A] [DecidableEq A]
    (f : J → B → F) (rows : J → A → F) (toDirection : (A → F) → B)
    (hsurj : Surjective toDirection)
    (hrepr : ∀ i v, f i (toDirection v) = dotProduct (rows i) v) (bag : J → Bool) :
    finrank F (selectedSpan rows bag ⊓ selectedSpan rows (fun j => !bag j) : Submodule F (A → F)) =
    finrank F (selectedSpan f bag ⊓ selectedSpan f (fun j => !bag j) : Submodule F (B → F)) := by
  have hc : (fun i => precompose toDirection (f i)) = fun i => dotFunctions A (rows i) := by
    funext i v
    exact hrepr i v
  rw [← width_map (precompose toDirection) (precompose_injective _ hsurj) f bag,
    hc, width_map (dotFunctions A) (dotFunctions_injective A) rows bag]

lemma selectedSpan_union {J V : Type*} [AddCommGroup V] [Module F V]
    (rows : J → V) (p q : J → Bool) :
    selectedSpan rows (fun j => p j || q j) = selectedSpan rows p ⊔ selectedSpan rows q := by
  unfold selectedSpan
  rw [← span_union]
  congr 1
  ext v
  constructor
  · rintro ⟨j,h,rfl⟩
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inl ⟨j,h,rfl⟩
    · exact Or.inr ⟨j,h,rfl⟩
  · rintro (⟨j,h,rfl⟩ | ⟨j,h,rfl⟩)
    · exact ⟨j, by simp [h], rfl⟩
    · exact ⟨j, by simp [h], rfl⟩

lemma restPartition {J : Type*} (L H : J → Bool) (hd : ∀ j, L j = true → H j = false) :
    (∀ j, (H j || !(L j || H j)) = !L j) ∧
    (∀ j, (L j || !(L j || H j)) = !H j) := by
  constructor <;> intro j <;> have hh := hd j <;> cases hL : L j <;> cases hH : H j <;> simp_all

lemma selectedSpan_ext {J V : Type*} [AddCommGroup V] [Module F V]
    {rows : J → V} {bag : J → Bool} {a b : Dual V}
    (h : ∀ j, bag j = true → a (rows j) = b (rows j)) :
    a.comp (selectedSpan rows bag).subtype = b.comp (selectedSpan rows bag).subtype := by
  have hl : selectedSpan rows bag ≤ LinearMap.ker (a - b) := by
    apply span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    change a (rows j) - b (rows j) = 0
    rw [h j hj, sub_self]
  apply LinearMap.ext
  intro v
  exact sub_eq_zero.mp (hl v.prop)

end Helpers

section Helpers

open Classical in
theorem countFiberProd {X Y A B : Type*} [Fintype X] [Fintype Y] [Finite A] [Finite B]
    (left : A → Prop) (right : B → Prop) (addrL : A → X) (addrR : B → Y)
    (compatible : X → Y → Prop) :
    Nat.card {p : A × B // left p.1 ∧ right p.2 ∧ compatible (addrL p.1) (addrR p.2)} =
      ∑ x : X, ∑ y : Y, if compatible x y then
        Nat.card {a : A // left a ∧ addrL a = x} * Nat.card {b : B // right b ∧ addrR b = y} else 0 := by
  let C := {p : A × B // left p.1 ∧ right p.2 ∧ compatible (addrL p.1) (addrR p.2)}
  let addr : C → X × Y := fun c => (addrL c.val.1, addrR c.val.2)
  change Nat.card C = _
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv addr), Nat.card_sigma, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  by_cases hv : compatible x y
  · rw [ite_eq_left hv, ← Nat.card_prod]
    apply Nat.card_congr
    refine
      { toFun := fun c =>
          ⟨⟨c.val.val.1, c.val.prop.1, congrArg Prod.fst c.prop⟩,
            ⟨c.val.val.2, c.val.prop.2.1, congrArg Prod.snd c.prop⟩⟩
        invFun := fun p =>
          ⟨⟨(p.1.val, p.2.val), p.1.prop.1, p.2.prop.1,
            by rw [p.1.prop.2, p.2.prop.2]; exact hv⟩, Prod.ext p.1.prop.2 p.2.prop.2⟩
        left_inv := fun c => Subtype.ext (Subtype.ext (Prod.eta _))
        right_inv := fun p => Prod.ext (Subtype.ext rfl) (Subtype.ext rfl) }
  · rw [ite_eq_right hv]
    haveI : IsEmpty {c : C // addr c = (x,y)} := ⟨fun c => hv (by
      have h1 : addrL c.val.val.1 = x := congrArg Prod.fst c.prop
      have h2 : addrR c.val.val.2 = y := congrArg Prod.snd c.prop
      exact (congrArg₂ compatible h1 h2) ▸ c.val.prop.2.2)⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

end Helpers

section Helpers

open Donor

abbrev WidthIn (J U : Type) := (J × U) ⊕ J
abbrev WidthOut (U : Type) (d : ℕ) := (U × Fin d) ⊕ Unit

def widthInRows {J U : Type} (x : WidthIn J U → Bool) : J → U → F := fun j u => b2z (x (.inl (j,u)))
def widthInMask {J U : Type} (x : WidthIn J U → Bool) : J → Bool := fun j => x (.inr j)

def widthOutGen {U : Type} {d : ℕ} (x : WidthOut U d → Bool) : Fin d → U → F :=
  fun t u => b2z (x (.inl (u,t)))

def widthPrepCost (J U : Type) [Fintype J] [Fintype U] (d : ℕ) : ℕ :=
  card (ProjIn (Bool × U) (Bool × J) U) * 4 +
  glCost (card (Bool × U)) (card (Bool × J)) (card U) (d+1) +
  card (WidthOut U d) * 2

theorem widthPrep {J U : Type} [Fintype J] [Fintype U] [DecidableEq U] (d : ℕ) :
    ∃ P : (WidthIn J U → Bool) → WidthOut U d → Bool,
      Cmp (WidthIn J U) (WidthOut U d) (widthPrepCost J U d) P ∧
      ∀ x : WidthIn J U → Bool,
        let K := selectedSpan (widthInRows x) (widthInMask x) ⊓
          selectedSpan (widthInRows x) (fun j => !(widthInMask x j))
        (P x (.inr ()) = true ↔ finrank F K ≤ d) ∧
        (P x (.inr ()) = true → span F (Set.range (widthOutGen (P x))) = K) := by
  classical
  let L := ProjIn (Bool × U) (Bool × J) U
  let O := SOut U (d+1)
  let A (x : WidthIn J U → Bool) : L → Bool := intersectSys (widthInRows x) (widthInMask x)
  have hA : Cmp (WidthIn J U) L (card L * 4) A := by
    apply Cmp.ofBits
    rintro ⟨⟨b,u⟩, (⟨b',j⟩ | v | ⟨⟩)⟩
    · have hb : Cb (WidthIn J U) 1 (fun x => x (.inr j) == b') := by
        cases b'
        · simpa using (Cb.not (Cb.var (ι := WidthIn J U) (.inr j)))
        · simpa using (Cb.var (ι := WidthIn J U) (.inr j)).mono (by decide : 0 ≤ 1)
      refine (Cb.and (Cb.and (Cb.const (b == b')) hb) (Cb.var (.inl (j,u)))).congr ?_
      intro x
      change (b == b' && x (.inr j) == b' && x (.inl (j,u))) =
        (b == b' && x (.inr j) == b' && zbit (b2z (x (.inl (j,u)))))
      rw [show zbit (b2z (x (.inl (j,u)))) = x (.inl (j,u)) from st_dec_b2z _]
    · exact (Cb.const (ι := WidthIn J U) (decide (u = v))).mono (by decide)
    · exact (Cb.const (ι := WidthIn J U) false).mono (by decide)
  obtain ⟨S, nf, hS, hs⟩ := glS (Bool × U) (Bool × J) U (d+1)
  let B (v : O → Bool) : WidthOut U d → Bool := elim
    (fun p => enabled v p.2.castSucc && v (.inl (p.1,p.2.castSucc)))
    (fun _ => !(enabled v (Fin.last d)))
  have hB : Cmp O (WidthOut U d) (card (WidthOut U d) * 2) B := by
    apply Cmp.ofBits
    rintro (⟨u,t⟩ | ⟨⟩)
    · exact (Cb.and (Cb.var (ι := O) (.inr (.inr (.inl t.castSucc))))
        (Cb.var (ι := O) (.inl (u,t.castSucc)))).mono (by decide)
    · exact (Cb.not (Cb.var (ι := O) (.inr (.inr (.inl (Fin.last d)))))).mono (by decide)
  refine ⟨fun x => B (S (A x)), Cmp.comp (Cmp.comp hA hS) hB, ?_⟩
  intro x K
  obtain ⟨hOK, hrank, hbasis⟩ := projected_submodule S nf hs (A x) K
    (intersectionSys_spec (widthInRows x) (widthInMask x))
  have hent := (hs (A x)).2 hOK
  have hflag : B (S (A x)) (.inr ()) = true ↔ nf (A x) ≤ d := by
    change (!(enabled (S (A x)) (Fin.last d))) = true ↔ _
    have hi := hent.2.1 (Fin.last d)
    change enabled (S (A x)) (Fin.last d) = true ↔ d < nf (A x) at hi
    cases h : enabled (S (A x)) (Fin.last d) <;> simp [h] at hi ⊢ <;> omega
  refine ⟨by rw [hrank]; exact hflag, ?_⟩
  intro hv
  have hcap := hflag.mp hv
  have hba := hbasis (hcap.trans (Nat.le_succ d))
  rw [← hba]
  have hz : column (S (A x)) (Fin.last d) = 0 := by
    have hf : enabled (S (A x)) (Fin.last d) = false := by
      change (!(enabled (S (A x)) (Fin.last d))) = true at hv
      cases h : enabled (S (A x)) (Fin.last d) <;> simp_all
    funext u
    simp [column, hf, b2z]
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact subset_span ⟨t.castSucc, rfl⟩
  · apply span_le.mpr
    rintro _ ⟨t,rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) t
    · rw [hz]
      exact Submodule.zero_mem _
    · exact subset_span ⟨j, rfl⟩

abbrev NullIn (J U : Type) := J × U
abbrev NullOut (J : Type) (d : ℕ) := J × Fin d

def nullDecoded {J U : Type} (x : NullIn J U → Bool) : J → U → F := fun j u => b2z (x (j,u))
def nullOutGen {J : Type} {d : ℕ} (x : NullOut J d → Bool) : Fin d → J → F :=
  fun t j => b2z (x (j,t))

def nullPrepCost (J U : Type) [Fintype J] [Fintype U] (d : ℕ) : ℕ :=
  card (ProjIn U Empty J) + glCost (card U) 0 (card J) d +
  card (NullOut J d)

theorem nullPrep {J U : Type} [Fintype J] [Fintype U] (d : ℕ) (hd : card J ≤ d) :
    ∃ P : (NullIn J U → Bool) → NullOut J d → Bool,
      Cmp (NullIn J U) (NullOut J d) (nullPrepCost J U d) P ∧
      ∀ x, span F (Set.range (nullOutGen (P x))) =
        LinearMap.ker (Fintype.linearCombination F (nullDecoded x)) := by
  classical
  let L := ProjIn U Empty J
  let A (x : NullIn J U → Bool) : L → Bool := system (fun u j => nullDecoded x j u) (fun _ => 0)
  have hA : Cmp (NullIn J U) L (card L) A := by
    rw [← Nat.mul_one (card L)]
    apply Cmp.ofBits
    rintro ⟨u, (b | j | ⟨⟩)⟩
    · exact b.elim
    · exact ((Cb.var (ι := NullIn J U) (j,u)).mono (by decide : 0 ≤ 1)).congr
        (fun x => (st_dec_b2z (x (j,u))).symm)
    · exact Cb.const false
  obtain ⟨S, nf, hS, hs⟩ := glS U Empty J d
  have hS' : Cmp L (SOut J d) (glCost (card U) 0 (card J) d) S := by simpa using hS
  let B (v : SOut J d → Bool) (it : NullOut J d) := enabled v it.2 && v (.inl it)
  have hB : Cmp (SOut J d) (NullOut J d) (card (NullOut J d)) B := by
    rw [← Nat.mul_one (card (NullOut J d))]
    apply Cmp.ofBits
    intro p
    exact Cb.and (Cb.var (ι := SOut J d) (.inr (.inr (.inl p.2))))
      (Cb.var (ι := SOut J d) (.inl p))
  refine ⟨fun x => B (S (A x)), Cmp.comp (Cmp.comp hA hS') hB, ?_⟩
  intro x
  let K := LinearMap.ker (Fintype.linearCombination F (nullDecoded x))
  obtain ⟨_, hr, hb⟩ := projected_submodule S nf hs (A x) K (null_iff (nullDecoded x))
  have hk : finrank F K ≤ d := (Submodule.finrank_le K).trans (by simpa using hd)
  exact hb (hr ▸ hk)

end Helpers

section Helpers

open Donor PackedTape

abbrev Raw (k r q n : ℕ) := InputSlot k r q n
abbrev FormIx (k r : ℕ) := Leaf k r × Fin 3
abbrev Param (k r : ℕ) := Fin (tapeSize k r)

variable {k r q n : ℕ}

def readName (v : Raw k r q n → Bool) : Bool → Word k := fun b j => b2z (v (nameSlot b j))
def readObs (v : Raw k r q n → Bool) : Fin q → Tape k r := fun i =>
  (fun j => b2z (v (obsKeySlot i j)), fun b t j => b2z (v (obsTapeSlot i b t j)))
def readRhs (v : Raw k r q n → Bool) : Fin q → F := fun i => b2z (v (rhsSlot i))
def readBag (v : Raw k r q n → Bool) : Fin n → Leaf k r → Bool := fun t j => v (bagSlot t j)
def readC (v : Raw k r q n → Bool) : Bool → Fin r → Word k := fun b t j => b2z (v (cSlot b t j))

lemma coord_card (k r : ℕ) : card (Coord k r) = tapeSize k r := by
  simp [Coord, tapeSize]
  ring

def latticeMap (hk : 0 < k) (obs : Fin q → Tape k r) :
    (Coord k r → F) →ₗ[F] (EqRow k q → F) :=
  LinearMap.pi fun i =>
    { toFun := dotProduct (row hk obs i)
      map_add' := fun u v => dotProduct_add _ _ _
      map_smul' := fun c u => dotProduct_smul c _ u }

abbrev TapeOut (k r : ℕ) := (Coord k r × (Param k r ⊕ Unit)) ⊕ Unit

def tapePrepGen (out : TapeOut k r → Bool) : Param k r → Coord k r → F :=
  fun t j => b2z (out (.inl (j, .inl t)))
def tapePrepPoint (out : TapeOut k r → Bool) : Coord k r → F :=
  fun j => b2z (out (.inl (j, .inr ())))

def tapePrepSysCost (k r q : ℕ) := card (ProjIn (EqRow k q) Empty (Coord k r))
def tapePrepCost (k r q : ℕ) : ℕ :=
  2 * (tapePrepSysCost k r q + glCost (card (EqRow k q)) 0 (tapeSize k r) (tapeSize k r)) +
    card (TapeOut k r)

lemma latticeSys_cmp (hk : 0 < k) (hom : Bool) :
    Cmp (Raw k r q n) (ProjIn (EqRow k q) Empty (Coord k r)) (tapePrepSysCost k r q)
      (fun v => system (row hk (readObs v)) (if hom then 0 else rowTarget (readName v) (readRhs v))) := by
  classical
  rw [tapePrepSysCost, ← Nat.mul_one (card (ProjIn (EqRow k q) Empty (Coord k r)))]
  apply Cmp.ofBits
  rintro ⟨i, (b | a | ⟨⟩)⟩
  · exact b.elim
  · rcases i with ⟨b,j⟩ | i
    · let c := zbit (row hk (fun _ : Fin q => 0) (.inl (b,j)) a)
      exact Cb.const (ι := Raw k r q n) c
    · rcases a with j | ⟨b,t,j⟩
      · refine ((Cb.var (ι := Raw k r q n) (obsKeySlot i j)).mono (by decide : 0 ≤ 1)).congr ?_
        intro x
        change x (obsKeySlot i j) = zbit (b2z (x (obsKeySlot i j)))
        exact (st_dec_b2z _).symm
      · refine ((Cb.var (ι := Raw k r q n) (obsTapeSlot i b t j)).mono (by decide : 0 ≤ 1)).congr ?_
        intro x
        change x (obsTapeSlot i b t j) = zbit (b2z (x (obsTapeSlot i b t j)))
        exact (st_dec_b2z _).symm
  · cases hom
    · rcases i with ⟨b,j⟩ | i
      · refine ((Cb.var (ι := Raw k r q n) (nameSlot b j)).mono (by decide : 0 ≤ 1)).congr ?_
        intro x
        change x (nameSlot b j) = zbit (b2z (x (nameSlot b j)))
        exact (st_dec_b2z _).symm
      · refine ((Cb.var (ι := Raw k r q n) (rhsSlot i)).mono (by decide : 0 ≤ 1)).congr ?_
        intro x
        change x (rhsSlot i) = zbit (b2z (x (rhsSlot i)))
        exact (st_dec_b2z _).symm
    · exact Cb.const false

set_option maxHeartbeats 1500000 in
theorem tapePrep (hk : 0 < k) :
    ∃ P : (Raw k r q n → Bool) → TapeOut k r → Bool,
      Cmp (Raw k r q n) (TapeOut k r) (tapePrepCost k r q) P ∧
      ∀ x,
        (P x (.inr ()) = true ↔ ∃ u, latticeMap hk (readObs x) u = rowTarget (readName x) (readRhs x)) ∧
        span F (Set.range (tapePrepGen (P x))) = LinearMap.ker (latticeMap hk (readObs x)) ∧
        (P x (.inr ()) = true →
          latticeMap hk (readObs x) (tapePrepPoint (P x)) = rowTarget (readName x) (readRhs x)) := by
  classical
  let D := Raw k r q n
  let M := card (EqRow k q)
  let N := tapeSize k r
  let I := ProjIn (EqRow k q) Empty (Coord k r)
  let O := SOut (Coord k r) N
  obtain ⟨S, nf, hS, hsem⟩ := glS (EqRow k q) Empty (Coord k r) N
  have hS' : Cmp I O (glCost M 0 N N) S := by
    simpa only [card_empty, coord_card] using hS
  let A (x : D → Bool) (b : Bool) : I → Bool :=
    system (row hk (readObs x)) (if b then 0 else rowTarget (readName x) (readRhs x))
  have hA (b : Bool) : Cmp D O (tapePrepSysCost k r q + glCost M 0 N N) (fun x => S (A x b)) :=
    Cmp.comp (latticeSys_cmp hk b) hS'
  let B (v : O ⊕ O → Bool) : TapeOut k r → Bool :=
    elim (fun (j, p) => elim
      (fun t => v (.inl (.inr (.inr (.inl t)))) && v (.inl (.inl (j,t))))
      (fun _ => v (.inr (.inr (.inl j)))) p)
      (fun _ => v (.inr (.inr (.inr (.inr ())))))
  have hB : Cmp (O ⊕ O) (TapeOut k r) (card (TapeOut k r)) B := by
    rw [← Nat.mul_one (card (TapeOut k r))]
    apply Cmp.ofBits
    rintro (⟨j, (t | ⟨⟩)⟩ | ⟨⟩)
    · exact Cb.and (Cb.var (ι := O ⊕ O) (.inl (.inr (.inr (.inl t)))))
        (Cb.var (ι := O ⊕ O) (.inl (.inl (j,t))))
    · exact (Cb.var (ι := O ⊕ O) (.inr (.inr (.inl j)))).mono (by decide)
    · exact (Cb.var (ι := O ⊕ O) (.inr (.inr (.inr (.inr ()))))).mono (by decide)
  let P (x : D → Bool) : TapeOut k r → Bool := B (elim (S (A x true)) (S (A x false)))
  have hP : Cmp D (TapeOut k r) (tapePrepCost k r q) P := by
    simpa [P, tapePrepCost, M, N, two_mul] using Cmp.comp (Cmp.pair (hA true) (hA false)) hB
  refine ⟨P,hP,?_⟩
  intro x
  let K := LinearMap.ker (latticeMap hk (readObs x))
  have hhom : ∀ z, solS (A x true) z ↔ z ∈ K := by
    intro z
    rw [show A x true = system (row hk (readObs x)) 0 from rfl, system_iff, LinearMap.mem_ker]
    exact ⟨fun h => funext h, fun h => congrFun h⟩
  obtain ⟨_, hdim, hg⟩ := projected_submodule S nf hsem _ K hhom
  have hwidth : finrank F K ≤ N := by
    simpa only [Module.finrank_fintype_fun_eq_card, coord_card] using Submodule.finrank_le K
  have hg' : span F (Set.range (tapePrepGen (P x))) = K := by
    exact hg (hdim ▸ hwidth)
  let b := rowTarget (readName x) (readRhs x)
  have haff (z : Coord k r → F) : solS (A x false) z ↔ latticeMap hk (readObs x) z = b := by
    rw [show A x false = system (row hk (readObs x)) b from rfl, system_iff]
    exact ⟨fun h => funext h, fun h => congrFun h⟩
  obtain ⟨hbad, hok⟩ := hsem (A x false)
  have hpoint (h : P x (.inr ()) = true) : latticeMap hk (readObs x) (tapePrepPoint (P x)) = b := by
    obtain ⟨hc, _, hp⟩ := hok h
    have hcard : Nat.card (Coord k r → F) = 2 ^ N := by
      rw [Nat.card_eq_fintype_card, card_fun, ZMod.card, coord_card]
    have hc' : Nat.card {z : Coord k r → F // solS (A x false) z} ≤ 2 ^ N := by
      rw [← hcard]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hn : nf (A x false) ≤ N := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
      rw [← hc]
      exact hc'
    have hh := (hp hn).1 0 (project_zero (S (A x false)))
    rw [project_point_zero] at hh
    exact (haff _).mp hh
  refine ⟨⟨fun h => ⟨_, hpoint h⟩, ?_⟩, hg', hpoint⟩
  rintro ⟨z,hz⟩
  cases h : P x (.inr ())
  · exact False.elim (hbad h _ ((haff _).mpr hz))
  · rfl

end Helpers

section Helpers

open Donor PackedTape

variable {k r q n : ℕ}

def mixSlots (hk : 0 < k) (b : Bool) (t : Fin (r+1)) (i : Fin k) : List (Coord k r) :=
  let gap := if b then 2 else 1
  [.inr (b,t,i), .inr (b,t,ix hk (i.val + gap)), .inr (b,t,ix hk (i.val + k - gap % k))]

def formSlots (hk : 0 < k) : FormIx k r → List (Coord k r)
  | (.inl j, _) => [.inl j]
  | (.inr (b,t,j),e) =>
    if e.val = 0 then mixSlots hk b t.castSucc (ix hk (j.val+1))
    else if e.val = 1 then mixSlots hk b t.castSucc (ix hk (j.val+2))
    else [.inr (b,t.succ,j)] ++ mixSlots hk b t.castSucc j ++
      [.inl (ix hk (j.val + k - feed b t.val % k))]

lemma formSlots_len (hk : 0 < k) (i : FormIx k r) : (formSlots hk i).length ≤ 5 := by
  rcases i with ⟨j | ⟨b,t,j⟩, e⟩
  · simp [formSlots]
  · by_cases h0 : e.val = 0 <;> by_cases h1 : e.val = 1 <;> simp [formSlots, mixSlots, h0,h1]

lemma flatten_symm_key (z : Coord k r → F) (j : Fin k) : (flatten.symm z).1 j = z (.inl j) := rfl

lemma flatten_symm_tape (z : Coord k r → F) (b : Bool) (t : Fin (r+1)) (j : Fin k) :
    (flatten.symm z).2 b t j = z (.inr (b,t,j)) := rfl

lemma formSlots_sum (hk : 0 < k) (i : FormIx k r) (z : Coord k r → F) :
    ((formSlots hk i).map z).sum = form hk i.1 i.2 (flatten.symm z) := by
  rcases i with ⟨j | ⟨b,t,j⟩, e⟩
  · simp [formSlots, form, flatten_symm_key]
  · by_cases h0 : e.val = 0
    · have he : e = 0 := Fin.ext h0
      simp [formSlots, mixSlots, form, mix, rot, flatten_symm_key, flatten_symm_tape, h0, he] <;> abel
    · have he : e ≠ 0 := fun h => h0 (congrArg Fin.val h)
      by_cases h1 : e.val = 1 <;>
        simp [formSlots, mixSlots, form, mix, rot, flatten_symm_key, flatten_symm_tape, h0, h1, he] <;> abel

lemma zbit_xor (x y : F) : zbit (x + y) = xor (zbit x) (zbit y) := by
  revert x y
  decide

lemma zbit_list {α : Type} (l : List α) (v : α → F) :
    zbit (l.map v).sum = l.foldr (fun i a => xor (zbit (v i)) a) false := by
  induction l with
  | nil => rfl
  | cons h l IH => simp only [List.map_cons, List.sum_cons, zbit_xor, IH, List.foldr_cons]

lemma formEvalCb {D : Type} (hk : 0 < k) (i : FormIx k r) (get : Coord k r → D) :
    Cb D 21 (fun x => zbit (form hk i.1 i.2 (flatten.symm (fun j => b2z (x (get j)))))) := by
  have h := fa_listXor (φ := fun j (x : D → Bool) => x (get j)) (fun j => Cb.var (get j)) (formSlots hk i)
  refine (h.mono (by have := formSlots_len hk i; omega)).congr ?_
  intro x
  rw [← formSlots_sum, zbit_list]
  simp only [zbit, st_dec_b2z]

abbrev FormData (k r : ℕ) := FormIx k r × (Param k r ⊕ Unit)

def linearRows (x : FormData k r → Bool) : FormIx k r → Param k r → F :=
  fun i t => b2z (x (i, .inl t))
def affineForms (x : FormData k r → Bool) : FormIx k r → F := fun i => b2z (x (i, .inr ()))

def evalForms (hk : 0 < k) (x : TapeOut k r → Bool) : FormData k r → Bool :=
  fun (i,p) => zbit (form hk i.1 i.2 (flatten.symm (fun j => b2z (x (.inl (j,p))))))

lemma evalFormsCmp (hk : 0 < k) :
    Cmp (TapeOut k r) (FormData k r) (card (FormData k r) * 21) (evalForms hk) := by
  apply Cmp.ofBits
  rintro ⟨i,p⟩
  exact formEvalCb (D := TapeOut k r) hk i (fun j => .inl (j,p))

lemma linearRows_eq (hk : 0 < k) (x : TapeOut k r → Bool) (i : FormIx k r) (t : Param k r) :
    linearRows (evalForms hk x) i t = form hk i.1 i.2 (flatten.symm (tapePrepGen x t)) :=
  zbit_decode _

lemma affineForms_eq (hk : 0 < k) (x : TapeOut k r → Bool) (i : FormIx k r) :
    affineForms (evalForms hk x) i = form hk i.1 i.2 (flatten.symm (tapePrepPoint x)) := zbit_decode _

lemma linearRows_eval (hk : 0 < k) (x : TapeOut k r → Bool) (i : FormIx k r)
    (a : Param k r → F) :
    dotProduct (linearRows (evalForms hk x) i) a =
      form hk i.1 i.2 (flatten.symm (Fintype.linearCombination F (tapePrepGen x) a)) := by
  let L : (Coord k r → F) →ₗ[F] F := (formLinear hk i.1 i.2).comp flatten.symm.toLinearMap
  change dotProduct (linearRows (evalForms hk x) i) a = L _
  rw [Fintype.linearCombination_apply, map_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  exact congrArg (fun b => a t * b) (linearRows_eq hk x i t)

end Helpers

namespace LayoutGuard

open Donor

variable {D J : Type} {n : ℕ}

abbrev mask (idx : Fin n × J → D) (x : D → Bool) (v : Fin n) (j : J) : Bool :=
  x (idx (v,j))

noncomputable def root (idx : Fin n × J → D) (v : Fin n) (x : D → Bool) : Bool := by
  classical
  exact decide (∀ j, mask idx x v j = true)

@[simp] theorem root_true (idx : Fin n × J → D) (v : Fin n) (x : D → Bool) :
    root idx v x = true ↔ ∀ j, mask idx x v j = true := by
  classical
  simp [root]

private def singleBit [DecidableEq J] (j one : J) (a : Bool) : Bool :=
  if j = one then a else !a

private theorem singleBit_true [DecidableEq J] (j one : J) (a : Bool) :
    singleBit j one a = true ↔ a = decide (j = one) := by
  by_cases h : j = one <;> cases a <;> simp [singleBit, h]

private def splitBit (a b c : Bool) : Bool := (!(a && b)) && !(xor c (a || b))

private theorem splitBit_true (a b c : Bool) :
    splitBit a b c = true ↔ (a = true → b = false) ∧ c = (a || b) := by
  cases a <;> cases b <;> cases c <;> decide

noncomputable def guard [DecidableEq J] (idx : Fin n × J → D) (v : Fin n)
    (c : TreeSchedule.Candidate J n) (x : D → Bool) : Bool := by
  classical
  exact match c with
    | .inl one => decide (∀ j, singleBit j one (mask idx x v j) = true)
    | .inr (l,h) => decide (∀ j, splitBit (mask idx x l j) (mask idx x h j) (mask idx x v j) = true)

@[simp] theorem guard_single_true [DecidableEq J] (idx : Fin n × J → D)
    (v : Fin n) (one : J) (x : D → Bool) :
    guard idx v (.inl one) x = true ↔ ∀ j, mask idx x v j = decide (j = one) := by
  classical
  simp only [guard, decide_eq_true_eq, singleBit_true]

@[simp] theorem guard_split_true [DecidableEq J] (idx : Fin n × J → D)
    (v l h : Fin n) (x : D → Bool) :
    guard idx v (.inr (l,h)) x = true ↔
      (∀ j, mask idx x l j = true → mask idx x h j = false) ∧
      ∀ j, mask idx x v j = (mask idx x l j || mask idx x h j) := by
  classical
  simp only [guard, decide_eq_true_eq, splitBit_true]
  exact ⟨fun q => ⟨fun j => (q j).1, fun j => (q j).2⟩, fun q j => ⟨q.1 j, q.2 j⟩⟩

noncomputable def valid [DecidableEq J] (idx : Fin n × J → D) (v : Fin n)
    (c : TreeSchedule.Candidate J n) (x : D → Bool) : Bool :=
  match c with
  | .inl _ => guard idx v c x
  | .inr (l,h) => decide (l < v ∧ h < v) && guard idx v c x

theorem valid_schedule [DecidableEq J] {T : Type} (idx : Fin n × J → D)
    (v : Fin n) (c : TreeSchedule.Candidate J n) (s : TreeSchedule.State D T n → Bool) :
    valid idx v c (TreeSchedule.data s) = TreeSchedule.validCand (guard idx) v s c := by
  rcases c with i | ⟨l,h⟩ <;> rfl

noncomputable def hasRoot (idx : Fin n × J → D) (x : D → Bool) : Bool := by
  classical
  exact decide (∃ v, root idx v x = true)

@[simp] theorem hasRoot_true (idx : Fin n × J → D) (x : D → Bool) :
    hasRoot idx x = true ↔ ∃ v : Fin n, ∀ j, mask idx x v j = true := by
  classical
  simp only [hasRoot, decide_eq_true_eq, root_true]

noncomputable def node [DecidableEq J] (idx : Fin n × J → D) (v : Fin n) (x : D → Bool) : Bool := by
  classical
  exact decide (∃ c, valid idx v c x = true)

noncomputable def layout [DecidableEq J] (idx : Fin n × J → D) (x : D → Bool) : Bool := by
  classical
  exact hasRoot idx x && decide (∀ v, node idx v x = true)

theorem node_true [DecidableEq J] (idx : Fin n × J → D) (v : Fin n) (x : D → Bool) :
    node idx v x = true ↔
      (∃ one : J, ∀ j, mask idx x v j = decide (j = one)) ∨
      ∃ l h : Fin n, l < v ∧ h < v ∧ (∀ j, mask idx x l j = true → mask idx x h j = false) ∧
        ∀ j, mask idx x v j = (mask idx x l j || mask idx x h j) := by
  classical
  simp only [node, decide_eq_true_eq]
  constructor
  · rintro ⟨one | ⟨l,h⟩, hc⟩
    · exact Or.inl ⟨one, (guard_single_true idx v one x).mp hc⟩
    · simp only [valid, Bool.and_eq_true, decide_eq_true_eq, guard_split_true] at hc
      exact Or.inr ⟨l, h, hc.1.1, hc.1.2, hc.2.1, hc.2.2⟩
  · rintro (⟨one, hone⟩ | ⟨l,h,hl,hh,hd,hu⟩)
    · exact ⟨.inl one, (guard_single_true idx v one x).mpr hone⟩
    · refine ⟨.inr (l,h), ?_⟩
      simp only [valid, Bool.and_eq_true, decide_eq_true_eq, guard_split_true]
      exact ⟨⟨hl,hh⟩,⟨hd,hu⟩⟩

theorem layout_true [DecidableEq J] (idx : Fin n × J → D) (x : D → Bool) :
    layout idx x = true ↔
      (∃ v : Fin n, ∀ j, mask idx x v j = true) ∧
      ∀ v : Fin n, (∃ one : J, ∀ j, mask idx x v j = decide (j = one)) ∨
        ∃ l h : Fin n, l < v ∧ h < v ∧ (∀ j, mask idx x l j = true → mask idx x h j = false) ∧
          ∀ j, mask idx x v j = (mask idx x l j || mask idx x h j) := by
  classical
  simp only [layout, hasRoot, Bool.and_eq_true, decide_eq_true_eq, root_true, node_true]

theorem layout_available [DecidableEq J] (idx : Fin n × J → D) (x : D → Bool)
    (h : layout idx x = true) {T : Type} (s : TreeSchedule.State D T n → Bool)
    (hs : TreeSchedule.data s = x) (v : Fin n) :
    ∃ c, TreeSchedule.validCand (guard idx) v s c = true := by
  classical
  simp only [layout, Bool.and_eq_true, decide_eq_true_eq] at h
  have hv := h.2 v
  simp only [node, decide_eq_true_eq] at hv
  obtain ⟨c,hc⟩ := hv
  exact ⟨c, by rw [← valid_schedule, hs]; exact hc⟩

def rootCost (J : Type) [Fintype J] : ℕ := card J + 1

def guardCost (J : Type) [Fintype J] : ℕ := card J * 10 + 1

def hasRootCost (J : Type) [Fintype J] (n : ℕ) : ℕ := n * (rootCost J + 1) + 1

def nodeCost (J : Type) [Fintype J] (n : ℕ) : ℕ :=
  (card J + n * n) * (guardCost J + 1) + 1

def layoutCost (J : Type) [Fintype J] (n : ℕ) : ℕ :=
  hasRootCost J n + (n * (nodeCost J n + 1) + 1) + 1

theorem root_cb [Fintype J] (idx : Fin n × J → D) (v : Fin n) :
    Cb D (rootCost J) (root idx v) := by
  have h := (Cb.bigAnd (fun j : J => Cb.var (idx (v,j)))).congr
    (φ' := root idx v) (fun x => by
      rw [Bool.eq_iff_iff]
      simp only [decide_eq_true_eq, root_true, mask])
  simpa only [rootCost, Nat.zero_add, Nat.mul_one] using h

theorem guard_cb [Fintype J] [DecidableEq J] (idx : Fin n × J → D) (v : Fin n)
    (c : TreeSchedule.Candidate J n) : Cb D (guardCost J) (guard idx v c) := by
  classical
  rcases c with one | ⟨l,h⟩
  · have hb (j : J) : Cb D 9 (fun x => singleBit j one (mask idx x v j)) := by
      by_cases hj : j = one
      · simpa [singleBit, hj] using (Cb.var (idx (v,j))).mono (by decide : 0 ≤ 9)
      · simpa [singleBit, hj] using (Cb.not (Cb.var (idx (v,j)))).mono (by decide : 1 ≤ 9)
    exact (Cb.bigAnd hb).congr (fun x => by simp [guard])
  · have hb (j : J) : Cb D 9 (fun x =>
        splitBit (mask idx x l j) (mask idx x h j) (mask idx x v j)) := by
      exact Cb.and (Cb.not (Cb.and (Cb.var (idx (l,j))) (Cb.var (idx (h,j)))))
        (Cb.not (Cb.xor (Cb.var (idx (v,j))) (Cb.or (Cb.var (idx (l,j))) (Cb.var (idx (h,j))))))
    exact (Cb.bigAnd hb).congr (fun x => by simp [guard])

theorem hasRoot_cb [Fintype J] (idx : Fin n × J → D) :
    Cb D (hasRootCost J n) (hasRoot idx) := by
  have h := (Cb.bigOr (root_cb idx)).congr (φ' := hasRoot idx) (fun x => by
    rw [Bool.eq_iff_iff]
    simp only [hasRoot, decide_eq_true_eq])
  simpa only [hasRootCost, card_fin] using h

theorem valid_cb [Fintype J] [DecidableEq J] (idx : Fin n × J → D) (v : Fin n)
    (c : TreeSchedule.Candidate J n) : Cb D (guardCost J) (valid idx v c) := by
  rcases c with one | ⟨l,h⟩
  · exact guard_cb idx v (.inl one)
  · by_cases hp : l < v ∧ h < v
    · exact (guard_cb idx v (.inr (l,h))).congr (fun x => by simp [valid, hp])
    · exact ((Cb.const (ι := D) false).mono
        (Nat.succ_le_succ (Nat.zero_le (card J * 10)))).congr
        (fun x => by simp [valid, hp])

theorem node_cb [Fintype J] [DecidableEq J] (idx : Fin n × J → D) (v : Fin n) :
    Cb D (nodeCost J n) (node idx v) := by
  have h := (Cb.bigOr (valid_cb idx v)).congr (φ' := node idx v) (fun x => by
    rw [Bool.eq_iff_iff]
    simp only [node, decide_eq_true_eq])
  simpa only [nodeCost, TreeSchedule.Candidate, card_sum, card_prod, card_fin] using h

theorem layout_cb [Fintype J] [DecidableEq J] (idx : Fin n × J → D) :
    Cb D (layoutCost J n) (layout idx) := by
  have h := (Cb.and (hasRoot_cb idx) (Cb.bigAnd (node_cb idx))).congr (φ' := layout idx)
    (fun x => by
      rw [Bool.eq_iff_iff]
      simp only [layout, Bool.and_eq_true, decide_eq_true_eq])
  simpa only [layoutCost, card_fin] using h

/-- Read one common result from all roots; no priority choice is needed. -/
noncomputable def readRoots {T : Type} (idx : Fin n × J → D)
    (s : TreeSchedule.State D T n → Bool) (t : T) : Bool := by
  classical
  exact decide (∃ v, (root idx v (TreeSchedule.data s) && TreeSchedule.table s v t) = true)

end LayoutGuard

namespace LeafTable

open Donor

abbrev Input (m d : ℕ) := (Fin m × Fin (d+3)) ⊕ (Fin 3 ⊕ (Unit ⊕ (Unit ⊕ Unit)))

namespace Input

abbrev coeff {m d : ℕ} (i : Fin m) (j : Fin (d+3)) : Input m d := .inl (i,j)
abbrev offset {m d : ℕ} (j : Fin 3) : Input m d := .inr (.inl j)
abbrev mask {m d : ℕ} : Input m d := .inr (.inr (.inl ()))
abbrev prefixBit {m d : ℕ} : Input m d := .inr (.inr (.inr (.inl ())))
abbrev rhs {m d : ℕ} : Input m d := .inr (.inr (.inr (.inr ())))

end Input

abbrev Forms := Fin 3 → Bool

/-- First the little-endian address, then the three unshifted form values. -/
def coordBit {d : ℕ} (a : Fin (2 ^ d)) (u : Forms) (j : Fin (d + 3)) : Bool :=
  if j.val < d then a.val.testBit j.val else u ⟨j.val - d, by have := j.isLt; omega⟩

def coord {d : ℕ} (a : Fin (2 ^ d)) (u : Forms) (j : Fin (d + 3)) : ZMod 2 :=
  b2z (coordBit a u j)

@[simp] theorem coord_address {d : ℕ} (a : Fin (2 ^ d)) (u : Forms) (j : Fin d) :
    coord a u ⟨j.val, by have := j.isLt; omega⟩ = vecN d a.val j := by
  simp [coord, coordBit, j.isLt, b2z, vecN]
@[simp] theorem coord_form {d : ℕ} (a : Fin (2 ^ d)) (u : Forms) (e : Fin 3) :
    coord a u ⟨d + e.val, by have := e.isLt; omega⟩ = b2z (u e) := by
  have hh : ¬ d + e.val < d := by omega
  have he : d + e.val - d = e.val := by omega
  simp [coord, coordBit, b2z, hh, he]

def value {m d : ℕ} (x : Input m d → Bool) (u : Forms) (e : Fin 3) : ZMod 2 :=
  b2z (u e) + b2z (x (Input.offset e))

def valid {m d : ℕ} (gate : Bool) (x : Input m d → Bool) (a : Fin (2 ^ d)) (u : Forms) : Prop :=
  (∀ i : Fin m, (∑ j : Fin (d + 3), coord a u j * b2z (x (Input.coeff i j))) = 0) ∧
  (if gate then value x u 2 = (1 + value x u 0) * value x u 1 + b2z (x Input.rhs)
    else x Input.mask = true → value x u 0 = b2z (x Input.prefixBit))

noncomputable def count {m d : ℕ} (gate : Bool) (x : Input m d → Bool) (a : Fin (2 ^ d)) : ℕ := by
  classical
  exact (Finset.univ.filter (valid gate x a)).card

private theorem b2z_xor : ∀ a b : Bool, b2z (xor a b) = b2z a + b2z b := by decide

private theorem raw_correct : ∀ m p a : Bool,
    (!m || !(xor a p)) = true ↔ (m = true → b2z a = b2z p) := by decide

private theorem gate_correct : ∀ a b c r : Bool,
    (!(xor c (xor (!a && b) r))) = true ↔ b2z c = (1 + b2z a) * b2z b + b2z r := by decide

private def affBit {m d : ℕ} (x : Input m d → Bool) (u : Forms) (e : Fin 3) : Bool :=
  xor (u e) (x (Input.offset e))

private theorem aff_correct {m d : ℕ} (x : Input m d → Bool) (u : Forms) (e : Fin 3) :
    b2z (affBit x u e) = value x u e := b2z_xor _ _

private def localOK {m d : ℕ} (gate : Bool) (x : Input m d → Bool) (u : Forms) : Bool :=
  if gate then !(xor (affBit x u 2) (xor (!(affBit x u 0) && affBit x u 1) (x Input.rhs)))
  else !(x Input.mask) || !(xor (affBit x u 0) (x Input.prefixBit))

private theorem localOK_correct {m d : ℕ} (gate : Bool) (x : Input m d → Bool) (u : Forms) :
    localOK gate x u = true ↔
      (if gate then value x u 2 = (1 + value x u 0) * value x u 1 + b2z (x Input.rhs)
        else x Input.mask = true → value x u 0 = b2z (x Input.prefixBit)) := by
  cases gate
  · simpa [localOK, aff_correct] using raw_correct (x Input.mask) (x Input.prefixBit) (affBit x u 0)
  · simpa [localOK, aff_correct] using gate_correct (affBit x u 0) (affBit x u 1)
      (affBit x u 2) (x Input.rhs)

private theorem affC {m d : ℕ} (u : Forms) (e : Fin 3) :
    Cb (Input m d) 5 (fun x => affBit x u e) :=
  Cb.xor (Cb.const (u e)) (Cb.var (Input.offset (m := m) (d := d) e))

private theorem localC {m d : ℕ} (gate : Bool) (u : Forms) :
    Cb (Input m d) 32 (fun x => localOK gate x u) := by
  cases gate
  · exact Cb.mono (Cb.or (Cb.not (Cb.var (Input.mask (m := m) (d := d))))
      (Cb.not (Cb.xor (affC u 0) (Cb.var (Input.prefixBit (m := m) (d := d)))))) (by decide)
  · exact Cb.mono (Cb.not (Cb.xor (affC u 2)
      (Cb.xor (Cb.and (Cb.not (affC u 0)) (affC u 1))
        (Cb.var (Input.rhs (m := m) (d := d)))))) (by decide)

private theorem rowC {m d : ℕ} (a : Fin (2 ^ d)) (u : Forms) (i : Fin m) :
    Cb (Input m d) (5 * (d + 3) + 2)
      (fun x => decide ((∑ j : Fin (d + 3), coord a u j * b2z (x (Input.coeff i j))) = 0)) := by
  classical
  let term := fun (j : Fin (d + 3)) (x : Input m d → Bool) =>
    decide (coord a u j ≠ 0) && x (Input.coeff i j)
  have ht (j : Fin (d + 3)) : Cb (Input m d) 1 (term j) := by
    by_cases hj : coord a u j ≠ 0
    · simpa [term, hj] using (Cb.mono (Cb.var (Input.coeff i j)) (show 0 ≤ 1 by decide))
    · have hz : coord a u j = 0 := by simpa only [not_ne_iff] using hj
      simpa [term, hz] using (Cb.const (ι := Input m d) false)
  have hc := Cb.not (Cb.bigXor ht)
  simp only [card_fin] at hc
  refine Cb.congr (Cb.mono hc (by omega)) (fun x => ?_)
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
  simpa [term, b2z] using
    (not_congr (fz2_zsum (d + 3) (coord a u) (fun j => x (Input.coeff i j)))).symm

private noncomputable def accept {m d : ℕ} (gate : Bool) (a : Fin (2 ^ d)) (x : Input m d → Bool)
    (u : Forms) : Bool := by
  classical
  exact (decide (∀ i : Fin m, (∑ j : Fin (d + 3), coord a u j * b2z (x (Input.coeff i j))) = 0)) &&
  localOK gate x u

private theorem accept_correct {m d : ℕ} (gate : Bool) (a : Fin (2 ^ d))
    (x : Input m d → Bool) (u : Forms) : accept gate a x u = true ↔ valid gate x a u := by
  simp only [accept, Bool.and_eq_true, decide_eq_true_eq, localOK_correct, valid]

private theorem acceptC {m d : ℕ} (gate : Bool) (a : Fin (2 ^ d)) (u : Forms) :
    Cb (Input m d) (m * (5 * (d + 3) + 3) + 34) (fun x => accept gate a x u) := by
  have h := Cb.bigAnd (rowC a u (m := m))
  simp only [card_fin] at h
  refine Cb.congr (Cb.mono (Cb.and h (localC gate u)) (by
    change m * (5 * (d + 3) + 3) + 1 + 32 + 1 ≤ _
    omega)) (fun x => ?_)
  rw [Bool.eq_iff_iff]
  simp only [accept, Bool.and_eq_true, decide_eq_true_eq]

private noncomputable def pop (v : Forms → Bool) : ℕ :=
  (Finset.univ.filter (fun u => v u = true)).card

private theorem forms_card : card Forms = 8 := by
  simp [Forms]

private noncomputable def samePattern (v p : Forms → Bool) : Bool := by
  classical
  exact decide (v = p)

private theorem patternC (p : Forms → Bool) :
    Cb Forms 17 (fun v => samePattern v p) := by
  have h (u : Forms) : Cb Forms 1 (fun v => if p u then v u else !v u) := by
    cases hp : p u
    · simpa [hp] using Cb.not (Cb.var u)
    · simpa [hp] using Cb.mono (Cb.var u) (show 0 ≤ 1 by decide)
  have h' := Cb.bigAnd h
  rw [forms_card] at h'
  refine Cb.congr h' (fun v => ?_)
  rw [Bool.eq_iff_iff]
  simp only [samePattern, decide_eq_true_eq]
  constructor
  · intro hv
    funext u
    specialize hv u
    cases hp : p u <;> cases hb : v u <;> simp_all
  · rintro rfl u
    cases v u <;> rfl

private theorem popC (t : ℕ) :
    Cmp Forms (Fin t) (5121 * t) (fun v j => (pop v).testBit j.val) := by
  have h (j : Fin t) : Cb Forms 5121 (fun v => (pop v).testBit j.val) := by
    classical
    have hp (p : Forms → Bool) := Cb.and (patternC p)
      (Cb.const (ι := Forms) ((pop p).testBit j.val))
    have hb := Cb.bigOr hp
    have hc : card (Forms → Bool) = 256 := by
      rw [card_fun, forms_card, card_bool]
      decide
    rw [hc] at hb
    refine Cb.congr hb (fun v => ?_)
    rw [Bool.eq_iff_iff]
    simp only [samePattern, decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨p, rfl, hp⟩
      exact hp
    · intro hv
      exact ⟨v, rfl, hv⟩
  simpa only [card_fin, Nat.mul_comm t 5121] using Cmp.ofBits h

private theorem count_eq_pop {m d : ℕ} (gate : Bool) (a : Fin (2 ^ d)) (x : Input m d → Bool) :
    count gate x a = pop (accept gate a x) := by
  classical
  unfold count pop
  apply congrArg Finset.card
  ext u
  simp only [Finset.mem_filter, mem_univ, true_and, accept_correct]

def budget (m d t : ℕ) : ℕ :=
  2 ^ d * (8 * (m * (5 * (d + 3) + 3) + 34) + 5121 * t)

theorem tableC (m d t : ℕ) (gate : Bool) :
    Cmp (Input m d) (Fin (2 ^ d) × Fin t) (budget m d t)
      (fun x p => (count gate x p.1).testBit p.2.val) := by
  have h (a : Fin (2 ^ d)) :
      Cmp (Input m d) (Fin t) (8 * (m * (5 * (d + 3) + 3) + 34) + 5121 * t)
        (fun x j => (count gate x a).testBit j.val) := by
    have ha := Cmp.ofBits (acceptC gate a (m := m))
    rw [forms_card] at ha
    refine Cmp.congr (Cmp.comp ha (popC t)) (fun x j => ?_)
    rw [count_eq_pop]
  simpa only [budget, card_fin] using Cmp.piU h

/-- The same specification with the three unshifted values in the original field. -/
def fieldCoord {d : ℕ} (a : Fin (2 ^ d)) (u : Fin 3 → ZMod 2)
    (j : Fin (d + 3)) : ZMod 2 :=
  if hj : j.val < d then vecN d a.val ⟨j.val, hj⟩
  else u ⟨j.val - d, by have := j.isLt; omega⟩

def fieldValid {m d : ℕ} (gate : Bool) (x : Input m d → Bool) (a : Fin (2 ^ d))
    (u : Fin 3 → ZMod 2) : Prop :=
  let v := fun e => u e + b2z (x (Input.offset e))
  (∀ i : Fin m, (∑ j : Fin (d + 3), fieldCoord a u j * b2z (x (Input.coeff i j))) = 0) ∧
  (if gate then v 2 = (1 + v 0) * v 1 + b2z (x Input.rhs)
    else x Input.mask = true → v 0 = b2z (x Input.prefixBit))

private theorem coord_fieldCoord {d : ℕ} (a : Fin (2 ^ d)) (u : Forms) (j : Fin (d + 3)) :
    coord a u j = fieldCoord a (fun e => b2z (u e)) j := by
  by_cases hj : j.val < d <;> simp [coord, coordBit, fieldCoord, b2z, vecN, hj]

theorem valid_iff_fieldValid {m d : ℕ} (gate : Bool) (x : Input m d → Bool)
    (a : Fin (2 ^ d)) (u : Forms) :
    valid gate x a u ↔ fieldValid gate x a (fun e => b2z (u e)) := by
  simp only [valid, fieldValid, coord_fieldCoord, value]

private theorem decode_encode : ∀ b : Bool, decide (b2z b ≠ 0) = b := by decide

private theorem encode_decode : ∀ z : ZMod 2, b2z (decide (z ≠ 0)) = z := by decide

theorem count_eq_fieldCard {m d : ℕ} (gate : Bool) (x : Input m d → Bool) (a : Fin (2 ^ d)) :
    count gate x a = Nat.card {u : Fin 3 → ZMod 2 // fieldValid gate x a u} := by
  classical
  have e : {u : Forms // valid gate x a u} ≃ {u : Fin 3 → ZMod 2 // fieldValid gate x a u} :=
    { toFun := fun u => ⟨_, (valid_iff_fieldValid gate x a u.val).mp u.property⟩
      invFun := fun u => ⟨fun i => decide (u.val i ≠ 0),
        (valid_iff_fieldValid gate x a _).mpr (by simpa only [encode_decode] using u.property)⟩
      left_inv := fun u => Subtype.ext (funext fun i => decode_encode (u.val i))
      right_inv := fun u => Subtype.ext (funext fun i => encode_decode (u.val i)) }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, card_subtype]
  unfold count
  apply congrArg Finset.card
  ext u
  simp

theorem fieldTableC (m d t : ℕ) (gate : Bool) :
    Cmp (Input m d) (Fin (2 ^ d) × Fin t) (budget m d t)
      (fun x p => (Nat.card {u : Fin 3 → ZMod 2 // fieldValid gate x p.1 u}).testBit p.2.val) := by
  refine Cmp.congr (tableC m d t gate) (fun x p => ?_)
  rw [count_eq_fieldCard]

end LeafTable

section Helpers

abbrev Predicates (J : Type*) := J → (Fin 3 → F) → Prop

def FormSpan {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (p : J → Bool) : Submodule F V := selectedSpan R (fun i => p i.1)

def CutSpan {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (p : J → Bool) : Submodule F V := FormSpan R p ⊓ FormSpan R (fun j => !p j)

lemma row_mem {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (p : J → Bool) {j : J} (hj : p j = true) (e : Fin 3) :
    R (j,e) ∈ FormSpan R p := subset_span ⟨(j,e), hj, rfl⟩

def localGood {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (P : Predicates J) (p : J → Bool) (f : Dual (FormSpan R p)) : Prop :=
  ∀ j (hj : p j = true), P j (fun e => f ⟨R (j,e), row_mem R p hj e⟩)

lemma localGood_extension {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (P : Predicates J) (p : J → Bool) (v : Dual V) :
    localGood R P p (v.comp (FormSpan R p).subtype) ↔ ∀ j, p j = true → P j (fun e => v (R (j,e))) :=
  Iff.rfl

def genMembers {ι V : Type*} [AddCommGroup V] [Module F V]
    (S : Submodule F V) (A : ι → V) (hA : span F (Set.range A) = S) (i : ι) : S :=
  ⟨A i, hA ▸ subset_span ⟨i,rfl⟩⟩

lemma genMembers_span {ι V : Type*} [AddCommGroup V] [Module F V]
    (S : Submodule F V) (A : ι → V) (hA : span F (Set.range A) = S) :
    span F (Set.range (genMembers S A hA)) = ⊤ := by
  let T := span F (Set.range (genMembers S A hA))
  have hmap : T.map S.subtype = S := by
    rw [show T = span F (Set.range (genMembers S A hA)) from rfl, Submodule.map_span, ← Set.range_comp]
    exact hA
  ext a
  constructor
  · intro _; trivial
  · intro _
    have ha : (a : V) ∈ T.map S.subtype := hmap.symm ▸ a.prop
    obtain ⟨b,hb,he⟩ := ha
    exact (S.injective_subtype he) ▸ hb

def genValue {ι V : Type*} [AddCommGroup V] [Module F V]
    {S : Submodule F V} {A : ι → V} (hA : span F (Set.range A) = S)
    (f : Dual S) : ι → F := fun i => f (genMembers S A hA i)

lemma genValue_injective {ι V : Type*} [AddCommGroup V] [Module F V]
    {S : Submodule F V} {A : ι → V} (hA : span F (Set.range A) = S) :
    Injective (genValue hA) := by
  intro f g h
  exact LinearMap.ext_on_range (genMembers_span S A hA) fun i => congrFun h i

def address {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (p : J → Bool) {d : ℕ} (A : Fin d → V)
    (hA : span F (Set.range A) = CutSpan R p) (f : Dual (FormSpan R p)) : Fin d → F :=
  genValue hA (restr inf_le_left f)

noncomputable def tableCount {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (P : Predicates J) (p : J → Bool) {d : ℕ} (A : Fin d → V)
    (hA : span F (Set.range A) = CutSpan R p) (addr : Fin d → F) : ℕ :=
  Nat.card {f : Dual (FormSpan R p) // localGood R P p f ∧ address R p A hA f = addr}

lemma address_extension {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (p : J → Bool) {d : ℕ} (A : Fin d → V)
    (hA : span F (Set.range A) = CutSpan R p) (f : Dual V) :
    address R p A hA (f.comp (FormSpan R p).subtype) = fun i => f (A i) := rfl

lemma leaf_span {J V : Type*} [DecidableEq J] [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (j : J) :
    span F (Set.range fun e => R (j,e)) = FormSpan R (fun a => decide (a = j)) := by
  unfold FormSpan selectedSpan
  congr 1
  ext x
  constructor
  · rintro ⟨e,rfl⟩
    exact ⟨(j,e), by simp, rfl⟩
  · rintro ⟨⟨a,e⟩,ha,rfl⟩
    have he : a = j := of_decide_eq_true ha
    subst a
    exact ⟨e,rfl⟩

theorem leaf_tableCount {J V : Type*} [DecidableEq J] [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (P : Predicates J) (j : J) {d : ℕ} (A : Fin d → V)
    (hA : span F (Set.range A) = CutSpan R (fun a => decide (a = j)))
    (x : Fin d → F) :
    tableCount R P (fun a => decide (a = j)) A hA x = Nat.card {y : Fin 3 → F // P j y ∧
      ∃ u : Dual V, (∀ t, u (A t) = x t) ∧ ∀ e, u (R (j,e)) = y e} := by
  let b : J → Bool := fun a => decide (a = j)
  let S := FormSpan R b
  let m : Dual S → (Fin 3 → F) := genValue (leaf_span R j)
  have hm : Injective m := genValue_injective _
  apply Nat.card_congr
  let mp (f : {f : Dual S // localGood R P b f ∧ address R b A hA f = x}) :
      {y : Fin 3 → F // P j y ∧ ∃ u : Dual V, (∀ t, u (A t) = x t) ∧ ∀ e, u (R (j,e)) = y e} := by
    refine ⟨m f.val, f.prop.1 j (by simp [b]), ?_⟩
    obtain ⟨u,hu⟩ := LinearMap.dualMap_surjective_of_injective S.injective_subtype f.val
    change u.comp S.subtype = f.val at hu
    refine ⟨u, ?_, ?_⟩
    · intro t
      have h := congrFun f.prop.2 t
      rw [← hu, address_extension] at h
      exact h
    · intro e
      rw [← hu]
      rfl
  refine Equiv.ofBijective mp ⟨?_,?_⟩
  · intro a b hab
    exact Subtype.ext (hm (congrArg Subtype.val hab))
  · intro y
    obtain ⟨u,hux,huy⟩ := y.prop.2
    let f := u.comp S.subtype
    have hg : localGood R P b f := by
      intro a ha
      have h : a = j := of_decide_eq_true ha
      subst a
      simpa only [f, LinearMap.comp_apply, Submodule.subtype_apply, huy] using y.prop.1
    have hx : address R b A hA f = x := funext hux
    refine ⟨⟨f,hg,hx⟩, Subtype.ext ?_⟩
    exact funext huy

def TripleRelation {ι κ τ V : Type*} [AddCommGroup V] [Module F V]
    (A : ι → V) (B : κ → V) (C : τ → V) (x : ι → F) (y : κ → F) (z : τ → F) : Prop :=
  ∃ u : Dual V, (∀ i, u (A i) = x i) ∧ (∀ i, u (B i) = y i) ∧ ∀ i, u (C i) = z i

noncomputable def splitAddressEquiv {ι κ τ V : Type*} [AddCommGroup V] [Module F V]
    (L H E : Submodule F V) (A : ι → V) (B : κ → V) (C : τ → V)
    (hA : span F (Set.range A) = LeftBoundary L H E)
    (hB : span F (Set.range B) = RightBoundary L H E)
    (hC : span F (Set.range C) = ParentBoundary L H E)
    (left : Dual L → Prop) (right : Dual H → Prop) (z : τ → F) :
    {u : Dual ↥(L ⊔ H) // left (restr le_sup_left u) ∧ right (restr le_sup_right u) ∧
      genValue hC (restr inf_le_left u) = z} ≃
    {p : Dual L × Dual H // left p.1 ∧ right p.2 ∧ TripleRelation A B C
      (genValue hA (restr inf_le_left p.1)) (genValue hB (restr inf_le_left p.2)) z} := by
  let X := {u : Dual ↥(L ⊔ H) // left (restr le_sup_left u) ∧ right (restr le_sup_right u) ∧
    genValue hC (restr inf_le_left u) = z}
  let Y := {p : Dual L × Dual H // left p.1 ∧ right p.2 ∧ TripleRelation A B C
    (genValue hA (restr inf_le_left p.1)) (genValue hB (restr inf_le_left p.2)) z}
  let f (u : X) : Y := by
    refine ⟨(restr le_sup_left u.val, restr le_sup_right u.val), u.prop.1, u.prop.2.1, ?_⟩
    let p := restr (S := ParentBoundary L H E) inf_le_left u.val
    have hx : ∃! v : Dual ↥(L ⊔ H), restr le_sup_left v = restr le_sup_left u.val ∧
        restr le_sup_right v = restr le_sup_right u.val ∧ restr inf_le_left v = p :=
      ⟨u.val, ⟨rfl,rfl,rfl⟩, fun _ h => restr_sup_injective h.1 h.2.1⟩
    obtain ⟨v, h1, h2, h3⟩ := (split_glue L H E _ _ p).mpr hx
    refine ⟨v, ?_, ?_, ?_⟩
    · intro i
      exact LinearMap.congr_fun h1 (genMembers _ _ hA i)
    · intro i
      exact LinearMap.congr_fun h2 (genMembers _ _ hB i)
    · intro i
      exact (LinearMap.congr_fun h3 (genMembers _ _ hC i)).trans (congrFun u.prop.2.2 i)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro u v h
    have he := congrArg Subtype.val h
    exact Subtype.ext (restr_sup_injective (congrArg Prod.fst he) (congrArg Prod.snd he))
  · intro q
    obtain ⟨v,hA',hB',hC'⟩ := q.prop.2.2
    let p := v.comp (ParentBoundary L H E).subtype
    have ha : v.comp (LeftBoundary L H E).subtype = restr inf_le_left q.val.1 :=
      genValue_injective hA (funext hA')
    have hb : v.comp (RightBoundary L H E).subtype = restr inf_le_left q.val.2 :=
      genValue_injective hB (funext hB')
    obtain ⟨u,hu,_⟩ := (split_glue L H E q.val.1 q.val.2 p).mp ⟨v,ha,hb,rfl⟩
    have hp : genValue hC (restr inf_le_left u) = z :=
      (congrArg (genValue hC) hu.2.2).trans (funext hC')
    exact ⟨⟨u, hu.1.symm ▸ q.prop.1, hu.2.1.symm ▸ q.prop.2.1, hp⟩,
      Subtype.ext (Prod.ext hu.1 hu.2.1)⟩

open Classical in
theorem splitAddress_count {ι κ τ V : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    [AddCommGroup V] [Module F V] [Finite V]
    (L H E : Submodule F V) (A : ι → V) (B : κ → V) (C : τ → V)
    (hA : span F (Set.range A) = LeftBoundary L H E)
    (hB : span F (Set.range B) = RightBoundary L H E)
    (hC : span F (Set.range C) = ParentBoundary L H E)
    (left : Dual L → Prop) (right : Dual H → Prop) (z : τ → F) :
    Nat.card {u : Dual ↥(L ⊔ H) // left (restr le_sup_left u) ∧ right (restr le_sup_right u) ∧
      genValue hC (restr inf_le_left u) = z} =
    ∑ x : ι → F, ∑ y : κ → F, if TripleRelation A B C x y z then
      Nat.card {u : Dual L // left u ∧ genValue hA (restr inf_le_left u) = x} *
      Nat.card {u : Dual H // right u ∧ genValue hB (restr inf_le_left u) = y}
      else 0 := by
  haveI : Finite (Dual L) := Finite.of_injective (fun u : Dual L => (u : L → F)) DFunLike.coe_injective
  haveI : Finite (Dual H) := Finite.of_injective (fun u : Dual H => (u : H → F)) DFunLike.coe_injective
  exact (Nat.card_congr (splitAddressEquiv L H E A B C hA hB hC left right z)).trans
    (countFiberProd left right (fun u => genValue hA (restr inf_le_left u))
      (fun u => genValue hB (restr inf_le_left u)) (fun x y => TripleRelation A B C x y z))

lemma formSpan_union {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (l h : J → Bool) :
    FormSpan R (fun j => l j || h j) = FormSpan R l ⊔ FormSpan R h :=
  selectedSpan_union R _ _

def dualCast {V : Type*} [AddCommGroup V] [Module F V]
    {S T : Submodule F V} (h : S = T) : Dual S ≃ Dual T :=
  Equiv.cast (congrArg (fun C : Submodule F V => Dual C) h)

lemma dualCast_restrict {V : Type*} [AddCommGroup V] [Module F V]
    {S T : Submodule F V} (h : S = T) (u : Dual V) :
    dualCast h (u.comp S.subtype) = u.comp T.subtype := by
  subst T
  rfl

lemma formSpan_union_good {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (P : Predicates J) (l h : J → Bool)
    (u : Dual V) :
    localGood R P (fun j => l j || h j) (u.comp (FormSpan R (fun j => l j || h j)).subtype) ↔
      localGood R P l (u.comp (FormSpan R l).subtype) ∧
      localGood R P h (u.comp (FormSpan R h).subtype) := by
  repeat rw [localGood_extension]
  constructor
  · intro g
    exact ⟨fun j hj => g j (by simp [hj]), fun j hj => g j (by simp [hj])⟩
  · rintro ⟨hl,hh⟩ j hj
    rw [Bool.or_eq_true] at hj
    exact hj.elim (hl j) (hh j)

open Classical in
theorem splitTableCount {J V : Type*} [AddCommGroup V] [Module F V] [Finite V]
    (R : J × Fin 3 → V) (P : Predicates J) (l h : J → Bool)
    (disj : ∀ j, l j = true → h j = false) {d : ℕ} (A B C : Fin d → V)
    (hA : span F (Set.range A) = CutSpan R l)
    (hB : span F (Set.range B) = CutSpan R h)
    (hC : span F (Set.range C) = CutSpan R (fun j => l j || h j)) (z : Fin d → F) :
    tableCount R P (fun j => l j || h j) C hC z =
      ∑ x : Fin d → F, ∑ y : Fin d → F, if TripleRelation A B C x y z then
        tableCount R P l A hA x * tableCount R P h B hB y else 0 := by
  let p := fun j => l j || h j
  let L := FormSpan R l
  let H := FormSpan R h
  let E := FormSpan R (fun j => !p j)
  have hh := restPartition l h disj
  have hLA : CutSpan R l = LeftBoundary L H E := by
    unfold CutSpan LeftBoundary L H E
    rw [← formSpan_union, show (fun j => h j || !p j) = (fun j => !l j) from funext hh.1]
  have hHB : CutSpan R h = RightBoundary L H E := by
    unfold CutSpan RightBoundary L H E
    rw [← formSpan_union, show (fun j => l j || !p j) = (fun j => !h j) from funext hh.2]
  have hP : FormSpan R p = L ⊔ H := formSpan_union R l h
  have hPC : CutSpan R p = ParentBoundary L H E := by
    unfold CutSpan ParentBoundary
    rw [hP]
  let hAA := hA.trans hLA
  let hBB := hB.trans hHB
  let hCC := hC.trans hPC
  have hl (f : Dual L) : address R l A hA f = genValue hAA (restr inf_le_left f) := by
    funext i
    rfl
  have hr (f : Dual H) : address R h B hB f = genValue hBB (restr inf_le_left f) := by
    funext i
    rfl
  have heq : tableCount R P p C hC z =
      Nat.card {u : Dual ↥(L ⊔ H) // localGood R P l (restr le_sup_left u) ∧ localGood R P h (restr le_sup_right u) ∧
        genValue hCC (restr inf_le_left u) = z} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquiv (dualCast hP)
    intro f
    obtain ⟨u,hu⟩ := LinearMap.dualMap_surjective_of_injective (FormSpan R p).injective_subtype f
    change u.comp (FormSpan R p).subtype = f at hu
    rw [← hu, dualCast_restrict, address_extension]
    have hc' : genValue hCC (restr inf_le_left (u.comp (L ⊔ H).subtype)) = fun i => u (C i) := rfl
    rw [hc']
    change (localGood R P p (u.comp (FormSpan R p).subtype) ∧ _) ↔
      (localGood R P l (u.comp L.subtype) ∧ localGood R P h (u.comp H.subtype) ∧ _)
    rw [formSpan_union_good]
    exact and_assoc
  rw [heq, splitAddress_count L H E A B C hAA hBB hCC (localGood R P l) (localGood R P h)]
  simp only [tableCount]
  apply sum_congr
  · exact congrArg (fun i => @Finset.univ (Fin d → F) i) (Subsingleton.elim _ _)
  intro x _
  apply sum_congr
  · exact congrArg (fun i => @Finset.univ (Fin d → F) i) (Subsingleton.elim _ _)
  intro y _
  by_cases hz : TripleRelation A B C x y z
  · simp only [hz, if_true]
    apply congrArg₂ Nat.mul <;> apply Nat.card_congr <;> apply Equiv.subtypeEquivRight
    · intro f
      exact and_congr_right' ((congrArg (· = x) (hl f)).symm.to_iff)
    · intro f
      exact and_congr_right' ((congrArg (· = y) (hr f)).symm.to_iff)
  · simp only [hz, if_false]

end Helpers

section Helpers

open Donor PackedTape

variable {k r q n : ℕ}

abbrev In (k r q n : ℕ) := Greedy.Input (Raw k r q n) k
abbrev PreMid (k r q n : ℕ) := In k r q n ⊕ (Unit ⊕ FormData k r)
abbrev BasisIx (k r n : ℕ) := Fin n ⊕ Leaf k r
abbrev Pre (k r q n d : ℕ) := PreMid k r q n ⊕ (BasisIx k r n × WidthOut (Param k r) d)

def preIn {d : ℕ} (x : Pre k r q n d → Bool) : In k r q n → Bool := x ∘ inl ∘ inl
def preRaw {d : ℕ} (x : Pre k r q n d → Bool) : Raw k r q n → Bool := preIn x ∘ inl
def preForms {d : ℕ} (x : Pre k r q n d → Bool) : FormData k r → Bool :=
  fun i => x (.inl (.inr (.inr i)))
def preAffine {d : ℕ} (x : Pre k r q n d → Bool) : Bool := x (.inl (.inr (.inl ())))
def preBasis {d : ℕ} (x : Pre k r q n d → Bool) (p : BasisIx k r n) : WidthOut (Param k r) d → Bool :=
  fun j => x (.inr (p,j))
def preBagIx [DecidableEq (Leaf k r)] (x : Raw k r q n → Bool) (i : BasisIx k r n) : Leaf k r → Bool :=
  i.elim (readBag x) (fun j a => decide (a = j))

def preWidth {d : ℕ} (x : Pre k r q n d → Bool) (p : BasisIx k r n) : Bool := preBasis x p (.inr ())
def preGen {d : ℕ} (x : Pre k r q n d → Bool) (p : BasisIx k r n) : Fin d → Param k r → F :=
  widthOutGen (preBasis x p)

def basisInput [DecidableEq (Leaf k r)] (i : BasisIx k r n) (x : PreMid k r q n → Bool) :
    WidthIn (FormIx k r) (Param k r) → Bool :=
  elim (fun (j,t) => x (.inr (.inr (j, .inl t))))
    (fun j => preBagIx (fun a => x (.inl (.inl a))) i j.1)

lemma basisInput_cmp [DecidableEq (Leaf k r)] (i : BasisIx k r n) :
    Cmp (PreMid k r q n) (WidthIn (FormIx k r) (Param k r))
      (card (WidthIn (FormIx k r) (Param k r))) (basisInput i) := by
  rw [← Nat.mul_one (card (WidthIn (FormIx k r) (Param k r)))]
  apply Cmp.ofBits
  rintro (⟨j,t⟩ | j)
  · exact (Cb.var (ι := PreMid k r q n) (.inr (.inr (j, .inl t)))).mono (by decide)
  · cases i with
    | inl u => exact (Cb.var (ι := PreMid k r q n) (.inl (.inl (bagSlot u j.1)))).mono (by decide)
    | inr u => exact Cb.const (decide (j.1 = u))

def preCost (k r q n d : ℕ) : ℕ :=
  tapePrepCost k r q + (card (FormData k r) * 21) +
  card (BasisIx k r n) *
    (card (WidthIn (FormIx k r) (Param k r)) + widthPrepCost (FormIx k r) (Param k r) d)

set_option maxHeartbeats 1000000 in
theorem preprocess [DecidableEq (Leaf k r)] [DecidableEq (Param k r)] (hk : 0 < k) (d : ℕ) :
    ∃ T : (In k r q n → Bool) → Pre k r q n d → Bool,
      Cmp (In k r q n) (Pre k r q n d) (preCost k r q n d) T ∧
      ∃ S : (Raw k r q n → Bool) → TapeOut k r → Bool,
      (∀ x,
        (S x (.inr ()) = true ↔ ∃ u, latticeMap hk (readObs x) u = rowTarget (readName x) (readRhs x)) ∧
        span F (Set.range (tapePrepGen (S x))) = LinearMap.ker (latticeMap hk (readObs x)) ∧
        (S x (.inr ()) = true →
          latticeMap hk (readObs x) (tapePrepPoint (S x)) = rowTarget (readName x) (readRhs x))) ∧
        ∀ x : In k r q n → Bool,
          preIn (T x) = x ∧ preAffine (T x) = S (x ∘ inl) (.inr ()) ∧
          preForms (T x) = evalForms hk (S (x ∘ inl)) ∧
          (∀ p,
            (preWidth (T x) p = true ↔ finrank F
              (CutSpan (linearRows (preForms (T x))) (preBagIx (preRaw (T x)) p)) ≤ d) ∧
            (preWidth (T x) p = true → span F (Set.range (preGen (T x) p)) =
              CutSpan (linearRows (preForms (T x))) (preBagIx (preRaw (T x)) p))) ∧
          ∀ v j, (∀ a, readBag (preRaw (T x)) v a = decide (a = j)) →
            preBasis (T x) (.inl v) = preBasis (T x) (.inr j) := by
  classical
  obtain ⟨S,hS,hSsem⟩ := tapePrep (k:=k) (r:=r) (q:=q) (n:=n) hk
  obtain ⟨B,hB,hBsem⟩ := widthPrep (J:=FormIx k r) (U:=Param k r) d
  let A (x : In k r q n → Bool) : PreMid k r q n → Bool :=
    elim x (elim (fun _ => S (x ∘ inl) (.inr ())) (evalForms hk (S (x ∘ inl))))
  have hextra : Cmp (TapeOut k r) (Unit ⊕ FormData k r) (card (FormData k r) * 21)
      (fun v => elim (fun _ => v (.inr ())) (evalForms hk v)) := by
    have h := Cmp.pair (Cmp.wire (fun _ : Unit => (inr () : TapeOut k r))) (evalFormsCmp (r:=r) hk)
    simpa only [Nat.zero_add] using h
  have hA : Cmp (In k r q n) (PreMid k r q n) (tapePrepCost k r q + card (FormData k r) * 21) A :=
    Cmp.keep (Cmp.comp (Cmp.sel inl hS) hextra)
  let T (x : In k r q n → Bool) : Pre k r q n d → Bool :=
    elim (A x) (fun (i,j) => B (basisInput i (A x)) j)
  have hT : Cmp (In k r q n) (Pre k r q n d) (preCost k r q n d) T := by
    have hb := Cmp.piU (F := fun (i : BasisIx k r n) (data : PreMid k r q n → Bool) => B (basisInput i data))
      (fun i => Cmp.comp (basisInput_cmp i) hB)
    exact Cmp.comp hA (Cmp.keep hb)
  refine ⟨T,hT,S,hSsem,?_⟩
  intro x
  refine ⟨rfl,rfl,rfl, ?_, ?_⟩
  · intro p
    exact hBsem (basisInput p (A x))
  · intro v j h
    have hEq : basisInput (.inl v) (A x) = basisInput (.inr j) (A x) := by
      funext u
      rcases u with ⟨i,t⟩ | i
      · rfl
      · exact h i.1
    change B (basisInput (.inl v) (A x)) = B (basisInput (.inr j) (A x))
    rw [hEq]

end Helpers

section Helpers

open Donor

variable {k r q : ℕ}

abbrev Direction (hk : 0 < k) (obs : Fin q → Tape k r) :=
  {z : Tape k r // (∀ b, z.2 b 0 = rot hk (start b) z.1) ∧ ∀ i, pair (obs i) z = 0}

def paramMap (o : TapeOut k r → Bool) : (Param k r → F) →ₗ[F] (Coord k r → F) :=
  Fintype.linearCombination F (tapePrepGen o)

lemma paramMap_range (hk : 0 < k) (obs : Fin q → Tape k r) (o : TapeOut k r → Bool)
    (h : span F (Set.range (tapePrepGen o)) = LinearMap.ker (latticeMap hk obs)) :
    LinearMap.range (paramMap o) = LinearMap.ker (latticeMap hk obs) := by
  rw [paramMap, Fintype.range_linearCombination, h]

lemma direction_iff (hk : 0 < k) (obs : Fin q → Tape k r) (z : Tape k r) :
    ((∀ b, z.2 b 0 = rot hk (start b) z.1) ∧ ∀ i, pair (obs i) z = 0) ↔
      latticeMap hk obs (flatten z) = 0 := by
  rw [← LinearMap.mem_ker]
  change _ ↔ latticeMap hk obs (flatten z) = 0
  have hz : (rowTarget (fun _ => 0) (fun _ => 0) : EqRow k q → F) = 0 := by
    funext u
    cases u <;> rfl
  rw [← hz]
  have he := (rowEquations hk (fun _ => 0) obs (fun _ => 0) z).symm.trans
    (show _ ↔ latticeMap hk obs (flatten z) = rowTarget (fun _ => 0) (fun _ : Fin q => 0) from
      ⟨fun h => funext h, fun h => congrFun h⟩)
  simpa only [Pi.zero_apply, add_zero] using he

def paramDirection (hk : 0 < k) (obs : Fin q → Tape k r) (o : TapeOut k r → Bool)
    (h : span F (Set.range (tapePrepGen o)) = LinearMap.ker (latticeMap hk obs))
    (a : Param k r → F) : Direction hk obs :=
  ⟨flatten.symm (paramMap o a), (direction_iff hk obs _).mpr (by
    rw [LinearEquiv.apply_symm_apply]
    have hx : paramMap o a ∈ LinearMap.range (paramMap o) := ⟨a,rfl⟩
    rw [paramMap_range hk obs o h] at hx
    exact hx)⟩

lemma paramDirection_surj (hk : 0 < k) (obs : Fin q → Tape k r) (o : TapeOut k r → Bool)
    (h : span F (Set.range (tapePrepGen o)) = LinearMap.ker (latticeMap hk obs)) :
    Surjective (paramDirection hk obs o h) := by
  intro z
  have hz : flatten z.val ∈ LinearMap.ker (latticeMap hk obs) := (direction_iff hk obs z.val).mp z.prop
  rw [← paramMap_range hk obs o h] at hz
  obtain ⟨a,ha⟩ := hz
  refine ⟨a, Subtype.ext ?_⟩
  change flatten.symm (paramMap o a) = z.val
  rw [ha, LinearEquiv.symm_apply_apply]

lemma post_width_eq (hk : 0 < k) (obs : Fin q → Tape k r) (o : TapeOut k r → Bool)
    (h : span F (Set.range (tapePrepGen o)) = LinearMap.ker (latticeMap hk obs))
    (p : Leaf k r → Bool) :
    finrank F (CutSpan (linearRows (evalForms hk o)) p) =
      let D := Direction hk obs
      let sp := fun bag => span F {f : D → F |
        ∃ (j : Leaf k r) (e : Fin 3), bag j = true ∧ f = fun z => form hk j e z.val}
      finrank F (sp p ⊓ sp (fun j => !p j) : Submodule F (D → F)) := by
  classical
  let f : FormIx k r → Direction hk obs → F := fun i z => form hk i.1 i.2 z.val
  let A := paramDirection hk obs o h
  have hrepr (i : FormIx k r) (a : Param k r → F) :
      f i (A a) = dotProduct (linearRows (evalForms hk o) i) a := (linearRows_eval hk o i a).symm
  have hwidth := width_coordinates f (linearRows (evalForms hk o)) A
    (paramDirection_surj hk obs o h) hrepr (fun i => p i.1)
  refine hwidth.trans ?_
  have hsp (b : Leaf k r → Bool) :
      selectedSpan f (fun i => b i.1) =
        span F {u : Direction hk obs → F | ∃ (j : Leaf k r) (e : Fin 3),
          b j = true ∧ u = fun z => form hk j e z.val} := by
    unfold selectedSpan
    apply congrArg (span F)
    ext u
    constructor
    · rintro ⟨⟨j,e⟩,h1,h2⟩
      exact ⟨j,e,h1,h2⟩
    · rintro ⟨j,e,h1,h2⟩
      exact ⟨(j,e),h1,h2⟩
  rw [hsp p, hsp (fun j => !p j)]

def gatePred (o : FormData k r → Bool) (c : Bool → Fin r → Word k) (pref : Fin k → Option F) :
    Predicates (Leaf k r) := fun j u =>
  let v := fun e => affineForms o (j,e) + u e
  match j with
  | .inl j => ∀ x, pref j = some x → v 0 = x
  | .inr (b,t,j) => v 2 = (1 + v 0) * v 1 + c b t j

lemma gatePred_point (hk : 0 < k) (o : TapeOut k r → Bool) (c : Bool → Fin r → Word k)
    (pref : Fin k → Option F) (a : Param k r → F) (j : Leaf k r) :
    gatePred (evalForms hk o) c pref j (fun e => dotProduct (linearRows (evalForms hk o) (j,e)) a) ↔
    localCheck hk c pref (flatten.symm (tapePrepPoint o + paramMap o a)) j := by
  have h (e : Fin 3) : affineForms (evalForms hk o) (j,e) +
      dotProduct (linearRows (evalForms hk o) (j,e)) a =
      form hk j e (flatten.symm (tapePrepPoint o + paramMap o a)) := by
    rw [affineForms_eq, linearRows_eval, map_add]
    exact ((formLinear hk j e).map_add _ _).symm
  rcases j with i | g
  · simp only [gatePred, h, localCheck, elim_inl]
  · simp only [gatePred, h, localCheck, elim_inr]

end Helpers

section Helpers

open Donor

variable {k r q : ℕ}

theorem root_tableCount (hk : 0 < k) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (obs : Fin q → Tape k r) (rhs : Fin q → F) (pref : Fin k → Option F)
    (o : TapeOut k r → Bool)
    (hgen : span F (Set.range (tapePrepGen o)) = LinearMap.ker (latticeMap hk obs))
    (hpoint : latticeMap hk obs (tapePrepPoint o) = rowTarget name rhs)
    {d : ℕ} (A : Fin d → Param k r → F)
    (hA : span F (Set.range A) = CutSpan (linearRows (evalForms hk o)) (fun _ => true)) :
    tableCount (linearRows (evalForms hk o)) (gatePred (evalForms hk o) c pref) (fun _ => true) A hA 0 =
      Nat.card {key // KeyOK hk name c obs rhs pref key} := by
  classical
  let P0 := Param k r → F
  let R := linearRows (evalForms hk o)
  let P := gatePred (evalForms hk o) c pref
  let S := FormSpan R (fun _ => true)
  let base := tapePrepPoint o
  let T (a : P0) := flatten.symm (base + paramMap o a)
  have hsys (a : P0) : (∀ b, (T a).2 b 0 = rot hk (start b) (T a).1 + name b) ∧
      ∀ i, pair (obs i) (T a) = rhs i := by
    apply (rowEquations hk name obs rhs (T a)).mp
    have ha : paramMap o a ∈ LinearMap.range (paramMap o) := ⟨a,rfl⟩
    rw [paramMap_range hk obs o hgen] at ha
    have hz : latticeMap hk obs (flatten (T a)) = rowTarget name rhs := by
      dsimp only [T]
      rw [LinearEquiv.apply_symm_apply, map_add, show latticeMap hk obs (paramMap o a) = 0 from ha, add_zero]
      exact hpoint
    exact fun i => congrFun hz i
  let u (a : P0) : Dual P0 := dotProductEquiv F (Param k r) a
  let z (a : P0) : Dual S := (u a).comp S.subtype
  have hval (a : P0) (i : FormIx k r) :
      affineForms (evalForms hk o) i + u a (R i) = form hk i.1 i.2 (T a) := by
    change affineForms (evalForms hk o) i + dotProduct a (R i) = _
    rw [dotProduct_comm, affineForms_eq, linearRows_eval, show T a = flatten.symm (base + paramMap o a) from rfl,
      map_add]
    exact ((formLinear hk i.1 i.2).map_add _ _).symm
  have hsem (a : P0) : localGood R P (fun _ => true) (z a) ↔ TapeOK hk name c obs rhs pref (T a) := by
    rw [show z a = (u a).comp S.subtype from rfl, localGood_extension]
    simp only [forall_const, TapeOK]
    have hq := hsys a
    constructor
    · intro hg
      refine ⟨hq.1, fun j => ?_, hq.2⟩
      have he := hg j
      change P j (fun e => dotProduct a (R (j,e))) at he
      exact (gatePred_point hk o c pref a j).mp (by simpa only [dotProduct_comm] using he)
    · intro hh j
      have he := (gatePred_point hk o c pref a j).mpr (hh.2.1 j)
      change P j (fun e => dotProduct a (R (j,e)))
      simpa only [P, R, dotProduct_comm] using he
  have hseparate (a b : P0) : z a = z b ↔ T a = T b := by
    constructor
    · intro he
      apply allForms_separate hk name (hsys a).1 (hsys b).1
      intro j e
      let i : S := ⟨R (j,e), row_mem R _ rfl e⟩
      have hv : u a (R (j,e)) = u b (R (j,e)) := LinearMap.congr_fun he i
      rw [← hval a (j,e), ← hval b (j,e), hv]
    · intro hT
      apply selectedSpan_ext
      intro i hi
      exact add_left_cancel (by rw [hval a, hval b, hT])
  have hzSurj : Surjective z := by
    intro g
    obtain ⟨v,hv⟩ := LinearMap.dualMap_surjective_of_injective S.injective_subtype g
    obtain ⟨a,ha⟩ := (dotProductEquiv F (Param k r)).surjective v
    exact ⟨a, by change (u a).comp S.subtype = _; rw [show u a = v from ha]; exact hv⟩
  have hTSurj (t : Tape k r) (ht : TapeOK hk name c obs rhs pref t) : ∃ a, T a = t := by
    have h0 : latticeMap hk obs (flatten t) = rowTarget name rhs := by
      funext i
      exact (rowEquations hk name obs rhs t).mpr ⟨ht.1,ht.2.2⟩ i
    have hk0 : flatten t - base ∈ LinearMap.ker (latticeMap hk obs) := by
      change latticeMap hk obs (flatten t - base) = 0
      rw [map_sub, h0, hpoint, sub_self]
    rw [← paramMap_range hk obs o hgen] at hk0
    obtain ⟨a,ha⟩ := hk0
    refine ⟨a,?_⟩
    apply (flatten (k:=k) (r:=r)).injective
    change flatten (flatten.symm (base + paramMap o a)) = flatten t
    rw [LinearEquiv.apply_symm_apply, ha]
    exact (add_comm base _).trans (sub_add_cancel _ _)
  have hroot : CutSpan R (fun _ => true) = ⊥ := by
    unfold CutSpan FormSpan selectedSpan
    simp
  have hAddr (g : Dual S) : address R (fun _ => true) A hA g = 0 := by
    funext i
    have hi : A i ∈ CutSpan R (fun _ => true) := (genMembers _ _ hA i).prop
    rw [hroot, Submodule.mem_bot] at hi
    have hai : CutSpan R (fun _ => true) ≤ S := inf_le_left
    let ai : S := ⟨A i, hai (genMembers _ _ hA i).prop⟩
    change g ai = 0
    exact (congrArg (fun t : S => g t) (Subtype.ext hi : ai = 0)).trans (map_zero g)
  have hcard : tableCount R P (fun _ => true) A hA 0 = Nat.card {g : Dual S // localGood R P (fun _ => true) g} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun g => ⟨And.left, fun hg => ⟨hg,hAddr g⟩⟩))
  rw [hcard, ← Nat.card_congr (tapeKeyEquiv hk name c obs rhs pref)]
  apply Nat.card_congr
  let a (g : Dual S) := Classical.choose (hzSurj g)
  have ha (g : Dual S) : z (a g) = g := Classical.choose_spec (hzSurj g)
  let f (g : {g : Dual S // localGood R P (fun _ => true) g}) : {t // TapeOK hk name c obs rhs pref t} :=
    ⟨T (a g.val), (hsem (a g.val)).mp ((ha g.val).symm ▸ g.prop)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro f₁ f₂ he
    have h := (hseparate (a f₁.val) (a f₂.val)).mpr (congrArg Subtype.val he)
    exact Subtype.ext ((ha f₁.val).symm.trans (h.trans (ha f₂.val)))
  · intro t
    obtain ⟨u,hu⟩ := hTSurj t.val t.prop
    have hg : localGood R P (fun _ => true) (z u) := (hsem u).mpr (hu.symm ▸ t.prop)
    exact ⟨⟨z u,hg⟩, Subtype.ext (((hseparate _ _).mp (ha (z u))).trans hu)⟩

end Helpers

section Helpers

open Donor PackedTape

variable {k r q n d : ℕ}

abbrev Addr (d : ℕ) := Fin (2^d)

abbrev TableIx (k r d : ℕ) := Addr d × Fin (tapeSize k r + 1)

abbrev JoinState (k r q n d : ℕ) := Pre k r q n d ⊕ (TableIx k r d ⊕ TableIx k r d)

end Helpers

section Helpers

open Donor PackedTape

variable {k r q n d : ℕ}

def prefixMask (x : In k r q n → Bool) (j : Fin k) : Bool := x (.inr (.inl j))
def prefixValue (x : In k r q n → Bool) (j : Fin k) : Bool := x (.inr (.inr j))
def readPref (x : In k r q n → Bool) (j : Fin k) : Option F :=
  if prefixMask x j then some (b2z (prefixValue x j)) else none

def isGate : Leaf k r → Bool := elim (fun _ => false) (fun _ => true)

abbrev LInput (d : ℕ) := LeafTable.Input (d+3) d

def leafLocalCost (k r d : ℕ) : ℕ := nullPrepCost (Fin (d+3)) (Param k r) (d+3) +
  card (LInput d) + LeafTable.budget (d+3) d (tapeSize k r + 1)

set_option maxHeartbeats 1400000 in
lemma leafLocal_cmp (j : Leaf k r) :
    ∃ FL : (Pre k r q n d → Bool) → TableIx k r d → Bool,
      Cmp (Pre k r q n d) (TableIx k r d) (leafLocalCost k r d) FL ∧
      ∀ (x : Pre k r q n d → Bool) (a : Addr d) (s : Fin (tapeSize k r+1)),
        FL x (a,s) = (Nat.card {y : Fin 3 → F //
          gatePred (preForms x) (readC (preRaw x)) (readPref (preIn x)) j y ∧
          ∃ u : Dual (Param k r → F), (∀ t, u (preGen x (.inr j) t) = vecN d a.val t) ∧
            ∀ e, u (linearRows (preForms x) (j,e)) = y e}).testBit s.val := by
  classical
  let D := Pre k r q n d
  let I := Fin (d+3)
  let U := Param k r
  let route : NullIn I U → D := fun (i,t) => Fin.addCases
    (fun u => .inr (.inr j, .inl (t,u)))
    (fun e => .inl (.inr (.inr ((j,e), .inl t)))) i
  obtain ⟨S,hS,hsem⟩ := nullPrep (J:=I) (U:=U) (d+3) (by simp [I])
  let A (x : D → Bool) : NullOut I (d+3) → Bool := S (x ∘ route)
  let B (v : D ⊕ NullOut I (d+3) → Bool) : LInput d → Bool := elim
    (fun (i,t) => v (.inr (t,i)))
    (elim (fun e => v (.inl (.inl (.inr (.inr ((j,e), .inr ()))))))
      (elim (fun _ => match j with
          | .inl j => v (.inl (.inl (.inl (.inr (.inl j)))))
          | .inr _ => false)
        (elim (fun _ => match j with
            | .inl j => v (.inl (.inl (.inl (.inr (.inr j)))))
            | .inr _ => false)
          (fun _ => match j with
            | .inl _ => false
            | .inr (b,t,i) => v (.inl (.inl (.inl (.inl (cSlot b t i)))))))))
  have hB : Cmp (D ⊕ NullOut I (d+3)) (LInput d) (card (LInput d)) B := by
    rw [← Nat.mul_one (card (LInput d))]
    apply Cmp.ofBits
    let Z := D ⊕ NullOut I (d+3)
    rintro (⟨i,t⟩ | e | ⟨⟩ | ⟨⟩ | ⟨⟩)
    · exact (Cb.var (ι:=Z) (.inr (t,i))).mono (by decide)
    · exact (Cb.var (ι:=Z) (.inl (.inl (.inr (.inr ((j,e), .inr ())))))).mono (by decide)
    · rcases j with u | ⟨b,t,u⟩
      · exact (Cb.var (ι:=Z) (.inl (.inl (.inl (.inr (.inl u)))))).mono (by decide)
      · exact Cb.const false
    · rcases j with u | ⟨b,t,u⟩
      · exact (Cb.var (ι:=Z) (.inl (.inl (.inl (.inr (.inr u)))))).mono (by decide)
      · exact Cb.const false
    · rcases j with u | ⟨b,t,u⟩
      · exact Cb.const false
      · exact (Cb.var (ι:=Z) (.inl (.inl (.inl (.inl (cSlot b t u)))))).mono (by decide)
  have hLeaf := LeafTable.fieldTableC (d+3) d (tapeSize k r+1) (isGate j)
  refine ⟨_, Cmp.comp (Cmp.comp (Cmp.keep (Cmp.sel route hS)) hB) hLeaf, ?_⟩
  intro x a s
  let w := B (elim x (A x))
  change (Nat.card {u // LeafTable.fieldValid (isGate j) w a u}).testBit s.val = _
  congr 1
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro y
  have hR := hsem (x ∘ route)
  let R := nullDecoded (x ∘ route)
  let G := preGen x (.inr j)
  let L := fun e : Fin 3 => linearRows (preForms x) (j,e)
  have hℓ (z : I → F) : (∀ i : Fin (d+3), dotProduct (nullOutGen (A x) i) z = 0) ↔
      ∃ u : Dual (U → F), ∀ t, u (R t) = z t := by
    rw [evalRange]
    have hspan : ∀ v : I → F, v ∈ span F (Set.range (nullOutGen (A x))) ↔
        (∑ i, v i • R i) = 0 := by
      intro v
      rw [hR, LinearMap.mem_ker, Fintype.linearCombination_apply]
    constructor
    · intro ht v hv
      let f : (I → F) →ₗ[F] F := dotProductEquiv F I z
      have hc : span F (Set.range (nullOutGen (A x))) ≤ LinearMap.ker f := by
        apply span_le.mpr
        rintro _ ⟨i,rfl⟩
        change dotProduct z (nullOutGen (A x) i) = 0
        rw [dotProduct_comm]
        exact ht i
      exact hc ((hspan v).mpr hv)
    · intro hv i
      rw [dotProduct_comm]
      exact hv _ ((hspan _).mp (subset_span ⟨i,rfl⟩))
  have he : (∃ u : Dual (U → F), ∀ t, u (R t) = LeafTable.fieldCoord a y t) ↔
      ∃ u : Dual (U → F), (∀ t, u (G t) = vecN d a.val t) ∧ ∀ e, u (L e) = y e := by
    have h1 (t : Fin d) : LeafTable.fieldCoord a y (Fin.castAdd 3 t) = vecN d a.val t := by
      simp [LeafTable.fieldCoord, t.isLt]
    have h2 (e : Fin 3) : LeafTable.fieldCoord a y (Fin.natAdd d e) = y e := by
      simp [LeafTable.fieldCoord, Nat.not_lt_of_ge (Nat.le_add_right d e.val)]
    have h3 (t : Fin d) : R (Fin.castAdd 3 t) = G t := by
      funext i
      simp [R, route, G, nullDecoded, preGen, widthOutGen, preBasis]
    have h4 (e : Fin 3) : R (Fin.natAdd d e) = L e := by
      funext i
      simp [R, route, L, nullDecoded, linearRows, preForms]
    constructor
    · rintro ⟨u,h⟩
      exact ⟨u, fun t => h3 t ▸ h1 t ▸ h (Fin.castAdd 3 t),
        fun e => h4 e ▸ h2 e ▸ h (Fin.natAdd d e)⟩
    · rintro ⟨u,hx,hy⟩
      refine ⟨u, Fin.addCases (fun t => ?_) (fun e => ?_)⟩
      · rw [h3, h1]; exact hx _
      · rw [h4, h2]; exact hy _
  unfold LeafTable.fieldValid
  have hc : (∀ i : Fin (d+3), (∑ t : I, LeafTable.fieldCoord a y t * b2z (w (.coeff i t))) = 0) ↔
      ∃ u : Dual (U → F), (∀ t, u (G t) = vecN d a.val t) ∧ ∀ e, u (L e) = y e := by
    have hrew : (fun i : Fin (d+3) => (∑ t : I, LeafTable.fieldCoord a y t * b2z (w (.coeff i t)))) =
        (fun i => dotProduct (nullOutGen (A x) i) (LeafTable.fieldCoord a y)) := by
      funext i
      rw [dotProduct_comm]
      rfl
    exact (congrArg (fun f : Fin (d+3) → F => ∀ i, f i = 0) hrew).to_iff.trans ((hℓ _).trans he)
  rw [hc, and_comm]
  apply and_congr_left'
  rcases j with j | ⟨b,t,j⟩
  · change (prefixMask (preIn x) j = true →
        y 0 + affineForms (preForms x) (.inl j, 0) = b2z (prefixValue (preIn x) j)) ↔
      (∀ v, readPref (preIn x) j = some v → affineForms (preForms x) (.inl j, 0) + y 0 = v)
    cases hb : prefixMask (preIn x) j <;> simp [readPref, hb, add_comm]
  · change (y 2 + affineForms (preForms x) (.inr (b,t,j), 2) =
        (1 + (y 0 + affineForms (preForms x) (.inr (b,t,j), 0))) *
          (y 1 + affineForms (preForms x) (.inr (b,t,j), 1)) + readC (preRaw x) b t j) ↔ _
    rw [add_comm (y 2), add_comm (y 0), add_comm (y 1)]
    rfl

end Helpers

section Helpers

open Donor PackedTape

variable {k r q n d : ℕ}

def bagRoute : Fin n × Leaf k r → Pre k r q n d := fun (v,j) => .inl (.inl (.inl (bagSlot v j)))

def inputHit (hk : 0 < k) (x : Raw k r q n → Bool) (key : Fin k → Bool) : Prop :=
  ∀ i, pair (readObs x i) ((fun j => b2z (key j)),
    actual hk (readName x) (readC x) (fun j => b2z (key j))) = readRhs x i

noncomputable def inputGood (hk : 0 < k) (w : ℕ) (x : Raw k r q n → Bool) : Bool := by
  classical
  let D := Direction hk (readObs x)
  let sp := fun b : Leaf k r → Bool => span F {f : D → F |
    ∃ (j : Leaf k r) (e : Fin 3), b j = true ∧ f = fun z => form hk j e z.val}
  exact decide (LayoutGuard.layout (fun (v,j) => bagSlot v j) x = true ∧
    ∀ v : Fin n, finrank F ((sp (readBag x v) ⊓ sp (fun j => !(readBag x v j))) : Submodule F (D → F)) ≤ w)

lemma tableCount_congr {J V : Type*} [AddCommGroup V] [Module F V] {d : ℕ}
    (R : J × Fin 3 → V) (P : Predicates J) {p p' : J → Bool} (hp : p = p')
    {A A' : Fin d → V} (he : A = A')
    (hA : span F (Set.range A) = CutSpan R p)
    (hA' : span F (Set.range A') = CutSpan R p') (x : Fin d → F) :
    tableCount R P p A hA x = tableCount R P p' A' hA' x := by
  subst p'; subst A'; rfl

lemma tableCount_bound {J U : Type*} [Fintype U] {d : ℕ}
    (R : J × Fin 3 → (U → F)) (P : Predicates J) (p : J → Bool) (A : Fin d → U → F)
    (hA : span F (Set.range A) = CutSpan R p) (x : Fin d → F) :
    tableCount R P p A hA x < 2 ^ (card U + 1) := by
  let S := FormSpan R p
  have h0 : finrank F (Dual S) ≤ card U := by
    rw [Subspace.dual_finrank_eq, ← Module.finrank_pi (R := F)]
    exact Submodule.finrank_le S
  have hNat : Nat.card F = 2 := by simp [Nat.card_eq_fintype_card, ZMod.card]
  have h1 : Nat.card (Dual S) ≤ 2 ^ card U := by
    rw [Module.natCard_eq_pow_finrank (K := F), hNat]
    exact Nat.pow_le_pow_right (by decide) h0
  letI : Finite (Dual (FormSpan R p)) :=
    Finite.of_injective (fun f : Dual S => (f : S → F)) DFunLike.coe_injective
  apply lt_of_le_of_lt (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)
  exact h1.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

lemma tabN_recover {t : ℕ} {v : ℕ} (hv : v < 2 ^ t) :
    tabN (fun i : Fin t => v.testBit i.val) = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < t
  · exact st_tabN_testBit _ ⟨j,hj⟩
  · have he : 2 ^ t ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow ((st_tabN_lt _).trans_le he), Nat.testBit_lt_two_pow (hv.trans_le he)]

lemma keyOK_card (hk : 0 < k) (x : Raw k r q n → Bool) (m p : Fin k → Bool) :
    Nat.card {key // KeyOK hk (readName x) (readC x) (readObs x) (readRhs x)
      (readPref (Greedy.input x m p)) key} = Greedy.cardinal (Greedy.matched (inputHit hk x) m p) := by
  classical
  apply Nat.card_congr
  let e : Word k ≃ (Fin k → Bool) :=
    { toFun := fun v j => zbit (v j)
      invFun := fun v j => b2z (v j)
      left_inv := fun _ => funext fun _ => zbit_decode _
      right_inv := fun _ => funext fun _ => st_dec_b2z _ }
  apply Equiv.subtypeEquiv e
  intro key
  have ht : (fun j => b2z (e key j)) = key := e.left_inv key
  unfold KeyOK Greedy.matched inputHit
  rw [ht]
  constructor
  · rintro ⟨hp,h⟩
    refine ⟨h, fun j hj => ?_⟩
    have h' := hp j (b2z (p j)) (by simp [readPref, prefixMask, prefixValue, Greedy.input, hj])
    have hx : e key j = zbit (key j) := rfl
    rw [hx,h']
    exact st_dec_b2z _
  · rintro ⟨h,hp⟩
    refine ⟨fun j s hs => ?_,h⟩
    cases hm : m j
    · simp [readPref, prefixMask, prefixValue, Greedy.input, hm] at hs
    · have h' := hp j hm
      have hval : b2z (p j) = s := by simpa [readPref, prefixMask, prefixValue, Greedy.input, hm] using hs
      rw [← hval, ← h']; exact (congrFun ht j).symm

def finalCountBudget (k r n : ℕ) : ℕ := (k+2) *
  (LayoutGuard.layoutCost (Leaf k r) n + (n+1) + n * (LayoutGuard.rootCost (Leaf k r) + 2) + 4)

abbrev TreeState (k r q n d : ℕ) := TreeSchedule.State (Pre k r q n d) (TableIx k r d) n

def zeroAddr (d : ℕ) : Addr d := ⟨0, Nat.two_pow_pos d⟩

noncomputable def fitSignal (x : Pre k r q n d → Bool) : Bool := by
  classical
  exact LayoutGuard.layout bagRoute x && decide (∀ v : Fin n, preWidth x (.inl v) = true)

def widenCount (k r : ℕ) (j : Fin (k+1)) : Fin (tapeSize k r + 1) :=
  ⟨j.val, j.isLt.trans_le (by change k+1 ≤ (2*r+3)*k+1; nlinarith)⟩

noncomputable def finishCount (s : TreeState k r q n d → Bool) : Greedy.Reply k → Bool :=
  elim (fun _ => fitSignal (TreeSchedule.data s)) (fun j =>
    fitSignal (TreeSchedule.data s) && preAffine (TreeSchedule.data s) &&
      LayoutGuard.readRoots bagRoute s (zeroAddr d, widenCount k r j))

lemma finishCount_cmp : Cmp (TreeState k r q n d) (Greedy.Reply k) (finalCountBudget k r n)
    (finishCount (k:=k) (r:=r) (q:=q) (n:=n) (d:=d)) := by
  classical
  let D := TreeState k r q n d
  let l := LayoutGuard.layoutCost (Leaf k r) n
  let a := LayoutGuard.rootCost (Leaf k r)
  have hg : Cb D (l+(n+1)+1) (fun s => fitSignal (TreeSchedule.data s)) := by
    have hwidth : Cb D (n+1) (fun s => decide (∀ v : Fin n, preWidth (TreeSchedule.data s) (.inl v) = true)) := by
      have h := Cb.bigAnd (fun v : Fin n => Cb.var (ι:=D) (.inl (.inr (.inl v, .inr ()))))
      simp only [card_fin, Nat.zero_add, Nat.mul_one] at h
      refine h.congr fun s => ?_
      exact TreeSchedule.decision_eq _ _ _
    exact Cb.and (Cmp.sel inl (LayoutGuard.layout_cb (bagRoute (k:=k) (r:=r) (q:=q) (n:=n) (d:=d)))) hwidth
  have hRead (t : TableIx k r d) : Cb D (n*(a+2)+1) (fun s => LayoutGuard.readRoots bagRoute s t) := by
    have hv (v : Fin n) : Cb D (a+1) (fun s => (LayoutGuard.root bagRoute v (TreeSchedule.data s) &&
        TreeSchedule.table s v t)) := by
      have h : Cb D a (fun s => LayoutGuard.root bagRoute v (TreeSchedule.data s)) :=
        Cmp.sel inl (LayoutGuard.root_cb bagRoute v)
      simpa only [Nat.add_zero] using Cb.and h (Cb.var (ι:=D) (.inr (v,t)))
    have h := (Cb.bigOr hv).congr (φ' := fun s => LayoutGuard.readRoots bagRoute s t)
      (fun z => by
        rw [Bool.eq_iff_iff]
        simp only [LayoutGuard.readRoots, decide_eq_true_eq])
    simpa only [card_fin, Nat.add_assoc] using h
  rw [show finalCountBudget k r n =
      card (Greedy.Reply k) * (l+(n+1)+n*(a+2)+4) by
    unfold finalCountBudget Greedy.Reply
    simp [l,a,Nat.add_comm,Nat.add_assoc] <;> omega]
  apply Cmp.ofBits
  rintro (⟨⟩ | i)
  · exact hg.mono (by omega)
  · apply Cb.mono (Cb.and (Cb.and hg (Cb.var (ι:=D) (.inl (.inl (.inr (.inl ())))))) (hRead _))
    omega

end Helpers

section Helpers

open Donor PackedTape

lemma leaf_card (k r : ℕ) : card (Leaf k r) = (2*r+1)*k := by
  simp [Leaf]
  ring

theorem gaussianBudget {a b c e T : ℕ} (h : a+b+c+e+2 ≤ 16*T) :
    glCost a b c e ≤ 2^36*T^6 := by
  unfold glCost
  calc
    _ ≤ 2^12*(16*T)^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 6)
    _ = _ := by ring

theorem widthBudget {J U : Type} [Fintype J] [Fintype U] {d T : ℕ}
    (hT : 1 ≤ T) (hJ : card J ≤ 3*T) (hU : card U ≤ T) (hd : d ≤ T) :
    card (WidthIn J U) + widthPrepCost J U d ≤ 2^38*T^6 := by
  simp only [widthPrepCost, WidthIn, WidthOut, ProjIn, card_prod, card_sum,
    card_bool, card_fin, card_unit]
  let a := card J
  let b := card U
  change a*b+a + (2*b*(2*a+(b+1))*4+glCost (2*b) (2*a) b (d+1)+(b*d+1)*2) ≤ _
  have hg := gaussianBudget (a:=2*b) (b:=2*a) (c:=b) (e:=d+1) (T:=T) (by omega)
  have hp : T^2 ≤ T^6 := Nat.pow_le_pow_right hT (by decide)
  have hq : 1 ≤ T^2 := Nat.one_le_pow _ _ hT
  have ht : T ≤ T^2 := by simpa only [pow_one] using (Nat.pow_le_pow_right hT (show 1 ≤ 2 by decide))
  have h1 := Nat.mul_le_mul hJ hU
  have h2 := Nat.mul_le_mul hU hd
  have h3 := Nat.mul_le_mul (show 2*b ≤ 2*T by omega) (show 2*a+(b+1) ≤ 8*T by omega)
  nlinarith only [hg,hp,hq,ht,h1,h2,h3,hJ]

theorem nullBudget {J U : Type} [Fintype J] [Fintype U] {d T : ℕ}
    (hT : 1 ≤ T) (hJ : card J ≤ T) (hU : card U ≤ T) (hd : d ≤ T) :
    nullPrepCost J U d ≤ 2^38*T^6 := by
  simp only [nullPrepCost, NullOut, ProjIn, card_prod, card_sum,
    card_empty, card_fin, card_unit, zero_add]
  let a := card J
  let b := card U
  change b*(a+1)+glCost b 0 a d+a*d ≤ _
  have h1 := Nat.mul_le_mul hU (show a+1 ≤ 2*T by omega)
  have h2 := Nat.mul_le_mul hJ hd
  have hg := gaussianBudget (a:=b) (b:=0) (c:=a) (e:=d) (T:=T) (by omega)
  nlinarith only [hg,h1,h2,Nat.pow_le_pow_right hT (show 2 ≤ 6 by decide)]

theorem tapeBudget {k r q T : ℕ} (hT : 1 ≤ T)
    (hN : tapeSize k r + 1 ≤ T) (hR : card (EqRow k q) ≤ 2*T) :
    tapePrepCost k r q ≤ 2^39*T^6 := by
  let N := tapeSize k r
  let R := card (EqRow k q)
  have hSys : tapePrepSysCost k r q = R*(N+1) := by
    unfold tapePrepSysCost ProjIn
    rw [card_prod, card_sum (α := Empty), card_empty, Nat.zero_add,
      card_sum (α := Coord k r) (β := Unit), coord_card, card_unit]
  have hOut : card (TapeOut k r) = N*(N+1)+1 := by
    unfold TapeOut
    rw [card_sum, card_prod, coord_card, card_sum, card_fin,
      card_unit]
  unfold tapePrepCost
  rw [hSys,hOut]
  change 2*(R*(N+1)+glCost R 0 N N)+(N*(N+1)+1) ≤ _
  have hg := gaussianBudget (a:=R) (b:=0) (c:=N) (e:=N) (T:=T) (by omega)
  have ha : R*(N+1) ≤ 2*T*T := Nat.mul_le_mul hR hN
  have hb : N*(N+1) ≤ T*T := Nat.mul_le_mul (show N ≤ T by omega) hN
  nlinarith only [ha,hb,hg,Nat.pow_le_pow_right hT (show 2 ≤ 6 by decide),Nat.one_le_pow 6 T hT]

end Helpers

section Helpers

section CompactBlocks

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

abbrev Common (A B C : Submodule K V) := (A ⊓ B) ⊓ C
abbrev Pairs (A B C : Submodule K V) := ((A ⊓ B) ⊔ (A ⊓ C)) ⊔ (B ⊓ C)
abbrev Side (A B C : Submodule K V) := (A ⊓ B) ⊔ (A ⊓ C)

theorem side_eq_inf_pairs (A B C : Submodule K V) :
    Side A B C = A ⊓ Pairs A B C := by
  have hle : Side A B C ≤ A := sup_le inf_le_left inf_le_left
  rw [inf_comm A (Pairs A B C), sup_inf_assoc_of_le _ hle]
  apply le_antisymm le_sup_left
  apply sup_le le_rfl
  exact (show B ⊓ C ⊓ A ≤ A ⊓ B from le_inf inf_le_right (inf_le_left.trans inf_le_left)).trans le_sup_left

theorem pair_disjoint (A B C : Submodule K V) :
    Disjoint (A.map (Pairs A B C).mkQ) (B.map (Pairs A B C).mkQ) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  obtain ⟨a,ha,rfl⟩ := Submodule.mem_map.mp hx
  obtain ⟨b,hb,he⟩ := Submodule.mem_map.mp hy
  have hab : a - b ∈ Pairs A B C := (Submodule.Quotient.eq _).mp he.symm
  obtain ⟨p,hp,w,hw,ep⟩ := Submodule.mem_sup.mp hab
  obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hp
  have hrs : a - v = b + w + u := calc
    a - v = (a - b) - v + b := by abel
    _ = b + w + u := by rw [← ep]; abel
  have h₁ : a - v ∈ A ⊓ B :=
    ⟨A.sub_mem ha hv.1, hrs ▸ B.add_mem (B.add_mem hb hw.1) hu.2⟩
  have h₂ : a ∈ Pairs A B C := by
    simpa only [sub_add_cancel] using (Pairs A B C).add_mem
      ((le_sup_left.trans le_sup_left : A ⊓ B ≤ Pairs A B C) h₁)
      ((le_sup_right.trans le_sup_left : A ⊓ C ≤ Pairs A B C) hv)
  exact (Submodule.Quotient.mk_eq_zero _).mpr h₂

theorem pairs_swap (A B C : Submodule K V) : Pairs A B C = Pairs B A C := by
  unfold Pairs
  rw [inf_comm A B, sup_assoc, sup_comm (A ⊓ C), ← sup_assoc]

theorem pairs_cycle (A B C : Submodule K V) : Pairs A B C = Pairs B C A := by
  unfold Pairs
  rw [inf_comm B A, inf_comm C A]
  ac_rfl

abbrev genSpan {J : Type} (v : J → V) : Submodule K V :=
  span K (Set.range v)

theorem agrees_span {J : Type} {u v : V →ₗ[K] K} {g : J → V}
    (h : ∀ j, u (g j) = v (g j)) :
    ∀ x ∈ genSpan (K:=K) g, u x = v x := by
  have hle : genSpan g ≤ LinearMap.ker (u-v) :=
    span_le.mpr (by rintro _ ⟨j,rfl⟩; exact sub_eq_zero.mpr (h j))
  exact fun x hx => sub_eq_zero.mp (hle hx)

theorem agrees_sup {U W : Submodule K V} {u v : V →ₗ[K] K}
    (hU : ∀ x ∈ U, u x = v x) (hW : ∀ x ∈ W, u x = v x) :
    ∀ x ∈ U ⊔ W, u x = v x := by
  intro x hx
  obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, map_add, hU a ha, hW b hb]

theorem cut_agreement {A B C : Submodule K V}
    {T U W Y J : Type} (t : T → V) (ab : U → V) (ac : W → V) (bc : Y → V)
    (ra rb rc : J → V)
    (hT : genSpan t = Common A B C)
    (hAB : genSpan t ⊔ genSpan ab = A ⊓ B)
    (hAC : genSpan t ⊔ genSpan ac = A ⊓ C)
    (hBC : genSpan t ⊔ genSpan bc = B ⊓ C)
    (hC : Side C A B ⊔ genSpan rc = C)
    (ha : ∀ j, ra j ∈ A) (hb : ∀ j, rb j ∈ B) (hr : ∀ j, ra j + rb j = rc j)
    (f g h : V →ₗ[K] K)
    (glue : ∀ (v : A →ₗ[K] K) (w : B →ₗ[K] K),
      (∀ x : ↥(A ⊓ B), v ⟨x, x.prop.1⟩ = w ⟨x, x.prop.2⟩) →
      ∃ b : V →ₗ[K] K, b.comp A.subtype = v ∧ b.comp B.subtype = w) :
    (∃ a : V →ₗ[K] K, (∀ x ∈ A, a x = f x) ∧ (∀ x ∈ B, a x = g x) ∧
      ∀ x ∈ C, a x = h x) ↔
    (∀ j, f (ra j) + g (rb j) = h (rc j)) ∧
    (∀ j, f (t j) = h (t j) ∧ g (t j) = h (t j)) ∧
    (∀ j, f (ac j) = h (ac j)) ∧ (∀ j, f (ab j) = g (ab j)) ∧
    (∀ j, g (bc j) = h (bc j)) := by
  have hm {S : Submodule K V} {J' : Type} {u : J' → V} (h : genSpan u ≤ S) (j : J') :
      u j ∈ S := h (subset_span ⟨j,rfl⟩)
  have ht (j : T) : t j ∈ Common A B C := hm hT.le j
  have hab (j : U) : ab j ∈ A ⊓ B := hm (hAB ▸ le_sup_right) j
  have hac (j : W) : ac j ∈ A ⊓ C := hm (hAC ▸ le_sup_right) j
  have hbc (j : Y) : bc j ∈ B ⊓ C := hm (hBC ▸ le_sup_right) j
  have hc (j : J) : rc j ∈ C := hm (hC ▸ le_sup_right) j
  constructor
  · rintro ⟨a,hA,hB,hC'⟩
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
    · rw [← hA _ (ha j), ← hB _ (hb j), ← map_add, hr, hC' _ (hc j)]
    · exact ⟨(hA _ (ht j).1.1).symm.trans (hC' _ (ht j).2),
        (hB _ (ht j).1.2).symm.trans (hC' _ (ht j).2)⟩
    · exact (hA _ (hac j).1).symm.trans (hC' _ (hac j).2)
    · exact (hA _ (hab j).1).symm.trans (hB _ (hab j).2)
    · exact (hB _ (hbc j).1).symm.trans (hC' _ (hbc j).2)
  · rintro ⟨hR,hD,hE,hF,hG⟩
    have hfg (x : ↥(A ⊓ B)) : f x = g x := by
      have h := agrees_sup (agrees_span (fun j => (hD j).1.trans (hD j).2.symm))
        (agrees_span hF)
      exact h _ (hAB.symm ▸ x.prop)
    obtain ⟨a,hA,hB⟩ := glue (f.comp A.subtype) (g.comp B.subtype) hfg
    have aA (x : V) (hx : x ∈ A) : a x = f x := LinearMap.congr_fun hA ⟨x,hx⟩
    have aB (x : V) (hx : x ∈ B) : a x = g x := LinearMap.congr_fun hB ⟨x,hx⟩
    refine ⟨a,aA,aB,?_⟩
    have h1 : ∀ x ∈ C ⊓ A, a x = h x := by
      rw [inf_comm C A, ← hAC]
      exact agrees_sup
        (agrees_span (fun j => (aA _ (ht j).1.1).trans (hD j).1))
        (agrees_span (fun j => (aA _ (hac j).1).trans (hE j)))
    have h2 : ∀ x ∈ C ⊓ B, a x = h x := by
      rw [inf_comm C B, ← hBC]
      exact agrees_sup
        (agrees_span (fun j => (aB _ (ht j).1.2).trans (hD j).2))
        (agrees_span (fun j => (aB _ (hbc j).1).trans (hG j)))
    have h3 : ∀ j, a (rc j) = h (rc j) := by
      intro j
      rw [← hr j, map_add, aA _ (ha j), aB _ (hb j), hR j, hr]
    rw [← hC]
    exact agrees_sup (agrees_sup h1 h2) (agrees_span h3)

end CompactBlocks

section Ranks

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable abbrev dim (S : Submodule K V) := finrank K S

theorem dimension_side (A B C : Submodule K V) :
    dim (Side A B C) + dim (Common A B C) = dim (A ⊓ B) + dim (A ⊓ C) := by
  have h : (A ⊓ B) ⊓ (A ⊓ C) = Common A B C := by
    unfold Common
    calc
      (A ⊓ B) ⊓ (A ⊓ C) = (A ⊓ A) ⊓ (B ⊓ C) := by ac_rfl
      _ = _ := by rw [inf_idem, inf_assoc]
  have hs := (A ⊓ B).finrank_sup_add_finrank_inf_eq (A ⊓ C)
  change dim (Side A B C) + dim ((A ⊓ B) ⊓ (A ⊓ C)) = _ at hs
  rwa [h] at hs

theorem dim_map_pairs (A B C : Submodule K V) :
    dim (A.map (Pairs A B C).mkQ) + dim (Side A B C) = dim A := by
  let Q := Pairs A B C
  let f := Q.mkQ.comp A.subtype
  have hr : LinearMap.range f = A.map Q.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : (LinearMap.ker f).map A.subtype = A ⊓ Q := by
    change (LinearMap.ker (Q.mkQ.comp A.subtype)).map A.subtype = _
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.map_comap_subtype]
  have h := f.finrank_range_add_finrank_ker
  rwa [hr, ← Submodule.finrank_map_subtype_eq A f.ker, hk, ← side_eq_inf_pairs] at h

theorem common_counts (A B C : Submodule K V) (hC : C ≤ A ⊔ B)
    {T AB AC BC E : ℕ}
    (ht : dim (Common A B C) = T)
    (hab : dim (A ⊓ B) = T+AB) (hac : dim (A ⊓ C) = T+AC)
    (hbc : dim (B ⊓ C) = T+BC) (he : dim C = dim (Side C A B)+E) :
    E+T+AB+AC ≤ dim A ∧ E+T+AB+BC ≤ dim B ∧ E+T+AC+BC ≤ dim C := by
  let Q := Pairs A B C
  let U := A.map Q.mkQ
  let W := B.map Q.mkQ
  let R := C.map Q.mkQ
  have swapAB : Q = Pairs B A C := pairs_swap A B C
  have swAC : Q = Pairs A C B := by
    change Pairs A B C = _
    unfold Pairs
    rw [inf_comm C B, sup_comm (A ⊓ B)]
  have cyc : Q = Pairs B C A := pairs_cycle A B C
  have cyc' : Q = Pairs C A B := cyc.trans (pairs_cycle B C A)
  have drA : Disjoint R U := by
    change Disjoint (C.map Q.mkQ) (A.map Q.mkQ)
    rw [swAC]
    exact (pair_disjoint A C B).symm
  have drB : Disjoint R W := by
    change Disjoint (C.map Q.mkQ) (B.map Q.mkQ)
    rw [cyc]
    exact (pair_disjoint B C A).symm
  have hle : R ≤ U ⊔ W := (Submodule.map_mono hC).trans_eq (Submodule.map_sup _ _ _)
  have rank_mono (X Y : Submodule K (V ⧸ Q)) (I : Disjoint R X)
      (h : R ≤ Y ⊔ X) : dim R ≤ dim Y := by
    have hh := R.finrank_sup_add_finrank_inf_eq X
    rw [I.eq_bot, finrank_bot, add_zero] at hh
    have h₁ := finrank_mono (sup_le h le_sup_right : R ⊔ X ≤ Y ⊔ X)
    have h₂ := Y.finrank_add_le_finrank_add_finrank X
    change dim (R ⊔ X) = dim R + dim X at hh
    change dim (R ⊔ X) ≤ dim (Y ⊔ X) at h₁
    change dim (Y ⊔ X) ≤ dim Y + dim X at h₂
    omega
  have hA := rank_mono W U drB hle
  have hB := rank_mono U W drA (sup_comm U W ▸ hle)
  have da : dim U + dim (Side A B C) = dim A := dim_map_pairs A B C
  have db : dim W + dim (Side B A C) = dim B := by
    change dim (B.map Q.mkQ) + dim (Side B A C) = dim B
    rw [swapAB]
    exact dim_map_pairs B A C
  have dc : dim R + dim (Side C A B) = dim C := by
    change dim (C.map Q.mkQ) + dim (Side C A B) = dim C
    rw [cyc']
    exact dim_map_pairs C A B
  have ha' := dimension_side A B C
  have hb' := dimension_side B A C
  have hc' := dimension_side C A B
  have hT' : Common B A C = Common A B C := by unfold Common; rw [inf_comm B A]
  have hT'' : Common C A B = Common A B C := by unfold Common; ac_rfl
  rw [ht,hab,hac] at ha'
  rw [hT',ht,inf_comm B A,hab,hbc] at hb'
  rw [hT'',ht,inf_comm C A,inf_comm C B,hac,hbc] at hc'
  omega

end Ranks

end Helpers

namespace CompactJoin

open Donor

abbrev Rows (J U : Type) := J × U
def readRows {J U : Type} (x : Rows J U → Bool) : J → U → F :=
  fun j u => b2z (x (j,u))

def rowSpan {J U : Type} (x : Rows J U → Bool) : Submodule F (U → F) :=
  span F (Set.range (readRows x))

def spanBoth {J K U : Type} (x : Rows (J ⊕ K) U → Bool) :
    Submodule F (U → F) × Submodule F (U → F) :=
  (rowSpan (fun p : Rows J U => x (.inl p.1,p.2)),
   rowSpan (fun p : Rows K U => x (.inr p.1,p.2)))

def intersectionCost (J K U : Type) [Fintype J] [Fintype K] [Fintype U] (d : ℕ) :=
  card (WidthIn (J ⊕ K) U) + widthPrepCost (J ⊕ K) U d

theorem intersection_cmp (J K U : Type) [Fintype J] [Fintype K] [Fintype U] [DecidableEq U]
    (d : ℕ) (hd : min (card J) (card K) ≤ d) :
    ∃ S, Cmp (Rows (J ⊕ K) U) (Rows (Fin d) U) (intersectionCost J K U d) S ∧
      ∀ x, rowSpan (S x) = (spanBoth x).1 ⊓ (spanBoth x).2 := by
  let flag : J ⊕ K → Bool := elim (fun _ => true) (fun _ => false)
  let input (x : Rows (J ⊕ K) U → Bool) : WidthIn (J ⊕ K) U → Bool := elim x flag
  have hin : Cmp _ _ (card (WidthIn (J ⊕ K) U)) input := by
    rw [← Nat.mul_one (card (WidthIn (J ⊕ K) U))]
    apply Cmp.ofBits
    rintro (p | j)
    · exact (Cb.var p).mono (by decide)
    · exact Cb.const (flag j)
  obtain ⟨Q,hQ,hsem⟩ := widthPrep (J:=J ⊕ K) (U:=U) d
  let out (p : Rows (Fin d) U) : WidthOut U d := .inl (p.2,p.1)
  refine ⟨fun x p => Q (input x) (out p), ?_, ?_⟩
  · simpa only [intersectionCost, Nat.add_zero] using (hin.comp hQ).comp (Cmp.wire out)
  · intro x
    let A := (spanBoth x).1
    let B := (spanBoth x).2
    have hA : selectedSpan (widthInRows (input x)) (widthInMask (input x)) = A := by
      unfold selectedSpan A spanBoth rowSpan
      apply congrArg (span F)
      ext v
      constructor
      · rintro ⟨(i | i), hi, rfl⟩
        · exact ⟨i,rfl⟩
        · cases hi
      · rintro ⟨i,rfl⟩
        exact ⟨.inl i,rfl,rfl⟩
    have hB : selectedSpan (widthInRows (input x)) (fun j => !widthInMask (input x) j) = B := by
      unfold selectedSpan B spanBoth rowSpan
      apply congrArg (span F)
      ext v
      constructor
      · rintro ⟨(i | i), hi, rfl⟩
        · cases hi
        · exact ⟨i,rfl⟩
      · rintro ⟨i,rfl⟩
        exact ⟨.inr i,rfl,rfl⟩
    have h := hsem (input x)
    dsimp only at h
    rw [hA,hB] at h
    have hAB : finrank F (A ⊓ B : Submodule F (U → F)) ≤ d := by
      apply le_trans _ hd
      exact le_min
        ((finrank_mono (show A ⊓ B ≤ A from inf_le_left)).trans
          (finrank_range_le_card (readRows (x ∘ fun p : Rows J U => (.inl p.1,p.2)))))
        ((finrank_mono (show A ⊓ B ≤ B from inf_le_right)).trans
          (finrank_range_le_card (readRows (x ∘ fun p : Rows K U => (.inr p.1,p.2)))))
    exact h.2 (h.1.mpr hAB)

def coordinateCost (J U : Type) [Fintype J] [Fintype U] :=
  glCost (card U) 0 (card J) (card J)

theorem coordinates_cmp (J U : Type) [Fintype J] [Fintype U] :
    ∃ S : ((Rows J U ⊕ U) → Bool) → J → Bool, Cmp _ _ (coordinateCost J U) S ∧
      ∀ x, (fun u => b2z (x (.inr u))) ∈ rowSpan (x ∘ inl) →
        (∑ j : J, b2z (S x j) • readRows (x ∘ inl) j) = fun u => b2z (x (.inr u)) := by
  classical
  let route : ProjIn U Empty J → Rows J U ⊕ U :=
    fun (u,p) => p.elim Empty.elim (elim (fun j => .inl (j,u)) (fun _ => .inr u))
  obtain ⟨S,nf,hS,hspec⟩ := glS U Empty J (card J)
  let proj (j : J) : SOut J (card J) := .inr (.inl j)
  refine ⟨fun x j => S (x ∘ route) (proj j), ?_, ?_⟩
  · simpa only [coordinateCost,card_empty,Nat.add_zero,Function.comp_def] using
      (Cmp.sel route hS).comp (Cmp.wire proj)
  · intro x hx
    let b : U → F := fun u => b2z (x (.inr u))
    let G : J → U → F := readRows (x ∘ inl)
    let v := x ∘ route
    let o := S v
    have hsolve (c : J → F) : solS v c ↔ ∑ j, c j • G j = b := by
      unfold solS
      simp only [exists_const, Fintype.sum_empty, zero_add, v, route, elim_inr, elim_inl]
      rw [funext_iff]
      refine forall_congr' fun u => ?_
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,b,G,readRows,Function.comp_apply]
      change (∑ j, b2z (x (.inl (j,u))) * c j) = b u ↔
        (∑ j, c j * b2z (x (.inl (j,u)))) = b u
      simp_rw [mul_comm]
    obtain ⟨a,ha⟩ := (mem_span_range_iff_exists_fun F).mp hx
    have hpos : successful o = true := by
      cases e : successful o
      · exact ((hspec v).1 e _ ((hsolve a).mpr ha)).elim
      · rfl
    have hcard := ((hspec v).2 hpos).1
    have hf : nf v ≤ card J := by
      have hh : Nat.card {c : J → F // solS v c} ≤ Nat.card (J → F) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      rw [hcard, Nat.card_eq_fintype_card, card_fun, ZMod.card] at hh
      exact (Nat.pow_le_pow_iff_right (by decide)).mp hh
    have ho := ((hspec v).2 hpos).2.2 hf
    have hp := (hsolve _).mp (ho.1 0 (project_zero o))
    rw [project_point_zero] at hp
    exact hp

end CompactJoin

namespace CompactJoin

open Donor

abbrev MatrixRows (d m : ℕ) := Rows (Fin d) (Fin m)
abbrev GeneratorInput (d m : ℕ) := Fin 3 × MatrixRows d m

def sourceRows {d m : ℕ} (v : GeneratorInput d m → Bool) (side : Fin 3) :
    MatrixRows d m → Bool := fun i => v (side,i)

def sourceSpan {d m : ℕ} (v : GeneratorInput d m → Bool) (side : Fin 3) :=
  rowSpan (sourceRows v side)

def twoFamilies {J K U : Type} (a : Rows J U → Bool) (b : Rows K U → Bool) :
    Rows (J ⊕ K) U → Bool := fun (j,u) => j.elim (fun i => a (i,u)) (fun i => b (i,u))

lemma twoFamilies_cmp {Q J K U : Type} {S T : ℕ}
    {a : (Q → Bool) → Rows J U → Bool} {b : (Q → Bool) → Rows K U → Bool}
    (ha : Cmp Q (Rows J U) S a) (hb : Cmp Q (Rows K U) T b) :
    Cmp Q (Rows (J ⊕ K) U) (S+T) (fun x => twoFamilies (a x) (b x)) := by
  let route : Rows (J ⊕ K) U → Rows J U ⊕ Rows K U :=
    fun (j,u) => j.elim (fun i => .inl (i,u)) (fun i => .inr (i,u))
  apply (ctrl_rewire (ha.pair hb) route).congr
  rintro x ⟨i|i,u⟩ <;> rfl

lemma spanTwoFamilies {J K U : Type} (a : Rows J U → Bool) (b : Rows K U → Bool) :
    spanBoth (twoFamilies a b) = (rowSpan a, rowSpan b) := rfl

def interCost (d m : ℕ) := intersectionCost (Fin d) (Fin d) (Fin m) d

def intersectionPair : Fin 3 → (Fin 3 × Fin 3) :=
  ![(0,1), (0,2), (1,2)]

theorem allIntersections_cmp (d m : ℕ) :
    ∃ S : (GeneratorInput d m → Bool) → (Fin 4 × MatrixRows d m) → Bool,
      Cmp _ _ (8*interCost d m) S ∧ ∀ x,
        (∀ i : Fin 3, rowSpan (fun p => S x (i.castSucc,p)) =
          sourceSpan x (intersectionPair i).1 ⊓ sourceSpan x (intersectionPair i).2) ∧
        rowSpan (fun p => S x (3,p)) =
          (sourceSpan x 0 ⊓ sourceSpan x 1) ⊓ sourceSpan x 2 := by
  obtain ⟨P,hP,hSpec⟩ := intersection_cmp (Fin d) (Fin d) (Fin m) d (by simp)
  let first (i : Fin 3) (x : GeneratorInput d m → Bool) : MatrixRows d m → Bool :=
    P (twoFamilies (sourceRows x (intersectionPair i).1) (sourceRows x (intersectionPair i).2))
  have hFirst (i : Fin 3) : Cmp _ _ (interCost d m) (first i) := by
    let a : MatrixRows d m → GeneratorInput d m := fun p => ((intersectionPair i).1,p)
    let b : MatrixRows d m → GeneratorInput d m := fun p => ((intersectionPair i).2,p)
    have h := (twoFamilies_cmp (Cmp.wire a) (Cmp.wire b)).comp hP
    simp only [Nat.zero_add] at h
    exact h.congr (fun _ _ => rfl)
  have semFirst (x : GeneratorInput d m → Bool) (i : Fin 3) :
      rowSpan (first i x) = sourceSpan x (intersectionPair i).1 ⊓ sourceSpan x (intersectionPair i).2 := by
    unfold first
    rw [hSpec, spanTwoFamilies]
    rfl
  let last (x : GeneratorInput d m → Bool) :=
    P (twoFamilies (first 0 x) (sourceRows x 2))
  have hLast : Cmp _ _ (2*interCost d m) last := by
    have h := (twoFamilies_cmp (hFirst 0) (Cmp.wire (fun p : MatrixRows d m => ((2 : Fin 3),p)))).comp hP
    rw [Nat.add_zero] at h
    rw [two_mul]
    exact h.congr (fun _ _ => rfl)
  let total (x : GeneratorInput d m → Bool) (u : Fin 4 × MatrixRows d m) : Bool :=
    Fin.lastCases (last x u.2) (fun i => first i x u.2) u.1
  have hTotal : Cmp _ _ (8*interCost d m) total := by
    have h (i : Fin 4) : Cmp (GeneratorInput d m) (MatrixRows d m)
        (2*interCost d m) (fun x p => total x (i,p)) := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [total,Fin.lastCases_last] using hLast
      · have h' := (hFirst j).mono (show interCost d m ≤ 2*interCost d m by omega)
        simpa only [total,Fin.lastCases_castSucc] using h'
    simpa only [card_fin, ← Nat.mul_assoc] using Cmp.piU h
  refine ⟨total,hTotal,fun x => ⟨fun i => ?_,?_⟩⟩
  · simpa only [total,Fin.lastCases_castSucc] using semFirst x i
  · change rowSpan (last x) = _
    unfold last
    rw [hSpec, spanTwoFamilies]
    change rowSpan (first 0 x) ⊓ sourceSpan x 2 = _
    rw [semFirst]
    rfl

end CompactJoin

namespace CompactJoin

open Donor

abbrev Retained {b : ℕ} (fl : Fin b → Bool) := {i : Fin b // fl i = true}

theorem retained_card {b : ℕ} (fl : Fin b → Bool) :
    card (Retained fl) = cnt fl b := by
  simp only [Retained, card_subtype, cnt, Fin.isLt, true_and]

private theorem reduced_column {D : ℕ} (M : Fin D × Fin D → Bool)
    (j : Fin D) (hj : gj D M (j,j) = true) :
    (fun i => mat (gj D M) i j) = Pi.single j (1 : F) := by
  funext i
  rw [mat, gj_pivcol M j hj i]
  by_cases h : i = j <;> simp [h]

private theorem reduced_expansion {a D : ℕ} (M : Fin D × Fin D → Bool) (hle : a ≤ D)
    (j : Fin a) :
    let R := mat (gj D M)
    let e := Fin.castLE hle
    (fun i => R i (e j)) = ∑ t : Fin a, R (e t) (e j) • Pi.single (e t) (1 : F) := by
  intro R e
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h : i.val < a
  · let t : Fin a := ⟨i.val,h⟩
    have ht : e t = i := Fin.ext rfl
    rw [sum_eq_single t]
    · simp [ht]
    · intro s _ hs
      have hh : i ≠ e s := fun hh => hs (Fin.ext (congrArg (fun a : Fin D => a.val) (hh.symm.trans ht.symm)))
      simp [hh]
    · simp
  · have hz := gj_upper M i (e j) (show (e j).val < i.val from
      lt_of_lt_of_le j.isLt (Nat.le_of_not_gt h))
    change b2z (gj D M (i,e j)) = _
    rw [hz]
    symm
    apply sum_eq_zero
    intro t _
    have ht : i ≠ e t := fun ht => h (ht ▸ t.isLt)
    simp [ht]

private theorem reduced_basis_expand {a D : ℕ} (M : Fin D × Fin D → Bool) (hle : a ≤ D)
    (j : Fin a) :
    let R := mat (gj D M)
    let e := Fin.castLE hle
    (fun i => R i (e j)) = ∑ t : Fin a,
      if gj D M (e t,e t) then R (e t) (e j) • (fun i => R i (e t)) else 0 := by
  intro R e
  rw [reduced_expansion M hle j]
  apply sum_congr rfl
  intro t _
  by_cases h : gj D M (e t,e t) = true
  · rw [ite_eq_left h, reduced_column M (e t) h]
  · change b2z (gj D M (e t,e j)) • _ = _
    have hz : R (e t) (e j) = 0 :=
      congrArg b2z (gj_zerorow M (e t) (Bool.eq_false_iff.mpr h) (e j))
    rw [ite_eq_right h]
    change b2z (gj D M (e t,e j)) • _ = _
    rw [show b2z (gj D M (e t,e j)) = 0 from hz, zero_smul]


private def matrixRoute {u b m : ℕ} (p : Fin (u+b+m) × Fin (u+b+m)) :
    Option (Rows (Fin u ⊕ Fin b) (Fin m)) :=
  if h : p.1.val < m ∧ p.2.val < u+b then
    some (finSumFinEquiv.symm ⟨p.2.val,h.2⟩,⟨p.1.val,h.1⟩)
  else none

private def pivotMatrix {u b m : ℕ} (x : Rows (Fin u ⊕ Fin b) (Fin m) → Bool) :=
  fun p : Fin (u+b+m) × Fin (u+b+m) => (matrixRoute p).elim false x

def extraFlag {u b m : ℕ} (x : Rows (Fin u ⊕ Fin b) (Fin m) → Bool) (j : Fin b) : Bool :=
  let t := (j.natAdd u).castAdd m
  gj (u+b+m) (pivotMatrix x) (t,t)

def flagCost (u b m : ℕ) := 1 + gjCost (u+b+m)

theorem flags_cmp (u b m : ℕ) :
    Cmp (Rows (Fin u ⊕ Fin b) (Fin m)) (Fin b) (flagCost u b m) extraFlag := by
  have h := (ccOption (matrixRoute (u:=u) (b:=b) (m:=m))).comp (cmp_gj (u+b+m))
  have output := h.comp (Cmp.wire (fun j : Fin b =>
    let t := (j.natAdd u).castAdd m
    (t,t)))
  rw [Nat.add_zero] at output
  exact output.congr (fun _ _ => rfl)

private theorem column_transport {n : ℕ} (U M : Matrix (Fin n) (Fin n) F) (j : Fin n) :
    U.mulVecLin (fun i => M i j) = fun i => (U * M) i j := rfl

theorem flags_spec {u b m : ℕ} (x : Rows (Fin u ⊕ Fin b) (Fin m) → Bool) :
    let g (i : Retained (extraFlag x)) := readRows x (.inr i.val)
    let E := span F (Set.range g)
    (spanBoth x).1 ⊔ E = (spanBoth x).1 ⊔ (spanBoth x).2 ∧
      Disjoint (spanBoth x).1 E ∧ LinearIndependent F g := by
  intro g E
  let D := u+b+m
  let M := pivotMatrix x
  let R := gj D M
  let e (j : Fin (u+b)) := j.castAdd m
  let a (j : Fin u) := e (j.castAdd b)
  let c (j : Fin b) := e (j.natAdd u)
  let h (j : Fin u ⊕ Fin b) := e (finSumFinEquiv j)
  have he₀ (i : Fin u) : h (.inl i) = a i := by rfl
  have he₁ (i : Fin b) : h (.inr i) = c i := by rfl
  obtain ⟨U,V,hU,hV⟩ := gj_equiv M
  let pad : (Fin m → F) →ₗ[F] (Fin D → F) :=
    LinearMap.pi fun i => if hi : i.val < m then LinearMap.proj ⟨i.val,hi⟩ else 0
  let trim : (Fin D → F) →ₗ[F] (Fin m → F) :=
    LinearMap.pi fun i => LinearMap.proj ⟨i.val,by have := i.isLt; omega⟩
  let f := U.mulVecLin.comp pad
  let rev := trim.comp V.mulVecLin
  have pad_col (j : Fin u ⊕ Fin b) : pad (readRows x j) = fun i => mat M i (h j) := by
    funext i
    have hj : (h j).val < u+b := (finSumFinEquiv j).isLt
    have he : finSumFinEquiv.symm ⟨(h j).val,hj⟩ = j :=
      finSumFinEquiv.symm_apply_apply j
    by_cases hi : i.val < m
    · simp [pad, LinearMap.pi_apply, hi, pivotMatrix, matrixRoute, hj, he, M, mat, b2z, readRows]
    · simp [pad, LinearMap.pi_apply, hi, pivotMatrix, matrixRoute, M, mat]
  have push (j : Fin u ⊕ Fin b) : f (readRows x j) = fun i => mat R i (h j) := by
    change U.mulVecLin (pad (readRows x j)) = _
    rw [pad_col, column_transport, ← hU]
  have pull (j : Fin u ⊕ Fin b) : rev (fun i => mat R i (h j)) = readRows x j := by
    change trim (V.mulVecLin _) = _
    rw [column_transport, ← hV, ← pad_col]
    funext i
    simp [trim, pad, LinearMap.pi_apply, i.isLt]
  have unit (j : Retained (extraFlag x)) : f (g j) = Pi.single (c j.val) (1 : F) := by
    change f (readRows x (.inr j.val)) = _
    rw [push,he₁]
    exact reduced_column M _ j.prop
  have hinj : Injective (fun j : Retained (extraFlag x) => c j.val) := by
    intro i j hj
    apply Subtype.ext
    apply Fin.ext
    have hh := congrArg (fun t : Fin D => t.val) hj
    change u+i.val.val = u+j.val.val at hh
    omega
  have vanishes (j : Retained (extraFlag x)) :
      (spanBoth x).1 ≤ LinearMap.ker ((LinearMap.proj (c j.val)).comp f) := by
    apply span_le.mpr
    rintro _ ⟨i,rfl⟩
    change f (readRows x (.inl i)) (c j.val) = 0
    rw [push,he₀]
    have hh : a i < c j.val := by
      change i.val < u+j.val.val
      have := i.isLt
      omega
    exact congrArg b2z (gj_upper M (c j.val) (a i) hh)
  have hspan : (spanBoth x).2 ≤ (spanBoth x).1 ⊔ E := by
    apply span_le.mpr
    rintro _ ⟨j,rfl⟩
    have exp := reduced_basis_expand M (show u+b ≤ D by omega) (finSumFinEquiv (.inr j))
    change (fun i => mat R i (h (.inr j))) = ∑ t : Fin (u+b),
      if R (e t,e t) then mat R (e t) (h (.inr j)) • (fun i => mat R i (e t)) else 0 at exp
    change readRows x (.inr j) ∈ (spanBoth x).1 ⊔ E
    rw [← pull (.inr j), exp, map_sum]
    apply Submodule.sum_mem
    intro t _
    have ht : t = finSumFinEquiv (finSumFinEquiv.symm t : Fin u ⊕ Fin b) :=
      (finSumFinEquiv.apply_symm_apply t).symm
    rw [ht]
    cases hs : (finSumFinEquiv.symm t : Fin u ⊕ Fin b) with
    | inl i =>
      split
      · rw [map_smul, ← show h (.inl i) = e (finSumFinEquiv (.inl i)) from rfl, pull]
        exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (subset_span ⟨i,rfl⟩))
      · rw [map_zero]
        exact Submodule.zero_mem _
    | inr i =>
      split
      · rename_i hi
        rw [map_smul, ← show h (.inr i) = e (finSumFinEquiv (.inr i)) from rfl, pull]
        exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (subset_span
          ⟨⟨i,hi⟩,rfl⟩))
      · rw [map_zero]
        exact Submodule.zero_mem _
  refine ⟨le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left hspan), ?_, ?_⟩
  · exact le_trans (span_mono (by rintro _ ⟨i,rfl⟩; exact ⟨i.val,rfl⟩)) le_sup_right
  · apply Submodule.disjoint_def.mpr
    intro v hv hv'
    obtain ⟨coeff,rfl⟩ := (mem_span_range_iff_exists_fun F).mp hv'
    have zero (j : Retained (extraFlag x)) : coeff j = 0 := by
      have eq := LinearMap.mem_ker.mp (vanishes j hv)
      change f (∑ i, coeff i • g i) (c j.val) = 0 at eq
      rw [map_sum] at eq
      simp only [map_smul,unit,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply] at eq
      rw [sum_eq_single j] at eq
      · simpa using eq
      · intro i _ hi
        exact by simp [Ne.symm (fun h => hi (hinj h))]
      · simp
    simp only [zero,zero_smul,sum_const_zero]
  · apply LinearIndependent.of_comp f
    simpa only [Function.comp_def,unit] using
      (Pi.linearIndependent_single_one (Fin D) F).comp _ hinj

end CompactJoin

namespace CompactJoin

open Donor

abbrev FlagInput (d m : ℕ) := GeneratorInput d m ⊕ (Fin 4 × MatrixRows d m)
abbrev FlagIndex (d : ℕ) := Fin 5 × Fin d

def inSpan {d m : ℕ} (x : FlagInput d m → Bool) (side : Fin 3) :=
  sourceSpan (x ∘ inl) side

def interRows {d m : ℕ} (x : FlagInput d m → Bool) (i : Fin 4) : MatrixRows d m → Bool :=
  fun j => x (.inr (i,j))

def interSpan {d m : ℕ} (x : FlagInput d m → Bool) (i : Fin 4) :=
  rowSpan (interRows x i)

def commonInput {d m : ℕ} (x : FlagInput d m → Bool) : Rows (Fin 0 ⊕ Fin d) (Fin m) → Bool :=
  fun (j,u) => elim Fin.elim0 (fun i => interRows x 3 (i,u)) j

def pairInput {d m : ℕ} (x : FlagInput d m → Bool) (c : Fin 3) :
    Rows (Fin d ⊕ Fin d) (Fin m) → Bool :=
  twoFamilies (interRows x 3) (interRows x c.castSucc)

def residualInput {d m : ℕ} (x : FlagInput d m → Bool) :
    Rows (Fin (d+d) ⊕ Fin d) (Fin m) → Bool :=
  twoFamilies (fun (j,u) => Fin.addCases (fun i => interRows x 1 (i,u))
    (fun i => interRows x 2 (i,u)) j) (sourceRows (x ∘ inl) 2)

def FlagBankCost (d m : ℕ) :=
  5 * max (flagCost 0 d m) (max (flagCost d d m) (flagCost (d+d) d m))

noncomputable def bankFlags {d m : ℕ} (x : FlagInput d m → Bool) (p : FlagIndex d) : Bool :=
  Fin.cases (extraFlag (residualInput x) p.2)
    (Fin.cases (extraFlag (commonInput x) p.2) (fun r => extraFlag (pairInput x r) p.2)) p.1

theorem bankFlags_cmp (d m : ℕ) :
    Cmp (FlagInput d m) (FlagIndex d) (FlagBankCost d m) bankFlags := by
  let S := max (flagCost 0 d m) (max (flagCost d d m) (flagCost (d+d) d m))
  have hb (i : Fin 5) : Cmp (FlagInput d m) (Fin d) S (fun x j => bankFlags x (i,j)) := by
    refine Fin.cases ?_ (fun e => ?_) i
    · let route : Rows (Fin (d+d) ⊕ Fin d) (Fin m) → FlagInput d m :=
        fun (j,u) => elim (fun l => Fin.addCases (fun k => .inr (1,k,u))
          (fun k => .inr (2,k,u)) l) (fun l => .inl (2,l,u)) j
      refine ((Cmp.sel route (flags_cmp (d+d) d m)).mono
        ((le_max_right _ _).trans (le_max_right _ _))).congr ?_
      intro x j
      change extraFlag (x ∘ route) j = extraFlag (residualInput x) j
      congr 1
      funext p
      rcases p with ⟨u|u,a⟩
      · induction u using Fin.addCases with
        | left k => simp [route,residualInput,twoFamilies,interRows]
        | right k => simp only [route, residualInput, twoFamilies, interRows, Function.comp_apply,
            elim_inl, Fin.addCases_right]
      · rfl
    · refine Fin.cases ?_ (fun i => ?_) e
      · let route : Rows (Fin 0 ⊕ Fin d) (Fin m) → FlagInput d m :=
          fun (j,u) => elim Fin.elim0 (fun k => .inr (3,k,u)) j
        refine ((Cmp.sel route (flags_cmp 0 d m)).mono (le_max_left _ _)).congr ?_
        intro x j
        change extraFlag (x ∘ route) j = extraFlag (commonInput x) j
        congr 1
        funext p
        rcases p with ⟨u|u,a⟩
        · exact Fin.elim0 u
        · rfl
      · let route : Rows (Fin d ⊕ Fin d) (Fin m) → FlagInput d m :=
          fun (j,u) => elim (fun k => .inr (3,k,u)) (fun k => .inr (i.castSucc,k,u)) j
        refine ((Cmp.sel route (flags_cmp d d m)).mono
          ((le_max_left _ _).trans (le_max_right _ _))).congr ?_
        intro x j
        change extraFlag (x ∘ route) j = extraFlag (pairInput x i) j
        congr 1
        funext p
        rcases p with ⟨u|u,a⟩ <;> rfl
  simpa only [FlagBankCost,card_fin,S] using Cmp.piU hb

lemma append_rows_span {d m : ℕ} (a b : MatrixRows d m → Bool) :
    rowSpan (fun (j,u) => Fin.addCases (fun i => a (i,u)) (fun i => b (i,u)) j) =
      rowSpan a ⊔ rowSpan b := by
  unfold rowSpan
  rw [← span_union]
  apply congrArg (span F)
  ext x
  constructor
  · rintro ⟨j,rfl⟩
    induction j using Fin.addCases with
    | left i =>
      exact Or.inl ⟨i, funext fun u => by simp [readRows]⟩
    | right i =>
      exact Or.inr ⟨i, funext fun u => by
        simp only [readRows, Fin.addCases_right]⟩
  · rintro (⟨j,rfl⟩ | ⟨j,rfl⟩)
    · exact ⟨j.castAdd d, funext fun u => by simp [readRows]⟩
    · exact ⟨j.natAdd d, funext fun u => by simp only [readRows, Fin.addCases_right]⟩

lemma common_spanBoth {d m : ℕ} (x : FlagInput d m → Bool) :
    spanBoth (commonInput x) = (⊥, interSpan x 3) := by
  apply Prod.ext
  · unfold spanBoth rowSpan
    have he : Set.range (readRows (fun p : Rows (Fin 0) (Fin m) => commonInput x (.inl p.1,p.2))) = ∅ := by
      ext v
      constructor
      · rintro ⟨j,_⟩
        exact Fin.elim0 j
      · simp
    rw [he, Submodule.span_empty]
  · rfl

lemma pair_spanBoth {d m : ℕ} (x : FlagInput d m → Bool) (c : Fin 3) :
    spanBoth (pairInput x c) = (interSpan x 3, interSpan x c.castSucc) := rfl

lemma residual_spanBoth {d m : ℕ} (x : FlagInput d m → Bool) :
    spanBoth (residualInput x) = (interSpan x 1 ⊔ interSpan x 2, inSpan x 2) := by
  unfold residualInput
  rw [spanTwoFamilies]
  exact Prod.ext (append_rows_span _ _) rfl

end CompactJoin

namespace CompactJoin

open Donor

lemma rowSpan_sum {J K U : Type} (a : Rows J U → Bool) (b : Rows K U → Bool) :
    rowSpan (twoFamilies a b) = rowSpan a ⊔ rowSpan b := by
  unfold rowSpan
  rw [← span_union]
  apply congrArg (span F)
  ext v
  constructor
  · rintro ⟨j|j,rfl⟩
    · exact Or.inl ⟨j,rfl⟩
    · exact Or.inr ⟨j,rfl⟩
  · rintro (⟨j,rfl⟩ | ⟨j,rfl⟩)
    · exact ⟨.inl j,rfl⟩
    · exact ⟨.inr j,rfl⟩

abbrev LiftIndex (d m : ℕ) := Bool × MatrixRows d m
abbrev Coefficients (d : ℕ) := Fin d × (Fin d ⊕ Fin d)

def liftCost (d m : ℕ) :=
  d*coordinateCost (Fin d ⊕ Fin d) (Fin m) + (2*d*m)*(d*5+1)

theorem lifts_cmp (d m : ℕ) :
    ∃ L : (GeneratorInput d m → Bool) → LiftIndex d m → Bool,
      Cmp _ _ (liftCost d m) L ∧ ∀ x (j : Fin d),
        readRows (fun p => L x (false,p)) j ∈ sourceSpan x 0 ∧
        readRows (fun p => L x (true,p)) j ∈ sourceSpan x 1 ∧
        (sourceSpan x 2 ≤ sourceSpan x 0 ⊔ sourceSpan x 1 →
          readRows (fun p => L x (false,p)) j + readRows (fun p => L x (true,p)) j =
          readRows (sourceRows x 2) j) := by
  obtain ⟨S,hS,hSol⟩ := coordinates_cmp (Fin d ⊕ Fin d) (Fin m)
  let route (j : Fin d) : Rows (Fin d ⊕ Fin d) (Fin m) ⊕ Fin m → GeneratorInput d m :=
    elim (fun (l,u) => l.elim (fun i => (0,i,u)) (fun i => (1,i,u))) (fun u => (2,j,u))
  let coeff (x : GeneratorInput d m → Bool) (p : Coefficients d) := S (x ∘ route p.1) p.2
  have hC : Cmp _ _ (d*coordinateCost (Fin d ⊕ Fin d) (Fin m)) coeff := by
    simpa only [card_fin,coeff,Function.comp_def] using Cmp.piU (fun j => Cmp.sel (route j) hS)
  let I := GeneratorInput d m ⊕ Coefficients d
  let side (b : Bool) : Fin 3 := if b then 1 else 0
  let col (b : Bool) (i : Fin d) : Fin d ⊕ Fin d := if b then .inr i else .inl i
  let vec (z : I → Bool) (p : LiftIndex d m) : F :=
    ∑ i : Fin d, b2z (z (.inr (p.2.1,col p.1 i))) * b2z (z (.inl (side p.1,i,p.2.2)))
  let f (z : I → Bool) (p : LiftIndex d m) := ctrlB (vec z p)
  have hf : Cmp _ _ ((2*d*m)*(d*5+1)) f := by
    have h (p : LiftIndex d m) : Cb I (d*5+1) (fun z => f z p) := by
      have v (i : I) : Cb I 0 (fun z => ctrlB (b2z (z i))) :=
        (Cb.var i).congr fun z => (ctrlB_F (z i)).symm
      simpa only [f,vec,card_fin] using ctrl_sum
        (fun i : Fin d => ctrl_mul (v (.inr (p.2.1,col p.1 i))) (v (.inl (side p.1,i,p.2.2))))
    simpa only [LiftIndex,MatrixRows,Rows,card_prod,card_bool,card_fin,mul_assoc]
      using Cmp.ofBits h
  let L (x : GeneratorInput d m → Bool) := f (elim x (coeff x))
  refine ⟨L, hC.keep.comp hf, ?_⟩
  intro x j
  have value (b : Bool) : readRows (fun p => L x (b,p)) j =
      ∑ i : Fin d, b2z (coeff x (j,col b i)) • readRows (sourceRows x (side b)) i := by
    funext u
    simp only [readRows,L,f,vec,sourceRows,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      elim_inl,elim_inr]
    exact ctrlF_B _
  have mem (b : Bool) : readRows (fun p => L x (b,p)) j ∈ sourceSpan x (side b) := by
    rw [value]
    exact (mem_span_range_iff_exists_fun F).mpr ⟨_,rfl⟩
  refine ⟨mem false,mem true,?_⟩
  intro hle
  let y := x ∘ route j
  have hY : rowSpan (y ∘ inl) = sourceSpan x 0 ⊔ sourceSpan x 1 := by
    have he : y ∘ inl = twoFamilies (sourceRows x 0) (sourceRows x 1) := by
      funext p
      rcases p with ⟨i|i,u⟩ <;> rfl
    rw [he, rowSpan_sum]
    rfl
  have hx : (fun u => b2z (y (.inr u))) ∈ rowSpan (y ∘ inl) := by
    rw [hY]
    apply hle
    exact subset_span ⟨j,rfl⟩
  have he := hSol y hx
  rw [Fintype.sum_sum_type] at he
  rw [value false,value true]
  exact he

end CompactJoin

namespace CompactJoin

open Donor

abbrev BlockInput (d m : ℕ) := FlagInput d m ⊕ LiftIndex d m
abbrev BlockRow (d : ℕ) := Fin 5 × Fin d

def fromBlock (side : Fin 3) (block : Fin 5) : Option (Fin 4 ⊕ Bool ⊕ Unit) :=
  (![
    ![some (.inr (.inl false)), some (.inl 3), some (.inl 0), some (.inl 1), none],
    ![some (.inr (.inl true)), some (.inl 3), some (.inl 0), none, some (.inl 2)],
    ![some (.inr (.inr ())), some (.inl 3), none, some (.inl 1), some (.inl 2)]
  ] : Fin 3 → Fin 5 → Option (Fin 4 ⊕ Bool ⊕ Unit)) side block

def blockWire {d m : ℕ} (side : Fin 3) (row : BlockRow d) (u : Fin m) : Option (BlockInput d m) :=
  (fromBlock side row.1).map fun pos =>
    pos.elim (fun j => .inl (.inr (j,row.2,u)))
      (elim (fun b => .inr (b,row.2,u)) (fun _ => .inl (.inl (2,row.2,u))))

def blockRows {d m : ℕ} (z : BlockInput d m → Bool) (side : Fin 3) :
    BlockRow d → Fin m → F :=
  fun row u => b2z ((blockWire side row u).elim false z)

def sourceCut {d m : ℕ} (z : BlockInput d m → Bool) (side : Fin 3) :=
  sourceSpan (z ∘ inl ∘ inl) side

def blockCoordCost (d m : ℕ) := 5*d*3*(1+coordinateCost (Fin d) (Fin m))

theorem blockCoordinates_cmp (d m : ℕ) :
    ∃ P : (BlockInput d m → Bool) → (Fin 3 × BlockRow d × Fin d) → Bool,
      Cmp _ _ (blockCoordCost d m) P ∧
      ∀ z side row, blockRows z side row ∈ sourceCut z side →
        (∑ j : Fin d, b2z (P z (side,row,j)) •
          readRows (sourceRows (z ∘ inl ∘ inl) side) j) = blockRows z side row := by
  obtain ⟨C,hC,hSol⟩ := coordinates_cmp (Fin d) (Fin m)
  let route (p : Fin 3 × BlockRow d) : Rows (Fin d) (Fin m) ⊕ Fin m → Option (BlockInput d m) :=
    elim (fun j => some (.inl (.inl (p.1,j)))) (fun u => blockWire p.1 p.2 u)
  let input (z : BlockInput d m → Bool) (p : Fin 3 × BlockRow d) (j : Rows (Fin d) (Fin m) ⊕ Fin m) :=
    (route p j).elim false z
  let G (p : Fin 3 × BlockRow d) (z : BlockInput d m → Bool) := C (input z p)
  have hG (p : Fin 3 × BlockRow d) : Cmp _ _ (1 + coordinateCost (Fin d) (Fin m)) (G p) :=
    (ccOption (route p)).comp hC
  let out (u : Fin 3 × BlockRow d × Fin d) : (Fin 3 × BlockRow d) × Fin d := ((u.1,u.2.1),u.2.2)
  refine ⟨fun z u => G (out u).1 z (out u).2, ?_, ?_⟩
  · have h := ctrl_rewire (Cmp.piU hG) out
    simpa only [blockCoordCost,BlockRow,card_prod,card_fin,
      Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using h
  · intro z side row h
    exact hSol (input z (side,row)) h

end CompactJoin

namespace CompactJoin

open Donor
open PEqualNP.Outside.L_meta_29774_aux

variable {d m : ℕ}

def interSpec (z : BlockInput d m → Bool) : Prop :=
  let x := z ∘ inl
  let A := sourceCut z 0
  let B := sourceCut z 1
  let C := sourceCut z 2
  interSpan x 0 = A ⊓ B ∧ interSpan x 1 = A ⊓ C ∧ interSpan x 2 = B ⊓ C ∧
  interSpan x 3 = Common A B C

def liftsSpec (z : BlockInput d m → Bool) : Prop :=
  ∀ j : Fin d,
    blockRows z 0 (0,j) ∈ sourceCut z 0 ∧
    blockRows z 1 (0,j) ∈ sourceCut z 1 ∧
    blockRows z 0 (0,j) + blockRows z 1 (0,j) = blockRows z 2 (0,j)

noncomputable def blockFlags (z : BlockInput d m → Bool) (i : Fin 5) : Fin d → Bool :=
  fun j => bankFlags (z ∘ inl) (i,j)

def blockCount (fl : Fin 5 → Fin d → Bool) (i : Fin 5) : ℕ := cnt (fl i) d

def blockGood (z : BlockInput d m → Bool) : Prop :=
  ∀ side row, blockRows z side row ∈ sourceCut z side

theorem rows_mem (z : BlockInput d m → Bool) (hi : interSpec z) (hl : liftsSpec z) :
    blockGood z := by
  dsimp only [interSpec] at hi
  obtain ⟨hAB,hAC,hBC,hT⟩ := hi
  have hU (i : Fin 4) (j : Fin d) : readRows (interRows (z ∘ inl) i) j ∈ interSpan (z ∘ inl) i :=
    subset_span ⟨j,rfl⟩
  intro s
  rintro ⟨b,i⟩
  have h0 : readRows (sourceRows (z ∘ inl ∘ inl) 2) i ∈ sourceCut z 2 :=
    subset_span ⟨i,rfl⟩
  fin_cases s <;> fin_cases b
  · exact (hl i).1
  · exact (hT ▸ hU 3 i).1.1
  · exact (hAB ▸ hU 0 i).1
  · exact (hAC ▸ hU 1 i).1
  · exact (sourceCut z 0).zero_mem
  · exact (hl i).2.1
  · exact (hT ▸ hU 3 i).1.2
  · exact (hAB ▸ hU 0 i).2
  · exact (sourceCut z 1).zero_mem
  · exact (hBC ▸ hU 2 i).1
  · exact h0
  · exact (hT ▸ hU 3 i).2
  · exact (sourceCut z 2).zero_mem
  · exact (hAC ▸ hU 1 i).2
  · exact (hBC ▸ hU 2 i).2

theorem independent_dimensions
    {T AB AC BC E : Type} [Fintype T] [Fintype AB] [Fintype AC] [Fintype BC] [Fintype E]
    (t : T → Fin m → F) (ab : AB → Fin m → F) (ac : AC → Fin m → F) (bc : BC → Fin m → F)
    {A B C : Submodule F (Fin m → F)}
    (ht : genSpan (K:=F) t = Common A B C)
    (hAB : genSpan (K:=F) t ⊔ genSpan (K:=F) ab = A ⊓ B)
    (hAC : genSpan (K:=F) t ⊔ genSpan (K:=F) ac = A ⊓ C)
    (hBC : genSpan (K:=F) t ⊔ genSpan (K:=F) bc = B ⊓ C)
    (tI : LinearIndependent F t) (abI : LinearIndependent F ab)
    (acI : LinearIndependent F ac) (bcI : LinearIndependent F bc)
    (tAB : Disjoint (genSpan (K:=F) t) (genSpan (K:=F) ab))
    (tAC : Disjoint (genSpan (K:=F) t) (genSpan (K:=F) ac))
    (tBC : Disjoint (genSpan (K:=F) t) (genSpan (K:=F) bc))
    (ra rb rc : E → Fin m → F)
    (rcI : LinearIndependent F rc)
    (hC : Side C A B ⊔ genSpan (K:=F) rc = C)
    (hCr : Disjoint (Side C A B) (genSpan (K:=F) rc))
    (hr : ∀ j, ra j ∈ A ∧ rb j ∈ B ∧ ra j + rb j = rc j)
    (lim : finrank F A ≤ d ∧ finrank F B ≤ d ∧ finrank F C ≤ d) :
    card E + card T + card AB + card AC ≤ d ∧
      card E + card T + card AB + card BC ≤ d ∧
      card E + card T + card AC + card BC ≤ d := by
  have dT : dim (genSpan (K:=F) t) = card T := (linearIndependent_iff_card_eq_finrank_span.mp tI).symm
  have rankSup {J : Type} [Fintype J] {x : J → Fin m → F}
      {U V : Submodule F (Fin m → F)} (h : U ⊔ genSpan (K:=F) x = V)
      (hd : Disjoint U (genSpan (K:=F) x)) (hi : LinearIndependent F x) :
      dim V = dim U + card J := by
    have H := U.finrank_sup_add_finrank_inf_eq (genSpan (K:=F) x)
    change dim (U ⊔ genSpan (K:=F) x) + dim (U ⊓ genSpan (K:=F) x) =
      dim U + dim (genSpan (K:=F) x) at H
    have hb : dim (⊥ : Submodule F (Fin m → F)) = 0 := finrank_bot F _
    have hx : dim (genSpan (K:=F) x) = card J :=
      (linearIndependent_iff_card_eq_finrank_span.mp hi).symm
    rwa [h, hd.eq_bot, hb, add_zero, hx] at H
  have hle : C ≤ A ⊔ B := by
    rw [← hC]
    refine sup_le (sup_le (inf_le_right.trans le_sup_left)
      (inf_le_right.trans le_sup_right)) (span_le.mpr ?_)
    rintro _ ⟨j,rfl⟩
    obtain ⟨ha,hb,he⟩ := hr j
    exact he ▸ Submodule.add_mem_sup ha hb
  obtain ⟨h₁,h₂,h₃⟩ := common_counts A B C hle
    (ht ▸ dT) ((rankSup hAB tAB abI).trans (congrArg (· + _) dT))
    ((rankSup hAC tAC acI).trans (congrArg (· + _) dT))
    ((rankSup hBC tBC bcI).trans (congrArg (· + _) dT)) (rankSup hC hCr rcI)
  exact ⟨h₁.trans lim.1, h₂.trans lim.2.1, h₃.trans lim.2.2⟩

def fieldBlocks (fl : Fin 5 → Fin d → Bool)
    (x y z : Fin 5 → Fin d → F) : Prop :=
  (∀ i, fl 0 i = true → x 0 i + y 0 i = z 0 i) ∧
  (∀ i, fl 1 i = true → x 1 i = z 1 i ∧ y 1 i = z 1 i) ∧
  (∀ i, fl 3 i = true → x 3 i = z 3 i) ∧
  (∀ i, fl 2 i = true → x 2 i = y 2 i) ∧
  (∀ i, fl 4 i = true → y 4 i = z 4 i)

set_option maxRecDepth 800 in
theorem joint_block_spec (z : BlockInput d m → Bool) (hi : interSpec z) (hl : liftsSpec z)
    :
    fitsW d (blockCount (blockFlags z)) ∧
    ∀ f g h : Dual (Fin m → F),
      (∃ a : Dual (Fin m → F),
        (∀ v ∈ sourceCut z 0, a v = f v) ∧ (∀ v ∈ sourceCut z 1, a v = g v) ∧
        ∀ v ∈ sourceCut z 2, a v = h v) ↔
      fieldBlocks (blockFlags z) (fun b i => f (blockRows z 0 (b,i)))
        (fun b i => g (blockRows z 1 (b,i))) (fun b i => h (blockRows z 2 (b,i))) := by
  let x := z ∘ inl
  let A := sourceCut z 0
  let B := sourceCut z 1
  let C := sourceCut z 2
  let fl := blockFlags z
  let t (j : Retained (extraFlag (commonInput x))) := readRows (commonInput x) (.inr j.val)
  let ab (j : Retained (extraFlag (pairInput x 0))) := readRows (pairInput x 0) (.inr j.val)
  let ac (j : Retained (extraFlag (pairInput x 1))) := readRows (pairInput x 1) (.inr j.val)
  let bc (j : Retained (extraFlag (pairInput x 2))) := readRows (pairInput x 2) (.inr j.val)
  let e (s : Fin 3) (j : Retained (extraFlag (residualInput x))) := blockRows z s (0,j.val)
  obtain ⟨pAB,pAC,pBC,pT⟩ := hi
  have ht : genSpan (K:=F) t = Common A B C ∧ LinearIndependent F t := by
    have ht := flags_spec (commonInput x)
    dsimp only at ht
    rw [common_spanBoth] at ht
    have he : genSpan (K:=F) t = interSpan x 3 := by
      simpa only [Prod.fst,Prod.snd,bot_sup_eq] using ht.1
    exact ⟨he.trans pT, ht.2.2⟩
  have hspanT : genSpan (K:=F) t = interSpan x 3 := ht.1.trans pT.symm
  have pair (i : Fin 3) (U : Submodule F (Fin m → F))
      (hU : interSpan x i.castSucc = U) (hTU : Common A B C ≤ U) :
      let v (j : Retained (extraFlag (pairInput x i))) :=
        readRows (pairInput x i) (.inr j.val)
      genSpan (K:=F) t ⊔ genSpan (K:=F) v = U ∧
        Disjoint (genSpan (K:=F) t) (genSpan v) ∧ LinearIndependent F v := by
    have h := flags_spec (pairInput x i)
    dsimp only at h
    rw [pair_spanBoth] at h
    have hle : interSpan x 3 ≤ U := pT.symm ▸ hTU
    rw [hU, sup_eq_right.mpr hle, ← hspanT] at h
    exact h
  have abd := pair 0 _ pAB inf_le_left
  have acd := pair 1 _ pAC (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have bcd := pair 2 _ pBC (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have ec : Side C A B ⊔ genSpan (K:=F) (e 2) = C ∧ Disjoint (Side C A B) (genSpan (K:=F) (e 2)) ∧
      LinearIndependent F (e 2) := by
    have h := flags_spec (residualInput x)
    dsimp only at h
    rw [residual_spanBoth] at h
    simp only [Prod.fst,Prod.snd] at h
    rw [pAC,pBC,inf_comm A C,inf_comm B C] at h
    have he : Side C A B ≤ C := sup_le inf_le_left inf_le_left
    change Side C A B ⊔ _ = Side C A B ⊔ C ∧ _ at h
    rw [sup_eq_right.mpr he] at h
    exact h
  have lim (s : Fin 3) : finrank F (sourceCut z s) ≤ d := by
    exact (finrank_range_le_card (readRows (sourceRows (z ∘ inl ∘ inl) s))).trans_eq
      (card_fin d)
  have he (j : Retained (extraFlag (residualInput x))) : e 0 j ∈ A ∧ e 1 j ∈ B ∧ e 0 j + e 1 j = e 2 j := hl j.val
  refine ⟨?_,?_⟩
  · have h := independent_dimensions t ab ac bc ht.1 abd.1 acd.1 bcd.1
      ht.2 abd.2.2 acd.2.2 bcd.2.2 abd.2.1 acd.2.1 bcd.2.1
      (e 0) (e 1) (e 2) ec.2.2 ec.1 ec.2.1 he ⟨lim 0,lim 1,lim 2⟩
    change cnt (extraFlag (residualInput x)) d + cnt (extraFlag (commonInput x)) d +
        cnt (extraFlag (pairInput x 0)) d + cnt (extraFlag (pairInput x 1)) d ≤ d ∧
      cnt (extraFlag (residualInput x)) d + cnt (extraFlag (commonInput x)) d +
        cnt (extraFlag (pairInput x 0)) d + cnt (extraFlag (pairInput x 2)) d ≤ d ∧
      cnt (extraFlag (residualInput x)) d + cnt (extraFlag (commonInput x)) d +
        cnt (extraFlag (pairInput x 1)) d + cnt (extraFlag (pairInput x 2)) d ≤ d
    simpa only [retained_card] using h
  · intro f g h
    have hGl (v : Dual A) (w : Dual B)
        (agree : ∀ x : ↥(A ⊓ B), v ⟨x,x.prop.1⟩ = w ⟨x,x.prop.2⟩) :
        ∃ a : Dual (Fin m → F), a.comp A.subtype = v ∧ a.comp B.subtype = w :=
      extend_agree A B v w (LinearMap.ext agree)
    have hs := cut_agreement t ab ac bc (e 0) (e 1) (e 2) ht.1 abd.1 acd.1 bcd.1 ec.1
      (fun i => (he i).1) (fun i => (he i).2.1) (fun i => (he i).2.2) f g h hGl
    refine hs.trans ?_
    simp only [fieldBlocks, Retained, Subtype.forall]
    rfl

end CompactJoin

namespace CompactJoin

open Donor

variable {d : ℕ}

abbrev PackedRows (d : ℕ) := Fin (d+d+d+d+d)

def packedFlags (fl : Fin 5 → Fin d → Bool) (s : Fin 3) : PackedRows d → Bool :=
  ceCat (fl 0) (fl 1) (if s = 1 then fun _ => false else fl 3)
    (if s = 2 then fun _ => false else fl 2) (if s = 0 then fun _ => false else fl 4)

def packedIndex (d : ℕ) : PackedRows d → BlockRow d :=
  ceCat (fun i => (0,i)) (fun i => (1,i)) (fun i => (3,i)) (fun i => (2,i)) (fun i => (4,i))

def packedPayload (P : Fin 3 × BlockRow d × Fin d → Bool) (s : Fin 3) :
    PackedRows d × Fin d → Bool := fun (i,j) => P (s,packedIndex d i,j)

def packedMatrices (fl : Fin 5 → Fin d → Bool) (P : Fin 3 × BlockRow d × Fin d → Bool)
    (s : Fin 3) : Fin d × Fin d → Bool :=
  ctrlPacked d (packedFlags fl s) (packedPayload P s)

theorem packedSlots (fl : Fin 5 → Fin d → Bool) (P : Fin 3 × BlockRow d × Fin d → Bool)
    (x : Fin 3 → V d) (val : Fin 3 → Fin 5 → Fin d → F)
    (fit : fitsW d (blockCount fl))
    (hv : ∀ s b i, (∑ j : Fin d, b2z (P (s,(b,i),j)) * x s j) = val s b i) :
    let v := fun s => (mat (packedMatrices fl P s)).mulVec (x s)
    Std d (blockCount fl 0) (blockCount fl 1) (blockCount fl 2) (blockCount fl 3)
      (blockCount fl 4) (v 0) (v 1) (v 2) ↔ fieldBlocks fl (val 0) (val 1) (val 2) := by
  intro v
  let n := blockCount fl
  have hg (s : Fin 3) : cnt (packedFlags fl s) (d+d+d+d+d) ≤ d := by
    rcases fit with ⟨f₀,f₁,f₂⟩
    fin_cases s <;> simp only [packedFlags,ceCat,swCntAppendAll,swCntFalse] <;>
      change _ ≤ d <;> norm_num <;> simp only [n,blockCount,swCntFalse, add_zero, zero_add] at * <;> omega
  let slot : ceSeg d d → BlockRow d := ceChoose (fun i : Fin d => (0,i)) (fun i => (1,i)) (fun i => (3,i))
      (fun i => (2,i)) (fun i => (4,i))
  have valAt (s : Fin 3) (p : ceSeg d d) (h : packedFlags fl s (cePos p) = true) :
      co (v s) (cnt (packedFlags fl s) (cePos p).val) = val s (slot p).1 (slot p).2 := by
    have he := ceHit (packedFlags fl s) (packedPayload P s) (x s) (hg s) (cePos p) h
    change co (v s) _ = _ at he
    rw [he]
    change (∑ j : Fin d, b2z (P (s,packedIndex d (cePos p),j)) * x s j) = _
    rw [show packedIndex d (cePos p) = slot p from ceCat_pos _ _ _ _ _ p]
    exact hv _ _ _
  have tail (s : Fin 3) (i : Fin d)
      (h : cnt (packedFlags fl s) (d+d+d+d+d) ≤ i.val) : v s i = 0 :=
    ceTail (packedFlags fl s) (packedPayload P s) (x s) i h
  let atSlot (b : Fin 5) (i : Fin d) : ceSeg d d :=
    ![inl i, .inr (.inl i), .inr (.inr (.inr (.inl i))),
      .inr (.inr (.inl i)), .inr (.inr (.inr (.inr i)))] b
  have hit (s : Fin 3 × Fin 5) (u : Fin d) (hh : fl s.2 u = true)
      (hs : fromBlock s.1 s.2 ≠ none) :
      co (v s.1) (cnt (packedFlags fl s.1) (cePos (atSlot s.2 u)).val) = val s.1 s.2 u := by
    rcases s with ⟨s,b⟩
    have he : packedFlags fl s (cePos (atSlot b u)) = true := by
      fin_cases s <;> fin_cases b <;>
        simp_all [packedFlags,atSlot,fromBlock,ceCat_pos,ceChoose]
    refine (valAt s (atSlot b u) he).trans ?_
    fin_cases b <;> rfl
  have hx (i : Fin d) (hi : fl 0 i = true) :
      co (v 0) (cnt (fl 0) i.val) + co (v 1) (cnt (fl 0) i.val) =
          co (v 2) (cnt (fl 0) i.val) ↔ val 0 0 i + val 1 0 i = val 2 0 i := by
    have he (s : Fin 3) : co (v s) (cnt (fl 0) i.val) = val s 0 i := by
      simpa [atSlot,ceCat_cnt,ceRank,ceChoose,packedFlags] using
        hit (s,0) i hi (by fin_cases s <;> decide)
    rw [he 0,he 1,he 2]
  have get (s : Fin 3) (b : Fin 5) (i : Fin d) (h : fl b i = true) (hs : fromBlock s b ≠ none) :=
    hit (s,b) i h hs
  have hy (s : Fin 3) (i : Fin d) (hi : fl 1 i = true) :
      co (v s) (n 0 + cnt (fl 1) i.val) = val s 1 i := by
    simpa [packedFlags,atSlot,ceCat_cnt,ceRank,ceChoose,n,blockCount] using
      get s 1 i hi (by fin_cases s <;> decide)
  have c1 (i : Fin d) (hi : fl 3 i = true) :
      co (v 0) (n 0 + n 1 + cnt (fl 3) i.val) = val 0 3 i ∧
      co (v 2) (n 0 + n 1 + cnt (fl 3) i.val) = val 2 3 i := by
    simpa [packedFlags,atSlot,ceCat_cnt,ceRank,ceChoose,n,blockCount] using
      And.intro (get 0 3 i hi (by decide)) (get 2 3 i hi (by decide))
  have c2 (i : Fin d) (hi : fl 2 i = true) :
      co (v 0) (n 0 + n 1 + n 3 + cnt (fl 2) i.val) = val 0 2 i ∧
      co (v 1) (n 0 + n 1 + cnt (fl 2) i.val) = val 1 2 i := by
    simpa [packedFlags,atSlot,ceCat_cnt,ceRank,ceChoose,n,blockCount,swCntFalse] using
      And.intro (get 0 2 i hi (by decide)) (get 1 2 i hi (by decide))
  have c3 (i : Fin d) (hi : fl 4 i = true) :
      co (v 1) (n 0 + n 1 + n 2 + cnt (fl 4) i.val) = val 1 4 i ∧
      co (v 2) (n 0 + n 1 + n 3 + cnt (fl 4) i.val) = val 2 4 i := by
    simpa [packedFlags,atSlot,ceCat_cnt,ceRank,ceChoose,n,blockCount,swCntFalse] using
      And.intro (get 1 4 i hi (by decide)) (get 2 4 i hi (by decide))
  have tails :
      (∀ i : Fin d, n 0 + n 1 + n 3 + n 2 ≤ i.val → v 0 i = 0) ∧
      (∀ i : Fin d, n 0 + n 1 + n 2 + n 4 ≤ i.val → v 1 i = 0) ∧
      (∀ i : Fin d, n 0 + n 1 + n 3 + n 4 ≤ i.val → v 2 i = 0) := by
    exact ⟨fun i h => tail 0 i (by simpa [packedFlags,ceCat,swCntAppendAll,swCntFalse,n,blockCount] using h),
      fun i h => tail 1 i (by simpa [packedFlags,ceCat,swCntAppendAll,swCntFalse,n,blockCount] using h),
      fun i h => tail 2 i (by simpa [packedFlags,ceCat,swCntAppendAll,swCntFalse,n,blockCount] using h)⟩
  change Std d (n 0) (n 1) (n 2) (n 3) (n 4) (v 0) (v 1) (v 2) ↔ _
  unfold Std fieldBlocks
  rw [and_iff_left tails]
  refine and_congr (swRankQuant (fl 0) _ _ hx) (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_)))
  · exact swRankQuant (fl 1) _ _ (fun i h => by rw [hy 0 i h,hy 1 i h,hy 2 i h])
  · exact swRankQuant (fl 3) _ _ (fun i h => by rw [(c1 i h).1,(c1 i h).2])
  · exact swRankQuant (fl 2) _ _ (fun i h => by rw [(c2 i h).1,(c2 i h).2])
  · exact swRankQuant (fl 4) _ _ (fun i h => by rw [(c3 i h).1,(c3 i h).2])

end CompactJoin

namespace CompactJoin

open Donor

def prepareCost (d m : ℕ) := 8*interCost d m + liftCost d m

theorem prepare_blocks (d m : ℕ) :
    ∃ P : (GeneratorInput d m → Bool) → BlockInput d m → Bool,
      Cmp _ _ (prepareCost d m) P ∧
      ∀ x,
        (P x ∘ inl ∘ inl = x) ∧ interSpec (P x) ∧
        (sourceSpan x 2 ≤ sourceSpan x 0 ⊔ sourceSpan x 1 → liftsSpec (P x)) := by
  obtain ⟨I,hI,hIS⟩ := allIntersections_cmp d m
  obtain ⟨L,hL,hLS⟩ := lifts_cmp d m
  let P (x : GeneratorInput d m → Bool) : BlockInput d m → Bool :=
    elim (elim x (I x)) (L x)
  refine ⟨P,hI.keep.pair hL,?_⟩
  intro x
  refine ⟨rfl,?_,?_⟩
  · have h := hIS x
    exact ⟨h.1 0,h.1 1,h.1 2,h.2⟩
  · intro hSrc j
    obtain ⟨ha,hb,hc⟩ := hLS x j
    exact ⟨ha,hb,hc hSrc⟩

def packRowsCost (d : ℕ) :=
    1+((d+d+d+d+d)+1)*((d+1)*6)+(card (Fin d × Fin d))*((d+d+d+d+d)*3+1)

private theorem cePos_surjective (d : ℕ) : Surjective (cePos (b:=d) (c:=d)) := by
  intro j
  induction j using Fin.addCases with
  | left j =>
    induction j using Fin.addCases with
    | left j =>
      induction j using Fin.addCases with
      | left j =>
        induction j using Fin.addCases with
        | left j => exact ⟨.inl j,rfl⟩
        | right j => exact ⟨.inr (.inl j),rfl⟩
      | right j => exact ⟨.inr (.inr (.inl j)),rfl⟩
    | right j => exact ⟨.inr (.inr (.inr (.inl j))),rfl⟩
  | right j => exact ⟨.inr (.inr (.inr (.inr j))),rfl⟩

theorem pack_rows_cmp {I : Type} {d m : ℕ}
    (C : (BlockInput d m → Bool) → (Fin 3 × BlockRow d × Fin d) → Bool)
    (hC : Cmp _ _ (blockCoordCost d m) C)
    (Z : (I → Bool) → BlockInput d m → Bool) {S : ℕ} (hZ : Cmp _ _ S Z) (s : Fin 3) :
    Cmp I (Fin d × Fin d)
      (S + (FlagBankCost d m + blockCoordCost d m + packRowsCost d))
      (fun x => packedMatrices (blockFlags (Z x)) (C (Z x)) s) := by
  let a : PackedRows d → FlagIndex d := packedIndex d
  let f (x : BlockInput d m → Bool) := packedFlags (blockFlags x) s
  let route (j : PackedRows d) : Option (FlagIndex d) :=
    if (fromBlock s (a j).1).isSome then some (a j) else none
  have hfa (x : BlockInput d m → Bool) (j : PackedRows d) :
      f x j = (route j).elim false (bankFlags (x ∘ inl)) := by
    obtain ⟨i,rfl⟩ := cePos_surjective d j
    simp only [f, packedFlags, route, a, packedIndex, ceCat_pos]
    rcases i with i|i|i|i|i <;> fin_cases s <;>
      simp [fromBlock,blockFlags,ceChoose]
  have hf : Cmp (BlockInput d m) (PackedRows d) (FlagBankCost d m+1) f := by
    exact ((Cmp.sel inl (bankFlags_cmp d m)).comp (ccOption route)).congr (fun x j => (hfa x j).symm)
  let b : PackedRows d × Fin d → Fin 3 × BlockRow d × Fin d :=
    fun p => (s,packedIndex d p.1,p.2)
  have h := ctrl_pack (K:=d) hf (ctrl_rewire hC b)
  have hh : Cmp (BlockInput d m) (Fin d × Fin d)
      (FlagBankCost d m + blockCoordCost d m + packRowsCost d)
      (fun x => packedMatrices (blockFlags x) (C x) s) := by
    refine (h.mono ?_).congr (fun _ _ => rfl)
    unfold packRowsCost
    simp only [card_prod,card_fin]
    omega
  exact hZ.comp hh

end CompactJoin

namespace CompactJoin

open Donor

theorem valid_eqns {J U : Type} [Fintype J] [DecidableEq J]
    {d : ℕ} (R : J → U → F) (G : Fin d → J → F)
    (hG : span F (Set.range G) = LinearMap.ker (Fintype.linearCombination F R))
    (x : J → F) :
    (∃ f : Dual (U → F), ∀ j, f (R j) = x j) ↔ ∀ i, dotProduct x (G i) = 0 := by
  rw [evalRange]
  have hm (a : J → F) :
      a ∈ span F (Set.range G) ↔ (∑ j, a j • R j) = 0 := by
    rw [hG, LinearMap.mem_ker, Fintype.linearCombination_apply]
  constructor
  · intro h i
    exact h _ ((hm _).mp (subset_span ⟨i,rfl⟩))
  · intro h a ha
    let f := dotProductEquiv F J x
    have hs : span F (Set.range G) ≤ LinearMap.ker f :=
      span_le.mpr (by rintro _ ⟨i,rfl⟩; exact h i)
    exact hs ((hm _).mpr ha)

def validCost (d m : ℕ) := nullPrepCost (Fin d) (Fin m) d + 1 + 2^d*(d*(d*6+7)+1)

theorem valid_cmp (d m : ℕ) :
    ∃ V : (Rows (Fin d) (Fin m) → Bool) → (Fin d → F) → Bool,
      Cmp _ _ (validCost d m) V ∧ ∀ x a, V x a = true ↔
        ∃ f : Dual (Fin m → F), ∀ i, f (readRows x i) = a i := by
  obtain ⟨P,hP,hS⟩ := nullPrep (J:=Fin d) (U:=Fin m) d (by simp)
  let route (p : Fin d × Fin (d+1)) : Option (NullOut (Fin d) d) :=
    Fin.lastCases none (fun j => some (j,p.1)) p.2
  let E (x : NullOut (Fin d) d → Bool) (p : Fin d × Fin (d+1)) :=
    (route p).elim false x
  refine ⟨fun x => ctrlSat (E (P x)),?_,?_⟩
  · simpa only [validCost,card_fin] using ctrl_pin (hP.comp (ccOption route))
  · intro x a
    rw [valid_eqns (readRows x) (nullOutGen (P x)) (hS x)]
    simp only [ctrlSat, decide_eq_true_eq]
    apply forall_congr'
    intro i
    change (∑ j, ctrlF (E (P x) (i,j.castSucc)) * a j) =
      ctrlF (E (P x) (i,Fin.last d)) ↔ dotProduct a (nullOutGen (P x) i) = 0
    simp only [E, route, Fin.lastCases_castSucc, Fin.lastCases_last, Option.elim_some,
      Option.elim_none, nullOutGen, ctrlF, b2z, Bool.false_eq_true, ite_false, dotProduct, mul_comm]

end CompactJoin

namespace CompactJoin

open Donor
open PEqualNP.Outside.L_meta_29774_aux

variable {d m : ℕ}

def triples {d m : ℕ} (x : GeneratorInput d m → Bool) (u v w : V d) : Prop :=
  TripleRelation (readRows (sourceRows x 0)) (readRows (sourceRows x 1))
    (readRows (sourceRows x 2)) u v w

theorem prepared_sem (z : BlockInput d m → Bool) (hi : interSpec z) (hl : liftsSpec z)
    (C : Fin 3 × BlockRow d × Fin d → Bool)
    (hC : ∀ s b, (∑ j : Fin d, b2z (C (s,b,j)) •
      readRows (sourceRows (z ∘ inl ∘ inl) s) j) = blockRows z s b)
    (A : Fin 3 → V d → Bool)
    (hA : ∀ s x, A s x = true ↔
      ∃ a : Dual (Fin m → F), ∀ j : Fin d, a (readRows (sourceRows (z ∘ inl ∘ inl) s) j) = x j) :
    let fl := blockFlags z
    let n := blockCount fl
    let p := packedMatrices fl C
    fitsW d n ∧ ∀ u v w : V d,
      triples (z ∘ inl ∘ inl) u v w ↔ A 0 u = true ∧ A 1 v = true ∧ A 2 w = true ∧
      Std d (n 0) (n 1) (n 2) (n 3) (n 4)
        ((mat (p 0)).mulVec u) ((mat (p 1)).mulVec v) ((mat (p 2)).mulVec w) := by
  intro fl n p
  obtain ⟨hfit,hStd⟩ := joint_block_spec z hi hl
  refine ⟨hfit,fun u v w => ?_⟩
  let x : Fin 3 → V d := ![u,v,w]
  let G (s : Fin 3) := readRows (sourceRows (z ∘ inl ∘ inl) s)
  have hs (f : Fin 3 → Dual (Fin m → F)) (hf : ∀ s j, f s (G s j) = x s j) :
      Std d (n 0) (n 1) (n 2) (n 3) (n 4)
        ((mat (p 0)).mulVec u) ((mat (p 1)).mulVec v) ((mat (p 2)).mulVec w) ↔
        fieldBlocks fl (fun b i => f 0 (blockRows z 0 (b,i)))
          (fun b i => f 1 (blockRows z 1 (b,i))) (fun b i => f 2 (blockRows z 2 (b,i))) := by
    apply packedSlots fl C x (fun s b i => f s (blockRows z s (b,i))) hfit
    intro s b i
    rw [← hC s (b,i), map_sum]
    exact sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul, hf s j]
  constructor
  · rintro ⟨a,h0,h1,h2⟩
    refine ⟨(hA 0 u).mpr ⟨a,h0⟩,(hA 1 v).mpr ⟨a,h1⟩,(hA 2 w).mpr ⟨a,h2⟩,?_⟩
    apply (hs (fun _ => a) (fun s => ?_)).mpr
    · exact (hStd a a a).mp ⟨a,fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
    · fin_cases s
      · exact h0
      · exact h1
      · exact h2
  · rintro ⟨au,av,aw,hr⟩
    obtain ⟨a,ha⟩ := (hA 0 u).mp au
    obtain ⟨b,hb⟩ := (hA 1 v).mp av
    obtain ⟨c,hc⟩ := (hA 2 w).mp aw
    let f : Fin 3 → Dual (Fin m → F) := ![a,b,c]
    have hmatch (s : Fin 3) : ∀ j, f s (G s j) = x s j := by
      fin_cases s
      · exact ha
      · exact hb
      · exact hc
    have field := (hs f hmatch).mp hr
    obtain ⟨p,hp0,hp1,hp2⟩ := (hStd a b c).mpr field
    have mem (s : Fin 3) (j : Fin d) : G s j ∈ sourceCut z s := subset_span ⟨j,rfl⟩
    exact ⟨p,fun j => (hp0 _ (mem 0 j)).trans (ha j),fun j => (hp1 _ (mem 1 j)).trans (hb j),
      fun j => (hp2 _ (mem 2 j)).trans (hc j)⟩

end CompactJoin

namespace CompactJoin

open Donor

abbrev RowMap (d : ℕ) := Fin d × Fin d

def padColumn {d : ℕ} (K : RowMap d → Bool) : Fin d × Fin (d+1) → Bool :=
  fun (i,n) => Fin.lastCases false (fun j => K (i,j)) n

lemma padColumn_cmp {d : ℕ} : Cmp (RowMap d) (Fin d × Fin (d+1)) 1 padColumn := by
  let wiring (p : Fin d × Fin (d+1)) : Option (RowMap d) :=
    Fin.lastCases none (fun j => some (p.1,j)) p.2
  apply (ccOption wiring).congr
  rintro K ⟨i,n⟩
  refine Fin.lastCases ?_ (fun j => ?_) n <;> simp [wiring, padColumn]

lemma padColumn_eq {d : ℕ} (K : RowMap d → Bool) (v : V d) :
    ctrlAffine (padColumn K) v = (mat K).mulVec v := by
  funext i
  unfold ctrlAffine
  simp only [Matrix.mulVec, dotProduct, mat]
  rw [Fin.sum_univ_castSucc]
  simp only [padColumn, Fin.lastCases_castSucc, Fin.lastCases_last,
    Fin.snoc_castSucc, Fin.snoc_last, Bool.false_eq_true, ite_false, zero_mul, add_zero]

theorem cast_std {b d : ℕ} (h : b = d) (n : Fin 5 → ℕ)
    (L M E : RowMap d → Bool) (x y z : V d) :
    Std b (n 0) (n 1) (n 2) (n 3) (n 4)
      (ctrlAffine (fun p => padColumn L (Fin.cast h p.1,p.2)) x)
      (ctrlAffine (fun p => padColumn M (Fin.cast h p.1,p.2)) y)
      ((mat (fun p => E (Fin.cast h p.1,p.2))).mulVec z) ↔
    Std d (n 0) (n 1) (n 2) (n 3) (n 4)
      ((mat L).mulVec x) ((mat M).mulVec y) ((mat E).mulVec z) := by
  subst b
  simp only [Fin.cast_refl]
  change Std d (n 0) (n 1) (n 2) (n 3) (n 4) (ctrlAffine (padColumn L) x)
    (ctrlAffine (padColumn M) y) ((mat E).mulVec z) ↔ _
  rw [padColumn_eq,padColumn_eq]

def dimsCost (d m : ℕ) := (5*(d+1))*(FlagBankCost d m+(d+1)*((d+1)*6))

theorem dims_cmp (d m : ℕ) :
    Cmp (BlockInput d m) (Fin 5 × Fin (d+1)) (dimsCost d m)
      (fun x p => decide (blockCount (blockFlags x) p.1 = p.2.val)) := by
  have h (p : Fin 5 × Fin (d+1)) :
      Cb (BlockInput d m) (FlagBankCost d m+(d+1)*((d+1)*6))
        (fun x => decide (blockCount (blockFlags x) p.1 = p.2.val)) := by
    have hf := ctrl_rewire
      (Cmp.sel (inl : FlagInput d m → BlockInput d m) (bankFlags_cmp d m))
      (fun j : Fin d => (p.1,j))
    have hc := Cb.comp (hf.comp (cmp_counter d p.2.val)) (Cb.var (Fin.last d, Fin.last p.2.val))
    have hh : p.2.val+1 ≤ d+1 := Nat.succ_le_of_lt p.2.isLt
    have hb := Nat.add_le_add_left
      (Nat.mul_le_mul_left (d+1) (Nat.mul_le_mul_right 6 hh)) (FlagBankCost d m)
    exact (hc.mono hb).congr (fun _ => rfl)
  have h' := Cmp.ofBits (F := fun (x : BlockInput d m → Bool) (p : Fin 5 × Fin (d+1)) =>
    decide (blockCount (blockFlags x) p.1 = p.2.val)) h
  simpa only [dimsCost,card_prod,card_fin] using h'

def generatorWire {d m t : ℕ} (p : GeneratorInput d m) : In0 d d d m t :=
  let j := p.2.1
  let columns : Fin 3 → Fin (d+d+d) :=
    ![nx (b:=d) (c:=d) j, ny (a:=d) (c:=d) j, nz (a:=d) (b:=d) j]
  .inl (p.2.2,(columns p.1).castSucc)

def generatorsOf {d m t : ℕ} (v : In0 d d d m t → Bool) : GeneratorInput d m → Bool :=
  v ∘ generatorWire

def inputRows {d m : ℕ} (H : Fin m → V d × V d × V d) (s : Fin 3) (j : Fin d) (i : Fin m) : F :=
  (![ (H i).1, (H i).2.1, (H i).2.2 ] : Fin 3 → V d) s j

theorem decoded_generators {d m t : ℕ} (H : Fin m → V d × V d × V d)
    (r : Fin m → F) (f g : Fin (2^d) → Fin (2^t)) (s : Fin 3) :
    readRows (sourceRows (generatorsOf (inpOf H r f g)) s) = inputRows H s := by
  funext j i
  fin_cases s
  · change b2z (inpOf H r f g (.inl (i,(nx (b:=d) (c:=d) j).castSucc))) = (H i).1 j
    simp only [inpOf, elim_inl, Fin.val_castSucc, dif_pos (nx (b:=d) (c:=d) j).isLt]
    exact (zbit_decode _).trans (ft_join_nx _ _)
  · change b2z (inpOf H r f g (.inl (i,(ny (a:=d) (c:=d) j).castSucc))) = (H i).2.1 j
    simp only [inpOf, elim_inl, Fin.val_castSucc, dif_pos (ny (a:=d) (c:=d) j).isLt]
    exact (zbit_decode _).trans (ft_join_ny _ _)
  · change b2z (inpOf H r f g (.inl (i,(nz (a:=d) (b:=d) j).castSucc))) = (H i).2.2 j
    simp only [inpOf, elim_inl, Fin.val_castSucc, dif_pos (nz (a:=d) (b:=d) j).isLt]
    exact (zbit_decode _).trans (ft_join_nz _ _)

def inputSpan {d m : ℕ} (H : Fin m → V d × V d × V d) (s : Fin 3) : Submodule F (Fin m → F) :=
  span F (Set.range (inputRows H s))

def inputLegal {d m : ℕ} (H : Fin m → V d × V d × V d) : Prop :=
  inputSpan H 2 ≤ inputSpan H 0 ⊔ inputSpan H 1

def relation {d m : ℕ} (H : Fin m → V d × V d × V d) : V d → V d → V d → Prop :=
  TripleRelation (inputRows H 0) (inputRows H 1) (inputRows H 2)

def controlCost (d m : ℕ) :=
  max (prepareCost d m+dimsCost d m)
    (max (prepareCost d m+(FlagBankCost d m+blockCoordCost d m+packRowsCost d)+1) (validCost d m))

set_option maxRecDepth 900 in
set_option maxHeartbeats 450000 in
theorem compact_ctl (d m t : ℕ) (hbound : controlCost d m ≤ swPartSize d d d m t)
    (ea eb : Fin (2^d) ≃ V d) :
    CtlSpecRel d d d m t inputLegal relation ea eb := by
  classical
  have hw : wOf d d d = d := by simp [wOf]
  obtain ⟨P,hP,hPS⟩ := prepare_blocks d m
  obtain ⟨C,hC,hCS⟩ := blockCoordinates_cmp d m
  obtain ⟨Vld,hV,hVS⟩ := valid_cmp d m
  let I := In0 d d d m t
  let select : GeneratorInput d m → I := generatorWire
  let Z (x : I → Bool) := P (generatorsOf x)
  have hZ : Cmp I (BlockInput d m) (prepareCost d m) Z :=
    Cmp.sel select hP
  let D (x : I → Bool) := blockCount (blockFlags (Z x))
  let mat0 (s : Fin 3) (x : I → Bool) := packedMatrices (blockFlags (Z x)) (C (Z x)) s
  let addr (s : Fin 3) (x : I → Bool) := Vld (sourceRows (generatorsOf x) s)
  have hD : Cmp I (Fin 5 × Fin (d+1)) (swPartSize d d d m t)
      (fun x p => decide (D x p.1 = p.2.val)) :=
    (hZ.comp (dims_cmp d m)).mono ((le_max_left ..).trans hbound)
  have hM (s : Fin 3) : Cmp I (RowMap d)
      (prepareCost d m+(FlagBankCost d m+blockCoordCost d m+packRowsCost d)) (mat0 s) :=
    pack_rows_cmp C hC Z hZ s
  have hPad (s : Fin 3) : Cmp I (Fin d × Fin (d+1)) (swPartSize d d d m t)
      (fun x => padColumn (mat0 s x)) :=
    ((hM s).comp padColumn_cmp).mono ((le_max_left ..).trans ((le_max_right ..).trans hbound))
  have hAdr (s : Fin 3) : Cmp I (V d) (swPartSize d d d m t) (addr s) :=
    (Cmp.sel (fun (j,i) => select (s,j,i)) hV).mono
      ((le_max_right ..).trans ((le_max_right ..).trans hbound))
  let e : Fin (wOf d d d) → Fin d := Fin.cast hw
  let E (x : I → Bool) (p : Fin (wOf d d d) × Fin d) := mat0 2 x (e p.1,p.2)
  let L (s : Fin 3) (x : I → Bool) (p : Fin (wOf d d d) × Fin (d+1)) :=
    padColumn (mat0 s x) (e p.1,p.2)
  have hE' := ctrl_rewire ((hM 2).mono (show _ ≤ swPartSize d d d m t by
    exact (Nat.le_succ _).trans ((le_max_left ..).trans ((le_max_right ..).trans hbound))))
    (fun p : Fin (wOf d d d) × Fin d => (e p.1,p.2))
  have hL' (s : Fin 3) := ctrl_rewire (hPad s)
    (fun p : Fin (wOf d d d) × Fin (d+1) => (e p.1,p.2))
  let ed : Fin (wOf d d d + 1) → Fin (d+1) := Fin.cast (congrArg (·+1) hw)
  have hD' := ctrl_rewire hD (fun p : Fin 5 × Fin (wOf d d d+1) => (p.1,ed p.2))
  have hs (H : Fin m → V d × V d × V d) (r : Fin m → F)
      (f g : Fin (2^d) → Fin (2^t)) (ok : inputLegal H) :
      let y := inpOf H r f g
      fitsW d (D y) ∧ ∀ u v w : V d,
        relation H u v w ↔ addr 0 y u = true ∧ addr 1 y v = true ∧ addr 2 y w = true ∧
          Std d (D y 0) (D y 1) (D y 2) (D y 3) (D y 4)
            ((mat (mat0 0 y)).mulVec u) ((mat (mat0 1 y)).mulVec v)
            ((mat (mat0 2 y)).mulVec w) := by
    intro y
    obtain ⟨hr,hI,hL⟩ := hPS (generatorsOf y)
    have hd (s : Fin 3) : sourceSpan (generatorsOf y) s = inputSpan H s :=
      congrArg (fun R => span F (Set.range R)) (decoded_generators H r f g s)
    have hG : sourceSpan (generatorsOf y) 2 ≤
        sourceSpan (generatorsOf y) 0 ⊔ sourceSpan (generatorsOf y) 1 := by
      rwa [hd,hd,hd]
    have hl := hL hG
    have hc' (s : Fin 3) (b : BlockRow d) := hCS (Z y) s b (rows_mem (Z y) hI hl s b)
    have hv' (s : Fin 3) (x : V d) := hVS (sourceRows (generatorsOf y) s) x
    have hv'' (s : Fin 3) (x : V d) : addr s y x = true ↔
        ∃ a : Dual (Fin m → F), ∀ j : Fin d,
          a (readRows (sourceRows (Z y ∘ inl ∘ inl) s) j) = x j := by
      rw [hr]
      exact hv' s x
    have h := prepared_sem (Z y) hI hl (C (Z y)) hc' (fun s => addr s y) hv''
    dsimp only at h
    rw [hr] at h
    have he (s : Fin 3) : readRows (sourceRows (generatorsOf y) s) = inputRows H s :=
      decoded_generators H r f g s
    simpa only [triples,relation,he] using h
  refine swCtlSpecRel ea eb (D:=D) (L:=L 0) (M:=L 1) (E:=E)
    (X:=addr 0) (Y:=addr 1) (Z:=addr 2) hD' (hL' 0) (hL' 1) hE' (hAdr 0) (hAdr 1) (hAdr 2) ?_ ?_
  · exact fun H r f g ok => hw.symm ▸ (hs H r f g ok).1
  · intro H r f g u v w ok
    intro y
    exact ((hs H r f g ok).2 u v w).trans
      (and_congr_right' (and_congr_right' (and_congr_right'
        (cast_std hw (D y) (mat0 0 y) (mat0 1 y) (mat0 2 y) u v w).symm)))

end CompactJoin

namespace CompactJoin

open Donor

set_option maxHeartbeats 800000 in
theorem control_budget (d m t : ℕ) :
    controlCost d m ≤ swPartSize d d d m t := by
  obtain ⟨P,hPdef⟩ : ∃ P, d+d+d+m+t+4 = P := ⟨_,rfl⟩
  let B := Phi d
  have hP : 4 ≤ P := by omega
  have hp : 1 ≤ P := by omega
  have hd : d ≤ P := by omega
  have hm : m ≤ P := by omega
  have hd₁ : d+1 ≤ P := by omega
  have hPow {a b : ℕ} (h : a ≤ b) : P^a ≤ P^b := Nat.pow_le_pow_right hp h
  have hOne (i : ℕ) : 1 ≤ P^i := Nat.one_le_pow _ _ hp
  have above (i : ℕ) (h : 1 ≤ i) : P ≤ P^i := by simpa only [pow_one] using hPow h
  have mulP {a b : ℕ} (ha : a ≤ P) (hb : b ≤ P) : a*b ≤ P^2 := by
    simpa only [pow_two] using Nat.mul_le_mul ha hb
  have h2B : 2^d ≤ B := two_pow_le_Phi d
  have hB : 1 ≤ B := (Nat.succ_le_of_lt (Nat.two_pow_pos d)).trans h2B
  have hG (u : ℕ) (hu : u ≤ 3*d) : glCost m 0 u u ≤ 2^36*P^6 :=
    gaussianBudget (T:=P) (by omega)
  have hCoord : coordinateCost (Fin d) (Fin m) ≤ 2^36*P^6 := by
    simpa only [coordinateCost,card_fin] using hG d (by omega)
  have hCoordPair : coordinateCost (Fin d ⊕ Fin d) (Fin m) ≤ 2^36*P^6 := by
    simpa only [coordinateCost,card_sum,card_fin] using hG (d+d) (by omega)
  have hInter : interCost d m ≤ 2^38*P^6 := by
    unfold interCost intersectionCost
    apply widthBudget hp
    · simp only [card_sum,card_fin]
      omega
    · simpa only [card_fin] using hm
    · exact hd
  have hFlag (u : ℕ) (hu : u ≤ 2*d) : flagCost u d m ≤ 2^37*P^7 := by
    unfold flagCost gjCost
    have h := Nat.pow_le_pow_left (show u+d+m+1 ≤ P by omega) 4
    nlinarith only [h,hPow (show 4 ≤ 7 by decide),hOne 7]
  have hBank : FlagBankCost d m ≤ 2^40*P^7 := by
    unfold FlagBankCost
    have h := max_le (hFlag 0 (by omega)) (max_le (hFlag d (by omega)) (hFlag (d+d) (by omega)))
    omega
  have hCoeff : blockCoordCost d m ≤ 2^41*P^7 := by
    unfold blockCoordCost
    have h := Nat.mul_le_mul hd (show 1+coordinateCost (Fin d) (Fin m) ≤ 2^37*P^6 by have := hOne 6; omega)
    nlinarith only [h]
  have hLift : liftCost d m ≤ 2^39*P^7 := by
    unfold liftCost
    have h₁ := Nat.mul_le_mul hd hCoordPair
    have h₂ := Nat.mul_le_mul (mulP hd hm) (show d*5+1 ≤ 6*P by omega)
    nlinarith only [h₁,h₂,hPow (show 3 ≤ 7 by decide)]
  have hPrepare : prepareCost d m ≤ 2^42*P^7 := by
    unfold prepareCost
    nlinarith only [hInter,hLift,hPow (show 6 ≤ 7 by decide)]
  have hDims : dimsCost d m ≤ 2^44*P^8 := by
    unfold dimsCost
    have he := mulP hd₁ hd₁
    have hh : FlagBankCost d m+(d+1)*((d+1)*6) ≤ 2^41*P^7 := by
      nlinarith only [he,hBank,hPow (show 2 ≤ 7 by decide)]
    have gg := Nat.mul_le_mul (show 5*(d+1) ≤ 5*P by omega) hh
    refine gg.trans ?_
    calc
      _ = (5*2^41)*P^8 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by decide)
  have hPack : packRowsCost d ≤ 2^10*P^3 := by
    unfold packRowsCost
    simp only [card_fin,card_prod]
    have h₁ := Nat.mul_le_mul (show d+d+d+d+d+1 ≤ 6*P by omega) (show (d+1)*6 ≤ 6*P by omega)
    have h₂ := Nat.mul_le_mul (mulP hd hd) (show 3*(d+d+d+d+d)+1 ≤ 16*P by omega)
    nlinarith only [h₁,h₂,hPow (show 2 ≤ 3 by decide),hOne 3]
  have hValid : validCost d m ≤ 2^40*P^6*B := by
    have hh := nullBudget (J:=Fin d) (U:=Fin m) (d:=d) hp
      (by simpa only [card_fin] using hd) (by simpa only [card_fin] using hm) hd
    have hk := Nat.mul_le_mul hd (show d*6+7 ≤ 13*P by omega)
    have hv := Nat.mul_le_mul h2B (show d*(d*6+7)+1 ≤ 14*P^2 by nlinarith only [hk,hOne 2])
    unfold validCost
    nlinarith only [hh,hv,Nat.mul_le_mul (le_refl (P^6)) hB,
      Nat.mul_le_mul_right B (hPow (show 2 ≤ 6 by decide)),hOne 6]
  have hJ : controlCost d m ≤ 2^46*P^8*B := by
    unfold controlCost
    have hb := Nat.mul_le_mul (le_refl (P^8)) hB
    refine max_le ?_ (max_le ?_ ?_)
    · nlinarith only [hPrepare,hDims,hb,hPow (show 7 ≤ 8 by decide)]
    · nlinarith only [hPrepare,hBank,hCoeff,hPack,hb,hOne 8,
        hPow (show 7 ≤ 8 by decide),hPow (show 3 ≤ 8 by decide)]
    · nlinarith only [hValid,Nat.mul_le_mul_right B (hPow (show 6 ≤ 8 by decide))]
  refine hJ.trans ?_
  have hC : 2^6 ≤ P^10 := (show (2 : ℕ)^6 ≤ 4^10 by decide).trans (Nat.pow_le_pow_left hP _)
  have h := Nat.mul_le_mul_left (2^40*P^8) hC
  rw [show swPartSize d d d m t = 2^40*P^18*B by simp only [swPartSize,hPdef,wOf,max_self,B]]
  refine Nat.mul_le_mul_right B ?_
  calc
    2^46*P^8 = (2^40*P^8)*2^6 := by ring
    _ ≤ (2^40*P^8)*P^10 := h
    _ = _ := by rw [Nat.mul_assoc, ← pow_add]

end CompactJoin

section Helpers

open Donor PackedTape CompactJoin

variable {k r q n d : ℕ}

abbrev TapeJoinInput (k r d : ℕ) := In0 d d d (tapeSize k r) (tapeSize k r+1)

def tapeJoinRoute (v l h : Fin n) : TapeJoinInput k r d → Option (JoinState k r q n d) :=
  let τ (s : Fin (d+d+d+1)) : Option (Fin n × Fin d) :=
    if h₁ : s.val < d then some (l,⟨s.val,h₁⟩)
    else if h₂ : s.val < d+d then some (h,⟨s.val-d,by omega⟩)
    else if h₃ : s.val < d+d+d then some (v,⟨s.val-(d+d),by omega⟩)
    else none
  elim (fun (i,s) => (τ s).map (fun (b,j) => .inl (.inr (.inl b,.inl (i,j)))))
    (fun p => some (.inr p))

def tapeJoinInput (v l h : Fin n) (x : JoinState k r q n d → Bool) (i : TapeJoinInput k r d) :=
  (tapeJoinRoute v l h i).elim false x

def tapeJoinRows (x : Pre k r q n d → Bool) (v l h : Fin n) (i : Param k r) : V d × V d × V d :=
  (fun j => preGen x (.inl l) j i, fun j => preGen x (.inl h) j i, fun j => preGen x (.inl v) j i)

def tapeTable (f : TableIx k r d → Bool) (b : Addr d) :
    Fin (2^(tapeSize k r + 1)) := ⟨tabN (fun j => f (b,j)), st_tabN_lt _⟩

theorem tapeJoinInput_eq (x : Pre k r q n d → Bool) (v l h : Fin n)
    (f g : TableIx k r d → Bool) :
    tapeJoinInput v l h (elim x (elim f g)) =
      inpOf (tapeJoinRows x v l h) (fun _ => 0) (tapeTable f) (tapeTable g) := by
  funext i
  rcases i with ⟨s,i⟩ | p
  · by_cases h₁ : i.val < d
    · have h₂ : i.val < d+d+d := by omega
      simpa only [tapeJoinInput,tapeJoinRoute,elim_inl,dif_pos h₁,dif_pos h₂,Option.map_some,Option.elim_some,
        inpOf,join3,tapeJoinRows,preGen,preBasis,widthOutGen,st_dec_b2z]
    · by_cases h₂ : i.val < d+d
      · have h₃ : i.val < d+d+d := by omega
        simpa only [tapeJoinInput,tapeJoinRoute,elim_inl,dif_neg h₁,dif_pos h₂,dif_pos h₃,
          Option.map_some,Option.elim_some,inpOf,join3,tapeJoinRows,preGen,preBasis,widthOutGen,st_dec_b2z]
      · by_cases h₃ : i.val < d+d+d
        · simpa only [tapeJoinInput,tapeJoinRoute,elim_inl,dif_neg h₁,dif_neg h₂,dif_pos h₃,
            Option.map_some,Option.elim_some,inpOf,join3,tapeJoinRows,preGen,preBasis,widthOutGen,st_dec_b2z]
        · simp [tapeJoinInput,tapeJoinRoute,inpOf,h₁,h₂,h₃]
  · rcases p with ⟨b,e⟩ | ⟨b,e⟩
    · exact (st_tabN_testBit (fun j => f (b,j)) e).symm
    · exact (st_tabN_testBit (fun j => g (b,j)) e).symm

end Helpers

section Helpers

open Donor PackedTape CompactJoin

variable {k r q n d : ℕ}

def compactLocalCost (k r d : ℕ) :=
  1 + weightedJoinCost d d d (tapeSize k r) (tapeSize k r+1)

def parentLegal {V : Type} [AddCommGroup V] [Module F V]
    (A B C : Fin d → V) : Prop :=
  span F (Set.range C) ≤ span F (Set.range A) ⊔ span F (Set.range B)

open Classical in
set_option maxRecDepth 850 in
set_option maxHeartbeats 500000 in
theorem compactLocal_cmp (v l h : Fin n) :
    ∃ W : (JoinState k r q n d → Bool) → TableIx k r d → Bool,
      Cmp _ _ (compactLocalCost k r d) W ∧
      ∀ (x : Pre k r q n d → Bool) (f g : TableIx k r d → Bool) (a : Addr d)
        (j : Fin (tapeSize k r + 1)),
        parentLegal (preGen x (.inl l)) (preGen x (.inl h)) (preGen x (.inl v)) →
        W (elim x (elim f g)) (a,j) =
          (∑ b : Addr d, ∑ c : Addr d, if TripleRelation
            (preGen x (.inl l)) (preGen x (.inl h)) (preGen x (.inl v))
            (vecN d b.val) (vecN d c.val) (vecN d a.val) then
            tabN (fun e => f (b,e))*tabN (fun e => g (c,e)) else 0).testBit j.val := by

  classical
  let m := tapeSize k r
  let t := m+1
  obtain ⟨J,hJ,hs⟩ := weightedJoinRel d d d m t
    (fun ea eb => compact_ctl d m t (control_budget d m t) ea eb)
  let cut (e : Fin t) : Fin (d+d+2*t+1) := ⟨e.val,by have := e.isLt; omega⟩
  let out (p : TableIx k r d) : Fin (2^d) × Fin (d+d+2*t+1) := (p.1,cut p.2)
  let route : TapeJoinInput k r d → Option (JoinState k r q n d) := tapeJoinRoute v l h
  refine ⟨fun x p => J (tapeJoinInput v l h x) (out p), ?_, ?_⟩
  · have he := ((ccOption route).comp hJ).comp (Cmp.wire out)
    rw [Nat.add_zero] at he
    exact he.congr (fun x p => rfl)
  · intro x f g a j hl
    change J (tapeJoinInput v l h (elim x (elim f g))) (a,cut j) = _
    rw [tapeJoinInput_eq]
    let H := tapeJoinRows x v l h
    have hA : inputRows H 0 = preGen x (.inl l) := by funext j i; rfl
    have hB : inputRows H 1 = preGen x (.inl h) := by funext j i; rfl
    have hC : inputRows H 2 = preGen x (.inl v) := by funext j i; rfl
    have hLeg : inputLegal H := by
      unfold inputLegal inputSpan
      rw [hA,hB,hC]
      exact hl
    have hv := hs H (fun _ => 0) (tapeTable f) (tapeTable g) a (cut j) hLeg
    change J (inpOf H (fun _ => 0) (tapeTable f) (tapeTable g)) (a,cut j) = _
    refine hv.trans (congrArg (fun v : ℕ => v.testBit j.val) ?_)
    refine sum_congr rfl fun b _ => sum_congr rfl fun c _ => ?_
    change (if relation H (vecN d b.val) (vecN d c.val) (vecN d a.val) then
      tabN (fun e => f (b,e)) * tabN (fun e => g (c,e)) else 0) = _
    rw [relation,hA,hB,hC]

end Helpers

section Helpers

open Donor PackedTape

variable {k r q n : ℕ}

def compactScheduleBudget (k r q n d : ℕ) : ℕ :=
  card (Fin n × TableIx k r d) + n * TreeSchedule.stepCost (Pre k r q n d)
    (Leaf k r) (TableIx k r d) n (max (leafLocalCost k r d) (compactLocalCost k r d))
    (LayoutGuard.guardCost (Leaf k r))

def compactOracleCost (k r q n d : ℕ) := preCost k r q n d + compactScheduleBudget k r q n d + finalCountBudget k r n

lemma parent_cut_le {J U : Type} [AddCommGroup U] [Module F U]
    (R : J × Fin 3 → U) (l h : J → Bool) (hd : ∀ j, l j = true → h j = false) :
    CutSpan R (fun j => l j || h j) ≤ CutSpan R l ⊔ CutSpan R h := by
  let e := fun j => !(l j || h j)
  let L := FormSpan R l
  let H := FormSpan R h
  let E := FormSpan R e
  have he := restPartition l h hd
  have hL : CutSpan R l = LeftBoundary L H E := by
    unfold CutSpan LeftBoundary L H E e
    rw [← formSpan_union, funext he.1]
  have hH : CutSpan R h = RightBoundary L H E := by
    unfold CutSpan RightBoundary L H E e
    rw [← formSpan_union, funext he.2]
  rw [hL,hH]
  unfold CutSpan
  rw [formSpan_union R l h]
  exact parentBoundary_le L H E

set_option maxHeartbeats 2500000 in
theorem compactCountOracle (hk : 0 < k) (w : ℕ) :
    let d := min (tapeSize k r) w
    ∃ O : (In k r q n → Bool) → Greedy.Reply k → Bool,
      Cmp (In k r q n) (Greedy.Reply k) (compactOracleCost k r q n d) O ∧
      Greedy.OracleSpec O (inputGood hk w) (inputHit hk) := by
  classical
  intro d
  let N := tapeSize k r
  let D := Pre k r q n d
  let J := Leaf k r
  let T := TableIx k r d
  let LV := Param k r → F
  let gr := LayoutGuard.guard (bagRoute (k:=k) (r:=r) (q:=q) (n:=n) (d:=d))
  obtain ⟨P,hP,S,hS,hPre⟩ := preprocess (k:=k) (r:=r) (q:=q) (n:=n) hk d
  choose FL hFL hLsem using fun j : J => leafLocal_cmp (k:=k) (r:=r) (q:=q) (n:=n) (d:=d) j
  choose FJ hFJ hJsem using fun v l h : Fin n => compactLocal_cmp (k:=k) (r:=r) (q:=q) (n:=n) (d:=d) v l h
  have hG := fun v c => LayoutGuard.guard_cb (bagRoute (k:=k) (r:=r) (q:=q) (n:=n) (d:=d)) v c
  have hR := TreeSchedule.run_cmp FL FJ gr
    (fun i => (hFL i).mono (le_max_left ..)) (fun v l h => (hFJ v l h).mono (le_max_right ..)) hG
  let O (x : In k r q n → Bool) := finishCount (TreeSchedule.run FL FJ gr (P x))
  refine ⟨O, Cmp.comp (Cmp.comp hP hR) finishCount_cmp, ?_⟩
  intro x m p
  let in0 := Greedy.input x m p
  let z := P in0
  let st := TreeSchedule.run FL FJ gr z
  let rowForm := linearRows (preForms z)
  let good := gatePred (preForms z) (readC x) (readPref in0)
  let bg := readBag x
  obtain ⟨hIn, hAffine, hForm, hW, hLeafBasis⟩ := hPre in0
  have hx : preRaw z = x := congrArg (fun f => f ∘ inl) hIn
  have hTape := hS x
  change preIn z = in0 at hIn
  change preRaw z = x at hx
  change preForms z = evalForms hk (S x) at hForm
  have hd : TreeSchedule.data st = z := TreeSchedule.run_data FL FJ gr z
  have hmask (v : Fin n) (j : J) : z (bagRoute (v,j)) = bg v j :=
    congrFun hx (bagSlot v j)
  have hLayout : LayoutGuard.layout bagRoute z = LayoutGuard.layout (fun p => bagSlot p.1 p.2) x := by
    rw [Bool.eq_iff_iff, LayoutGuard.layout_true, LayoutGuard.layout_true]
    simp only [LayoutGuard.mask, hmask, bg, readBag]
  have hfit : fitSignal z = inputGood hk w x := by
    rw [Bool.eq_iff_iff]
    unfold fitSignal inputGood
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hLayout]
    apply and_congr_right'
    apply forall_congr'
    intro v
    have hf := (hW (.inl v)).1
    change preWidth z (.inl v) = true ↔ _ at hf
    rw [hf]
    have he : preBagIx (preRaw z) (.inl v) = bg v := congrArg (fun f => readBag f v) hx
    rw [he]
    have hh : finrank F (CutSpan rowForm (bg v)) ≤ N :=
      (Submodule.finrank_le _).trans (by simp [N, Param])
    have hw := post_width_eq hk (readObs x) (S x) hTape.2.1 (bg v)
    have heq := congrArg (fun R => finrank F (CutSpan R (bg v))) (congrArg linearRows hForm)
    have hw' := heq.trans hw
    change finrank F (CutSpan rowForm (bg v)) ≤ d ↔ _
    rw [← hw']
    exact ⟨fun hz => hz.trans (min_le_right ..), fun hz => le_min hh hz⟩
  refine ⟨(congrArg fitSignal hd).trans hfit, ?_⟩
  intro j
  change (fitSignal (TreeSchedule.data st) && preAffine (TreeSchedule.data st) &&
      LayoutGuard.readRoots bagRoute st (zeroAddr d, widenCount k r j)) = _
  rw [hd, hfit]
  cases hf : inputGood hk w x
  · simp
  · have hf' : fitSignal z = true := hfit.trans hf
    have hLay : LayoutGuard.layout bagRoute z = true := by
      unfold fitSignal at hf'
      exact (Bool.and_eq_true_iff.mp hf').1
    have hWx : ∀ v : Fin n, preWidth z (.inl v) = true := by
      unfold fitSignal at hf'
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hf').2
    have hspan (v : Fin n) : span F (Set.range (preGen z (.inl v))) = CutSpan rowForm (bg v) := by
      have h := (hW (.inl v)).2 (hWx v)
      rw [hx] at h
      exact h
    have hLayoutFacts := (LayoutGuard.layout_true bagRoute z).mp hLay
    have hcard := keyOK_card (k:=k) (r:=r) (q:=q) (n:=n) hk x m p
    change preAffine z = S x (.inr ()) at hAffine
    cases ha : preAffine z
    · have hb : S x (.inr ()) = false := hAffine.symm.trans ha
      have hn : IsEmpty {key // KeyOK hk (readName x) (readC x) (readObs x) (readRhs x) (readPref in0) key} := ⟨fun u => by
        let y : Tape k r := (u.val, actual hk (readName x) (readC x) u.val)
        have hsys : latticeMap hk (readObs x) (flatten y) = rowTarget (readName x) (readRhs x) := by
          funext i
          apply (rowEquations hk (readName x) (readObs x) (readRhs x) y).mpr _ i
          exact ⟨fun b => actual_zero hk (readName x) (readC x) u.val b, u.prop.2⟩
        exact Bool.noConfusion (hb.symm.trans (hTape.1.mpr ⟨_,hsys⟩))⟩
      have hz := Nat.card_eq_zero.mpr (Or.inl hn)
      simp [ha, ← hcard, hz]
    · have hso : S x (.inr ()) = true := hAffine.symm.trans ha
      have hpoint := hTape.2.2 hso
      let C (v : Fin n) (a : Addr d) : ℕ :=
        tableCount rowForm good (bg v) (preGen z (.inl v)) (hspan v) (vecN d a.val)
      let bits (v : Fin n) (u : T) := (C v u.1).testBit u.2.val
      have hb (v : Fin n) (a : Addr d) : C v a < 2 ^ (N+1) := by
        have h := tableCount_bound rowForm good (bg v) (preGen z (.inl v)) (hspan v) (vecN d a.val)
        simpa [C, N, Param] using h
      have hAvail := LayoutGuard.layout_available (T:=T) bagRoute z hLay
      have hleaf (v : Fin n) (i : J) (hi : gr v (.inl i) z = true) : FL i z = bits v := by
        have hb' : bg v = fun t => decide (t = i) := by
          funext t
          simpa only [LayoutGuard.mask, hmask] using (LayoutGuard.guard_single_true bagRoute v i z).mp hi t
        have hSingle : ∀ a, readBag (preRaw z) v a = decide (a = i) := fun a =>
          (congrFun (congrArg (fun f => readBag f v) hx) a).trans (congrFun hb' a)
        have hB := hLeafBasis v i hSingle
        have he : preGen z (.inl v) = preGen z (.inr i) := congrArg widthOutGen hB
        have hs : span F (Set.range (preGen z (.inr i))) = CutSpan rowForm (fun t => decide (t=i)) := by
          rw [← he, ← hb']; exact hspan v
        funext t
        rcases t with ⟨a,j⟩
        have hC := tableCount_congr rowForm good hb' he (hspan v) hs (vecN d a.val)
        have hbyte := hLsem i z a j
        rw [leaf_tableCount rowForm good i _ hs] at hC
        change _ = (C v a).testBit j.val
        rw [hbyte]
        have hP : gatePred (preForms z) (readC (preRaw z)) (readPref (preIn z)) = good := by rw [hIn,hx]
        rw [hP]
        exact congrArg (fun c => c.testBit j.val) hC.symm
      have hjoin (v l h : Fin n) (_ : l < v) (_ : h < v) (hv : gr v (.inr (l,h)) z = true) :
          FJ v l h (elim z (elim (bits l) (bits h))) = bits v := by
        obtain ⟨hdis, hUnion⟩ := (LayoutGuard.guard_split_true bagRoute v l h z).mp hv
        have hd' : ∀ i, bg l i = true → bg h i = false := by
          simpa only [LayoutGuard.mask, hmask] using hdis
        have hp : bg v = fun j => bg l j || bg h j := by
          funext i
          simpa only [LayoutGuard.mask, hmask] using hUnion i
        have hs : span F (Set.range (preGen z (.inl v))) = CutSpan rowForm (fun j => bg l j || bg h j) := hp ▸ hspan v
        funext j
        rcases j with ⟨a,i⟩
        have hCnt := tableCount_congr rowForm good hp rfl (hspan v) hs (vecN d a.val)
        rw [splitTableCount rowForm good (bg l) (bg h) hd' _ _ _ (hspan l) (hspan h) hs] at hCnt
        obtain ⟨ev,hev⟩ := vecEquiv_exists d
        have hvec (b : Addr d) : ev b = vecN d b.val := funext (hev b)
        have hLegal : parentLegal (preGen z (.inl l)) (preGen z (.inl h)) (preGen z (.inl v)) := by
          unfold parentLegal
          rw [hspan l, hspan h, hs]
          exact parent_cut_le rowForm (bg l) (bg h) hd'
        rw [hJsem v l h z (bits l) (bits h) a i hLegal]
        change _ = (C v a).testBit i.val
        congr 1
        rw [show C v a = _ from hCnt]
        rw [← Equiv.sum_comp ev]
        refine sum_congr rfl fun x _ => ?_
        rw [← Equiv.sum_comp ev, hvec]
        refine sum_congr rfl fun y _ => ?_
        rw [hvec]
        have hl' : tabN (fun e => bits l (x,e)) = C l x := tabN_recover (hb l x)
        have hh' : tabN (fun e => bits h (y,e)) = C h y := tabN_recover (hb h y)
        rw [hl', hh']
      have hRun := TreeSchedule.run_sem FL FJ gr z bits (hAvail (elim z (fun _ => false)) rfl) hleaf hjoin
      have hzero : vecN d (zeroAddr d).val = 0 := by funext i; simp [vecN, zeroAddr]
      let amt := Greedy.cardinal (Greedy.matched (inputHit hk x) m p)
      have hRootCounts (v : Fin n) (hv : LayoutGuard.root bagRoute v z = true) : C v (zeroAddr d) = amt := by
        have hfull : bg v = fun _ => true := by
          funext i
          simpa only [LayoutGuard.mask, hmask] using (LayoutGuard.root_true bagRoute v z).mp hv i
        have hS' : span F (Set.range (preGen z (.inl v))) = CutSpan rowForm (fun _ => true) :=
          hfull ▸ hspan v
        have hA := tableCount_congr rowForm good hfull rfl (hspan v) hS' 0
        change C v (zeroAddr d) = _
        dsimp only [C]
        rw [hzero, hA]
        have hForm' : preForms z = evalForms hk (S x) := hForm
        simpa only [rowForm, good, hForm', amt] using
          (root_tableCount hk (readName x) (readC x) (readObs x) (readRhs x) (readPref in0)
            (S x) hTape.2.1 hpoint _ (by simpa only [rowForm,hForm'] using hS')).trans hcard
      have hread : LayoutGuard.readRoots bagRoute st (zeroAddr d, widenCount k r j) = amt.testBit j.val := by
        have hex : ∃ v, LayoutGuard.root bagRoute v (TreeSchedule.data st) = true := by
          rw [hd]
          obtain ⟨v,hv⟩ := hLayoutFacts.1
          exact ⟨v,(LayoutGuard.root_true bagRoute v z).mpr hv⟩
        obtain ⟨v,hv⟩ := hex
        have hr (u : Fin n) (hu : LayoutGuard.root bagRoute u (TreeSchedule.data st) = true) :
            TreeSchedule.table st u (zeroAddr d, widenCount k r j) = amt.testBit j.val := by
          rw [hd] at hu
          rw [hRun, show bits u (zeroAddr d, widenCount k r j) = (C u (zeroAddr d)).testBit j.val from rfl,
            hRootCounts u hu]
        rw [Bool.eq_iff_iff]
        simp only [LayoutGuard.readRoots, decide_eq_true_eq, Bool.and_eq_true]
        exact ⟨fun ⟨u,hu,hh⟩ => (hr u hu) ▸ hh, fun hh => ⟨v,hv,(hr v hv).symm ▸ hh⟩⟩
      simp [ha, hread, amt]

end Helpers

section Helpers

open Donor PackedTape

set_option maxHeartbeats 120000 in
theorem countCostBound (k r n T : ℕ) (hT : 1 ≤ T)
    (hn : n ≤ T) (hL : card (Leaf k r) ≤ T) (hk : k+2 ≤ T) :
    finalCountBudget k r n ≤ 2^10*T^5 := by
  let L := card (Leaf k r)
  change L ≤ T at hL
  have hpow {a b : ℕ} (h : a ≤ b) := Nat.pow_le_pow_right hT h
  have h₁ (a : ℕ) : 1 ≤ T^a := Nat.one_le_pow _ _ hT
  have hsmall (b : ℕ) (h : 1 ≤ b) : T ≤ T^b := by simpa only [pow_one] using hpow h
  have hCand : L+n*n ≤ 2*T^2 := by
    have hn2 : n*n ≤ T^2 := by simpa only [pow_two] using Nat.mul_le_mul hn hn
    have hmon := hsmall 2 (by decide)
    omega
  unfold finalCountBudget LayoutGuard.layoutCost LayoutGuard.hasRootCost LayoutGuard.nodeCost
    LayoutGuard.rootCost LayoutGuard.guardCost
  have hJ := Nat.mul_le_mul hCand (show L*10+1+1 ≤ 12*T by omega)
  have hc : (L+n*n)*(L*10+1+1)+1+1 ≤ 26*T^3 := by nlinarith only [hJ,h₁ 3]
  have h1 := Nat.mul_le_mul hn hc
  have h2 := Nat.mul_le_mul hn (show L+1+1 ≤ 3*T by omega)
  have h3 := Nat.mul_le_mul hn (show L+1+2 ≤ 4*T by omega)
  have h4 := Nat.mul_le_mul hk (show n*(L+1+1)+1+(n*((L+n*n)*(L*10+1+1)+1+1)+1)+1+(n+1)+n*(L+1+2)+4 ≤ 64*T^4 by
    nlinarith only [h1,h2,h3,hn,h₁ 4,hsmall 4 (by decide),hpow (show 2 ≤ 4 by decide)])
  nlinarith only [h4,h₁ 5]

set_option maxHeartbeats 120000 in
set_option maxRecDepth 900 in
theorem preStateCardBound (k r q n d T : ℕ) (hT : 1 ≤ T)
    (hN : tapeSize k r + 1 ≤ T) (hd : d ≤ tapeSize k r)
    (hn : n ≤ T) (hL : card (Leaf k r)*3 ≤ T) (hk : k+2 ≤ T) (hq : q ≤ T) :
    card (Pre k r q n d) ≤ 10*T^3 := by
  let N := tapeSize k r
  let L := card (Leaf k r)
  change N+1 ≤ T at hN
  change d ≤ N at hd
  change L*3 ≤ T at hL
  have hL0 : L ≤ N := by
    rw [show L = (2*r+1)*k from leaf_card ..]
    exact Nat.mul_le_mul_right k (by omega)
  have hpow {a b : ℕ} (h : a ≤ b) := Nat.pow_le_pow_right hT h
  have h₁ (a : ℕ) : 1 ≤ T^a := Nat.one_le_pow _ _ hT
  have hsmall (b : ℕ) (h : 1 ≤ b) : T ≤ T^b := by simpa only [pow_one] using hpow h
  have m₂ {a b : ℕ} (ha : a ≤ T) (hb : b ≤ T) : a*b ≤ T^2 := by
    simpa only [pow_two] using Nat.mul_le_mul ha hb
  have hFI : card (FormIx k r) = L*3 := by simp [FormIx,L]
  have hFD : card (FormData k r) = L*3*(N+1) := by simp [FormData,hFI,Param,N]
  have hBI : card (BasisIx k r n) = n+L := by simp [BasisIx,L]
  have hRaw : card (Raw k r q n) = (2+2*r)*k+q*(N+1)+n*((2*r+1)*k) :=
    card_inputSlot k r q n
  have hIn : card (In k r q n) = card (Raw k r q n) + (k+k) := by
    unfold In Greedy.Input
    rw [card_sum, card_sum (α := Fin k) (β := Fin k), card_fin]
  have hMid : card (PreMid k r q n) =
      card (Raw k r q n)+(k+k)+(1+L*3*(N+1)) := by
    unfold PreMid
    rw [card_sum, card_sum (α := Unit) (β := FormData k r),
      card_unit,hIn,hFD]
  have hWidth : card (WidthOut (Param k r) d) = N*d+1 := by
    simp only [WidthOut, Param, card_sum, card_prod, card_fin,
      card_unit, N]
  unfold Pre
  rw [card_sum,card_prod (α := BasisIx k r n) (β := WidthOut (Param k r) d),
    hBI,hWidth,hMid,hRaw]
  have hCell : (2*r+1)*k ≤ T := (leaf_card k r).symm.le.trans (hL0.trans (by omega))
  have hs : (2+2*r)*k ≤ N := Nat.mul_le_mul_right k (by omega)
  have hu : N*d+1 ≤ 2*T^2 := by nlinarith only [m₂ (show N ≤ T by omega) (show d ≤ T by omega),h₁ 2]
  have h := Nat.mul_le_mul (show n+L ≤ 2*T by omega) hu
  nlinarith only [h,m₂ hq hN,m₂ hn hCell,m₂ hL hN,hs,hN,hk,h₁ 3,
    hpow (show 2 ≤ 3 by decide),hsmall 3 (by decide)]

end Helpers

section Helpers

open Donor PackedTape

set_option maxHeartbeats 100000 in
theorem compactLocalCostBound
    (k r d T B : ℕ) (hT : 1 ≤ T) (hB0 : Phi d = B)
    (hN : tapeSize k r + 1 ≤ T) (hJ : 3*d+tapeSize k r+(tapeSize k r+1)+4 ≤ T)
    (hm : d+3 ≤ T) :
    max (leafLocalCost k r d) (compactLocalCost k r d) ≤ 2^62*T^30*B := by
  let N := tapeSize k r
  change N+1 ≤ T at hN
  change 3*d+N+(N+1)+4 ≤ T at hJ
  have hz : 3*d ≤ T := by omega
  have hpow {a b : ℕ} (h : a ≤ b) := Nat.pow_le_pow_right hT h
  have h₁ (a : ℕ) : 1 ≤ T^a := Nat.one_le_pow _ _ hT
  have hsmall (b : ℕ) (h : 1 ≤ b) : T ≤ T^b := by simpa only [pow_one] using hpow h
  have hB' : 2^d ≤ B := hB0 ▸ two_pow_le_Phi d
  have hB : 1 ≤ B := (Nat.succ_le_of_lt (Nat.two_pow_pos d)).trans hB'
  have m₂ {a b : ℕ} (ha : a ≤ T) (hb : b ≤ T) : a*b ≤ T^2 := by
    simpa only [pow_two] using Nat.mul_le_mul ha hb
  apply max_le
  · unfold leafLocalCost
    have hNull := nullBudget (J:=Fin (d+3)) (U:=Param k r) hT
      (by simpa using hm) (by simpa only [Param,card_fin] using (show N ≤ T by omega)) hm
    have hIn : card (LInput d) ≤ T^2+6 := by
      simp only [LInput,LeafTable.Input,card_prod,card_sum,card_fin,card_unit]
      have h := m₂ hm hm
      omega
    have hLeaf : LeafTable.budget (d+3) d (N+1) ≤ 2^20*T^2*B := by
      have hZ := Nat.mul_le_mul hm (show 5*(d+3)+3 ≤ 8*T by omega)
      have harg : 8*((d+3)*(5*(d+3)+3)+34)+5121*(N+1) ≤ 2^20*T^2 := by
        nlinarith only [hZ,hN,h₁ 2,hsmall 2 (by decide)]
      exact (Nat.mul_le_mul hB' harg).trans_eq (mul_comm _ _)
    change nullPrepCost (Fin (d+3)) (Param k r) (d+3) + card (LInput d) +
      LeafTable.budget (d+3) d (N+1) ≤ _
    nlinarith only [hNull,hIn,hLeaf,Nat.mul_le_mul (h₁ 30) hB,
      Nat.mul_le_mul (hpow (show 6 ≤ 30 by decide)) hB,
      Nat.mul_le_mul (hpow (show 2 ≤ 30 by decide)) hB,
      Nat.mul_le_mul_right B (hpow (show 2 ≤ 30 by decide))]
  · have hw : weightedJoinCost d d d N (N+1) ≤ 2^60*T^30*B := by
      unfold weightedJoinCost
      simp only [wOf,max_self,hB0]
      exact Nat.mul_le_mul_right B (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    change 1 + weightedJoinCost d d d N (N+1) ≤ _
    nlinarith only [hw,Nat.mul_le_mul (h₁ 30) hB]

set_option maxHeartbeats 120000 in
theorem compactScheduleCostBound (k r q n d T B : ℕ) (hT : 1 ≤ T) (hB : 1 ≤ B)
    (hn : n ≤ T) (hL : card (Leaf k r) ≤ T)
    (hTab : card (TableIx k r d) ≤ T*B)
    (hPT : card (Pre k r q n d) ≤ 10*T^3)
    (hLoc : max (leafLocalCost k r d) (compactLocalCost k r d) ≤ 2^62*T^30*B) :
    compactScheduleBudget k r q n d ≤ 2^66*T^33*B := by
  let L := card (Leaf k r)
  change L ≤ T at hL
  have hpow {a b : ℕ} (h : a ≤ b) := Nat.pow_le_pow_right hT h
  have h₁ (a : ℕ) : 1 ≤ T^a := Nat.one_le_pow _ _ hT
  have hsmall (b : ℕ) (h : 1 ≤ b) : T ≤ T^b := by simpa only [pow_one] using hpow h
  have hCand : L+n*n ≤ 2*T^2 := by
    have hn2 : n*n ≤ T^2 := by simpa only [pow_two] using Nat.mul_le_mul hn hn
    have hmon := hsmall 2 (by decide)
    omega
  rw [compactScheduleBudget, card_prod (α := Fin n) (β := TableIx k r d),card_fin]
  have ht := Nat.mul_le_mul hn hTab
  have hState : card (Pre k r q n d) + n*card (TableIx k r d) ≤ 11*T^3*B := by
    nlinarith only [ht,hPT,Nat.mul_le_mul (le_refl (T^3)) hB,
      Nat.mul_le_mul_right B (hpow (show 2 ≤ 3 by decide))]
  have hl : max (leafLocalCost k r d) (compactLocalCost k r d)+LayoutGuard.guardCost (Leaf k r)+2
      ≤ 2^63*T^30*B := by
    change max (leafLocalCost k r d) (compactLocalCost k r d) + (L*10+1)+2 ≤ _
    nlinarith only [hLoc,hL,Nat.mul_le_mul (hsmall 30 (by decide)) hB,Nat.mul_le_mul (h₁ 30) hB]
  have h1 := Nat.mul_le_mul hCand hl
  have h2 := Nat.mul_le_mul hState (show 2*(L+n*n)+1 ≤ 5*T^2 by nlinarith only [hCand,h₁ 2])
  have hs : TreeSchedule.stepCost (Pre k r q n d) (Leaf k r) (TableIx k r d) n
      (max (leafLocalCost k r d) (compactLocalCost k r d)) (LayoutGuard.guardCost (Leaf k r))
      ≤ 2^65*T^32*B := by
    have hc : card (TreeSchedule.Candidate (Leaf k r) n) = L+n*n := by
      unfold TreeSchedule.Candidate
      rw [card_sum,card_prod (α := Fin n) (β := Fin n),card_fin]
    have hs : card (TreeSchedule.State (Pre k r q n d) (TableIx k r d) n) =
        card (Pre k r q n d) + n*card (TableIx k r d) := by
      unfold TreeSchedule.State
      rw [card_sum,card_prod (α := Fin n) (β := TableIx k r d),card_fin]
    rw [TreeSchedule.stepCost,hc,hs]
    nlinarith only [h1,h2,Nat.mul_le_mul_right B (hpow (show 5 ≤ 32 by decide)),Nat.mul_le_mul (h₁ 32) hB]
  have hn' := Nat.mul_le_mul hn hs
  nlinarith only [ht,hn',Nat.mul_le_mul_right B (hpow (show 2 ≤ 33 by decide))]

set_option maxHeartbeats 180000 in
set_option maxRecDepth 900 in
theorem compact_full_size (k r q n w : ℕ) (hn0 : n ≤ (k+r+q+5)^2) :
    let N := tapeSize k r
    let d := min N w
    (k+1)*compactOracleCost k r q n d + k*k+3*k+2+1 ≤ 2^160*(k+r+q+5)^100*Phi d := by
  intro N d
  obtain ⟨P,hPdef⟩ : ∃ P : ℕ, P = k+r+q+5 := ⟨_,rfl⟩
  rw [← hPdef] at hn0
  obtain ⟨T,hT0⟩ : ∃ T : ℕ, 4*P^2 = T := ⟨_,rfl⟩
  obtain ⟨B,hB0⟩ : ∃ B : ℕ, Phi d = B := ⟨_,rfl⟩
  let L := card (Leaf k r)
  let R := card (EqRow k q)
  have hP : 5 ≤ P := by omega
  have hP2 : P ≤ P^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ P by omega) (show 1 ≤ 2 by decide)
  have h25 : 25 ≤ P^2 := Nat.pow_le_pow_left hP 2
  have hN0 : 2*N ≤ P^2 := by
    rw [hPdef]
    change 2*((2*r+3)*k) ≤ (k+r+q+5)^2
    nlinarith only [four_mul_le_sq_add k r, Nat.zero_le (k*q), Nat.zero_le (r*q),
      Nat.zero_le (q*q), Nat.zero_le k, Nat.zero_le r, Nat.zero_le q]
  have hT : 1 ≤ T := by omega
  have hpow {a b : ℕ} (h : a ≤ b) := Nat.pow_le_pow_right hT h
  have h₁ (a : ℕ) : 1 ≤ T^a := Nat.one_le_pow _ _ hT
  have hsmall (b : ℕ) (h : 1 ≤ b) : T ≤ T^b := by simpa only [pow_one] using hpow h
  have hB' : 2^d ≤ B := hB0 ▸ two_pow_le_Phi d
  have hB : 1 ≤ B := (Nat.succ_le_of_lt (Nat.two_pow_pos d)).trans hB'
  have hN : N+1 ≤ T := by omega
  have hd : d ≤ N := min_le_left ..
  have hn : n ≤ T := by omega
  have hL0 : L ≤ N := by
    rw [show L = (2*r+1)*k by exact leaf_card ..]
    exact Nat.mul_le_mul_right k (by omega)
  have hR : R ≤ T := by
    have he : R = 2*k+q := by simp [R]
    omega
  have hL : L*3 ≤ T := by omega
  have hk : k+2 ≤ T := by omega
  have hm : d+3 ≤ T := by omega
  have hz : 3*d ≤ T := by omega
  have m₂ {a b : ℕ} (ha : a ≤ T) (hb : b ≤ T) : a*b ≤ T^2 := by
    simpa only [pow_two] using Nat.mul_le_mul ha hb
  have hTP := tapeBudget (k:=k) (r:=r) (q:=q) hT hN (by omega : R ≤ 2*T)
  have hFI : card (FormIx k r) = L*3 := by simp [FormIx,L]
  have hFD : card (FormData k r) = L*3*(N+1) := by simp [FormData,hFI,Param,N]
  have hBI : card (BasisIx k r n) = n+L := by simp [BasisIx,L]
  have hWP := widthBudget (J:=FormIx k r) (U:=Param k r) (d:=d) hT
    (hFI.symm ▸ (by omega : L*3 ≤ 3*T)) (by simpa only [Param,card_fin] using (show N ≤ T by omega)) (show d ≤ T by omega)
  have hPre : preCost k r q n d ≤ 2^41*T^7 := by
    rw [preCost,hFD,hBI]
    have h := Nat.mul_le_mul (show n+L ≤ 2*T by omega) hWP
    nlinarith only [hTP,m₂ hL hN,h,hpow (show 6 ≤ 7 by decide),hpow (show 2 ≤ 7 by decide)]
  have hLoc := compactLocalCostBound k r d T B hT hB0 hN (by omega) hm
  have hPT := preStateCardBound k r q n d T hT hN hd hn hL hk (by omega)
  have hTab : card (TableIx k r d) ≤ T*B := by
    simp only [TableIx,Addr,card_prod,card_fin]
    change 2^d*(N+1) ≤ T*B
    exact (Nat.mul_le_mul hB' hN).trans_eq (mul_comm _ _)
  have hSch := compactScheduleCostBound k r q n d T B hT hB hn (by omega) hTab hPT hLoc
  have hFin := countCostBound k r n T hT hn (by omega) hk
  have hOr : compactOracleCost k r q n d ≤ 2^67*T^33*B := by
    unfold compactOracleCost
    nlinarith only [hPre,hSch,hFin,Nat.mul_le_mul (hpow (show 7 ≤ 33 by decide)) hB,
      Nat.mul_le_mul (hpow (show 5 ≤ 33 by decide)) hB,Nat.mul_le_mul (h₁ 33) hB]
  have ho := Nat.mul_le_mul (show k+1 ≤ T by omega) hOr
  have hb : (k+1)*compactOracleCost k r q n d + k*k+3*k+2+1 ≤ 2^69*T^34*B := by
    nlinarith only [ho,m₂ (show k ≤ T by omega) (show k ≤ T by omega),hk,
      Nat.mul_le_mul (hpow (show 2 ≤ 34 by decide)) hB,
      Nat.mul_le_mul (hsmall 34 (by decide)) hB,Nat.mul_le_mul (h₁ 34) hB]
  rw [hB0, ← hPdef]
  refine hb.trans ?_
  calc
    _ = (2^69*4^34)*(P^68*B) := by
      rw [← hT0, mul_pow, ← pow_mul]
      simp only [Nat.mul_assoc]
    _ = 2^137*P^68*B := by
      rw [show (2 : ℕ)^69*4^34 = 2^137 by norm_num]
      exact (Nat.mul_assoc _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right B (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by decide))
      (Nat.pow_le_pow_right (by omega) (by decide)))

end Helpers

namespace Donor

open PEqualNP.CircuitLowerBounds

theorem Cmp.extract {ι κ : Type} {S : ℕ} {F : (ι → Bool) → κ → Bool} (h : Cmp ι κ S F)
    (n : ℕ) (ws : ι → ℕ) (hws : ∀ j, ws j < n + 1) :
    ∃ (gs : List Gate) (outs : κ → ℕ),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) ∧
      (∀ o : ℕ, PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨gs, o⟩) ∧
      gs.length ≤ S + 1 ∧ (∀ k, outs k < n + gs.length) ∧
      ∀ (o : ℕ) (x : List Bool), x.length = n → ∀ k,
        ((⟨gs, o⟩ : Circuit).wires x).getD (outs k) false =
          F (fun j => (x ++ [false]).getD (ws j) false) k := by
  have g0 : Good n [⟨GateOp.or, []⟩] := by
    have := fa_good_snoc n [] ⟨GateOp.or, []⟩ ⟨by simp, by simp⟩ (by simp) (by simp) (by simp)
    simpa using this
  obtain ⟨more, outs, g1, l1, b1, v1⟩ := h n [⟨GateOp.or, []⟩] g0 (by simp) ws
    (by simpa using hws)
  refine ⟨[(⟨GateOp.or, []⟩ : Gate)] ++ more, outs, g1.1,
    fun o => by intro j hj i hi; exact g1.2 j hj i hi, by simp; omega, ?_, ?_⟩
  · intro k; have := b1 k; simp at this ⊢; omega
  · intro o x hx k
    exact v1 x hx k

end Donor

namespace Serialization

open PEqualNP.Outside.L_meta_29774_aux PEqualNP.Outside.L_meta_29774_aux.PackedTape

variable {k r q n : ℕ}

private def sides {α : Type} (f : Bool → List α) : List α := f false ++ f true
private def rows {α : Type} {m : ℕ} (f : Fin m → List α) : List α := (List.finRange m).flatMap f
private def lane {α : Type} {m k : ℕ} (f : Fin m → Fin k → α) : List α :=
  rows (fun t => List.ofFn (f t))

private theorem length_rows {α : Type} {m : ℕ} (f : Fin m → List α) (d : ℕ)
    (h : ∀ i, (f i).length = d) : (rows f).length = m * d := by
  change ((List.ofFn (fun i : Fin m => i)).flatMap f).length = m * d
  simp only [List.length_flatMap, List.map_ofFn, Function.comp_def, h, List.ofFn_const,
    List.sum_replicate_nat]

private theorem length_lane {α : Type} {m k : ℕ} (f : Fin m → Fin k → α) :
    (lane f).length = m * k :=
  length_rows _ _ (fun _ => by simp)

private theorem mem_sides {α : Type} {f : Bool → List α} (b : Bool) {a : α}
    (h : a ∈ f b) : a ∈ sides f := by
  cases b
  · exact List.mem_append_left _ h
  · exact List.mem_append_right _ h

private theorem mem_rows {α : Type} {m : ℕ} {f : Fin m → List α} (i : Fin m) {a : α}
    (h : a ∈ f i) : a ∈ rows f :=
  List.mem_flatMap.mpr ⟨i, List.mem_finRange i, h⟩

private theorem mem_lane {α : Type} {m k : ℕ} (f : Fin m → Fin k → α) (t : Fin m) (j : Fin k) :
    f t j ∈ lane f :=
  mem_rows t (List.mem_ofFn.mpr ⟨j, rfl⟩)

private def bagRow (v : Fin n) : List (InputSlot k r q n) :=
  List.ofFn (fun j => bagSlot v (.inl j)) ++ sides (fun b => lane (fun t j => bagSlot v (.inr (b, t, j))))

private theorem bagRow_length (v : Fin n) :
    (bagRow (k := k) (r := r) (q := q) v).length = (2 * r + 1) * k := by
  simp only [bagRow, sides, List.length_append, List.length_ofFn, length_lane]
  ring

def wordBits (v : Word k) : List Bool := List.ofFn (fun j : Fin k => decide (v j ≠ 0))
def obsLaneBits (side : Bool) (tape : Tape k r) : List Bool :=
  (List.finRange (r + 1)).flatMap (fun j => wordBits (tape.2 side j))
def leafBits (p : Leaf k r → Bool) : List Bool :=
  List.ofFn (fun j : Fin k => p (.inl j)) ++
    [false, true].flatMap (fun b => (List.finRange r).flatMap (fun t =>
      List.ofFn (fun j : Fin k => p (.inr (b, t, j)))))

section SlotBits
variable (name : Bool → Word k) (c : Bool → Fin r → Word k) (obs : Fin q → Tape k r)
    (rhs : Fin q → F) (bag : Fin n → Leaf k r → Bool)

@[simp] theorem slotBit_name (b : Bool) (j : Fin k) :
    slotBit name c obs rhs bag (nameSlot b j) = decide (name b j ≠ 0) := rfl
@[simp] theorem slotBit_c (b : Bool) (t : Fin r) (j : Fin k) :
    slotBit name c obs rhs bag (cSlot b t j) = decide (c b t j ≠ 0) := rfl
@[simp] theorem slotBit_obsKey (i : Fin q) (j : Fin k) :
    slotBit name c obs rhs bag (obsKeySlot i j) = decide ((obs i).1 j ≠ 0) := rfl
@[simp] theorem slotBit_obsTape (i : Fin q) (b : Bool) (t : Fin (r + 1)) (j : Fin k) :
    slotBit name c obs rhs bag (obsTapeSlot i b t j) = decide ((obs i).2 b t j ≠ 0) := rfl
@[simp] theorem slotBit_rhs (i : Fin q) :
    slotBit name c obs rhs bag (rhsSlot i) = decide (rhs i ≠ 0) := rfl
@[simp] theorem slotBit_bag (v : Fin n) (l : Leaf k r) :
    slotBit name c obs rhs bag (bagSlot v l) = bag v l := rfl

end SlotBits

end Serialization

namespace Serialization

open PEqualNP.Outside.L_meta_29774_aux PEqualNP.Outside.L_meta_29774_aux.PackedTape
open Donor

variable {k r q n digits : ℕ}

abbrev ObsPort (k r q : ℕ) := Fin q × Coord k r
abbrev EvalPort (k r q n digits : ℕ) := InputSlot k r q n ⊕ Fin digits

private def tapePorts {α : Type} (tag : Coord k r → α) : List α :=
  List.ofFn (fun j => tag (.inl j)) ++
    sides (fun b => lane (fun t j => tag (.inr (b,t,j))))

theorem length_tapePorts {α : Type} (tag : Coord k r → α) :
    (tapePorts tag).length = tapeSize k r := by
  simp only [tapePorts, sides, List.length_append, List.length_ofFn, length_lane, tapeSize]
  ring

theorem mem_tapePorts {α : Type} (tag : Coord k r → α) (u : Coord k r) :
    tag u ∈ tapePorts tag := by
  rcases u with j | ⟨b,t,j⟩
  · apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · apply List.mem_append_right
    exact mem_sides b (mem_lane (fun t j => tag (.inr (b,t,j))) t j)

def obsOrder (k r q : ℕ) : List (ObsPort k r q) :=
  rows (fun i => tapePorts (fun u => (i,u)))

def obsBit (obs : Fin q → Tape k r) (p : ObsPort k r q) : Bool :=
  p.2.elim (fun j => zbit ((obs p.1).1 j))
    (fun (b,t,j) => zbit ((obs p.1).2 b t j))

def masks (obs : Fin q → Tape k r) : List Bool :=
  (List.finRange q).flatMap (fun i =>
    wordBits (obs i).1 ++ obsLaneBits false (obs i) ++ obsLaneBits true (obs i))

theorem map_tapePorts {α : Type} (tag : Coord k r → α) (f : α → Bool) (obs : Tape k r)
    (h : ∀ u, f (tag u) = obsBit (fun _ : Fin 1 => obs) (0,u)) :
    (tapePorts tag).map f = wordBits obs.1 ++ obsLaneBits false obs ++ obsLaneBits true obs := by
  simp only [tapePorts, sides, lane, rows, wordBits, obsLaneBits, List.map_append,
    List.map_flatMap, List.map_ofFn, Function.comp_def, h, obsBit, elim_inl, elim_inr,
    List.append_assoc, zbit]

theorem map_obsOrder (obs : Fin q → Tape k r) :
    (obsOrder k r q).map (obsBit obs) = masks obs := by
  unfold obsOrder rows masks
  rw [List.map_flatMap]
  congr 1
  funext i
  exact map_tapePorts (fun u => (i,u)) _ (obs i) (fun _ => rfl)

theorem obsOrder_length : (obsOrder k r q).length = q * tapeSize k r :=
  length_rows _ _ (fun _ => length_tapePorts _)

theorem obsOrder_mem (s : ObsPort k r q) : s ∈ obsOrder k r q :=
  mem_rows s.1 (mem_tapePorts (fun u => (s.1,u)) s.2)

def obsSlot (i : Fin q) (u : Coord k r) : InputSlot k r q n :=
  u.elim (obsKeySlot i) (fun (b,t,j) => obsTapeSlot i b t j)

def evalOrder (k r q n digits : ℕ) : List (EvalPort k r q n digits) :=
  rows (fun i => tapePorts (fun u => .inl (obsSlot i u))) ++
  rows (fun v => (bagRow v).map inl) ++
  List.ofFn inr ++
  sides (fun b => List.ofFn (fun j => .inl (nameSlot b j))) ++
  sides (fun b => lane (fun t j => .inl (cSlot b t j))) ++
  List.ofFn (fun i => .inl (rhsSlot i))

def evalBits (obs : Fin q → Tape k r) (bag : Fin n → Leaf k r → Bool)
    (price : Fin digits → Bool) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (rhs : Fin q → F) : List Bool :=
  masks obs ++ (List.finRange n).flatMap (fun v => leafBits (bag v)) ++
    List.ofFn price ++ wordBits (name false) ++ wordBits (name true) ++
    [false,true].flatMap (fun b => (List.finRange r).flatMap (fun t => wordBits (c b t))) ++
    List.ofFn (fun j : Fin q => decide (rhs j ≠ 0))

theorem evalOrder_length : (evalOrder k r q n digits).length =
    q * tapeSize k r + n * ((2*r+1)*k) + digits + (2+2*r)*k + q := by
  have ht : (rows (fun i => tapePorts (fun u => (inl (obsSlot i u) : EvalPort k r q n digits)))).length =
      q * tapeSize k r := length_rows _ _ (fun _ => length_tapePorts _)
  have hb : (rows (fun v => (bagRow v).map (inl : InputSlot k r q n → EvalPort k r q n digits))).length =
      n * ((2*r+1)*k) := length_rows _ _ (fun v => by rw [List.length_map, bagRow_length])
  simp only [evalOrder, ht, hb, sides, List.length_append, List.length_ofFn, length_lane]
  ring

theorem evalOrder_mem (s : InputSlot k r q n) : inl s ∈ evalOrder k r q n digits := by
  have hObs (i : Fin q) (u : Coord k r) : inl (obsSlot i u) ∈ evalOrder k r q n digits := by
    unfold evalOrder
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (mem_rows i (mem_tapePorts _ u))))))
  rcases s with ⟨b,j⟩ | (⟨b,t,j⟩ | (⟨i, u⟩ | ⟨v, u⟩))
  · unfold evalOrder
    exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (mem_sides b (List.mem_ofFn.mpr ⟨j, rfl⟩))))
  · unfold evalOrder
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_sides b (mem_lane (fun t j => (inl (cSlot b t j) : EvalPort k r q n digits)) t j)))
  · rcases u with j | (⟨b,t,j⟩ | ⟨⟩)
    · exact hObs i (.inl j)
    · exact hObs i (.inr (b,t,j))
    · unfold evalOrder
      exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · have hm : bagSlot (q:=q) v u ∈ bagRow v := by
      rcases u with j | ⟨b,t,j⟩
      · exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
      · exact List.mem_append_right _ (mem_sides b (mem_lane _ t j))
    unfold evalOrder
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _
        (mem_rows v (List.mem_map.mpr ⟨_,hm,rfl⟩))))))

theorem map_evalOrder (obs : Fin q → Tape k r) (bag : Fin n → Leaf k r → Bool)
    (price : Fin digits → Bool) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (rhs : Fin q → F) :
    (evalOrder k r q n digits).map (elim (slotBit name c obs rhs bag) price) =
      evalBits obs bag price name c rhs := by
  unfold evalOrder evalBits
  let f := elim (slotBit name c obs rhs bag) price
  have ho (i : Fin q) :
      (tapePorts (fun u => (inl (obsSlot i u) : EvalPort k r q n digits))).map f =
        wordBits (obs i).1 ++ obsLaneBits false (obs i) ++ obsLaneBits true (obs i) := by
    apply map_tapePorts
    rintro (j | ⟨b,t,j⟩) <;> rfl
  have hb (v : Fin n) : ((bagRow v).map (inl : _ → EvalPort k r q n digits)).map f =
      leafBits (bag v) := by
    simp only [bagRow, sides, lane, rows, leafBits, List.map_map, List.map_append, List.map_flatMap,
      List.map_ofFn, Function.comp_def, f, elim_inl, slotBit_bag, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
  simp only [List.map_append, rows, List.map_flatMap, ho, hb, masks, List.map_ofFn, Function.comp_def,
    f, elim_inl, elim_inr, sides, lane, rows, slotBit_name, slotBit_c, slotBit_rhs, wordBits,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

noncomputable def address {α : Type} (slots : List α) (a : α) : ℕ := by
  classical
  exact slots.idxOf a

theorem address_lt {α : Type} {slots : List α} {a : α} (ha : a ∈ slots) :
    address slots a < slots.length := by
  classical
  exact List.idxOf_lt_length_of_mem ha

theorem address_read {α : Type} (slots : List α) (a : α) (ha : a ∈ slots) (f : α → Bool) :
    ((slots.map f) ++ [false]).getD (address slots a) false = f a := by
  have h := address_lt ha
  have hmap : address slots a < (slots.map f).length := by simpa using h
  rw [List.getD_append _ _ _ _ hmap, List.getD_eq_getElem _ _ hmap, List.getElem_map]
  classical
  exact congrArg f (List.getElem_idxOf (List.idxOf_lt_length_of_mem ha))

end Serialization

namespace Design

variable {J T : Type} [Fintype J] [DecidableEq J] [Fintype T]
variable {n : ℕ}

def support (p : J → Bool) : Finset J :=
  Finset.univ.filter fun j => p j = true

def nodes (p : J → Bool) : ℕ := 2 * (support p).card - 1

def Single (p : J → Bool) : Prop := ∃ j, p = fun a => decide (a = j)

def Apart (a b : J → Bool) : Prop := ∀ j, a j = true → b j = false

def Cover (p a b : J → Bool) : Prop := Apart a b ∧ p = fun j => a j || b j

def Row (bag : Fin n → J → Bool) (v : Fin n) : Prop :=
  Single (bag v) ∨ ∃ l h : Fin n, l < v ∧ h < v ∧ Cover (bag v) (bag l) (bag h)

abbrev Bank (J T : Type) (n : ℕ) := T × (Unit ⊕ (Fin n × J))

def ready (x : Bank J T n → Bool) (p : T) := x (p, .inl ())
def rows (x : Bank J T n → Bool) (p : T) (i : Fin n) (j : J) := x (p, .inr (i,j))

theorem single_iff (p : J → Bool) : Single p ↔ (support p).card = 1 := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by ext j; simp [support]⟩
  · rintro ⟨a, h⟩
    refine ⟨a, funext fun j => ?_⟩
    have hj : p j = true ↔ j = a := by
      simpa [support] using (Finset.ext_iff.mp h j)
    exact Bool.eq_iff_iff.mpr (hj.trans (Iff.of_eq decide_eq_true_eq).symm)

theorem support_cover {p a b : J → Bool} (h : Cover p a b) :
    (support p).card = (support a).card + (support b).card := by
  obtain ⟨hd, hp⟩ := h
  unfold support
  rw [hp]
  have hs : (Finset.univ.filter fun j => (a j || b j) = true) =
      (Finset.univ.filter fun j => a j = true) ∪ (Finset.univ.filter fun j => b j = true) := by
    ext j
    simp [Bool.or_eq_true]
  rw [hs, Finset.card_union_of_disjoint]
  refine Finset.disjoint_left.mpr ?_
  intro j hj hj'
  have h1 : a j = true := (Finset.mem_filter.mp hj).2
  have h2 : b j = true := (Finset.mem_filter.mp hj').2
  simp [hd j h1] at h2

def Cert (mask : T → J → Bool) (pass : T → Bool) (p : T)
    (bag : Fin n → J → Bool) : Prop :=
  0 < nodes (mask p) ∧ nodes (mask p) ≤ n ∧
    (∀ v : Fin n, v.val + 1 = nodes (mask p) → bag v = mask p) ∧
    ∀ v : Fin n, v.val < nodes (mask p) → (∃ q, pass q = true ∧ bag v = mask q) ∧ Row bag v

def joinRows (mask : T → J → Bool) (p a b : T)
    (A B : Fin n → J → Bool) (v : Fin n) : J → Bool :=
  if v.val < nodes (mask a) then A v
  else if v.val < nodes (mask a) + nodes (mask b) then
    B ⟨v.val - nodes (mask a), (Nat.sub_le ..).trans_lt v.isLt⟩
  else mask p

theorem cert_single (mask : T → J → Bool) (pass : T → Bool) (p : T)
    (hp : pass p = true) (hs : (support (mask p)).card = 1) (hn : 0 < n) :
    Cert (n:=n) mask pass p (fun _ => mask p) := by
  have hnodes : nodes (mask p) = 1 := by simp [nodes, hs]
  refine ⟨by omega, by omega, fun _ _ => rfl, fun _ _ => ⟨⟨p, hp, rfl⟩, ?_⟩⟩
  exact Or.inl ((single_iff _).mpr hs)

theorem cert_join (mask : T → J → Bool) (pass : T → Bool) (p a b : T)
    (hp : pass p = true) (hc : Cover (mask p) (mask a) (mask b))
    (hpn : nodes (mask p) ≤ n) {A B : Fin n → J → Bool}
    (ha : Cert mask pass a A) (hb : Cert mask pass b B) :
    Cert mask pass p (joinRows mask p a b A B) := by
  let m := nodes (mask a)
  let t := nodes (mask b)
  let C := joinRows mask p a b A B
  obtain ⟨ha, han, har, hav⟩ := ha
  obtain ⟨hb, hbn, hbr, hbv⟩ := hb
  have hlen : nodes (mask p) = m + t + 1 := by
    dsimp only [m, t, nodes] at *
    have h := support_cover hc
    omega
  have hA (v : Fin n) (hv : v.val < m) : C v = A v := by
    exact if_pos hv
  have hB (v : Fin n) (hv : v.val < t) :
      C ⟨m + v.val, by omega⟩ = B v := by
    simp [C, joinRows, ← show m = nodes (mask a) from rfl,
      ← show t = nodes (mask b) from rfl, hv]
  have hC (v : Fin n) (hv : m + t ≤ v.val) : C v = mask p := by
    have hh : ¬ v.val < m + t := by omega
    have hh' : ¬ v.val < m := by omega
    exact (if_neg hh').trans (if_neg hh)
  change Cert mask pass p C
  refine ⟨by omega, hpn, fun v hv => hC v (by omega), ?_⟩
  intro v hv
  by_cases hvm : v.val < m
  · obtain ⟨⟨q, hq, he⟩, h | ⟨l, r, hl, hr, h⟩⟩ := hav v hvm
    · exact ⟨⟨q, hq, (hA v hvm).trans he⟩, Or.inl (hA v hvm ▸ h)⟩
    change l.val < v.val at hl
    change r.val < v.val at hr
    refine ⟨⟨q, hq, (hA v hvm).trans he⟩, Or.inr ⟨l, r, hl, hr, ?_⟩⟩
    simpa only [hA v hvm, hA l (by omega), hA r (by omega)] using h
  by_cases hvt : v.val < m + t
  · let i : Fin n := ⟨v.val - m, (Nat.sub_le ..).trans_lt v.isLt⟩
    have hi : i.val < t := by dsimp [i]; omega
    have ei : v = ⟨m+i.val, by omega⟩ := Fin.ext (by dsimp [i]; omega)
    have e : C v = B i := by nth_rw 1 [ei]; exact hB i hi
    obtain ⟨⟨q, hq, he⟩, h | ⟨l, r, hl, hr, h⟩⟩ := hbv i hi
    · exact ⟨⟨q, hq, e.trans he⟩, Or.inl (e ▸ h)⟩
    change l.val < i.val at hl
    change r.val < i.val at hr
    let al : Fin n := ⟨m+l.val, by omega⟩
    let ar : Fin n := ⟨m+r.val, by omega⟩
    have ei' : v.val = m+i.val := congrArg Fin.val ei
    refine ⟨⟨q,hq,e.trans he⟩, Or.inr ⟨al,ar,?_,?_,?_⟩⟩
    · change m+l.val < v.val
      omega
    · change m+r.val < v.val
      omega
    · simpa only [e, show C al = B l from hB l (by omega),
        show C ar = B r from hB r (by omega)] using h
  have hv' : v.val = m+t := by omega
  let l : Fin n := ⟨m-1, by omega⟩
  let r : Fin n := ⟨t-1, by omega⟩
  let ar : Fin n := ⟨m+r.val, by dsimp [r]; omega⟩
  have hl : l.val < m := by dsimp [l]; omega
  have hr : r.val < t := by dsimp [r]; omega
  have el : C l = mask a := (hA l hl).trans (har l (by dsimp [l]; omega))
  have er : C ar = mask b := (hB r hr).trans (hbr r (by dsimp [r]; omega))
  have ev := hC v (by omega)
  refine ⟨⟨p,hp,ev⟩, Or.inr ⟨l, ar, ?_, ?_, ?_⟩⟩
  · change l.val < v.val
    omega
  · change m+r.val < v.val
    omega
  · simpa only [ev, el, er] using hc

def First {α : Type} (key : α → ℕ) (f : α → Bool) (a : α) : Prop :=
  f a = true ∧ ∀ b, key b < key a → f b = false

theorem first_exists {α : Type} (key : α → ℕ) (f : α → Bool)
    (h : ∃ a, f a = true) : ∃ a, First key f a := by
  classical
  have he : ∃ m, ∃ a, key a = m ∧ f a = true := by
    obtain ⟨a, ha⟩ := h
    exact ⟨key a, a, rfl, ha⟩
  obtain ⟨a, e, ha⟩ := Nat.find_spec he
  refine ⟨a, ha, fun b hb => ?_⟩
  cases hf : f b
  · rfl
  · exact False.elim (not_lt_of_ge (Nat.find_min' he ⟨b, rfl, hf⟩) (e ▸ hb))

theorem first_unique {α : Type} {key : α → ℕ} (hinj : Injective key)
    {f : α → Bool} {a b : α} (ha : First key f a) (hb : First key f b) : a = b := by
  apply hinj
  rcases lt_trichotomy (key a) (key b) with h | h | h
  · exact False.elim (Bool.noConfusion (ha.1.symm.trans (hb.2 a h)))
  · exact h
  · exact False.elim (Bool.noConfusion (hb.1.symm.trans (ha.2 b h)))

noncomputable def chooseBit {α : Type} (key : α → ℕ) (f g : α → Bool) : Bool := by
  classical
  exact decide (∃ a, First key f a ∧ g a = true)

theorem chooseBit_eq {α : Type} {key : α → ℕ} (hinj : Injective key)
    {f g : α → Bool} {a : α} (ha : First key f a) : chooseBit key f g = g a := by
  classical
  rw [Bool.eq_iff_iff, chooseBit, decide_eq_true_eq]
  exact ⟨fun ⟨b,hb,hg⟩ => first_unique hinj hb ha ▸ hg, fun hg => ⟨a,ha,hg⟩⟩

noncomputable def orderKey (α : Type) [Fintype α] (a : α) : ℕ :=
  (Fintype.equivFin α a).val

theorem orderKey_injective (α : Type) [Fintype α] : Injective (orderKey α) :=
  fun _ _ e => (Fintype.equivFin α).injective (Fin.ext e)

noncomputable def candidate (mask : T → J → Bool)
    (x : Bank J T n → Bool) (p : T) (ab : T × T) : Bool := by
  classical
  exact decide (Cover (mask p) (mask ab.1) (mask ab.2)) && ready x ab.1 && ready x ab.2

theorem candidate_true {mask : T → J → Bool} {x : Bank J T n → Bool} {p : T} {ab : T × T} :
    candidate mask x p ab = true ↔
      Cover (mask p) (mask ab.1) (mask ab.2) ∧ ready x ab.1 = true ∧ ready x ab.2 = true := by
  classical
  simp only [candidate, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

noncomputable def step (mask : T → J → Bool) (pass : T → Bool)
    (x : Bank J T n → Bool) : Bank J T n → Bool := by
  classical
  exact fun (p, bit) => if pass p = true then
    if (support (mask p)).card = 1 then bit.elim (fun _ => true) (fun v => mask p v.2)
    else bit.elim (fun _ => decide (∃ ab, candidate mask x p ab = true))
      (fun v => chooseBit (orderKey (T × T)) (candidate mask x p) fun ab =>
        joinRows mask p ab.1 ab.2 (rows x ab.1) (rows x ab.2) v.1 v.2)
    else false

noncomputable def run (mask : T → J → Bool) (pass : T → Bool) : ℕ → Bank J T n → Bool
  | 0 => fun _ => false
  | t+1 => step mask pass (run mask pass t)

theorem run_sound (mask : T → J → Bool) (pass : T → Bool)
    (hn : 0 < n) (hs : ∀ p, nodes (mask p) ≤ n) (t : ℕ) (p : T)
    (hp : ready (run mask pass t : Bank J T n → Bool) p = true) :
    Cert (n:=n) mask pass p (rows (run mask pass t) p) := by
  classical
  induction t generalizing p with
  | zero => contradiction
  | succ t ih =>
    by_cases hpass : pass p = true
    · by_cases hsingle : (support (mask p)).card = 1
      · have hrow : rows (run mask pass (t+1)) p = fun _ : Fin n => mask p := by
          funext i j
          simp [rows, run, step, hpass, hsingle]
        rw [hrow]
        exact cert_single mask pass p hpass hsingle hn
      · let x : Bank J T n → Bool := run mask pass t
        have he : ∃ ab, candidate mask x p ab = true := by
          simpa [ready, run, step, hpass, hsingle, x] using hp
        obtain ⟨ab, hab⟩ := first_exists (orderKey (T × T)) _ he
        obtain ⟨hc, ha, hb⟩ := candidate_true.mp hab.1
        have hrow : rows (run mask pass (t+1)) p =
            joinRows mask p ab.1 ab.2 (rows x ab.1) (rows x ab.2) := by
          funext i j
          simp only [rows, run, step, hpass, hsingle, ↓reduceIte, elim_inr]
          exact chooseBit_eq (orderKey_injective _) hab
        rw [hrow]
        exact cert_join mask pass p ab.1 ab.2 hpass hc (hs p) (ih _ ha) (ih _ hb)
    · simp [ready, run, step, hpass] at hp

theorem run_complete (mask : T → J → Bool) (pass : T → Bool)
    (bag : Fin n → J → Bool) (hrow : ∀ v, Row bag v)
    (hmask : ∀ v, ∃ p, pass p = true ∧ bag v = mask p)
    (v : Fin n) (p : T) (he : bag v = mask p) (hp : pass p = true)
    (t : ℕ) (ht : v.val < t) :
    ready (run mask pass t : Bank J T n → Bool) p = true := by
  classical
  induction t generalizing v p with
  | zero => omega
  | succ t ih =>
    by_cases hsingle : (support (mask p)).card = 1
    · simp [ready, run, step, hp, hsingle]
    have hjoin : ∃ ab, candidate mask (run mask pass t : Bank J T n → Bool) p ab = true := by
      rcases hrow v with h | ⟨l,r,hl,hr,h⟩
      · exact False.elim (hsingle ((single_iff _).mp (he ▸ h)))
      change l.val < v.val at hl
      change r.val < v.val at hr
      obtain ⟨a,ha,ea⟩ := hmask l
      obtain ⟨b,hb,eb⟩ := hmask r
      refine ⟨(a,b), candidate_true.mpr ⟨?_, ih l a ea ha (by omega), ih r b eb hb (by omega)⟩⟩
      simpa only [he,ea,eb] using h
    simp [ready, run, step, hp, hsingle, hjoin]

def capReady {c : ℕ} (root : T) (bank : Fin (c+1) × Bank J T n → Bool) (d : Fin (c+1)) : Bool :=
  ready (fun u => bank (d,u)) root

noncomputable def output {c digits : ℕ} (root : T)
    (bank : Fin (c+1) × Bank J T n → Bool) :
    (Fin n × J) ⊕ Fin digits → Bool :=
  elim
    (fun v => chooseBit Fin.val (capReady root bank) fun d => rows (fun u => bank (d,u)) root v.1 v.2)
    (fun e => chooseBit Fin.val (capReady root bank) fun d => d.val.testBit e.val)

theorem output_spec (mask : T → J → Bool) (root : T)
    (hroot : mask root = fun _ => true) (hn : 0 < n)
    (hs : ∀ p, nodes (mask p) ≤ n) (hsize : nodes (mask root) = n)
    (rank : (J → Bool) → ℕ) (c digits : ℕ) (hrank : ∀ p, rank (mask p) ≤ c)
    (bag₀ : Fin n → J → Bool) (hrow₀ : ∀ v, Row bag₀ v)
    (hmask₀ : ∀ v, ∃ p, bag₀ v = mask p) (hroot₀ : ∃ v, bag₀ v = fun _ => true) :
    let bank : Fin (c+1) × Bank J T n → Bool := fun (d,u) =>
      run mask (fun p => decide (rank (mask p) ≤ d.val)) n u
    let o : (Fin n × J) ⊕ Fin digits → Bool := output root bank
    let bag := fun (v : Fin n) (j : J) => o (.inl (v,j))
    ∃ d : Fin (c+1),
      (∀ e : Fin digits, o (.inr e) = d.val.testBit e.val) ∧
      (∃ top : Fin n, bag top = fun _ => true) ∧
      (∀ v, Row bag v ∧ (∃ p, bag v = mask p) ∧ rank (bag v) ≤ d.val) ∧
      ∀ (alt : Fin n → J → Bool) (cost : ℕ),
        (∃ top : Fin n, alt top = fun _ => true) →
        (∀ v, Row alt v ∧ (∃ p, alt v = mask p) ∧ rank (alt v) ≤ cost) →
        d.val ≤ cost := by
  classical
  intro bank o bag
  let F := capReady root bank
  obtain ⟨top,hTop⟩ := hroot₀
  have hx : F ⟨c, by omega⟩ = true := by
    change ready (run mask (fun p => decide (rank (mask p) ≤ c)) n : Bank J T n → Bool) root = true
    apply run_complete mask _ bag₀ hrow₀ _ top root (hTop.trans hroot.symm)
      (decide_eq_true (hrank root)) n top.isLt
    intro v
    obtain ⟨p,hp⟩ := hmask₀ v
    exact ⟨p,decide_eq_true (hrank p),hp⟩
  obtain ⟨d,hd⟩ := first_exists Fin.val F ⟨⟨c,by omega⟩,hx⟩
  let now : Bank J T n → Bool := fun u => bank (d,u)
  have ho : bag = rows now root := by
    funext v j
    exact chooseBit_eq Fin.val_injective hd
  have hv : Cert mask (fun p => decide (rank (mask p) ≤ d.val)) root bag := by
    rw [ho]
    exact run_sound mask _ hn hs n root hd.1
  obtain ⟨_,_,hfull,hgood⟩ := hv
  refine ⟨d, fun _ => chooseBit_eq Fin.val_injective hd, ⟨⟨n-1, by omega⟩,?_⟩, ?_, ?_⟩
  · exact (hfull _ (by rw [hsize]; simp; omega)).trans hroot
  · intro v
    obtain ⟨⟨p,hp,he⟩,hv⟩ := hgood v (hsize.symm ▸ v.isLt)
    exact ⟨hv,⟨p,he⟩,he.symm ▸ of_decide_eq_true hp⟩
  · intro alt cost hAlt hAv
    by_contra h
    have hc : cost < d.val := by omega
    let dc : Fin (c+1) := ⟨cost, hc.trans d.isLt⟩
    obtain ⟨a,ha⟩ := hAlt
    have he : F dc = true := by
      change ready (run mask (fun p => decide (rank (mask p) ≤ cost)) n : Bank J T n → Bool) root = true
      apply run_complete mask _ alt (fun v => (hAv v).1) _ a root (ha.trans hroot.symm) _ n a.isLt
      · intro v
        obtain ⟨_, ⟨p,hp⟩, hw⟩ := hAv v
        exact ⟨p,decide_eq_true (hp ▸ hw),hp⟩
      · exact decide_eq_true (ha.trans hroot.symm ▸ (hAv a).2.2)
    exact Bool.noConfusion (he.symm.trans (hd.2 dc hc))

abbrev Rect (k r : ℕ) :=
  Fin k × Fin (k+1) × (Bool → Fin k) × (Bool → Fin k) ×
    (Bool → Fin (k+1)) × (Bool → Fin (r+1)) × (Bool → Fin (r+1))

abbrev Leaf (k r : ℕ) := Fin k ⊕ (Bool × Fin r × Fin k)

def shape {k r : ℕ} (hk : 0 < k) : Rect k r → Leaf k r → Bool
  | (site,len,slope,origin,width,lo,hi) =>
    let arc := fun (j a : Fin k) (w : Fin (k+1)) => (j.val+k-a.val) % k < w.val
    elim (fun j => decide (arc j site len)) (fun (b,t,j) =>
      decide ((lo b).val ≤ t.val ∧ t.val < (hi b).val ∧
        arc j ⟨((origin b).val + (slope b).val*t.val) % k, Nat.mod_lt _ hk⟩ (width b)))

def whole {k r : ℕ} (hk : 0 < k) : Rect k r :=
  (⟨0,hk⟩, Fin.last k, fun _ => ⟨0,hk⟩, fun _ => ⟨0,hk⟩,
    fun _ => Fin.last k, fun _ => 0, fun _ => Fin.last r)

theorem shape_whole {k r : ℕ} (hk : 0 < k) :
    shape (r:=r) hk (whole hk) = fun _ => true := by
  funext i
  rcases i with j | ⟨b,t,j⟩
  · exact decide_eq_true (Nat.mod_lt _ hk)
  · exact decide_eq_true ⟨Nat.zero_le _, t.isLt, Nat.mod_lt _ hk⟩

theorem leafCount (k r : ℕ) : card (Leaf k r) = (2*r+1)*k := by
  simp only [Leaf, card_sum, card_prod, card_bool, card_fin]
  ring

theorem nodes_le (p : J → Bool) : nodes p ≤ 2*card J-1 := by
  have h := Finset.card_le_univ (support p)
  unfold nodes
  omega

theorem nodes_full : nodes (fun _ : J => true) = 2*card J-1 := by
  simp [nodes, support]

theorem rows_iff (bag : Fin n → J → Bool) (v : Fin n) :
    Row bag v ↔ (∃ one : J, ∀ i, bag v i = decide (i = one)) ∨
      ∃ l h : Fin n, l < v ∧ h < v ∧ (∀ i, bag l i = true → bag h i = false) ∧
        ∀ i, bag v i = (bag l i || bag h i) := by
  simp [Row, Single, Cover, Apart, funext_iff]

end Design

namespace Design

open Donor

def selectCost (m s t : ℕ) : ℕ := m * (s + m * (s+2) + t + 4) + 1

theorem select_cb {E K : Type} [Fintype K] (key : K → ℕ)
    {s t : ℕ} (f g : K → (E → Bool) → Bool)
    (hf : ∀ k, Cb E s (f k)) (hg : ∀ k, Cb E t (g k)) :
    Cb E (selectCost (card K) s t)
      (fun x => chooseBit key (fun k => f k x) (fun k => g k x)) := by
  classical
  let before (a b : K) (x : E → Bool) := if key b < key a then !(f b x) else true
  have hbefore (a b : K) : Cb E (s+1) (before a b) := by
    by_cases e : key b < key a
    · simpa [before,e] using Cb.not (hf b)
    · simpa [before,e] using (Cb.const (ι:=E) true).mono (by omega : 1 ≤ s+1)
  have hinner (a : K) :
      Cb E (s + (card K * (s+1+1) + 1) + 1 + t + 1)
        (fun x => f a x && decide (∀ b, before a b x = true) && g a x) :=
    Cb.and (Cb.and (hf a) (Cb.bigAnd (hbefore a))) (hg a)
  refine (Cb.bigOr hinner).mono (show _ ≤ selectCost _ _ _ by
      unfold selectCost
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      rw [show s+1+1 = s+2 by omega]
      omega) |>.congr ?_
  intro x
  classical
  rw [chooseBit, Bool.eq_iff_iff]
  have he (a : K) : (∀ b, before a b x = true) ↔ ∀ b, key b < key a → f b x = false := by
    constructor
    · intro h b hb
      simpa [before, hb] using h b
    · intro h b
      by_cases hb : key b < key a
      · simp [before, hb, h b hb]
      · simp [before, hb]
  simp only [Bool.and_eq_true, decide_eq_true_eq, he, First] <;>
    exact (Iff.of_eq (@decide_eq_true_eq _ (Classical.propDecidable _))).symm

variable {J T : Type} [Fintype J] [DecidableEq J] [Fintype T] {n : ℕ}

abbrev Input (J T : Type) (n : ℕ) := T ⊕ Bank J T n

def stepCost (J T : Type) [Fintype J] [Fintype T] (n : ℕ) : ℕ :=
  card (Bank J T n) * (selectCost (card (T × T)) 3 1 + 1)

theorem step_cmp (mask : T → J → Bool) :
    Cmp (Input J T n) (Bank J T n) (stepCost J T n)
      (fun x => step mask (x ∘ inl) (x ∘ inr)) := by
  classical
  let Z := Input J T n
  let m := card (T × T)
  have hsmall : m * 4 + 1 ≤ selectCost m 3 1 := by
    unfold selectCost
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega
  have hsingle : 1 ≤ selectCost m 3 1 := by omega
  have hCandidate (p : T) (ab : T × T) :
      Cb Z 3 (fun x => candidate mask (x ∘ inr) p ab) :=
    Cb.and (Cb.and (Cb.const (decide (Cover (mask p) (mask ab.1) (mask ab.2))))
      (Cb.var (ι:=Z) (.inr (ab.1, .inl ())))) (Cb.var (ι:=Z) (.inr (ab.2, .inl ())))
  have hRow (p : T) (ab : T × T) (v : Fin n) (j : J) :
      Cb Z 1 (fun x => joinRows mask p ab.1 ab.2
        (rows (x ∘ inr) ab.1) (rows (x ∘ inr) ab.2) v j) := by
    unfold joinRows
    split_ifs
    · exact (Cb.var (ι:=Z) (.inr (ab.1, .inr (v,j)))).mono (by decide)
    · exact (Cb.var _).mono (by decide)
    · exact Cb.const (mask p j)
  apply Cmp.ofBits
  rintro ⟨p,b⟩
  have h :
      Cb Z (selectCost m 3 1)
        (fun x => if (support (mask p)).card = 1 then
          b.elim (fun _ => true) (fun v => mask p v.2)
        else b.elim (fun _ => decide (∃ ab, candidate mask (x ∘ inr) p ab = true))
          (fun v => chooseBit (orderKey (T × T)) (candidate mask (x ∘ inr) p) fun ab =>
            joinRows mask p ab.1 ab.2 (rows (x ∘ inr) ab.1) (rows (x ∘ inr) ab.2) v.1 v.2)) := by
    by_cases h : (support (mask p)).card = 1
    · simpa only [h, ↓reduceIte] using (Cb.const (ι := Z)
        (b.elim (fun _ => true) (fun v => mask p v.2))).mono hsingle
    simp only [h, ↓reduceIte]
    rcases b with _ | ⟨v,j⟩
    · exact (Cb.bigOr (hCandidate p)).mono hsmall
    · exact select_cb (orderKey (T × T)) _ _ (hCandidate p) (fun ab => hRow p ab v j)
  refine ((Cb.and (Cb.var (.inl p)) h).mono (by simp [m])).congr ?_
  intro x
  change _ = step mask (x ∘ inl) (x ∘ inr) (p,b)
  cases hxp : x (.inl p) <;> simp [step, hxp]

theorem run_cmp (mask : T → J → Bool) :
    Cmp T (Bank J T n) ((n+1)*stepCost J T n) (fun pass => run mask pass n) := by
  let s := stepCost J T n
  have hs : card (Bank J T n) * 1 ≤ s := by
    unfold s stepCost
    exact Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.zero_le _))
  have h0 : Cmp T (Bank J T n) s (fun _ _ => false) :=
    (Cmp.ofBits (fun _ => Cb.const false)).mono hs
  have h := Cmp.chain n s (fun t v => run mask v t)
    (fun _ x => step mask (x ∘ inl) (x ∘ inr))
    h0 (fun _ _ => step_cmp mask) (fun _ _ _ => rfl)
  simpa only [Nat.add_zero, Fin.val_last, s] using
    Cmp.comp h (Cmp.wire (fun p => (Fin.last n,p)))

theorem all_cmp (mask : T → J → Bool) (c : ℕ) :
    Cmp (Fin (c+1) × T) (Fin (c+1) × Bank J T n)
      ((c+1)*((n+1)*stepCost J T n))
      (fun x (d,u) => run mask (fun p => x (d,p)) n u) := by
  simpa only [card_fin] using
    (Cmp.piU (I:=Fin (c+1)) (fun d => Cmp.sel (fun p : T => (d,p)) (run_cmp (n:=n) mask)))

theorem output_cmp (c digits : ℕ) (root : T) :
    Cmp (Fin (c+1) × Bank J T n) ((Fin n × J) ⊕ Fin digits)
      (card ((Fin n × J) ⊕ Fin digits) * selectCost (c+1) 0 1) (output root) := by
  let E := Fin (c+1) × Bank J T n
  have hf (d : Fin (c+1)) : Cb E 0 (fun x => capReady root x d) := Cb.var (ι:=E) (d,(root,.inl ()))
  apply Cmp.ofBits
  rintro (⟨v,j⟩ | e)
  · simpa only [card_fin, output, elim_inl, elim_inr, rows] using
      select_cb Fin.val _ _ hf (fun d => (Cb.var (ι:=E) (d,(root,inr (v,j)))).mono (by decide : 0 ≤ 1))
  · simpa only [card_fin, output, elim_inl, elim_inr, rows] using
      select_cb Fin.val _ _ hf (fun d => Cb.const (d.val.testBit e.val))

end Design

namespace Design

open Donor
open PackedTape
open Serialization

variable {k r q : ℕ}

def obsRaw (x : ObsPort k r q → Bool) : Raw k r q 0 → Bool
  | .inr (.inr (.inl (i,.inl j))) => x (i,.inl j)
  | .inr (.inr (.inl (i,.inr (.inl (b,t,j))))) => x (i,.inr (b,t,j))
  | _ => false

theorem obsRaw_cmp :
    Cmp (ObsPort k r q) (Raw k r q 0) (card (Raw k r q 0)) obsRaw := by
  rw [← Nat.mul_one (card (Raw k r q 0))]
  apply Cmp.ofBits
  rintro (⟨b,j⟩ | (⟨b,t,j⟩ | (⟨i,(j | (⟨b,t,j⟩ | ⟨⟩))⟩ | ⟨v,j⟩)))
  · exact Cb.const false
  · exact Cb.const false
  · exact (Cb.var (ι:=ObsPort k r q) (i,.inl j)).mono (by decide)
  · exact (Cb.var (ι:=ObsPort k r q) (i,.inr (b,t,j))).mono (by decide)
  · exact Cb.const false
  · exact Cb.const false

theorem readObs_obsBit (obs : Fin q → Tape k r) : readObs (obsRaw (obsBit obs)) = obs := by
  funext i
  apply Prod.ext
  · funext j
    exact zbit_decode ((obs i).1 j)
  · funext b t j
    exact zbit_decode ((obs i).2 b t j)

noncomputable def cutWidth (hk : 0 < k) (obs : Fin q → Tape k r) (p : Leaf k r → Bool) : ℕ :=
  let D := Direction hk obs
  let sp := fun bag => span F {f : D → F |
    ∃ (j : Leaf k r) (e : Fin 3), bag j = true ∧ f = fun z => form hk j e z.val}
  finrank F (sp p ⊓ sp (fun j => !p j) : Submodule F (D → F))

abbrev Caps (k r : ℕ) := Fin (tapeSize k r + 1) × Rect k r
abbrev WIn (k r : ℕ) := WidthIn (FormIx k r) (Param k r)

def thresholdCost (k r d : ℕ) : ℕ :=
  card (WIn k r) + widthPrepCost (FormIx k r) (Param k r) d

def rankCost (k r q : ℕ) : ℕ :=
  card (Raw k r q 0) + tapePrepCost k r q + card (FormData k r)*21 +
    ∑ s : Caps k r, thresholdCost k r s.1.val

def thresholdIn (hk : 0 < k) (p : Rect k r) (v : FormData k r → Bool) : WIn k r → Bool :=
  elim (fun (j,t) => v (j,.inl t)) (fun j => shape hk p j.1)

theorem thresholdIn_cmp (hk : 0 < k) (p : Rect k r) :
    Cmp (FormData k r) (WIn k r) (card (WIn k r)) (thresholdIn hk p) := by
  rw [← Nat.mul_one (card (WIn k r))]
  apply Cmp.ofBits
  rintro (⟨j,t⟩ | j)
  · exact (Cb.var (ι:=FormData k r) (j,.inl t)).mono (by decide)
  · exact Cb.const (shape hk p j.1)

theorem rank_cmp (hk : 0 < k) :
    Cmp (ObsPort k r q) (Caps k r) (rankCost k r q)
      (fun v (d,p) => decide (cutWidth hk (readObs (obsRaw v)) (shape hk p) ≤ d.val)) ∧
    ∀ (obs : Fin q → Tape k r) (p : Leaf k r → Bool), cutWidth hk obs p ≤ tapeSize k r := by
  classical
  obtain ⟨S,hS,hsem⟩ := tapePrep (k:=k) (r:=r) (q:=q) (n:=0) hk
  choose W hW hWsem using fun d : Fin (tapeSize k r+1) =>
    widthPrep (J:=FormIx k r) (U:=Param k r) d.val
  let M (x : FormData k r → Bool) (s : Caps k r) (_ : Unit) :=
    W s.1 (thresholdIn hk s.2 x) (.inr ())
  have hM (s : Caps k r) : Cmp (FormData k r) Unit (thresholdCost k r s.1.val) (fun x => M x s) := by
    have h := Cmp.comp (Cmp.comp (thresholdIn_cmp hk s.2) (hW s.1))
      (Cmp.wire (fun _ : Unit => (inr () : WidthOut (Param k r) s.1.val)))
    simpa only [Nat.add_zero, thresholdCost, M] using h
  have hfin : Cmp (FormData k r) (Caps k r)
      (∑ s : Caps k r, thresholdCost k r s.1.val) (fun x s => M x s ()) := by
    simpa only [Nat.add_zero] using
      Cmp.comp (Cmp.pi hM) (Cmp.wire (fun s : Caps k r => (s,())))
  refine ⟨?_,?_⟩
  · apply Cmp.congr (Cmp.comp (Cmp.comp (Cmp.comp obsRaw_cmp hS) (evalFormsCmp hk)) hfin)
    intro v s
    let o := S (obsRaw v)
    let x := thresholdIn hk s.2 (evalForms hk o)
    change W s.1 x (.inr ()) = decide (cutWidth hk (readObs (obsRaw v)) (shape hk s.2) ≤ s.1.val)
    rw [Bool.eq_iff_iff, decide_eq_true_eq, (hWsem s.1 x).1]
    change finrank F (CutSpan (linearRows (evalForms hk o)) (shape hk s.2)) ≤ s.1.val ↔ _
    rw [post_width_eq hk _ o (hsem (obsRaw v)).2.1] <;> rfl
  · intro obs p
    let u := obsRaw (obsBit obs)
    have hEq := readObs_obsBit obs
    change readObs u = obs at hEq
    have h := post_width_eq hk (readObs u) (S u) (hsem u).2.1 p
    change finrank F (CutSpan (linearRows (evalForms hk (S u))) p) =
      cutWidth hk (readObs u) p at h
    rw [hEq] at h
    rw [← h]
    exact (Submodule.finrank_le _).trans (by simp [Param])

end Design

open scoped Fin.NatCast
section Helpers

-- Layout construction adapted from L-meta-29773, PR 41929.
variable {α : Type*}
def valid (B : ℕ → Set α) (v : ℕ) : Prop :=
  (∃ x, B v = {x}) ∨ ∃ a < v, ∃ b < v, Disjoint (B a) (B b) ∧ B v = B a ∪ B b
def built (P : Set α → Prop) (S : Set α) (m : Nat) : Prop :=
  ∃ B : ℕ → Set α, (∃ v < 2*m-1, B v = S) ∧ ∀ v < 2*m-1, P (B v) ∧ valid B v
lemma build_one {P : Set α → Prop} {x : α} (hp : P {x}) : built P {x} 1 := by
  exact ⟨fun _ => {x}, ⟨0, by decide, rfl⟩, fun _ _ => ⟨hp, Or.inl ⟨x,rfl⟩⟩⟩
lemma build_join {P : Set α → Prop} {S T : Set α} {m n : Nat}
    (hs : built P S m) (ht : built P T n) (hd : Disjoint S T) (hp : P (S ∪ T)) :
    built P (S ∪ T) (m+n) := by
  rcases hs with ⟨A, ⟨a, ha, ea⟩, hA⟩
  rcases ht with ⟨B, ⟨b, hb, eb⟩, hB⟩
  let u := 2*m-1
  let w := 2*n-1
  change a < u at ha
  change b < w at hb
  have root : u+w+1 = 2*(m+n)-1 := by dsimp [u,w] at *; omega
  let C := fun i => if i < u then A i else if i < u+w then B (i-u) else S ∪ T
  have eA (i) (h : i < u) : C i = A i := if_pos h
  have eB (i) (h : i < w) : C (u+i) = B i := by simp [C, h]
  have eC : C (u+w) = S ∪ T := by simp [C]
  refine ⟨C, ⟨u+w, by omega, eC⟩, ?_⟩
  intro v hv
  by_cases h : v < u
  · obtain ⟨hP, hx | ⟨i,hi,j,hj,hD,hU⟩⟩ := hA v h
    · exact ⟨eA v h ▸ hP, Or.inl ((eA v h) ▸ hx)⟩
    refine ⟨eA v h ▸ hP, Or.inr ⟨i,hi,j,hj,?_,?_⟩⟩
    · simpa only [eA i (by omega), eA j (by omega)] using hD
    · simpa only [eA i (by omega), eA j (by omega), eA v h] using hU
  by_cases h' : v < u+w
  · obtain ⟨i, rfl⟩ : ∃ i, v = u+i := ⟨v-u, by omega⟩
    have hi : i < w := by omega
    obtain ⟨hP, hx | ⟨j,hj,l,hl,hD,hU⟩⟩ := hB i hi
    · exact ⟨eB i hi ▸ hP, Or.inl ((eB i hi) ▸ hx)⟩
    refine ⟨eB i hi ▸ hP, Or.inr ⟨u+j,by omega,u+l,by omega,?_,?_⟩⟩
    · simpa only [eB j (by omega), eB l (by omega)] using hD
    · simpa only [eB j (by omega), eB l (by omega), eB i hi] using hU
  have ev : v = u+w := by omega
  subst v
  refine ⟨eC ▸ hp, Or.inr ⟨a,by omega,u+b,by omega,?_,?_⟩⟩
  · simpa only [eA a ha, eB b hb, ea, eb] using hd
  · rw [eC, eA a ha, eB b hb, ea, eb]

lemma build_groups {k m : Nat} (hk : 0 < k) (hm : 0 < m) (key : α → Fin k) (slot : α → ℕ)
    (bound : ∀ i, slot i < m) (uniqueCell : ∀ j t, t < m →
      ∃ i, ∀ x, (key x = j ∧ slot x = t) ↔ x = i)
    (P : Set α → Prop)
    (hCell : ∀ j a b, a < b → b ≤ m → P {x | key x = j ∧ a ≤ slot x ∧ slot x < b})
    (hPre : ∀ c ≤ k, P {x | (key x).val < c}) :
    built P Set.univ (m*k) := by
  have leaf (j : Fin k) (t : ℕ) (ht : t < m) :
      built P {x | key x = j ∧ slot x = t} 1 := by
    obtain ⟨i, hi⟩ := uniqueCell j t ht
    have e : {x | key x = j ∧ slot x = t} = ({i} : Set α) := Set.ext hi
    rw [e]
    apply build_one
    have h := hCell j t (t+1) (by omega) (by omega)
    convert h using 1
    rw [← e]
    ext x
    simp only [Set.mem_setOf_eq]
    omega
  have col (j : Fin k) (b : Nat) (hb : 0 < b) (hb' : b ≤ m) :
      built P {x | key x = j ∧ slot x < b} b := by
    induction b with
    | zero => omega
    | succ b ih =>
      by_cases h : b = 0
      · subst b
        simpa using leaf j 0 hm
      have h₁ := ih (by omega) (by omega)
      have h₂ := leaf j b (by omega)
      have e : {x | key x = j ∧ slot x < b} ∪ {x | key x = j ∧ slot x = b} =
          {x | key x = j ∧ slot x < b+1} := by ext x; simp; omega
      rw [← e]
      apply build_join h₁ h₂
      · exact Set.disjoint_left.mpr (by intro x hx hx'; exact (hx.2.ne hx'.2))
      · rw [e]; simpa using hCell j 0 (b+1) (by omega) hb'
  have pre (c : Nat) (hc : 0 < c) (hc' : c ≤ k) :
      built P {x | (key x).val < c} (m*c) := by
    induction c with
    | zero => omega
    | succ c ih =>
      let j : Fin k := ⟨c, by omega⟩
      have h₂ := col j m hm le_rfl
      simp only [bound, and_true] at h₂
      by_cases h : c = 0
      · subst c
        simpa [j, Nat.lt_one_iff, Fin.ext_iff] using h₂
      have h₁ := ih (by omega) (by omega)
      have e : {x | (key x).val < c} ∪ {x | key x = j} = {x | (key x).val < c+1} := by
        ext x; simp [j, Fin.ext_iff]; omega
      rw [← e, Nat.mul_succ]
      apply build_join h₁ h₂
      · exact Set.disjoint_left.mpr (by intro x hx hx'; change key x = j at hx'; change (key x).val < c at hx; rw [hx'] at hx; exact (lt_irrefl c hx))
      · rw [e]; exact hPre _ hc'
  simpa using pre k hk le_rfl

set_option maxHeartbeats 2000000 in
theorem baseLayout : ∀ (k r : Nat) (hk : 0 < k),
  let G := Bool × Fin r × Fin k
  let I := Fin k ⊕ G
  let ix := fun s : Nat => (⟨s % k, Nat.mod_lt _ hk⟩ : Fin k)
  let feed := fun (b : Bool) (t : Nat) => if b then 3*(t+1)+1 else 2*t
  let leafCount := (2*r+1)*k
  let n := 2*leafCount-1
  let Bag := Fin n → I → Bool
  let arc := fun (j a : Fin k) (len : Fin (k+1)) =>
    (j.val+k-a.val) % k < len.val
  let geometric := fun (p : I → Bool) =>
    ∃ (rootSite : Fin k) (rootLen : Fin (k+1)) (slope origin : Bool → Fin k)
      (width : Bool → Fin (k+1)) (lo hi : Bool → Fin (r+1)), ∀ i : I,
        p i = elim (fun coord => decide (arc coord rootSite rootLen)) (fun g : G =>
          let b := g.1
          let time := g.2.1.val
          decide ((lo b).val ≤ time ∧ time < (hi b).val ∧
            arc g.2.2 (ix ((origin b).val+(slope b).val*time)) (width b))) i
  let layout := fun (bag : Bag) =>
    (∃ top : Fin n, ∀ i, bag top i = true) ∧ ∀ v : Fin n, geometric (bag v) ∧
      ((∃ one : I, ∀ i, bag v i = decide (i = one)) ∨
        ∃ l h : Fin n, l < v ∧ h < v ∧ (∀ i, bag l i = true → bag h i = false) ∧
          ∀ i, bag v i = (bag l i || bag h i))
  ∃ bag : Bag, layout bag := by
  classical
  intro k r hk G I ix feed leafCount n Bag arc geometric layout
  letI : NeZero k := ⟨hk.ne'⟩
  let key : I → Fin k := elim id (fun g : G => g.2.2 - (feed g.1 g.2.1.val : Fin k))
  let base := fun b : Bool => if b then r+1 else 1
  let slot : I → ℕ := elim (fun _ => 0) (fun g : G => base g.1 + g.2.1.val)
  have keyL (j : Fin k) : key (.inl j) = j := rfl
  have keyR (b : Bool) (t : Fin r) (j : Fin k) :
      key (.inr (b,t,j)) = j - (feed b t.val : Fin k) := rfl
  have sbound (i : I) : slot i < 2*r+1 := by
    rcases i with j | ⟨b,t,j⟩
    · dsimp [slot]; omega
    · cases b <;> dsimp [slot,base] <;> omega
  have uniqueCell (j : Fin k) (a : ℕ) (ha : a < 2*r+1) :
      ∃ i : I, ∀ x, (key x = j ∧ slot x = a) ↔ x = i := by
    by_cases h0 : a = 0
    · subst a
      refine ⟨.inl j, ?_⟩
      rintro (x | ⟨b,t,x⟩)
      · simp [key,slot]; exact ⟨congrArg inl, inl.inj⟩
      · cases b <;> simp [slot,base] <;> omega
    let b : Bool := decide (r < a)
    let t : Fin r := ⟨a-base b, by dsimp [b,base]; split <;> rename_i e <;> simp_all <;> omega⟩
    have ht : base b + t.val = a := by dsimp [b,base,t]; split <;> rename_i e <;> simp_all <;> omega
    refine ⟨.inr (b,t,j+(feed b t.val : Fin k)), ?_⟩
    rintro (x | ⟨b',t',x⟩)
    · simp [slot, Ne.symm h0]
    change (x - _ = j ∧ base b' + t'.val = a) ↔ _
    constructor
    · rintro ⟨he,ha'⟩
      have eb : b' = b := by cases b' <;> cases eb' : b <;> simp_all [base] <;> omega
      subst b'
      have et : t' = t := Fin.ext (by omega)
      subst t'
      rw [sub_eq_iff_eq_add] at he
      rw [he]
    · intro he
      cases he
      exact ⟨add_sub_cancel_right ..,ht⟩
  have ixcast (i : Nat) : ix i = (i : Fin k) := rfl
  have castVal (j : Fin k) : (j.val : Fin k) = j := by ext; simp
  have subval (j a : Fin k) : (j.val+k-a.val)%k = (j-a).val := by
    rw [Fin.val_sub]; congr 1; have := a.isLt; omega
  have arcEq (j a : Fin k) (w : Fin (k+1)) : arc j a w ↔ (j-a).val < w.val := by
    change (j.val+k-a.val)%k < _ ↔ _; rw [subval]
  have arcone (j a : Fin k) : (j-a).val < 1 ↔ j = a := by
    rw [Nat.lt_one_iff]; exact (Fin.ext_iff (a := j-a) (b := 0)).symm.trans sub_eq_zero
  have feedlin (b : Bool) (t : ℕ) :
      feed b t = feed b 0 + (if b then 3 else 2)*t := by cases b <;> dsimp [feed] <;> omega
  have castMul (u v : Nat) : ((u*v : Nat) : Fin k) = (u : Fin k)*(v : Fin k) := by
    apply Fin.ext; simp [Fin.val_mul]
  have geo (a : Fin k) (w : Fin (k+1)) (lo hi : Nat) :
      geometric (fun i => decide ((key i-a).val < w.val ∧ lo ≤ slot i ∧ slot i < hi)) := by
    let trunc := fun (b : Bool) (u : ℕ) => (⟨min r (u-base b), by omega⟩ : Fin (r+1))
    refine ⟨a, if lo = 0 ∧ 0 < hi then w else 0,
      fun b => ((if b then 3 else 2 : Nat) : Fin k), fun b => a + (feed b 0 : Fin k),
      fun _ => w, fun b => trunc b lo, fun b => trunc b hi, ?_⟩
    rintro (j | ⟨b,t,j⟩)
    · simp only [elim_inl, decide_eq_decide]
      change ((j-a).val < w.val ∧ lo ≤ 0 ∧ 0 < hi) ↔ _
      simp only [arcEq]
      split_ifs <;> (try simp only [Fin.val_zero]) <;> omega
    simp only [elim_inr, decide_eq_decide]
    change ((j - (feed b t.val : Fin k) - a).val < w.val ∧ lo ≤ base b+t.val ∧ base b+t.val < hi) ↔ _
    rw [arcEq, ixcast, Nat.cast_add, castMul, castVal, castVal]
    rw [feedlin b t.val, Nat.cast_add, castMul]
    have eqs : j - ((feed b 0 : Fin k) + ((if b then 3 else 2 : Nat) : Fin k) * (t.val : Fin k)) - a =
        j - (a + (feed b 0 : Fin k) + ((if b then 3 else 2 : Nat) : Fin k) * (t.val : Fin k)) := by abel
    rw [eqs]
    simp only [and_true, decide_eq_decide, trunc]
    omega

  let flag := fun (S : Set I) (i : I) => decide (i ∈ S)
  have goodCell (j : Fin k) (a b : ℕ) (_ : a < b) (_ : b ≤ 2*r+1) :
      geometric (flag {x | key x = j ∧ a ≤ slot x ∧ slot x < b}) := by
    convert geo j ⟨1, by omega⟩ a b using 1
    funext x
    simp only [flag, Set.mem_setOf_eq, decide_eq_decide, arcone]
  have goodPre (c : Nat) (hc : c ≤ k) :
      geometric (flag {x | (key x).val < c}) := by
    convert geo 0 ⟨c, by omega⟩ 0 (2*r+1) using 1
    funext x
    simp [flag, sbound]
  obtain ⟨B, ⟨top,ht,et⟩, H⟩ :=
    build_groups hk (by omega : 0 < 2*r+1) key slot sbound uniqueCell
      (fun S => geometric (flag S)) goodCell goodPre
  refine ⟨fun v => flag (B v.val), ⟨⟨⟨top,ht⟩,?_⟩,?_⟩⟩
  · intro i; simp [flag,et]
  intro v
  refine ⟨(H v.val v.isLt).1,?_⟩
  rcases (H v.val v.isLt).2 with ⟨i,hi⟩ | ⟨a,ha,b,hb,hd,he⟩
  · exact Or.inl ⟨i,fun x => by simp [flag,hi]⟩
  refine Or.inr ⟨⟨a,ha.trans v.isLt⟩,⟨b,hb.trans v.isLt⟩,ha,hb,?_,?_⟩
  · intro x hx; simpa [flag] using Set.disjoint_left.mp hd (of_decide_eq_true hx)
  · intro x; simp [flag,he]

end Helpers

namespace Design

open Donor
open PackedTape
open Serialization

abbrev TreeSize (k r : ℕ) := 2*((2*r+1)*k)-1
abbrev Digits (k r : ℕ) := Nat.log2 (tapeSize k r)+1
abbrev Wires (k r : ℕ) := (Fin (TreeSize k r) × Leaf k r) ⊕ Fin (Digits k r)

def GoodLayout {k r : ℕ} (hk : 0 < k) (bag : Fin (TreeSize k r) → Leaf k r → Bool) : Prop :=
  (∃ top : Fin (TreeSize k r), bag top = fun _ => true) ∧
  ∀ v, (∃ p, bag v = shape hk p) ∧ Row bag v

def Fits {k r q : ℕ} (hk : 0 < k) (obs : Fin q → Tape k r)
    (bag : Fin (TreeSize k r) → Leaf k r → Bool) (cost : ℕ) : Prop :=
  GoodLayout hk bag ∧ ∀ v, cutWidth hk obs (bag v) ≤ cost

theorem fits_mono {k r q : ℕ} {hk : 0 < k} {obs : Fin q → Tape k r}
    {bag : Fin (TreeSize k r) → Leaf k r → Bool} {a b : ℕ}
    (ha : Fits hk obs bag a) (h : a ≤ b) : Fits hk obs bag b :=
  ⟨ha.1, fun v => (ha.2 v).trans h⟩

theorem boxes_iff {k r : ℕ} (hk : 0 < k) (p : Leaf k r → Bool) :
    (∃ (rootSite : Fin k) (rootLen : Fin (k+1)) (slope origin : Bool → Fin k)
      (width : Bool → Fin (k+1)) (lo hi : Bool → Fin (r+1)), ∀ i : Leaf k r,
        p i = elim (fun coord => decide ((coord.val+k-rootSite.val) % k < rootLen.val))
          (fun g : Bool × Fin r × Fin k =>
          let b := g.1
          let time := g.2.1.val
          let a := ((origin b).val+(slope b).val*time) % k
          decide ((lo b).val ≤ time ∧ time < (hi b).val ∧
            (g.2.2.val+k-a) % k < (width b).val)) i) ↔
    ∃ a : Rect k r, p = shape hk a := by
  constructor
  · rintro ⟨a,b,c,d,e,f,g,h⟩
    refine ⟨(a,b,c,d,e,f,g), funext fun i => ?_⟩
    simpa only [shape] using h i
  · rintro ⟨⟨a,b,c,d,e,f,g⟩,h⟩
    exact ⟨a,b,c,d,e,f,g,congrFun h⟩

theorem baseGood {k r : ℕ} (hk : 0 < k) :
    ∃ bag : Fin (TreeSize k r) → Leaf k r → Bool, GoodLayout hk bag := by
  obtain ⟨bag, ⟨v,hv⟩,hrows⟩ := PEqualNP.Outside.L_meta_29774_aux.baseLayout k r hk
  exact ⟨bag,⟨v,funext hv⟩,fun u => ⟨(boxes_iff hk (bag u)).mp (hrows u).1,
    (rows_iff bag u).mpr (hrows u).2⟩⟩

def designCost (k r q : ℕ) : ℕ :=
  rankCost k r q + (tapeSize k r+1)*((TreeSize k r+1)*stepCost (Leaf k r) (Rect k r) (TreeSize k r)) +
    card (Wires k r)*selectCost (tapeSize k r+1) 0 1

set_option maxHeartbeats 1600000 in
theorem optimize_cmp {k r q : ℕ} (hk : 0 < k) :
    ∃ o : (ObsPort k r q → Bool) → Wires k r → Bool,
      Cmp (ObsPort k r q) (Wires k r) (designCost k r q) o ∧
      ∀ obs : Fin q → Tape k r,
        let bag := fun v j => o (obsBit obs) (.inl (v,j))
        let price := tabN (fun e => o (obsBit obs) (.inr e))
        Fits hk obs bag price ∧ ∀ alt cost, Fits hk obs alt cost → price ≤ cost := by
  classical
  let N := tapeSize k r
  let n := TreeSize k r
  let T := Rect k r
  let J := Leaf k r
  let choose (obs : Fin q → Tape k r) : Wires k r → Bool :=
    output (c:=N) (n:=n) (whole hk) (fun s =>
      run (shape hk) (fun p => decide (cutWidth hk obs (shape hk p) ≤ s.1.val)) n s.2)
  let o (x : ObsPort k r q → Bool) : Wires k r → Bool := choose (readObs (obsRaw x))
  have hRank := rank_cmp (r:=r) (q:=q) hk
  have hc : Cmp (ObsPort k r q) (Wires k r) (designCost k r q) o :=
    Cmp.comp (Cmp.comp hRank.1 (all_cmp (n:=n) (shape hk) N))
      (output_cmp (n:=n) (J:=J) N (Digits k r) (whole hk))
  refine ⟨o,hc,?_⟩
  intro obs bag price
  obtain ⟨base,hBase⟩ := baseGood (r:=r) hk
  have hn : 0 < n := by
    have := Nat.mul_pos (show 0 < 2*r+1 by omega) hk
    dsimp [n, TreeSize]
    omega
  have hs (p : T) : nodes (shape hk p) ≤ n := by
    simpa only [leafCount] using nodes_le (shape hk p)
  have hw : nodes (shape (r:=r) hk (whole hk)) = n := by
    rw [shape_whole, nodes_full, leafCount]
  obtain ⟨d, hbits, hroot, hrows, hmin⟩ :=
    output_spec (shape hk) (whole hk) (shape_whole hk) hn hs hw
      (cutWidth hk obs) N (Digits k r) (fun p => hRank.2 obs (shape hk p)) base
      (fun v => (hBase.2 v).2) (fun v => (hBase.2 v).1) hBase.1
  let out := choose obs
  have he : o (obsBit obs) = out := congrArg choose (readObs_obsBit obs)
  have hprice : price = d.val := by
    change tabN (fun e => o (obsBit obs) (.inr e)) = _
    rw [he]
    have h : (fun e : Fin (Digits k r) => out (.inr e)) = fun e => d.val.testBit e.val := funext hbits
    rw [h]
    exact tabN_recover ((Nat.le_of_lt_succ d.isLt).trans_lt Nat.lt_log2_self)
  have hbag : bag = fun v j => out (.inl (v,j)) := by
    funext v j
    exact congrFun he (.inl (v,j))
  rw [hprice, hbag]
  refine ⟨⟨⟨hroot,fun v => ⟨(hrows v).2.1,(hrows v).1⟩⟩,fun v => (hrows v).2.2⟩,?_⟩
  intro alt cost ha
  exact hmin alt cost ha.1.1 (fun v => ⟨(ha.1.2 v).2,(ha.1.2 v).1,ha.2 v⟩)

end Design

namespace Design

open Donor
open PackedTape

theorem rect_card_bound (k r q : ℕ) :
    card (Rect k r) ≤ (k+r+q+5)^12 := by
  simp only [Rect, card_prod, card_fin, card_fun, card_bool]
  let P := k+r+q+5
  have hk : k ≤ P := by dsimp [P]; omega
  have hk' : k+1 ≤ P := by dsimp [P]; omega
  have hr : r+1 ≤ P := by dsimp [P]; omega
  have h := Nat.mul_le_mul hk (Nat.mul_le_mul hk'
    (Nat.mul_le_mul (Nat.pow_le_pow_left hk 2)
      (Nat.mul_le_mul (Nat.pow_le_pow_left hk 2)
        (Nat.mul_le_mul (Nat.pow_le_pow_left hk' 2)
          (Nat.mul_le_mul (Nat.pow_le_pow_left hr 2) (Nat.pow_le_pow_left hr 2))))))
  exact h.trans_eq (by ring)

set_option maxHeartbeats 2500000 in
theorem design_size (k r q : ℕ) :
    designCost k r q + 1 ≤ 2^80*(k+r+q+5)^80 := by
  let P := k+r+q+5
  obtain ⟨A, hAeq⟩ : ∃ A : ℕ, A = P^2 := ⟨P^2,rfl⟩
  let N := tapeSize k r
  let L := (2*r+1)*k
  let n := TreeSize k r
  let M := card (Rect k r)
  let R := card (EqRow k q)
  have hP : 5 ≤ P := by dsimp [P]; omega
  have hAp : 1 ≤ A := by rw [hAeq]; exact Nat.pow_pos (by omega : 0 < P)
  have hpow (i j : ℕ) (h : i ≤ j) : A^i ≤ A^j := Nat.pow_le_pow_right hAp h
  have hpA : P ≤ A := by
    rw [hAeq]
    simpa only [pow_one] using Nat.pow_le_pow_right (show 1 ≤ P by omega) (show 1 ≤ 2 by decide)
  have hA (i : ℕ) : 1 ≤ A^i := Nat.pow_pos hAp
  have hN : N+1 ≤ A := by
    have h : (2*r+3)*k+1 ≤ (k+r+2)^2 := by
      nlinarith only [Nat.zero_le k, Nat.zero_le r, Nat.zero_le (k*k), Nat.zero_le (r*r)]
    rw [hAeq]
    exact h.trans (Nat.pow_le_pow_left (show k+r+2 ≤ P by dsimp [P]; omega) 2)
  have hL : L ≤ A := by
    calc
      L ≤ N := Nat.mul_le_mul_right k (by omega)
      _ ≤ A := by omega
  have hn : n+1 ≤ 2*A := by change 2*L-1+1 ≤ _; omega
  have hM : M ≤ A^6 := (rect_card_bound k r q).trans_eq (by rw [hAeq, ← pow_mul])
  have hR : R ≤ 2*A := by
    simp only [R, EqRow, card_sum, card_prod, card_bool, card_fin]
    exact (show 2*k+q ≤ 2*P by dsimp [P]; omega).trans (by omega)
  have hTP : tapePrepCost k r q ≤ 2^39*A^6 :=
    tapeBudget (k:=k) (r:=r) (q:=q) hAp hN hR
  have hRaw : card (Raw k r q 0) ≤ 2*A^2 := by
    rw [show card (Raw k r q 0) = (2+2*r)*k + q*(N+1) by
      unfold Raw
      rw [card_inputSlot]
      simp [inputs, N]]
    have ha : (2+2*r)*k ≤ N := Nat.mul_le_mul_right _ (by omega)
    have hq : q ≤ A := (show q ≤ P by dsimp [P]; omega).trans hpA
    have h₁ := Nat.mul_le_mul hq hN
    nlinarith only [ha,hN,h₁,hpow 1 2 (by decide),pow_one A]
  have hFormIx : card (FormIx k r) = 3*L := by
    simp only [FormIx, card_prod, card_fin, leafCount, L, mul_comm]
  have hParam : card (Param k r) = N := card_fin _
  have hFD : card (FormData k r)*21 ≤ 64*A^2 := by
    unfold FormData
    rw [card_prod, card_sum, hFormIx, hParam, card_unit]
    nlinarith only [Nat.mul_le_mul hL hN]
  have hTh (d : ℕ) (hd : d ≤ N) : thresholdCost k r d ≤ 2^38*A^6 := by
    unfold thresholdCost
    exact widthBudget (J:=FormIx k r) (U:=Param k r) (d:=d) hAp
      (by rw [hFormIx]; omega) (by rw [hParam]; omega) (by omega)
  have hCap : card (Caps k r) ≤ A^7 := by
    change card (Fin (N+1) × Rect k r) ≤ _
    rw [card_prod,card_fin]
    change (N+1)*M ≤ _
    exact (Nat.mul_le_mul hN hM).trans_eq (by ring)
  have hSum : (∑ d : Caps k r, thresholdCost k r d.1.val) ≤ 2^38*A^13 := by
    calc
      _ ≤ ∑ _d : Caps k r, 2^38*A^6 := by
        exact Finset.sum_le_sum (fun d _ => hTh _ (by have := d.1.isLt; omega))
      _ ≤ _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        exact (Nat.mul_le_mul_right _ hCap).trans_eq (by ring)
  have hRank : rankCost k r q ≤ 2^41*A^13 := by
    unfold rankCost
    have h₂ := hpow 2 13 (by decide)
    have h₆ := hpow 6 13 (by decide)
    omega
  have hJ : card (Leaf k r) = L := leafCount k r
  have hNL : n*L ≤ 2*A^2 := by
    exact (Nat.mul_le_mul (show n ≤ 2*A by omega) hL).trans_eq (by ring)
  have hBank : card (Bank (Leaf k r) (Rect k r) n) ≤ 3*A^8 := by
    change card (Rect k r × (Unit ⊕ (Fin n × Leaf k r))) ≤ _
    rw [card_prod,card_sum,card_unit,
      card_prod (α:=Fin n) (β:=Leaf k r),card_fin,hJ]
    change M*(1+n*L) ≤ _
    exact (Nat.mul_le_mul hM (show 1+n*L ≤ 3*A^2 by have := hA 2; omega)).trans_eq (by ring)
  have hPair : card (Rect k r × Rect k r) ≤ A^12 := by
    rw [card_prod]
    exact (Nat.mul_le_mul hM hM).trans_eq (by ring)
  have hSelect : selectCost (card (Rect k r × Rect k r)) 3 1+1 ≤ 16*A^24 := by
    let Q := card (Rect k r × Rect k r)
    have h := Nat.mul_le_mul hPair (show 3+Q*(3+2)+1+4 ≤ 13*A^12 by have := hA 12; omega)
    unfold selectCost
    nlinarith only [h,hA 24]
  have hStep : stepCost (Leaf k r) (Rect k r) n ≤ 48*A^32 := by
    unfold stepCost
    exact (Nat.mul_le_mul hBank hSelect).trans_eq (by ring)
  have hRun : (N+1)*((n+1)*stepCost (Leaf k r) (Rect k r) n) ≤ 96*A^34 :=
    (Nat.mul_le_mul hN (Nat.mul_le_mul hn hStep)).trans_eq (by ring)
  have hD : Digits k r ≤ A := (Nat.succ_le_succ (Nat.log2_le_self N)).trans hN
  have hWire : card (Wires k r) ≤ 3*A^2 := by
    simp only [Wires,card_sum,card_prod,card_fin,hJ]
    have hh : A ≤ A^2 := by simpa only [pow_one] using hpow 1 2 (by decide)
    exact (Nat.add_le_add hNL (hD.trans hh)).trans_eq (by ring)
  have hOut : card (Wires k r)*selectCost (N+1) 0 1 ≤ 24*A^4 := by
    have h := Nat.mul_le_mul hN (show 0+(N+1)*(0+2)+1+4 ≤ 7*A by omega)
    have hh : selectCost (N+1) 0 1 ≤ 8*A^2 := by
      unfold selectCost
      nlinarith only [h,hA 2]
    exact (Nat.mul_le_mul hWire hh).trans_eq (by ring)
  have hm : designCost k r q + 1 ≤ 2^43*A^34 := by
    unfold designCost
    change rankCost k r q + (N+1)*((n+1)*stepCost (Leaf k r) (Rect k r) n) +
      card (Wires k r)*selectCost (N+1) 0 1 + 1 ≤ _
    have h₁ := hpow 13 34 (by decide)
    have h₂ := hpow 4 34 (by decide)
    have h₃ := hA 34
    omega
  refine hm.trans ?_
  have hE : A^34 = P^68 := by rw [hAeq, ← pow_mul]
  rw [hE]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (by decide))
    (Nat.pow_le_pow_right (by omega : 1 ≤ P) (by decide))

end Design

end PEqualNP.Outside.L_meta_29774_aux

open PEqualNP.Outside.L_meta_29774_aux PEqualNP.Outside.L_meta_29774_aux.Donor PEqualNP.Outside.L_meta_29774_aux.PackedTape
open PEqualNP.Outside.L_meta_29774_aux.Design PEqualNP.Outside.L_meta_29774_aux.Serialization

set_option maxRecDepth 1800 in
set_option maxHeartbeats 3500000 in
theorem PEqualNP.Outside.L_meta_29774 : ∀ (k r q : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let X := W × (Bool → Fin (r+1) → W)
  let G := Bool × Fin r × Fin k
  let I := Fin k ⊕ G
  let N := (2*r+3)*k
  let ix := fun s : Nat => (⟨s % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (v : W) (j : Fin k) => v (ix (j.val+k-s % k))
  let start := fun (b : Bool) => if b then 3 else 1
  let feed := fun (b : Bool) (t : Nat) => if b then 3*(t+1)+1 else 2*t
  let mix := fun (b : Bool) (v : W) (j : Fin k) =>
    let d := if b then 2 else 1
    v j + v (ix (j.val+d)) + v (ix (j.val+k-d % k))
  let pair := fun (v z : X) => dotProduct v.1 z.1 +
    ∑ s : Fin (r+1), (dotProduct (v.2 false s) (z.2 false s) + dotProduct (v.2 true s) (z.2 true s))
  let form : I → Fin 3 → X → F := Sum.elim (fun j _ z => z.1 j) (fun g e z =>
    let b := g.1
    let t := g.2.1
    let j := g.2.2
    let y := mix b (z.2 b t.castSucc)
    if e.val = 0 then y (ix (j.val+1)) else if e.val = 1 then y (ix (j.val+2))
    else z.2 b t.succ j + y j + rot (feed b t.val) z.1 j)
  let leafCount := (2*r+1)*k
  let n := 2*leafCount-1
  let Bag := Fin n → I → Bool
  let arc := fun (j a : Fin k) (len : Fin (k+1)) =>
    (j.val+k-a.val) % k < len.val
  let geometric := fun (p : I → Bool) =>
    ∃ (rootSite : Fin k) (rootLen : Fin (k+1)) (slope origin : Bool → Fin k)
      (width : Bool → Fin (k+1)) (lo hi : Bool → Fin (r+1)), ∀ i : I,
        p i = Sum.elim (fun coord => decide (arc coord rootSite rootLen)) (fun g : G =>
          let b := g.1
          let time := g.2.1.val
          decide ((lo b).val ≤ time ∧ time < (hi b).val ∧
            arc g.2.2 (ix ((origin b).val+(slope b).val*time)) (width b))) i
  let layout := fun (bag : Bag) =>
    (∃ top : Fin n, ∀ i, bag top i = true) ∧ ∀ v : Fin n, geometric (bag v) ∧
      ((∃ one : I, ∀ i, bag v i = decide (i = one)) ∨
        ∃ l h : Fin n, l < v ∧ h < v ∧ (∀ i, bag l i = true → bag h i = false) ∧
          ∀ i, bag v i = (bag l i || bag h i))
  let dir := fun (obs : Fin q → X) =>
    {z : X // (∀ b, z.2 b 0 = rot (start b) z.1) ∧ ∀ i, pair (obs i) z = 0}
  let fits := fun (obs : Fin q → X) (bag : Bag) (cap : Nat) =>
    let D := dir obs
    let span := fun (p : I → Bool) => Submodule.span F
      {f : D → F | ∃ (j : I) (e : Fin 3), p j = true ∧ f = fun z : D => form j e z.val}
    layout bag ∧ ∀ v : Fin n, Module.finrank F
      ((span (bag v) ⊓ span (fun j => !(bag v j))) : Submodule F (D → F)) ≤ cap
  let digits := Nat.log2 N+1
  let pack := fun v : W => List.ofFn (fun j : Fin k => decide (v j ≠ 0))
  let lanes := fun (side : Bool) (tape : X) => (List.finRange (r+1)).flatMap (fun j => pack (tape.2 side j))
  let masks := fun (obs : Fin q → X) => (List.finRange q).flatMap (fun i =>
    pack (obs i).1 ++ lanes false (obs i) ++ lanes true (obs i))
  let leafBits := fun (p : I → Bool) => List.ofFn (fun j : Fin k => p (.inl j)) ++
    [false,true].flatMap (fun b => (List.finRange r).flatMap (fun t =>
      List.ofFn (fun j : Fin k => p (.inr (b,t,j)))))
  let P := k+r+q+5
  let pi := q*N
  ∃ (A : PEqualNP.CircuitLowerBounds.Circuit) (treeWire : Fin n → I → Fin (pi+A.size))
    (widthWire : Fin digits → Fin (pi+A.size)),
    PEqualNP.MetaComplexity.FanInTwo A ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack pi A ∧
    A.output = (widthWire 0).val ∧ A.size ≤ 2^80*P^80 ∧
    let design := fun (obs : Fin q → X) (v : Fin n) (j : I) =>
      (A.wires (masks obs)).getD (treeWire v j).val false
    let priceBit := fun (obs : Fin q → X) (e : Fin digits) => (A.wires (masks obs)).getD (widthWire e).val false
    let price := fun (obs : Fin q → X) => ∑ e : Fin digits, if priceBit obs e then 2^e.val else 0
    (∀ obs : Fin q → X, fits obs (design obs) (price obs) ∧
      ∀ (alt : Bag) (cost : Nat), fits obs alt cost → price obs ≤ cost) ∧
    ∀ cap : Nat,
      let w := min N cap
      let inputs := pi+n*leafCount+digits+(2+2*r)*k+q
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (ok : Fin (inputs+C.size))
        (countWire : Fin (k+1) → Fin (inputs+C.size)) (keyWire : Fin k → Fin (inputs+C.size)),
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
        C.output = ok.val ∧ C.size ≤ 2^160*P^100*2^(w % 2)*7^(w/2) ∧
        ∀ (obs : Fin q → X) (name : Bool → W) (c : Bool → Fin r → W) (rhs : Fin q → F),
        let bits := masks obs ++ (List.finRange n).flatMap (fun v => leafBits (design obs v)) ++
          List.ofFn (priceBit obs) ++ pack (name false) ++ pack (name true) ++
          [false,true].flatMap (fun b => (List.finRange r).flatMap (fun t => pack (c b t))) ++
          List.ofFn (fun j : Fin q => decide (rhs j ≠ 0))
        let wire := fun i : Fin (inputs+C.size) => (C.wires bits).getD i.val false
        let actual := fun (key : W) (b : Bool) (time : Fin (r+1)) =>
          ((List.finRange r).take time.val).foldl (fun prev tick =>
            let y := mix b prev
            fun j : Fin k => y j + (1+y (ix (j.val+1)))*y (ix (j.val+2)) +
              rot (feed b tick.val) key j + c b tick j) (rot (start b) key + name b)
        let hit := fun key : W => ∀ i, pair (obs i) (key,actual key) = rhs i
        let cnt := Nat.card {key : W // hit key}
        let out := fun j => (if wire (keyWire j) then 1 else 0 : F)
        let code : W → Nat := fun v => ∑ j : Fin k, if v j = 0 then 0 else 2^j.val
        (wire ok = true ↔ price obs ≤ cap) ∧
          (∀ s, wire (countWire s) = (if wire ok then cnt else 0).testBit s.val) ∧
          (wire ok = true → 0 < cnt → hit out ∧ ∀ key, hit key → code out ≤ code key) ∧
          ((wire ok = false ∨ cnt = 0) → out = 0) := by
  classical
  intro k r q hk F W X G I N ix rot start feed mix pair form leafCount n Bag arc geometric layout
    dir fits digits pack lanes masks leafBits P pi
  have hLayout (bag : Bag) : layout bag ↔ GoodLayout hk bag := by
    unfold layout GoodLayout
    refine and_congr (exists_congr fun v => ?_) (forall_congr' fun v => ?_)
    · exact funext_iff.symm
    · exact and_congr (boxes_iff hk (bag v)) (rows_iff bag v).symm
  have hFits (obs : Fin q → X) (bag : Bag) (cap : ℕ) : fits obs bag cap ↔ Fits hk obs bag cap := by
    change (layout bag ∧ ∀ v, cutWidth hk obs (bag v) ≤ cap) ↔ _
    rw [Fits, hLayout]
  obtain ⟨o, ho, hō⟩ := optimize_cmp (r:=r) (q:=q) hk
  let addr (s : ObsPort k r q) := address (obsOrder k r q) s
  have ha (s : ObsPort k r q) : addr s < pi+1 := by
    have h := address_lt (obsOrder_mem s)
    rw [obsOrder_length] at h
    exact Nat.lt_succ_of_lt h
  obtain ⟨gs, wa, hfa, hba, hsa, hwa, hva⟩ := ho.extract pi addr ha
  let A : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs,wa (.inr 0)⟩
  let treeWire (v : Fin n) (j : I) : Fin (pi+A.size) := ⟨wa (.inl (v,j)),hwa _⟩
  let widthWire (e : Fin digits) : Fin (pi+A.size) := ⟨wa (.inr e),hwa _⟩
  refine ⟨A,treeWire,widthWire,hfa,hba _,rfl,hsa.trans (design_size k r q),?_⟩
  intro design priceBit price
  have hc (obs : Fin q → X) (s : Wires k r) :
      (A.wires (masks obs)).getD (wa s) false = o (obsBit obs) s := by
    have h := map_obsOrder obs
    change (obsOrder k r q).map (obsBit obs) = masks obs at h
    have hlen : (masks obs).length = pi := by rw [← h, List.length_map, obsOrder_length]
    have haddr : (fun s => ((masks obs)++[false]).getD (addr s) false) = obsBit obs := by
      funext s
      rw [← h]
      exact address_read _ _ (obsOrder_mem s) _
    have he := hva A.output (masks obs) hlen s
    rw [haddr] at he
    exact he
  have hopt (obs : Fin q → X) : Fits hk obs (design obs) (price obs) ∧
      ∀ alt cost, Fits hk obs alt cost → price obs ≤ cost := by
    have hb : design obs = fun v j => o (obsBit obs) (.inl (v,j)) := by
      funext v j
      exact hc obs (.inl (v,j))
    have hp : price obs = tabN (fun e => o (obsBit obs) (.inr e)) := by
      unfold price tabN
      exact Finset.sum_congr rfl (fun e _ => by rw [show priceBit obs e =
        o (obsBit obs) (.inr e) from hc obs (.inr e)])
    rw [hb,hp]
    exact hō obs
  refine ⟨fun obs => ⟨(hFits _ _ _).mpr (hopt obs).1,
    fun alt cost hf => (hopt obs).2 alt cost ((hFits _ _ _).mp hf)⟩,?_⟩
  intro cap w inputs
  have hRoom : n ≤ (k+r+q+5)^2 := by
    have hs : 2*((2*r+1)*k) ≤ (k+r+2)^2 := by
      zify
      nlinarith only [sq_nonneg ((k : ℤ)-r), Int.natCast_nonneg k, Int.natCast_nonneg r]
    exact (Nat.sub_le ..).trans (hs.trans (Nat.pow_le_pow_left (by omega) 2))
  obtain ⟨O,hO,hsem⟩ := compactCountOracle (k:=k) (r:=r) (q:=q) (n:=n) hk cap
  let sOrder := evalOrder k r q n digits
  let sAddr (s : InputSlot k r q n) := address sOrder (.inl s)
  have hAddr (s : InputSlot k r q n) : sAddr s < inputs+1 := by
    have h := address_lt (evalOrder_mem (digits:=digits) s)
    rw [evalOrder_length] at h
    exact Nat.lt_succ_of_lt h
  obtain ⟨cs, alloc, hfan, hback, hlen, halloc, hval⟩ := (Greedy.wrap_cmp hO).extract inputs sAddr hAddr
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨cs,alloc (.inl (.inl ()))⟩
  let ok : Fin (inputs+C.size) := ⟨alloc (.inl (.inl ())),halloc _⟩
  let countWire (s : Fin (k+1)) : Fin (inputs+C.size) := ⟨alloc (.inl (.inr s)),halloc _⟩
  let keyWire (j : Fin k) : Fin (inputs+C.size) := ⟨alloc (.inr j),halloc _⟩
  refine ⟨C,ok,countWire,keyWire,hfan,hback _,rfl,?_,?_⟩
  · exact hlen.trans (by simpa only [Phi,mul_assoc,pow_two] using compact_full_size k r q n cap hRoom)
  intro obs name c rhs bits wire actual hit cnt out code
  let a := slotBit name c obs rhs (design obs)
  have hOrder := map_evalOrder obs (design obs) (priceBit obs) name c rhs
  change sOrder.map (Sum.elim a (priceBit obs)) = bits at hOrder
  have hb : bits.length = inputs := by rw [← hOrder,List.length_map,evalOrder_length]
  have hx : (fun s => (bits++[false]).getD (sAddr s) false) = a := by
    funext s
    rw [← hOrder]
    exact address_read _ _ (evalOrder_mem s) _
  have hw (j : Greedy.Output k) : (C.wires bits).getD (alloc j) false = Greedy.wrap O a j := by
    rw [← hx]
    exact hval C.output bits hb j
  have hn : readName a = name := by
    funext b j
    exact zbit_decode (name b j)
  have hC : readC a = c := by
    funext b t j
    exact zbit_decode (c b t j)
  have hObs : readObs a = obs := by
    funext i
    apply Prod.ext
    · funext j
      exact zbit_decode ((obs i).1 j)
    · funext b t j
      exact zbit_decode ((obs i).2 b t j)
  have hRhs : readRhs a = rhs := by
    funext i
    exact zbit_decode (rhs i)
  have hfit : inputGood hk cap a = true ↔ price obs ≤ cap := by
    have hGood := (hopt obs).1.1
    have hl : LayoutGuard.layout (fun (v,j) => bagSlot v j) a = true := by
      rw [LayoutGuard.layout_true]
      have hh := (hLayout (design obs)).mpr hGood
      change (∃ top : Fin n, ∀ j, design obs top j = true) ∧
        (∀ v : Fin n, geometric (design obs v) ∧ _) at hh
      exact ⟨hh.1, fun v => (hh.2 v).2⟩
    unfold inputGood
    rw [decide_eq_true_eq]
    change (LayoutGuard.layout (fun (v,j) => bagSlot v j) a = true ∧
      ∀ v, cutWidth hk (readObs a) (design obs v) ≤ cap) ↔ _
    rw [and_iff_right hl,hObs]
    exact ⟨fun hr => (hopt obs).2 (design obs) cap ⟨hGood,hr⟩,
      fun h => (fits_mono (hopt obs).1 h).2⟩
  let dec (x : Fin k → Bool) : W := fun j => b2z (x j)
  let enc (x : W) : Fin k → Bool := fun j => zbit (x j)
  have he (x : W) : dec (enc x) = x := funext fun j => zbit_decode (x j)
  have hd (x : Fin k → Bool) : enc (dec x) = x := funext fun j => st_dec_b2z (x j)
  have hh (x : Fin k → Bool) : inputHit hk a x ↔ hit (dec x) := by
    unfold inputHit
    rw [hn,hC,hObs,hRhs]
    rfl
  have hcnt : Greedy.cardinal (inputHit hk a) = cnt := by
    apply Nat.card_congr
    let e : (Fin k → Bool) ≃ W := ⟨dec,enc,hd,he⟩
    exact Equiv.subtypeEquiv e hh
  have hcode (x : Fin k → Bool) : code (dec x) = Greedy.code x := by
    unfold Greedy.code
    change (∑ j : Fin k, if b2z (x j) = 0 then 0 else 2^j.val) = _
    apply Finset.sum_congr rfl
    intro j _
    cases h : x j <;> simp [h,b2z]
  obtain ⟨hOk,hCount,hMin,hZero⟩ := Greedy.wrap_spec hsem a
  have hOkWire : wire ok = inputGood hk cap a := (hw (.inl (.inl ()))).trans hOk
  have hout : out = dec (fun j => Greedy.wrap O a (.inr j)) := by
    funext j
    exact congrArg b2z (hw (.inr j))
  refine ⟨hOkWire.symm ▸ hfit, ?_, ?_, ?_⟩
  · intro s
    exact (hw (.inl (.inr s))).trans (by rw [hCount s,hcnt,hOkWire])
  · intro hOK hp
    obtain ⟨hu,hmin⟩ := hMin (hOkWire.symm.trans hOK) (hcnt.symm ▸ hp)
    rw [hout]
    refine ⟨(hh _).mp hu, fun y hy => ?_⟩
    have ha := hmin (enc y) ((hh _).mpr ((he y).symm ▸ hy))
    rw [← hcode,← hcode,he] at ha
    exact ha
  · intro hz
    have hz' : inputGood hk cap a = false ∨ Greedy.cardinal (inputHit hk a) = 0 := by
      simpa only [← hOkWire,hcnt] using hz
    rw [hout, hZero hz']
    rfl
