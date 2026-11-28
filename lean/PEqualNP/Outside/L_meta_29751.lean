import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29751

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
  Sum.elim (fun j _ z => z.1 j) (fun g e z =>
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
  Sum.elim (fun j => ∀ x, pref j = some x → form hk (.inl j) 0 z = x)
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

def sign (a : F) : ℤ := if a = 0 then 1 else -1

lemma sign_add (a b : F) : sign (a + b) = sign a * sign b := by
  revert a b
  decide

lemma sign_zero : sign 0 = 1 := rfl
lemma sign_one : sign 1 = -1 := by decide

lemma cancellation {A : Type*} [AddCommGroup A] [Module F A] [Fintype A]
    (f : A →ₗ[F] F) (hf : f ≠ 0) : (∑ a : A, sign (f a)) = 0 := by
  have h : ∃ a, f a ≠ 0 := by
    by_contra! h
    exact hf (LinearMap.ext fun a => h a)
  obtain ⟨a, ha⟩ := h
  have h1 : f a = 1 := (ffCases (f a)).resolve_left ha
  have h2 := Equiv.sum_comp (Equiv.addRight a) (fun x : A => sign (f x))
  change (∑ x : A, sign (f (x + a))) = ∑ x : A, sign (f x) at h2
  simp_rw [map_add, sign_add, h1, sign_one, mul_neg, mul_one, Finset.sum_neg_distrib] at h2
  omega

open Classical in
lemma annihilatorIndicator {V : Type*} [AddCommGroup V] [Module F V]
    (R : Submodule F V) [Fintype R.dualAnnihilator] (x : V) :
    ∑ h : R.dualAnnihilator, sign (h.val x) = (if x ∈ R then (Nat.card R.dualAnnihilator : ℤ) else 0) := by
  by_cases hx : x ∈ R
  · have hz (h : R.dualAnnihilator) : h.val x = 0 := (Submodule.mem_dualAnnihilator _).mp h.prop x hx
    rw [ite_eq_left hx, Nat.card_eq_fintype_card]
    simp only [hz, sign_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · let f : R.dualAnnihilator →ₗ[F] F := (Module.Dual.eval F V x).comp R.dualAnnihilator.subtype
    have hf : f ≠ 0 := by
      intro heq
      apply hx
      rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
      intro g hg
      exact LinearMap.congr_fun heq ⟨g, hg⟩
    exact (cancellation (A := R.dualAnnihilator) f hf).trans (ite_eq_right hx).symm

theorem enumeration_bound {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (R : Submodule F V) (w : ℕ) (hw : Module.finrank F V ≤ 3 * w) :
    min (Module.finrank F R) (Module.finrank F R.dualAnnihilator) ≤ (3 * w) / 2 := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq R
  omega

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
  toFun z := Sum.elim z.1 (fun p => z.2 p.1 p.2.1 p.2.2)
  invFun u := (fun j => u (.inl j), fun b t j => u (.inr (b,t,j)))
  left_inv _ := rfl
  right_inv x := by funext j; cases j <;> rfl
  map_add' _ _ := by funext j; cases j <;> rfl
  map_smul' _ _ := by funext j; cases j <;> rfl

def row {k r q : ℕ} (hk : 0 < k) (obs : Fin q → Tape k r) : EqRow k q → Coord k r → F :=
  Sum.elim (fun (p : Bool × Fin k) => Pi.single (.inr (p.1, 0, p.2)) 1 +
    Pi.single (.inl (ix hk (p.2.val + k - start p.1 % k))) 1)
    (fun i => flatten (obs i))

def rowTarget {k q : ℕ} (name : Bool → Word k) (rhs : Fin q → F) : EqRow k q → F :=
  Sum.elim (fun p => name p.1 p.2) rhs

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
  refine Finset.sum_congr rfl fun s _ => ?_
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
      · simp only [form, Sum.elim_inr, h0, ite_true, mix, Pi.add_apply, Prod.snd_add]
        abel
      · by_cases h1 : e.val = 1 <;>
          simp only [form, Sum.elim_inr, h0, h1, Nat.one_ne_zero, ite_true, ite_false, mix, rot,
            Pi.add_apply, Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' c v := by
    rcases i with j | ⟨b,t,j⟩
    · rfl
    · have hfst : (c • v).1 = fun j => c * v.1 j := rfl
      have hsnd : (c • v).2 = fun b t j => c * v.2 b t j := rfl
      by_cases h0 : e.val = 0
      · simp only [form, Sum.elim_inr, h0, ite_true, mix, hsnd, RingHom.id_apply, smul_eq_mul]
        ring
      · by_cases h1 : e.val = 1 <;>
          simp only [form, Sum.elim_inr, h0, h1, Nat.one_ne_zero, ite_true, ite_false, mix, rot,
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

def Compatible {V : Type*} [AddCommGroup V] [Module F V] (L H E : Submodule F V)
    (a : Dual (LeftBoundary L H E)) (b : Dual (RightBoundary L H E))
    (p : Dual (ParentBoundary L H E)) : Prop :=
  ∃ v : Dual V, v.comp (LeftBoundary L H E).subtype = a ∧
    v.comp (RightBoundary L H E).subtype = b ∧
    v.comp (ParentBoundary L H E).subtype = p

noncomputable def splitCountEquiv {V : Type*} [AddCommGroup V] [Module F V]
    (L H E : Submodule F V) (p : Dual (ParentBoundary L H E))
    (goodL : Dual L → Prop) (goodH : Dual H → Prop) :
    {u : Dual ↥(L ⊔ H) // restr inf_le_left u = p ∧
      goodL (restr le_sup_left u) ∧ goodH (restr le_sup_right u)} ≃
    {fg : Dual L × Dual H // goodL fg.1 ∧ goodH fg.2 ∧
      Compatible L H E (restr inf_le_left fg.1) (restr inf_le_left fg.2) p} := by
  let f (u : {u : Dual ↥(L ⊔ H) // restr inf_le_left u = p ∧
      goodL (restr le_sup_left u) ∧ goodH (restr le_sup_right u)}) :
      {fg : Dual L × Dual H // goodL fg.1 ∧ goodH fg.2 ∧
        Compatible L H E (restr inf_le_left fg.1) (restr inf_le_left fg.2) p} :=
    ⟨(restr le_sup_left u.val, restr le_sup_right u.val), u.prop.2.1, u.prop.2.2,
      (split_glue L H E _ _ p).mpr
        ⟨u.val, ⟨rfl, rfl, u.prop.1⟩, fun _ hy => restr_sup_injective hy.1 hy.2.1⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro u v huv
    have h := congrArg Subtype.val huv
    exact Subtype.ext (restr_sup_injective (congrArg Prod.fst h) (congrArg Prod.snd h))
  · intro fg
    obtain ⟨u, ht, _⟩ := (split_glue L H E fg.val.1 fg.val.2 p).mp fg.prop.2.2
    exact ⟨⟨u, ht.2.2, ht.1.symm ▸ fg.prop.1, ht.2.1.symm ▸ fg.prop.2.1⟩,
      Subtype.ext (Prod.ext ht.1 ht.2.1)⟩

def selectedSpan {J V : Type*} [AddCommGroup V] [Module F V]
    (rows : J → V) (bag : J → Bool) : Submodule F V :=
  Submodule.span F {v | ∃ j, bag j = true ∧ v = rows j}

lemma maskedSpan {J V : Type*} [AddCommGroup V] [Module F V]
    (rows : J → V) (bag : J → Bool) :
    Submodule.span F (Set.range fun j => if bag j then rows j else 0) = selectedSpan rows bag := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change (if bag j then rows j else 0) ∈ selectedSpan rows bag
    by_cases hj : bag j = true
    · rw [ite_eq_left hj]
      exact Submodule.subset_span ⟨j, hj, rfl⟩
    · simp [hj]
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    exact Submodule.subset_span ⟨j, ite_eq_left hj⟩

lemma evalRange {J V : Type*} [Fintype J] [DecidableEq J] [AddCommGroup V] [Module F V]
    (rows : J → V) (x : J → F) :
    (∃ u : Dual V, ∀ j, u (rows j) = x j) ↔
      ∀ a : J → F, (∑ j, a j • rows j) = 0 → dotProduct x a = 0 := by
  let A : (J → F) →ₗ[F] V := Fintype.linearCombination F rows
  let ℓ := dotProductEquiv F J x
  have hsum (a : J → F) : A a = ∑ j, a j • rows j := by
    simp [A, Fintype.linearCombination_apply]
  have hunit (j : J) : A (Pi.single j 1) = rows j := by
    rw [hsum, Finset.sum_eq_single j]
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

end PEqualNP.Outside.L_meta_29751


-- Circuit, signed join, and projected-system helpers adapted from Zaz Brown.
-- Source: lean/PEqualNP/Outside/L_meta_33648.lean at 04168edab39014e515fbb09f71ba0651b69367a8.
-- Accepted in 2405e8184772d046cf97bcd918d1ca98d549a9ee, Apache-2.0.
-- Join wrapper chooses u = floor of half the total boundary dimension.

namespace PEqualNP.Outside.L_meta_29751.Donor

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

def cntP {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) : ℕ :=
  (Finset.univ.filter (fun q : Fin N => q < p ∧ pv R q = true)).card

def cntN {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) : ℕ :=
  (Finset.univ.filter (fun q : Fin N => q < p ∧ pv R q = false)).card

def rkOf {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) : ℕ :=
  (Finset.univ.filter (fun q : Fin N => pv R q = true)).card

def rowSlot {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (s : Fin K)
    (j : Fin (m + N + 1)) : Bool :=
  decide (∃ p : Fin N, pv R p = true ∧ cntP R p = s.val ∧ R (cl m p, j) = true)

def kerSlot {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (s : Fin K)
    (j : Fin N) : Bool :=
  decide (∃ q : Fin N, pv R q = false ∧ cntN R q = s.val ∧
    xor (decide (j = q)) (R (cl m j, cl m q)) = true)

def deadSlot {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (s : Fin K) :
    Bool :=
  decide (¬ ∃ q : Fin N, pv R q = false ∧ cntN R q = s.val)

def kerPt {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (lam : V K) : V N :=
  fun j => (if R (cl m j, rc m N) then 1 else 0) +
    ∑ s : Fin K, lam s * (if kerSlot K R s j then 1 else 0)

def nx {a b c : ℕ} (j : Fin a) : Fin (a + b + c) := ⟨j.val, by omega⟩
def ny {a b c : ℕ} (j : Fin b) : Fin (a + b + c) := ⟨a + j.val, by omega⟩
def nz {a b c : ℕ} (j : Fin c) : Fin (a + b + c) := ⟨a + b + j.val, by omega⟩

def LrBits {m N d : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (e : Fin d → Fin N) : Fin d × Fin (K + 1) → Bool := fun p =>
  if h : p.2.val < K then rowSlot K R ⟨p.2.val, h⟩ (cl m (e p.1)) else false

def LnBits {m N d : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (e : Fin d → Fin N) : Fin d × Fin (K + 1) → Bool := fun p =>
  if h : p.2.val < K then kerSlot K R ⟨p.2.val, h⟩ (e p.1) else R (cl m (e p.1), rc m N)

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
    Cmp ι (κ ⊕ κ') (S + S') (fun v => Sum.elim (F v) (F' v)) := by
  intro n gs hg hpos ws hws
  obtain ⟨m1, o1, g1, l1, b1, v1⟩ := h1 n gs hg hpos ws hws
  obtain ⟨m2, o2, g2, l2, b2, v2⟩ := h2 n (gs ++ m1) g1 (by simp; omega) ws
    (by intro j; have := hws j; simp; omega)
  refine ⟨m1 ++ m2, Sum.elim o1 o2, by simpa [List.append_assoc] using g2, by simp; omega, ?_, ?_⟩
  · intro k
    cases k with
    | inl k => have := b1 k; simp; omega
    | inr k => have := b2 k; simp at this ⊢; omega
  · intro x hx k
    cases k with
    | inl k =>
      simp only [Sum.elim_inl]
      rw [← List.append_assoc, fa_val_append n (gs ++ m1) m2 x _ hx (by
        have := b1 k; simp; omega)]
      exact v1 x hx k
    | inr k =>
      simp only [Sum.elim_inr]
      rw [← List.append_assoc, v2 x hx k]
      congr 1
      funext j
      exact fa_val_append n gs m1 x _ hx (hws j)

theorem Cmp.keep {ι κ : Type} {S : ℕ} {F : (ι → Bool) → κ → Bool} (h : Cmp ι κ S F) :
    Cmp ι (ι ⊕ κ) S (fun v => Sum.elim v (F v)) := by
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
    (h : ∀ i, Cmp ι κ s (F i)) : Cmp ι (I × κ) (Fintype.card I * s) (fun v p => F p.1 v p.2) := by
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
    (hc : ∀ i < n, ∀ v, c (i + 1) v = G i (Sum.elim v (c i v))) :
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
          (Sum.inl (Sum.inr (⟨p.1.val, hp⟩, p.2)) : (ι ⊕ (Fin (n + 1) × σ)) ⊕ σ)
        else Sum.inr p.2))
    refine Cmp.congr (Cmp.mono C (by simp [Nat.succ_mul])) ?_
    intro v p
    by_cases hp : p.1.val < n + 1
    · simp [hp]
    · have hp' : p.1.val = n + 1 := by omega
      simp only [hp, ↓reduceDIte, Sum.elim_inr]
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
  have g := fa_gate (ι := Unit ⊕ Unit) GateOp.and (by simp) [Sum.inl (), Sum.inr ()] (by simp)
  have := Cmp.comp (Cmp.pair h h') g
  exact Cmp.congr this (fun v k => by simp [GateOp.eval])

theorem Cb.or {ι : Type} {S S' : ℕ} {φ ψ : (ι → Bool) → Bool} (h : Cb ι S φ) (h' : Cb ι S' ψ) :
    Cb ι (S + S' + 1) (fun v => φ v || ψ v) := by
  have g := fa_gate (ι := Unit ⊕ Unit) GateOp.or (by simp) [Sum.inl (), Sum.inr ()] (by simp)
  have := Cmp.comp (Cmp.pair h h') g
  exact Cmp.congr this (fun v k => by simp [GateOp.eval])

theorem Cb.xor {ι : Type} {S S' : ℕ} {φ ψ : (ι → Bool) → Bool} (h : Cb ι S φ) (h' : Cb ι S' ψ) :
    Cb ι (S + S' + 4) (fun v => xor (φ v) (ψ v)) := by
  have l : Cb (Unit ⊕ Unit) 0 (fun v => v (Sum.inl ())) := Cb.var _
  have r : Cb (Unit ⊕ Unit) 0 (fun v => v (Sum.inr ())) := Cb.var _
  have g := Cb.and (Cb.or l r) (Cb.not (Cb.and l r))
  have := Cmp.comp (Cmp.pair h h') g
  refine Cmp.congr (Cmp.mono this (by omega)) ?_
  intro v k
  simp only [Sum.elim_inl, Sum.elim_inr]
  cases φ v <;> cases ψ v <;> rfl

theorem Cb.mux {ι : Type} {S S' S'' : ℕ} {χ φ ψ : (ι → Bool) → Bool} (hc : Cb ι S χ)
    (h : Cb ι S' φ) (h' : Cb ι S'' ψ) :
    Cb ι (S + S' + S'' + 4) (fun v => if χ v then φ v else ψ v) := by
  have c : Cb ((Unit ⊕ Unit) ⊕ Unit) 0 (fun v => v (Sum.inl (Sum.inl ()))) := Cb.var _
  have l : Cb ((Unit ⊕ Unit) ⊕ Unit) 0 (fun v => v (Sum.inl (Sum.inr ()))) := Cb.var _
  have r : Cb ((Unit ⊕ Unit) ⊕ Unit) 0 (fun v => v (Sum.inr ())) := Cb.var _
  have g := Cb.or (Cb.and c l) (Cb.and (Cb.not c) r)
  have := Cmp.comp (Cmp.pair (Cmp.pair hc h) h') g
  refine Cmp.congr (Cmp.mono this (by omega)) ?_
  intro v k
  simp only [Sum.elim_inl, Sum.elim_inr]
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
    Cb ι (Fintype.card I * (s + 1) + 1) (fun v => decide (∃ i, φ i v = true)) := by
  have := fa_listOr h (Finset.univ : Finset I).toList
  rw [Finset.length_toList, Finset.card_univ] at this
  refine Cb.congr this (fun v => ?_)
  rw [Bool.eq_iff_iff]
  simp [List.any_eq_true]

theorem Cb.bigAnd {ι I : Type} [Fintype I] {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (Fintype.card I * (s + 1) + 1) (fun v => decide (∀ i, φ i v = true)) := by
  have := fa_listAnd h (Finset.univ : Finset I).toList
  rw [Finset.length_toList, Finset.card_univ] at this
  refine Cb.congr this (fun v => ?_)
  rw [Bool.eq_iff_iff]
  simp [List.all_eq_true]

theorem Cb.bigXor {ι I : Type} [Fintype I] {s : ℕ} {φ : I → (ι → Bool) → Bool}
    (h : ∀ i, Cb ι s (φ i)) :
    Cb ι (Fintype.card I * (s + 4) + 1)
      (fun v => decide ((Finset.univ.filter (fun i => φ i v = true)).card % 2 = 1)) := by
  have := fa_listXor h (Finset.univ : Finset I).toList
  rw [Finset.length_toList, Finset.card_univ] at this
  refine Cb.congr this (fun v => ?_)
  rw [fa_xor_sum (fun i => φ i v), Finset.sum_map_toList, Finset.card_filter]

theorem Cmp.ofBits {ι κ : Type} [Fintype κ] {s : ℕ} {F : (ι → Bool) → κ → Bool}
    (h : ∀ k, Cb ι s (fun v => F v k)) : Cmp ι κ (Fintype.card κ * s) F := by
  have := Cmp.comp (Cmp.piU (I := κ) (κ := Unit) (F := fun k v _ => F v k) h)
    (Cmp.wire (fun k : κ => (k, ())))
  exact this

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
  rw [Fintype.card_fin] at this
  exact this

theorem Cw.const {ι : Type} {W : ℕ} (c : BitVec W) : Cw ι W W (fun _ => c) := by
  have := Cw.ofBits (ι := ι) (φ := fun _ => c) (s := 1) (fun i => Cb.const _)
  rw [Nat.mul_one] at this
  exact this

theorem fb_addcore (W : ℕ) (c0 : Bool) :
    Cmp (Fin W ⊕ Fin W) (Fin W) (13 * (W + 1))
      (fun u i => (bv (fun j => u (Sum.inl j)) + bv (fun j => u (Sum.inr j)) +
        BitVec.setWidth W (BitVec.ofBool c0)).getLsbD i.val) := by
  have hch := Cmp.chain (ι := Fin W ⊕ Fin W) (σ := Unit) W 5
    (fun i u _ => BitVec.carry i (bv (fun j => u (Sum.inl j))) (bv (fun j => u (Sum.inr j))) c0)
    (fun i w _ => if h : i < W then
      ((w (Sum.inl (Sum.inl ⟨i, h⟩)) && w (Sum.inl (Sum.inr ⟨i, h⟩)) ||
        w (Sum.inl (Sum.inl ⟨i, h⟩)) && w (Sum.inr ())) ||
        w (Sum.inl (Sum.inr ⟨i, h⟩)) && w (Sum.inr ())) else false)
    (by
      refine Cmp.mono (Cmp.congr (Cb.const c0) ?_) (by omega)
      intro v k
      cases c0 <;> simp [BitVec.carry, Nat.mod_one])
    (by
      intro i hi
      have h := Cb.or (Cb.or (Cb.and (Cb.var (ι := (Fin W ⊕ Fin W) ⊕ Unit) (Sum.inl (Sum.inl ⟨i, hi⟩)))
          (Cb.var (Sum.inl (Sum.inr ⟨i, hi⟩))))
        (Cb.and (Cb.var (Sum.inl (Sum.inl ⟨i, hi⟩))) (Cb.var (Sum.inr ()))))
        (Cb.and (Cb.var (Sum.inl (Sum.inr ⟨i, hi⟩))) (Cb.var (Sum.inr ())))
      refine Cmp.mono (Cmp.congr h ?_) (by omega)
      intro v k
      simp [hi])
    (by
      intro i hi u
      funext k
      have hx : (bv (fun j => u (Sum.inl j))).getLsbD i = u (Sum.inl ⟨i, hi⟩) :=
        getLsbD_bv (fun j => u (Sum.inl j)) ⟨i, hi⟩
      have hy : (bv (fun j => u (Sum.inr j))).getLsbD i = u (Sum.inr ⟨i, hi⟩) :=
        getLsbD_bv (fun j => u (Sum.inr j)) ⟨i, hi⟩
      rw [BitVec.carry_succ, hx, hy]
      simp only [dite_true, hi, Sum.elim_inl, Sum.elim_inr, Bool.atLeastTwo])
  have hk := Cmp.keep hch
  have hb : Cmp ((Fin W ⊕ Fin W) ⊕ Fin (W + 1) × Unit) (Fin W) (Fintype.card (Fin W) * 8)
      (fun w i => xor (w (Sum.inl (Sum.inl i)))
        (xor (w (Sum.inl (Sum.inr i))) (w (Sum.inr ((⟨i.val, by omega⟩ : Fin (W + 1)), ()))))) := by
    apply Cmp.ofBits
    intro i
    exact Cb.mono (Cb.xor (Cb.var (Sum.inl (Sum.inl i)))
      (Cb.xor (Cb.var (Sum.inl (Sum.inr i))) (Cb.var (Sum.inr ((⟨i.val, by omega⟩ : Fin (W + 1)), ()))))) (by omega)
  refine Cmp.mono (Cmp.congr (Cmp.comp hk hb) ?_) (by rw [Fintype.card_fin]; omega)
  intro v i
  rw [BitVec.getLsbD_add_add_bool i.isLt]
  have hx : (bv (fun j => v (Sum.inl j))).getLsbD i.val = v (Sum.inl i) :=
    getLsbD_bv (fun j => v (Sum.inl j)) i
  have hy : (bv (fun j => v (Sum.inr j))).getLsbD i.val = v (Sum.inr i) :=
    getLsbD_bv (fun j => v (Sum.inr j)) i
  rw [hx, hy]
  rfl

theorem fb_adc {ι : Type} {W S S' : ℕ} {φ ψ : (ι → Bool) → BitVec W} (c0 : Bool)
    (h : Cw ι W S φ) (h' : Cw ι W S' ψ) :
    Cw ι W (S + S' + 13 * (W + 1))
      (fun v => φ v + ψ v + BitVec.setWidth W (BitVec.ofBool c0)) := by
  refine Cmp.congr (Cmp.comp (Cmp.pair h h') (fb_addcore W c0)) ?_
  intro v i
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [bv_getLsbD, bv_getLsbD]

theorem fb_not {ι : Type} {W S : ℕ} {φ : (ι → Bool) → BitVec W} (h : Cw ι W S φ) :
    Cw ι W (S + W) (fun v => ~~~ φ v) := by
  have hb : Cmp (Fin W) (Fin W) (Fintype.card (Fin W) * 1) (fun u i => !u i) := by
    apply Cmp.ofBits
    intro i
    exact Cb.mono (Cb.not (Cb.var i)) (by omega)
  refine Cmp.mono (Cmp.congr (Cmp.comp h hb) ?_) (by rw [Fintype.card_fin]; omega)
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

theorem Cw.neg {ι : Type} {W S : ℕ} {φ : (ι → Bool) → BitVec W} (h : Cw ι W S φ) :
    Cw ι W (S + 20 * (W + 1)) (fun v => - φ v) := by
  refine Cw.mono (Cw.congr (fb_adc true (Cw.const (ι := ι) (0 : BitVec W)) (fb_not h)) ?_)
    (by omega)
  intro v
  rw [fb_sub_eq]
  simp

theorem fb_term (W k : ℕ) :
    Cw (Fin W ⊕ Fin W) W W
      (fun u => if (bv (fun j => u (Sum.inr j))).getLsbD k = true
        then bv (fun j => u (Sum.inl j)) <<< k else 0) := by
  have hb := Cw.ofBits (ι := Fin W ⊕ Fin W) (W := W) (s := 1)
    (φ := fun u => if (bv (fun j => u (Sum.inr j))).getLsbD k = true
        then bv (fun j => u (Sum.inl j)) <<< k else 0)
    (by
      intro i
      by_cases hk : k ≤ i.val
      · have hkW : k < W := lt_of_le_of_lt hk i.isLt
        refine Cb.congr (Cb.and (Cb.var (Sum.inr ⟨k, hkW⟩))
          (Cb.var (Sum.inl ⟨i.val - k, by omega⟩))) ?_
        intro v
        have hy : (bv (fun j => v (Sum.inr j))).getLsbD k = v (Sum.inr ⟨k, hkW⟩) :=
          getLsbD_bv (fun j => v (Sum.inr j)) ⟨k, hkW⟩
        have hx : (bv (fun j => v (Sum.inl j))).getLsbD (i.val - k)
            = v (Sum.inl ⟨i.val - k, by omega⟩) :=
          getLsbD_bv (fun j => v (Sum.inl j)) ⟨i.val - k, by omega⟩
        rw [hy]
        cases hv : v (Sum.inr ⟨k, hkW⟩)
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
      (fun u => (bv (fun j => u (Sum.inl j))).mulRec (bv (fun j => u (Sum.inr j))) s) := by
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
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [bv_getLsbD, bv_getLsbD, BitVec.getLsbD_mul]

theorem Cw.mux {ι : Type} {W S S' S'' : ℕ} {χ : (ι → Bool) → Bool} {φ ψ : (ι → Bool) → BitVec W}
    (hc : Cb ι S χ) (h : Cw ι W S' φ) (h' : Cw ι W S'' ψ) :
    Cw ι W (S + S' + S'' + 4 * W) (fun v => if χ v then φ v else ψ v) := by
  have hb : Cmp (Unit ⊕ (Fin W ⊕ Fin W)) (Fin W) (Fintype.card (Fin W) * 4)
      (fun w i => if w (Sum.inl ()) then w (Sum.inr (Sum.inl i)) else w (Sum.inr (Sum.inr i))) := by
    apply Cmp.ofBits
    intro i
    exact Cb.mono (Cb.mux (Cb.var (Sum.inl ())) (Cb.var (Sum.inr (Sum.inl i)))
      (Cb.var (Sum.inr (Sum.inr i)))) (by omega)
  refine Cmp.mono (Cmp.congr (Cmp.comp (Cmp.pair hc (Cmp.pair h h')) hb) ?_)
    (by rw [Fintype.card_fin]; omega)
  intro v i
  simp only [Sum.elim_inl, Sum.elim_inr]
  cases χ v <;> simp

theorem Cmp.ofWords {ι α : Type} [Fintype α] {W s : ℕ} {G : (ι → Bool) → α → BitVec W}
    (h : ∀ x : α, Cw ι W s (fun v => G v x)) :
    Cmp ι (α × Fin W) (Fintype.card α * s) (fun v => untab (G v)) := by
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

theorem fc_A_id {D : ℕ} (p : Fin D) (l : List (Fin D)) (M : Fin D × Fin D → Bool)
    (hp : M (p, p) = true) : l.foldl (fun M i => gjStep (false, p, i) M) M = M := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    have : gjStep (false, p, i) M = M := by
      unfold gjStep
      have hc : gjCtl (false, p, i) M = false := by simp [gjCtl, hp]
      rw [hc, fc_rowAdd_false]
    rw [this]
    exact ih

theorem fc_B_id {D : ℕ} (p : Fin D) (l : List (Fin D)) (M : Fin D × Fin D → Bool)
    (hp : M (p, p) = false) : l.foldl (fun M i => gjStep (true, p, i) M) M = M := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    have : gjStep (true, p, i) M = M := by
      unfold gjStep
      have hc : gjCtl (true, p, i) M = false := by simp [gjCtl, hp]
      rw [hc, fc_rowAdd_false]
    rw [this]
    exact ih

theorem fc_A {D : ℕ} (p : Fin D) (k : ℕ) (hk : p.val = k) (l : List (Fin D))
    (hl : ∀ i ∈ l, i ≠ p) (M : Fin D × Fin D → Bool) (hI : fc_Inv k M) :
    fc_Inv k (l.foldl (fun M i => gjStep (false, p, i) M) M) ∧
    ((l.foldl (fun M i => gjStep (false, p, i) M) M) (p, p) = false →
      l.foldl (fun M i => gjStep (false, p, i) M) M = M ∧
      ∀ i ∈ l, (p < i ∨ M (i, i) = false) → M (i, p) = false) := by
  induction l with
  | nil => exact ⟨hI, fun _ => ⟨rfl, fun i hi => absurd hi (List.not_mem_nil)⟩⟩
  | cons i l ih =>
    have ih' := ih (fun i' h' => hl i' (List.mem_cons_of_mem _ h'))
    have hip : i ≠ p := hl i (List.mem_cons_self)
    rw [List.foldl_cons]
    by_cases hc : gjCtl (false, p, i) M = true
    · have hc' := hc
      simp only [gjCtl, Bool.false_eq_true, if_false, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, Bool.not_eq_true'] at hc'
      obtain ⟨⟨hfree, hip1⟩, hpp⟩ := hc'
      have hrow : ∀ q : Fin D, q.val < k → M (i, q) = false := by
        intro q hq
        apply hI.2.1 i q hq
        rcases hfree with hf | hf
        · left
          have : p.val < i.val := hf
          omega
        · right
          exact hf
      have hM1pp : gjStep (false, p, i) M (p, p) = true := by
        simp [gjStep, gjT, gjS, rowAdd, hc, hip1, hpp]
      rw [fc_A_id p l _ hM1pp]
      refine ⟨?_, ?_⟩
      · apply fc_Inv_congr k M _ _ hI
        intro j q hq
        simp only [gjStep, gjT, gjS, rowAdd, Bool.false_eq_true, if_false, hc]
        split
        · rw [hrow q hq]
          simp
        · rfl
      · intro h
        rw [hM1pp] at h
        exact absurd h (by simp)
    · have hcf : gjCtl (false, p, i) M = false := by simpa using hc
      have hM1 : gjStep (false, p, i) M = M := by
        unfold gjStep
        rw [hcf, fc_rowAdd_false]
      rw [hM1]
      refine ⟨ih'.1, ?_⟩
      intro h
      obtain ⟨hM, hrest⟩ := ih'.2 h
      refine ⟨hM, ?_⟩
      intro i' hi' hfree
      rcases List.mem_cons.1 hi' with rfl | hi'
      · rw [hM] at h
        rcases hfree with hf | hf
        · simpa [gjCtl, hf, h] using hcf
        · simpa [gjCtl, hf, h] using hcf
      · exact hrest i' hi' hfree

theorem fc_B {D : ℕ} (p : Fin D) (k : ℕ) (l : List (Fin D))
    (hl : ∀ i ∈ l, i ≠ p) (M : Fin D × Fin D → Bool) (hpp : M (p, p) = true)
    (hrow : ∀ q : Fin D, q.val < k → M (p, q) = false) :
    (∀ i q : Fin D, q.val < k →
      (l.foldl (fun M i => gjStep (true, p, i) M) M) (i, q) = M (i, q)) ∧
    (∀ j, (l.foldl (fun M i => gjStep (true, p, i) M) M) (p, j) = M (p, j)) ∧
    (∀ i, i ≠ p → (i ∈ l ∨ M (i, p) = false) →
      (l.foldl (fun M i => gjStep (true, p, i) M) M) (i, p) = false) := by
  induction l generalizing M with
  | nil =>
    refine ⟨fun _ _ _ => rfl, fun _ => rfl, ?_⟩
    intro i _ h
    rcases h with h | h
    · exact absurd h (List.not_mem_nil)
    · exact h
  | cons i l ih =>
    have hip : i ≠ p := hl i (List.mem_cons_self)
    rw [List.foldl_cons]
    have h1 : ∀ j, gjStep (true, p, i) M (p, j) = M (p, j) := by
      intro j
      simp [gjStep, gjT, gjS, rowAdd, Ne.symm hip]
    have h2 : ∀ i' q : Fin D, q.val < k → gjStep (true, p, i) M (i', q) = M (i', q) := by
      intro i' q hq
      simp [gjStep, gjT, gjS, rowAdd, hrow q hq]
    have h3 : gjStep (true, p, i) M (i, p) = false := by
      simp [gjStep, gjT, gjS, rowAdd, gjCtl, hpp]
    have h4 : ∀ i', i' ≠ i → gjStep (true, p, i) M (i', p) = M (i', p) := by
      intro i' hi'
      simp [gjStep, gjT, gjS, rowAdd, hi']
    obtain ⟨ia, ib, ic⟩ := ih (fun i' h' => hl i' (List.mem_cons_of_mem _ h'))
      (gjStep (true, p, i) M) (by rw [h1]; exact hpp)
      (fun q hq => by rw [h1]; exact hrow q hq)
    refine ⟨?_, ?_, ?_⟩
    · intro i' q hq
      rw [ia i' q hq, h2 i' q hq]
    · intro j
      rw [ib j, h1 j]
    · intro i' hi'p h
      apply ic i' hi'p
      by_cases hii : i' = i
      · right
        rw [hii]
        exact h3
      · rcases h with h | h
        · rcases List.mem_cons.1 h with h | h
          · exact absurd h hii
          · left
            exact h
        · right
          rw [h4 i' hii]
          exact h

def fc_col {D : ℕ} (p : Fin D) (M : Fin D × Fin D → Bool) : Fin D × Fin D → Bool :=
  ((List.finRange D).filter (fun i => i ≠ p)).foldl (fun M i => gjStep (true, p, i) M)
    (((List.finRange D).filter (fun i => i ≠ p)).foldl (fun M i => gjStep (false, p, i) M) M)

theorem fc_gj_eq {D : ℕ} (M : Fin D × Fin D → Bool) :
    gj D M = (List.finRange D).foldl (fun M p => fc_col p M) M := by
  unfold gj sched
  rw [List.foldl_flatMap]
  simp only [List.foldl_append, List.foldl_map, fc_col]

theorem fc_colInv {D : ℕ} (p : Fin D) (M : Fin D × Fin D → Bool) (hI : fc_Inv p.val M) :
    fc_Inv (p.val + 1) (fc_col p M) := by
  have hl : ∀ i ∈ (List.finRange D).filter (fun i => i ≠ p), i ≠ p := by
    intro i hi
    rw [List.mem_filter] at hi
    simpa using hi.2
  have hmem : ∀ i, i ≠ p → i ∈ (List.finRange D).filter (fun i => i ≠ p) := by
    intro i hi
    rw [List.mem_filter]
    exact ⟨List.mem_finRange i, by simpa using hi⟩
  obtain ⟨hIA, hA⟩ := fc_A p p.val rfl _ hl M hI
  unfold fc_col
  generalize ((List.finRange D).filter (fun i => i ≠ p)).foldl
    (fun M i => gjStep (false, p, i) M) M = MA at hIA hA
  by_cases hpp : MA (p, p) = true
  · have hrow : ∀ q : Fin D, q.val < p.val → MA (p, q) = false :=
      fun q hq => hIA.2.1 p q hq (Or.inl le_rfl)
    obtain ⟨ba, bb, bc⟩ := fc_B p p.val _ hl MA hpp hrow
    generalize ((List.finRange D).filter (fun i => i ≠ p)).foldl
      (fun M i => gjStep (true, p, i) M) MA = MB at ba bb bc
    obtain ⟨ha, hb, hc⟩ := hIA
    have hBpp : MB (p, p) = true := by rw [bb]; exact hpp
    refine ⟨?_, ?_, ?_⟩
    · intro q hq hqq i
      by_cases hqp : q = p
      · subst hqp
        by_cases hiq : i = q
        · subst hiq
          simp [hqq]
        · rw [bc i hiq (Or.inl (hmem i hiq))]
          simp [hiq]
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h)
          omega
        rw [ba _ _ hq'] at hqq ⊢
        exact ha q hq' hqq i
    · intro i q hq hfree
      have hip : i ≠ p := by
        intro h
        subst h
        rcases hfree with hf | hf
        · omega
        · rw [hBpp] at hf
          exact absurd hf (by simp)
      by_cases hqp : q = p
      · subst hqp
        exact bc i hip (Or.inl (hmem i hip))
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h)
          omega
        rw [ba _ _ hq']
        apply hb i q hq'
        by_cases hi : i.val < p.val
        · right
          rcases hfree with hf | hf
          · omega
          · rw [← ba _ _ hi]
            exact hf
        · left
          omega
    · intro p' q hqp' hp' hp'p'
      have hq' : q.val < p'.val := hqp'
      by_cases hpe : p' = p
      · subst hpe
        rw [bb]
        exact hrow q hq'
      · have hp'' : p'.val < p.val := by
          have : p'.val ≠ p.val := fun h => hpe (Fin.ext h)
          omega
        rw [ba _ _ (by omega)]
        rw [ba _ _ hp''] at hp'p'
        exact hc p' q hqp' hp'' hp'p'
  · have hppf : MA (p, p) = false := by simpa using hpp
    rw [fc_B_id p _ MA hppf]
    obtain ⟨hMeq, hcol⟩ := hA hppf
    obtain ⟨ha, hb, hc⟩ := hIA
    have hfreecol : ∀ i : Fin D, (p.val + 1 ≤ i.val ∨ MA (i, i) = false) → MA (i, p) = false := by
      intro i hfree
      by_cases hip : i = p
      · rw [hip]
        exact hppf
      · rw [hMeq] at hfree ⊢
        apply hcol i (hmem i hip)
        rcases hfree with hf | hf
        · left
          show p.val < i.val
          omega
        · right
          exact hf
    refine ⟨?_, ?_, ?_⟩
    · intro q hq hqq i
      by_cases hqp : q = p
      · subst hqp
        rw [hppf] at hqq
        exact absurd hqq (by simp)
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h)
          omega
        exact ha q hq' hqq i
    · intro i q hq hfree
      by_cases hqp : q = p
      · subst hqp
        exact hfreecol i hfree
      · have hq' : q.val < p.val := by
          have : q.val ≠ p.val := fun h => hqp (Fin.ext h)
          omega
        apply hb i q hq'
        rcases hfree with hf | hf
        · left
          omega
        · right
          exact hf
    · intro p' q hqp' hp' hp'p'
      have hpe : p' ≠ p := by
        intro h
        subst h
        rw [hppf] at hp'p'
        exact absurd hp'p' (by simp)
      have hp'' : p'.val < p.val := by
        have : p'.val ≠ p.val := fun h => hpe (Fin.ext h)
        omega
      exact hc p' q hqp' hp'' hp'p'

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

theorem fc_cols {D : ℕ} (R : Fin D × Fin D → Bool)
    (hpiv : ∀ p, R (p, p) = true → ∀ i, R (i, p) = decide (i = p))
    (hzero : ∀ q, R (q, q) = false → ∀ j, R (q, j) = false)
    (l : List (Fin D × Fin D)) (hnd : l.Nodup) (hne : ∀ e ∈ l, e.1 ≠ e.2) :
    ∀ A : Matrix (Fin D) (Fin D) (ZMod 2),
      (∀ i j, A i j = if i = j then (if R (i, i) then 1 else 0)
        else if (i, j) ∈ l then 0 else if R (i, j) then 1 else 0) →
      A * (l.map (fun e => tmat e.1 e.2 (R e))).prod = mat R := by
  induction l with
  | nil =>
    intro A hA
    simp only [List.map_nil, List.prod_nil, mul_one]
    ext i j
    rw [hA i j]
    by_cases hij : i = j
    · subst hij
      simp [mat]
    · simp [mat, hij]
  | cons e l ih =>
    intro A hA
    obtain ⟨p, q⟩ := e
    have hpq : p ≠ q := hne (p, q) (List.mem_cons_self)
    have hnotin : (p, q) ∉ l := (List.nodup_cons.1 hnd).1
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    apply ih (List.nodup_cons.1 hnd).2 (fun e' h' => hne e' (List.mem_cons_of_mem _ h'))
    have hkey : ∀ a, a ≠ p → R (p, q) = true → A a p = 0 := by
      intro a hap hR
      have hpp : R (p, p) = true := by
        by_contra h
        have := hzero p (by simpa using h) q
        rw [this] at hR
        exact absurd hR (by simp)
      have hcol := hpiv p hpp a
      rw [hA a p, if_neg hap]
      split
      · rfl
      · rw [hcol]
        simp [hap]
    intro i j
    by_cases hjq : j = q
    · subst hjq
      rw [tmat, Matrix.mul_transvection_apply_same]
      by_cases hip : i = p
      · subst hip
        rw [hA i j, if_neg hpq, if_pos (List.mem_cons_self), hA i i, if_pos rfl,
          if_neg hpq, if_neg hnotin]
        by_cases hR : R (i, j) = true
        · have hpp : R (i, i) = true := by
            by_contra h
            have := hzero i (by simpa using h) j
            rw [this] at hR
            exact absurd hR (by simp)
          simp [hR, hpp]
        · simp [hR]
      · have hz : (if R (p, j) = true then (1 : ZMod 2) else 0) * A i p = 0 := by
          by_cases hR : R (p, j) = true
          · rw [hkey i hip hR]
            simp
          · simp [hR]
        rw [hz, add_zero, hA i j]
        have hmem : ((i, j) ∈ (p, j) :: l) ↔ (i, j) ∈ l := by
          rw [List.mem_cons]
          constructor
          · rintro (h | h)
            · exact absurd (Prod.ext_iff.1 h).1 hip
            · exact h
          · exact Or.inr
        simp only [hmem]
    · rw [tmat, Matrix.mul_transvection_apply_of_ne _ _ _ _ hjq, hA i j]
      have hmem : ((i, j) ∈ (p, q) :: l) ↔ (i, j) ∈ l := by
        rw [List.mem_cons]
        constructor
        · rintro (h | h)
          · exact absurd (Prod.ext_iff.1 h).2 hjq
          · exact h
        · exact Or.inr
      simp only [hmem]

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
  Sum.elim (gjStep e (fun p => v (Sum.inl p)))
    (Φ (tmat (gjT e) (gjS e) (gjCtl e (fun p => v (Sum.inl p)))) (fun k => v (Sum.inr k)))

def fd_stepG {D : ℕ} {τ α : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (g : α → (Fin D × Fin D → Bool) → Matrix (Fin D) (Fin D) (ZMod 2))
    (x : α) (v : (Fin D × Fin D) ⊕ τ → Bool) : (Fin D × Fin D) ⊕ τ → Bool :=
  Sum.elim (fun p => v (Sum.inl p))
    (Φ (g x (fun p => v (Sum.inl p))) (fun k => v (Sum.inr k)))

theorem fd_fold1 {D : ℕ} {τ : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (hmul : ∀ A B T, Φ (A * B) T = Φ B (Φ A T)) :
    ∀ (L : List (Bool × Fin D × Fin D)), (∀ e ∈ L, e.2.1 ≠ e.2.2) →
    ∀ v : (Fin D × Fin D) ⊕ τ → Bool,
      (fun p => (L.foldl (fun acc e => fd_step Φ e acc) v) (Sum.inl p)) =
        L.foldl (fun M e => gjStep e M) (fun p => v (Sum.inl p)) ∧
      Φ (mat (fun p => v (Sum.inl p))) (fun k => v (Sum.inr k)) =
        Φ (mat (fun p => (L.foldl (fun acc e => fd_step Φ e acc) v) (Sum.inl p)))
          (fun k => (L.foldl (fun acc e => fd_step Φ e acc) v) (Sum.inr k)) := by
  intro L
  induction L with
  | nil => intro _ v; exact ⟨rfl, rfl⟩
  | cons e L ih =>
    intro hL v
    have he := hL e (List.mem_cons_self)
    obtain ⟨h1, h2⟩ := ih (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) (fd_step Φ e v)
    refine ⟨h1, ?_⟩
    rw [List.foldl_cons, ← h2]
    rw [gjStep_mat e he (fun p => v (Sum.inl p)), hmul]
    rfl

theorem fd_foldG {D : ℕ} {τ α : Type}
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool))
    (h1 : ∀ T, Φ 1 T = T) (hmul : ∀ A B T, Φ (A * B) T = Φ B (Φ A T))
    (g : α → (Fin D × Fin D → Bool) → Matrix (Fin D) (Fin D) (ZMod 2)) :
    ∀ (L : List α) (v : (Fin D × Fin D) ⊕ τ → Bool),
      (fun p => (L.foldl (fun acc x => fd_stepG Φ g x acc) v) (Sum.inl p)) =
        (fun p => v (Sum.inl p)) ∧
      (fun k => (L.foldl (fun acc x => fd_stepG Φ g x acc) v) (Sum.inr k)) =
        Φ ((L.map (fun x => g x (fun p => v (Sum.inl p)))).prod) (fun k => v (Sum.inr k)) := by
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
    Cb ((Fin D × Fin D) ⊕ τ) 6 (fun v => gjCtl e (fun p => v (Sum.inl p))) := by
  rcases e with ⟨k, p, i⟩
  cases k
  · have h := Cb.and (Cb.and (Cb.or (Cb.const (ι := (Fin D × Fin D) ⊕ τ) (decide (p < i)))
        (Cb.not (Cb.var (Sum.inl (i, i))))) (Cb.var (Sum.inl (i, p))))
        (Cb.not (Cb.var (Sum.inl (p, p))))
    refine Cb.mono (Cb.congr h ?_) (by norm_num)
    intro v
    simp [gjCtl]
  · have h := Cb.and (Cb.var (ι := (Fin D × Fin D) ⊕ τ) (Sum.inl (i, p)))
        (Cb.var (Sum.inl (p, p)))
    refine Cb.mono (Cb.congr h ?_) (by norm_num)
    intro v
    simp [gjCtl]

theorem fd_bit {D : ℕ} {τ : Type} (e : Bool × Fin D × Fin D) (p : Fin D × Fin D) :
    Cb ((Fin D × Fin D) ⊕ τ) 11 (fun v => gjStep e (fun p => v (Sum.inl p)) p) := by
  by_cases h : p.1 = gjT e
  · have hh := Cb.xor (Cb.var (ι := (Fin D × Fin D) ⊕ τ) (Sum.inl p))
        (Cb.and (fd_ctl (τ := τ) e) (Cb.var (Sum.inl (gjS e, p.2))))
    refine Cb.mono (Cb.congr hh ?_) (by norm_num)
    intro v
    simp [gjStep, rowAdd, h]
  · refine Cb.mono (Cb.congr (Cb.var (Sum.inl p)) ?_) (by norm_num)
    intro v
    simp [gjStep, rowAdd, h]

theorem fd_TS_ne {D : ℕ} (e : Bool × Fin D × Fin D) (he : e.2.1 ≠ e.2.2) : gjT e ≠ gjS e := by
  rcases e with ⟨k, p, i⟩
  cases k
  · simpa [gjT, gjS] using he
  · simpa [gjT, gjS] using (Ne.symm he)

theorem fd_cost_le (D sE sZ : ℕ) :
    Fintype.card (Fin D × Fin D) * 11 + (6 + 0 + sE) ≤ sE + sZ + 16 * (D + 1) ^ 2 := by
  have h : Fintype.card (Fin D × Fin D) = D * D := by simp
  rw [h]
  nlinarith [Nat.zero_le D, Nat.zero_le sZ]

theorem fd_cmp_step {D : ℕ} {τ : Type} [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool)) (sE sZ : ℕ)
    (hE : ∀ t s : Fin D, t ≠ s →
      Cmp (Unit ⊕ τ) τ sE (fun v => Φ (tmat t s (v (Sum.inl ()))) (fun k => v (Sum.inr k))))
    (e : Bool × Fin D × Fin D) (he : e.2.1 ≠ e.2.2) :
    Cmp ((Fin D × Fin D) ⊕ τ) ((Fin D × Fin D) ⊕ τ) (sE + sZ + 16 * (D + 1) ^ 2)
      (fd_step Φ e) := by
  have hm : Cmp ((Fin D × Fin D) ⊕ τ) (Fin D × Fin D) (Fintype.card (Fin D × Fin D) * 11)
      (fun v => gjStep e (fun p => v (Sum.inl p))) :=
    Cmp.ofBits (fun p => fd_bit e p)
  have hc : Cmp ((Fin D × Fin D) ⊕ τ) Unit 6
      (fun v _ => gjCtl e (fun p => v (Sum.inl p))) := fd_ctl e
  have ht := Cmp.comp (Cmp.pair hc (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) Sum.inr))
    (hE (gjT e) (gjS e) (fd_TS_ne e he))
  have h := Cmp.pair hm ht
  refine Cmp.mono (Cmp.congr h ?_) (fd_cost_le D sE sZ)
  intro v k
  rfl

theorem fd_cmp_stepZ {D : ℕ} {τ : Type} [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool)) (sE sZ : ℕ)
    (hZ : ∀ q : Fin D,
      Cmp (Unit ⊕ τ) τ sZ (fun v => Φ (zmat q (v (Sum.inl ()))) (fun k => v (Sum.inr k))))
    (q : Fin D) :
    Cmp ((Fin D × Fin D) ⊕ τ) ((Fin D × Fin D) ⊕ τ) (sE + sZ + 16 * (D + 1) ^ 2)
      (fd_stepG Φ (fun (q : Fin D) M => zmat q (!M (q, q))) q) := by
  have hc : Cmp ((Fin D × Fin D) ⊕ τ) Unit (0 + 1)
      (fun v _ => !v (Sum.inl (q, q))) := Cb.not (Cb.var (Sum.inl (q, q)))
  have ht := Cmp.comp (Cmp.pair hc (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) Sum.inr))
    (hZ q)
  have h := Cmp.pair (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := Fin D × Fin D) Sum.inl) ht
  refine Cmp.mono (Cmp.congr h ?_) (by nlinarith [Nat.zero_le D, Nat.zero_le sE])
  intro v k
  rfl

theorem fd_cmp_stepT {D : ℕ} {τ : Type} [Fintype τ]
    (Φ : Matrix (Fin D) (Fin D) (ZMod 2) → (τ → Bool) → (τ → Bool)) (sE sZ : ℕ)
    (hE : ∀ t s : Fin D, t ≠ s →
      Cmp (Unit ⊕ τ) τ sE (fun v => Φ (tmat t s (v (Sum.inl ()))) (fun k => v (Sum.inr k))))
    (e : Fin D × Fin D) (he : e.1 ≠ e.2) :
    Cmp ((Fin D × Fin D) ⊕ τ) ((Fin D × Fin D) ⊕ τ) (sE + sZ + 16 * (D + 1) ^ 2)
      (fd_stepG Φ (fun (e : Fin D × Fin D) M => tmat e.1 e.2 (M e)) e) := by
  have hc : Cmp ((Fin D × Fin D) ⊕ τ) Unit 0
      (fun v _ => v (Sum.inl e)) := Cb.var (Sum.inl e)
  have ht := Cmp.comp (Cmp.pair hc (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) Sum.inr))
    (hE e.1 e.2 he)
  have h := Cmp.pair (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := Fin D × Fin D) Sum.inl) ht
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
      Cmp (Unit ⊕ τ) τ sE (fun v => Φ (tmat t s (v (Sum.inl ()))) (fun k => v (Sum.inr k))))
    (hZ : ∀ q : Fin D,
      Cmp (Unit ⊕ τ) τ sZ (fun v => Φ (zmat q (v (Sum.inl ()))) (fun k => v (Sum.inr k)))) :
    Cmp ((Fin D × Fin D) ⊕ τ) τ (phiCost D sE sZ)
      (fun v => Φ (mat (fun p => v (Sum.inl p))) (fun k => v (Sum.inr k))) := by
  have c1 := Cmp.foldl (sched D) (fd_step Φ)
    (fun e he => fd_cmp_step Φ sE sZ hE e (sched_ne e he))
  have c2 := Cmp.foldl (List.finRange D)
    (fd_stepG Φ (fun (q : Fin D) M => zmat q (!M (q, q))))
    (fun q _ => fd_cmp_stepZ Φ sE sZ hZ q)
  have c3 := Cmp.foldl (offdiag D)
    (fd_stepG Φ (fun (e : Fin D × Fin D) M => tmat e.1 e.2 (M e)))
    (fun e he => fd_cmp_stepT Φ sE sZ hE e (fd_offdiag_ne e he))
  have c := Cmp.comp (Cmp.comp (Cmp.comp c1 c2) c3)
    (Cmp.wire (ι := (Fin D × Fin D) ⊕ τ) (κ := τ) Sum.inr)
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
    have hg : (sched D).foldl (fun M e => gjStep e M) (fun p => v (Sum.inl p)) =
        gj D (fun p => v (Sum.inl p)) := rfl
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

theorem fp_ext_inj (n : ℕ) {k : ℕ} (hk : k ≤ n) : Function.Injective (fp_ext n (k := k)) := by
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
    apply Finset.sum_eq_zero
    intro b _
    simp [mat, fp_pad, ha]

theorem fp_cardV (n : ℕ) : Fintype.card (V n) = 2 ^ n := by
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

theorem fp_bound (d k W A B Y : ℕ) (hA : A ≤ max d k * max d k)
    (hB : B ≤ 2 ^ (max d k) * W) (hY : Y ≤ 29 * ((W + 1) * 2 ^ (max d k))) :
    A + B + phiCost (max d k) Y 0 ≤ tcost d k W := by
  unfold phiCost tcost
  have hp : 1 ≤ 2 ^ (max d k) := Nat.one_le_two_pow
  have hm : max d k + 1 ≤ d + k + 2 := by omega
  have hC : (max d k + 1) ^ 2 ≤ (d + k + 2) ^ 2 := Nat.pow_le_pow_left hm 2
  have hA' : A ≤ (d + k + 2) ^ 2 := by
    have h0 : max d k * max d k = (max d k) ^ 2 := (sq _).symm
    have : (max d k) ^ 2 ≤ (max d k + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ _) 2
    omega
  have hB' : B ≤ (W + 1) * 2 ^ (max d k) := by
    have : 2 ^ (max d k) * W ≤ (W + 1) * 2 ^ (max d k) := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_right _ (Nat.le_succ _)
    omega
  have hQ : 1 ≤ (d + k + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hX : 1 ≤ (W + 1) * 2 ^ (max d k) := Nat.mul_pos (by omega) hp
  have := fp_arith ((d + k + 2) ^ 2) ((W + 1) * 2 ^ (max d k)) A B ((max d k + 1) ^ 2) Y
    hA' hB' hC hY hQ hX
  have e : 2 ^ 9 * (d + k + 2) ^ 4 * (W + 1) * 2 ^ (max d k) =
      512 * ((d + k + 2) ^ 2 * (d + k + 2) ^ 2) * ((W + 1) * 2 ^ (max d k)) := by ring
  rw [e]
  simpa using this

theorem fp_sum_eq {n W : ℕ} (f : V n → BitVec W) (z : V n) :
    (∑ x : V n, if x = z then f x else 0) = f z := by
  rw [Finset.sum_ite_eq' Finset.univ z f]
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
      (fun v => tab (fun k => v (Sum.inr k)) ((A (v (Sum.inl ()))).mulVec x)) := by
  have h := Cw.mux (Cb.var (Sum.inl () : Unit ⊕ (V n × Fin W)))
    (Cw.var (fun i : Fin W => (Sum.inr ((A true).mulVec x, i) : Unit ⊕ (V n × Fin W))))
    (Cw.var (fun i : Fin W => (Sum.inr ((A false).mulVec x, i) : Unit ⊕ (V n × Fin W))))
  refine (h.mono (by omega)).congr ?_
  intro v
  cases hv : v (Sum.inl ()) <;> simp [tab]

theorem fp_pull_step (n W : ℕ) (A : Bool → Matrix (Fin n) (Fin n) (ZMod 2)) :
    Cmp (Unit ⊕ (V n × Fin W)) (V n × Fin W) (Fintype.card (V n) * (4 * W))
      (fun v => fp_pullPhi n W (A (v (Sum.inl ()))) (fun k => v (Sum.inr k))) := by
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
  apply Finset.sum_congr rfl
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

theorem fp_zsum {n W : ℕ} (q : Fin n) (f : V n → BitVec W) (z : V n) :
    (∑ x : V n, if Function.update x q 0 = z then f x else 0) =
      if z q = 0 then f z + f (Function.update z q 1) else 0 := by
  have two : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  split_ifs with hz
  · have hne : z ≠ Function.update z q 1 := by
      intro h
      have := congrFun h q
      rw [Function.update_self, hz] at this
      exact absurd this (by decide)
    have key : ∀ x : V n, (if Function.update x q 0 = z then f x else 0) =
        (if x = z then f x else 0) + (if x = Function.update z q 1 then f x else 0) := by
      intro x
      by_cases h1 : x = z
      · subst h1
        have : Function.update x q 0 = x := by
          rw [← hz]
          exact Function.update_eq_self q x
        rw [if_pos this, if_pos rfl, if_neg hne, add_zero]
      · by_cases h2 : x = Function.update z q 1
        · subst h2
          have : Function.update (Function.update z q 1) q 0 = z := by
            rw [Function.update_idem, ← hz]
            exact Function.update_eq_self q z
          rw [if_pos this, if_neg h1, if_pos rfl, zero_add]
        · have : ¬ Function.update x q 0 = z := by
            intro h
            rcases two (x q) with h0 | h0
            · apply h1
              funext i
              by_cases hi : i = q
              · subst hi
                rw [h0, hz]
              · have := congrFun h i
                rwa [Function.update_of_ne hi] at this
            · apply h2
              funext i
              by_cases hi : i = q
              · subst hi
                rw [h0, Function.update_self]
              · have := congrFun h i
                rw [Function.update_of_ne hi] at this
                rw [Function.update_of_ne hi, this]
          rw [if_neg this, if_neg h1, if_neg h2, add_zero]
    simp only [key]
    rw [Finset.sum_add_distrib, fp_sum_eq, fp_sum_eq]
  · apply Finset.sum_eq_zero
    intro x _
    rw [if_neg]
    intro h
    apply hz
    rw [← h, Function.update_self]

theorem fp_push_z_cw (n W : ℕ) (q : Fin n) (z : V n) :
    Cw (Unit ⊕ (V n × Fin W)) W (25 * (W + 1))
      (fun v => ∑ x : V n, if (zmat q (v (Sum.inl ()))).transpose.mulVec x = z
        then tab (fun k => v (Sum.inr k)) x else 0) := by
  by_cases hz : z q = 0
  · have h := Cw.mux (Cb.var (Sum.inl () : Unit ⊕ (V n × Fin W)))
      (Cw.add
        (Cw.var (fun i : Fin W => (Sum.inr (z, i) : Unit ⊕ (V n × Fin W))))
        (Cw.var (fun i : Fin W =>
          (Sum.inr (Function.update z q 1, i) : Unit ⊕ (V n × Fin W)))))
      (Cw.var (fun i : Fin W => (Sum.inr (z, i) : Unit ⊕ (V n × Fin W))))
    refine (h.mono (by omega)).congr ?_
    intro v
    cases hv : v (Sum.inl ())
    · simp only [fp_zmat_false, Matrix.transpose_one, Matrix.one_mulVec, fp_sum_eq]
      simp [tab]
    · simp only [fp_zmat_true_mulVec, fp_zsum, hz]
      simp [tab]
  · have h := Cw.mux (Cb.var (Sum.inl () : Unit ⊕ (V n × Fin W)))
      (Cw.const (ι := Unit ⊕ (V n × Fin W)) (0 : BitVec W))
      (Cw.var (fun i : Fin W => (Sum.inr (z, i) : Unit ⊕ (V n × Fin W))))
    refine (h.mono (by omega)).congr ?_
    intro v
    cases hv : v (Sum.inl ())
    · simp only [fp_zmat_false, Matrix.transpose_one, Matrix.one_mulVec, fp_sum_eq]
      simp [tab]
    · simp only [fp_zmat_true_mulVec, fp_zsum, hz]
      simp

theorem fp_push_z_step (n W : ℕ) (q : Fin n) :
    Cmp (Unit ⊕ (V n × Fin W)) (V n × Fin W) (Fintype.card (V n) * (25 * (W + 1)))
      (fun v => fp_pushPhi n W (zmat q (v (Sum.inl ()))) (fun k => v (Sum.inr k))) := by
  unfold fp_pushPhi
  exact Cmp.ofWords (fun z => fp_push_z_cw n W q z)

theorem fp_push_t_step (n W : ℕ) (t s : Fin n) (hts : t ≠ s) :
    Cmp (Unit ⊕ (V n × Fin W)) (V n × Fin W) (Fintype.card (V n) * (4 * W))
      (fun v => fp_pushPhi n W (tmat t s (v (Sum.inl ()))) (fun k => v (Sum.inr k))) := by
  have h := fp_pull_step n W (fun c => (tmat t s c).transpose)
  refine h.congr ?_
  intro v k
  rw [fp_push_tmat n W t s hts]

theorem fp_pad_cb (n : ℕ) {d k : ℕ} (τ : Type) (p : Fin n × Fin n) :
    Cb ((Fin d × Fin k) ⊕ τ) 1 (fun v => fp_pad n (fun e => v (Sum.inl e)) p) := by
  by_cases h : p.1.val < d ∧ p.2.val < k
  · refine ((Cb.var (Sum.inl (⟨p.1.val, h.1⟩, ⟨p.2.val, h.2⟩) :
      (Fin d × Fin k) ⊕ τ)).mono (by omega)).congr ?_
    intro v
    simp [fp_pad, h]
  · refine (Cb.const false).congr ?_
    intro v
    simp only [fp_pad, dif_neg h]

theorem cmp_pull (d k W : ℕ) :
    Cmp ((Fin d × Fin k) ⊕ (V d × Fin W)) (V k × Fin W) (tcost d k W)
      (fun v => untab (fun lam : V k =>
        tab (fun p => v (Sum.inr p)) ((mat (fun p => v (Sum.inl p))).mulVec lam))) := by
  have hd : d ≤ max d k := le_max_left d k
  have hk : k ≤ max d k := le_max_right d k
  have pre : Cmp ((Fin d × Fin k) ⊕ (V d × Fin W))
      ((Fin (max d k) × Fin (max d k)) ⊕ (V (max d k) × Fin W)) _ _ :=
    Cmp.pair
      (Cmp.ofBits (s := 1) (F := fun v p => fp_pad (max d k) (fun e => v (Sum.inl e)) p)
        (fun p => fp_pad_cb (max d k) (V d × Fin W) p))
      (Cmp.wire (fun p : V (max d k) × Fin W =>
        (Sum.inr (fp_res d hd p.1, p.2) : (Fin d × Fin k) ⊕ (V d × Fin W))))
  have mid := cmp_phi (max d k) (V (max d k) × Fin W) (fp_pullPhi (max d k) W)
    (fp_pull_one _ _) (fp_pull_mul _ _)
    (Fintype.card (V (max d k)) * (4 * W)) (Fintype.card (V (max d k)) * (4 * W))
    (fun t s _ => fp_pull_step _ _ (fun c => tmat t s c))
    (fun q => fp_pull_step _ _ (fun c => zmat q c))
  have post := Cmp.wire (ι := V (max d k) × Fin W)
    (fun p : V k × Fin W => (fp_ext (max d k) p.1, p.2))
  have tot := (pre.comp mid).comp post
  refine (tot.mono ?_).congr ?_
  · have hb := fp_bound d k W (max d k * max d k) 0
      (Fintype.card (V (max d k)) * (4 * W) + Fintype.card (V (max d k)) * (4 * W))
      le_rfl (Nat.zero_le _) (by rw [fp_cardV]; nlinarith [Nat.one_le_two_pow (n := max d k)])
    have e : phiCost (max d k) (Fintype.card (V (max d k)) * (4 * W))
        (Fintype.card (V (max d k)) * (4 * W)) =
        phiCost (max d k) (Fintype.card (V (max d k)) * (4 * W) +
          Fintype.card (V (max d k)) * (4 * W)) 0 := by
      unfold phiCost
      ring
    rw [e]
    simp only [Fintype.card_prod, Fintype.card_fin]
    omega
  · intro v p
    obtain ⟨lam, i⟩ := p
    have e : fp_res d hd ((mat (fp_pad (max d k) (fun e => v (Sum.inl e)))).mulVec
        (fp_ext (max d k) lam)) = (mat (fun p => v (Sum.inl p))).mulVec lam := by
      rw [fp_pad_mulVec hk, fp_res_ext]
    show (bv (fun i => v (Sum.inr (fp_res d hd
      ((mat (fp_pad (max d k) (fun e => v (Sum.inl e)))).mulVec (fp_ext (max d k) lam)), i)))).getLsbD
        i.val = _
    rw [e]
    rfl

theorem fp_bv_false (W : ℕ) : bv (fun _ : Fin W => false) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bv, BitVec.getLsbD_ofFnLE]
  simp

theorem cmp_push (d k W : ℕ) :
    Cmp ((Fin d × Fin k) ⊕ (V k × Fin W)) (V d × Fin W) (tcost d k W)
      (fun v => untab (fun z : V d =>
        ∑ lam : V k, if (mat (fun p => v (Sum.inl p))).mulVec lam = z
          then tab (fun p => v (Sum.inr p)) lam else 0)) := by
  have hd : d ≤ max d k := le_max_left d k
  have hk : k ≤ max d k := le_max_right d k
  have tb : ∀ p : V (max d k) × Fin W, Cb ((Fin d × Fin k) ⊕ (V k × Fin W)) 1
      (fun v => if (∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0)
        then v (Sum.inr (fp_res k hk p.1, p.2)) else false) := by
    intro p
    by_cases h : ∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0
    · refine ((Cb.var (Sum.inr (fp_res k hk p.1, p.2) :
        (Fin d × Fin k) ⊕ (V k × Fin W))).mono (by omega)).congr ?_
      intro v
      rw [if_pos h]
    · refine (Cb.const false).congr ?_
      intro v
      rw [if_neg h]
  have pre : Cmp ((Fin d × Fin k) ⊕ (V k × Fin W))
      ((Fin (max d k) × Fin (max d k)) ⊕ (V (max d k) × Fin W)) _ _ :=
    Cmp.pair
      (Cmp.ofBits (s := 1)
        (F := fun v p => fp_pad (max d k) (fun e => v (Sum.inl e)) (p.2, p.1))
        (fun p => fp_pad_cb (max d k) (V k × Fin W) (p.2, p.1)))
      (Cmp.ofBits (s := 1)
        (F := fun v (p : V (max d k) × Fin W) =>
          if (∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0)
            then v (Sum.inr (fp_res k hk p.1, p.2)) else false) tb)
  have mid := cmp_phi (max d k) (V (max d k) × Fin W) (fp_pushPhi (max d k) W)
    (fp_push_one _ _) (fp_push_mul _ _)
    (Fintype.card (V (max d k)) * (4 * W)) (Fintype.card (V (max d k)) * (25 * (W + 1)))
    (fun t s hts => fp_push_t_step _ _ t s hts)
    (fun q => fp_push_z_step _ _ q)
  have post := Cmp.wire (ι := V (max d k) × Fin W)
    (fun p : V d × Fin W => (fp_ext (max d k) p.1, p.2))
  have tot := (pre.comp mid).comp post
  refine (tot.mono ?_).congr ?_
  · have hb := fp_bound d k W (max d k * max d k) (2 ^ (max d k) * W)
      (Fintype.card (V (max d k)) * (4 * W) + Fintype.card (V (max d k)) * (25 * (W + 1)))
      le_rfl le_rfl (by rw [fp_cardV]; nlinarith [Nat.one_le_two_pow (n := max d k)])
    have e : phiCost (max d k) (Fintype.card (V (max d k)) * (4 * W))
        (Fintype.card (V (max d k)) * (25 * (W + 1))) =
        phiCost (max d k) (Fintype.card (V (max d k)) * (4 * W) +
          Fintype.card (V (max d k)) * (25 * (W + 1))) 0 := by
      unfold phiCost
      ring
    rw [e]
    simp only [Fintype.card_prod, Fintype.card_fin, fp_cardV] at hb ⊢
    omega
  · intro v p
    obtain ⟨z, i⟩ := p
    show (∑ x : V (max d k),
      if (mat (fun p : Fin (max d k) × Fin (max d k) =>
          fp_pad (max d k) (fun e => v (Sum.inl e)) (p.2, p.1))).transpose.mulVec x =
          fp_ext (max d k) z
        then tab (fun p : V (max d k) × Fin W =>
          if (∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0)
            then v (Sum.inr (fp_res k hk p.1, p.2)) else false) x else 0).getLsbD i.val =
      (∑ lam : V k, if (mat (fun p => v (Sum.inl p))).mulVec lam = z
          then tab (fun p => v (Sum.inr p)) lam else 0).getLsbD i.val
    congr 1
    symm
    have hT : (mat (fun p : Fin (max d k) × Fin (max d k) =>
          fp_pad (max d k) (fun e => v (Sum.inl e)) (p.2, p.1))).transpose =
        mat (fp_pad (max d k) (fun e => v (Sum.inl e))) := rfl
    rw [hT]
    apply Fintype.sum_of_injective (fp_ext (max d k)) (fp_ext_inj _ hk)
    · intro x hx
      have hs : ¬ ∀ j : Fin (max d k), k ≤ j.val → x j = 0 := by
        intro h
        apply hx
        refine ⟨fp_res k hk x, ?_⟩
        funext j
        by_cases hj : j.val < k
        · simp [fp_ext, fp_res, hj]
        · simp [fp_ext, hj, h j (by omega)]
      have : tab (fun p : V (max d k) × Fin W =>
          if (∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0)
            then v (Sum.inr (fp_res k hk p.1, p.2)) else false) x = 0 := by
        unfold tab
        simp only [if_neg hs]
        exact fp_bv_false W
      rw [this]
      simp
    · intro lam
      have hs : ∀ j : Fin (max d k), k ≤ j.val → fp_ext (max d k) lam j = 0 := by
        intro j hj
        simp [fp_ext, Nat.not_lt.mpr hj]
      have e1 : tab (fun p : V (max d k) × Fin W =>
          if (∀ j : Fin (max d k), k ≤ j.val → p.1 j = 0)
            then v (Sum.inr (fp_res k hk p.1, p.2)) else false) (fp_ext (max d k) lam) =
          tab (fun p => v (Sum.inr p)) lam := by
        unfold tab
        simp only [if_pos hs, fp_res_ext]
      rw [e1, fp_pad_mulVec hk]
      by_cases h : (mat (fun p => v (Sum.inl p))).mulVec lam = z
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun h' => h (fp_ext_inj _ hd h'))]

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
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
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
      simp only [Finset.prod_const_one, Finset.mem_univ, forall_true_left]
      congr 1
      exact propext funext_iff.symm
    simp only [this, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    simp
  | append_singleton L e ih =>
    intro xi
    have hn := List.nodup_append.1 hL
    have he : e ∉ L := fun h => hn.2.2 e h e (by simp) rfl
    rw [List.foldl_append]
    change List.foldl (fun T e => fe_layer e T) T L (Function.update xi e 0) +
      sgn (xi e) * List.foldl (fun T e => fe_layer e T) T L (Function.update xi e 1) = _
    rw [ih hn.1, ih hn.1, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
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
  have hc : Fintype.card (V d) = 2 ^ d := by simp [V]
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
    apply Finset.sum_congr rfl
    intro x _
    rw [fe_k_full]

theorem fg_z2 (u : ZMod 2) : u = 0 ∨ u = 1 := by
  revert u; decide

theorem fg_sgn_add {W : ℕ} (u v : ZMod 2) : (sgn (u + v) : BitVec W) = sgn u * sgn v := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases fg_z2 u with rfl | rfl <;> rcases fg_z2 v with rfl | rfl <;> simp [sgn, h11]

theorem fg_sgn_sum {W : ℕ} {ι : Type} (s : Finset ι) (u : ι → ZMod 2) :
    (sgn (∑ i ∈ s, u i) : BitVec W) = ∏ i ∈ s, sgn (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, fg_sgn_add, ih]

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

theorem fg_split {R : Type} [AddCommMonoid R] (K : ℕ) (h : V (K + 1) → R) :
    (∑ lam : V (K + 1), h lam) =
      (∑ mu : V K, h (@Fin.snoc K (fun _ => ZMod 2) mu 0)) +
      (∑ mu : V K, h (@Fin.snoc K (fun _ => ZMod 2) mu 1)) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (K + 1) => ZMod 2)).sum_comp, Fintype.sum_prod_type]
  have h2 : ∀ F : ZMod 2 → R, ∑ x, F x = F 0 + F 1 := fun F => Fin.sum_univ_two F
  rw [h2]
  rfl

theorem fg_dot {a K : ℕ} (L : Matrix (Fin a) (Fin (K + 1)) (ZMod 2)) (mu : V K) (x : V a) :
    (L.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0)) ⬝ᵥ x =
      ∑ s : Fin K, mu s * ∑ j, L j s.castSucc * x j := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    mul_zero, add_zero, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem vecEquiv_exists (a : ℕ) :
    ∃ e : Fin (2 ^ a) ≃ V a, ∀ ix j, e ix j = if ix.val.testBit j.val then 1 else 0 := by
  let e0 : Fin (2 ^ a) → V a := fun ix j => if ix.val.testBit j.val then 1 else 0
  have hinj : Function.Injective e0 := by
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

theorem fourier_id (K a b c W : ℕ) (f : V a → BitVec W) (g : V b → BitVec W)
    (Lx : Matrix (Fin a) (Fin (K + 1)) (ZMod 2)) (Ly : Matrix (Fin b) (Fin (K + 1)) (ZMod 2))
    (Lz : Matrix (Fin c) (Fin (K + 1)) (ZMod 2)) (σ : Fin K → ZMod 2) (z : V c) :
    (∑ ζ : V c, sgn (ζ ⬝ᵥ z) * ∑ lam : V (K + 1), if Lz.mulVec lam = ζ then
        (if lam (Fin.last K) ≠ 0 then 0 else
          (if (∑ s : Fin K, lam s.castSucc * σ s) ≠ 0 then
            -((∑ x, sgn (Lx.mulVec lam ⬝ᵥ x) * f x) * (∑ y, sgn (Ly.mulVec lam ⬝ᵥ y) * g y))
          else (∑ x, sgn (Lx.mulVec lam ⬝ᵥ x) * f x) * (∑ y, sgn (Ly.mulVec lam ⬝ᵥ y) * g y)))
        else 0)
      = 2 ^ K * ∑ x, ∑ y,
          if (∀ s : Fin K, (∑ j, Lx j s.castSucc * x j) + (∑ j, Ly j s.castSucc * y j) +
              (∑ j, Lz j s.castSucc * z j) = σ s) then f x * g y else 0 := by
  have h11 : (1 : ZMod 2) ≠ 0 := by decide
  have step1 : ∀ (w : V (K + 1) → BitVec W),
      (∑ ζ : V c, sgn (ζ ⬝ᵥ z) * ∑ lam : V (K + 1), if Lz.mulVec lam = ζ then w lam else 0) =
        ∑ lam : V (K + 1), sgn (Lz.mulVec lam ⬝ᵥ z) * w lam := by
    intro w
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun lam _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [step1, fg_split]
  simp only [Fin.snoc_last, Fin.snoc_castSucc, ne_eq, not_true_eq_false, if_false, h11,
    not_false_eq_true, if_true, mul_zero, Finset.sum_const_zero, add_zero]
  have term : ∀ mu : V K,
      sgn (Lz.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ z) *
        (if (∑ s : Fin K, mu s * σ s) = 0 then
          (∑ x, sgn (Lx.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ x) * f x) *
            (∑ y, sgn (Ly.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ y) * g y)
         else
          -((∑ x, sgn (Lx.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ x) * f x) *
            (∑ y, sgn (Ly.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ y) * g y)))
      = ∑ x, ∑ y, sgn (∑ s : Fin K, mu s * ((∑ j, Lx j s.castSucc * x j) +
          (∑ j, Ly j s.castSucc * y j) + (∑ j, Lz j s.castSucc * z j) + σ s)) * (f x * g y) := by
    intro mu
    have hs : ∀ x y, (sgn (∑ s : Fin K, mu s * ((∑ j, Lx j s.castSucc * x j) +
          (∑ j, Ly j s.castSucc * y j) + (∑ j, Lz j s.castSucc * z j) + σ s)) : BitVec W) =
        sgn (Lz.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ z) * sgn (∑ s : Fin K, mu s * σ s) *
          sgn (Lx.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ x) *
          sgn (Ly.mulVec (@Fin.snoc K (fun _ => ZMod 2) mu 0) ⬝ᵥ y) := by
      intro x y
      rw [fg_dot, fg_dot, fg_dot, ← fg_sgn_add, ← fg_sgn_add, ← fg_sgn_add]
      congr 1
      simp only [mul_add, Finset.sum_add_distrib]
      ring
    have hif : ∀ t : BitVec W, (if (∑ s : Fin K, mu s * σ s) = 0 then t else -t) =
        sgn (∑ s : Fin K, mu s * σ s) * t := by
      intro t
      unfold sgn
      split_ifs <;> simp
    rw [hif, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hs]
    ring
  simp only [ite_not]
  rw [Finset.sum_congr rfl (fun mu _ => term mu)]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_mul, fg_char]
  have hiff : ((fun s : Fin K => (∑ j, Lx j s.castSucc * x j) + (∑ j, Ly j s.castSucc * y j) +
      (∑ j, Lz j s.castSucc * z j) + σ s) = 0) ↔
      (∀ s : Fin K, (∑ j, Lx j s.castSucc * x j) + (∑ j, Ly j s.castSucc * y j) +
        (∑ j, Lz j s.castSucc * z j) = σ s) := by
    constructor
    · intro h s
      have := congrFun h s
      exact CharTwo.add_eq_zero.mp this
    · intro h
      funext s
      exact CharTwo.add_eq_zero.mpr (h s)
  by_cases hc : (∀ s : Fin K, (∑ j, Lx j s.castSucc * x j) + (∑ j, Ly j s.castSucc * y j) +
        (∑ j, Lz j s.castSucc * z j) = σ s)
  · rw [if_pos (hiff.mpr hc), if_pos hc]
  · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc]
    simp

theorem kernel_id (K a b c W : ℕ) (f : V a → BitVec W) (g : V b → BitVec W)
    (Lx : Matrix (Fin a) (Fin (K + 1)) (ZMod 2)) (Ly : Matrix (Fin b) (Fin (K + 1)) (ZMod 2))
    (Lz : Matrix (Fin c) (Fin (K + 1)) (ZMod 2)) (dead : Fin K → Bool)
    (S : V a → V b → V c → Prop) [∀ x y z, Decidable (S x y z)]
    (hsol : ∀ lam : V (K + 1), lam (Fin.last K) = 1 →
      S (Lx.mulVec lam) (Ly.mulVec lam) (Lz.mulVec lam))
    (huniq : ∀ x y z, S x y z → ∃! lam : V (K + 1), lam (Fin.last K) = 1 ∧
      (∀ s : Fin K, dead s = true → lam s.castSucc = 0) ∧
      Lx.mulVec lam = x ∧ Ly.mulVec lam = y ∧ Lz.mulVec lam = z) (z : V c) :
    (∑ lam : V (K + 1), if Lz.mulVec lam = z then
        (if (lam (Fin.last K) = 0 ∨ ∃ s : Fin K, dead s = true ∧ lam s.castSucc ≠ 0) then 0
         else f (Lx.mulVec lam) * g (Ly.mulVec lam)) else 0)
      = ∑ x, ∑ y, if S x y z then f x * g y else 0 := by
  classical
  have hL : (∑ lam : V (K + 1), if Lz.mulVec lam = z then
        (if (lam (Fin.last K) = 0 ∨ ∃ s : Fin K, dead s = true ∧ lam s.castSucc ≠ 0) then 0
         else f (Lx.mulVec lam) * g (Ly.mulVec lam)) else 0) =
      ∑ lam ∈ Finset.univ.filter (fun lam : V (K + 1) => Lz.mulVec lam = z ∧
        lam (Fin.last K) = 1 ∧ ∀ s : Fin K, dead s = true → lam s.castSucc = 0),
        f (Lx.mulVec lam) * g (Ly.mulVec lam) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun lam _ => ?_
    by_cases h1 : Lz.mulVec lam = z
    · by_cases h2 : lam (Fin.last K) = 0
      · have : ¬ lam (Fin.last K) = 1 := by rw [h2]; decide
        simp [h1, h2]
      · have h3 : lam (Fin.last K) = 1 := (fg_z2 _).resolve_left h2
        by_cases h4 : ∃ s : Fin K, dead s = true ∧ lam s.castSucc ≠ 0
        · have : ¬ ∀ s : Fin K, dead s = true → lam s.castSucc = 0 := by
            intro hh
            obtain ⟨s, hs, hne⟩ := h4
            exact hne (hh s hs)
          rw [if_pos h1, if_pos (Or.inr h4), if_neg (fun hh => this hh.2.2)]
        · have : ∀ s : Fin K, dead s = true → lam s.castSucc = 0 := by
            intro s hs
            by_contra hne
            exact h4 ⟨s, hs, hne⟩
          rw [if_pos h1, if_neg (fun hh => hh.elim h2 h4), if_pos ⟨h1, h3, this⟩]
    · rw [if_neg h1, if_neg (fun hh => h1 hh.1)]
  have hR : (∑ x, ∑ y, if S x y z then f x * g y else 0) =
      ∑ p ∈ Finset.univ.filter (fun p : V a × V b => S p.1 p.2 z), f p.1 * g p.2 := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [hL, hR]
  refine Finset.sum_bij (fun lam _ => (Lx.mulVec lam, Ly.mulVec lam)) ?_ ?_ ?_ ?_
  · intro lam hlam
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam ⊢
    have := hsol lam hlam.2.1
    rw [hlam.1] at this
    exact this
  · intro l1 h1 l2 h2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have hS := hsol l1 h1.2.1
    obtain ⟨l0, _, hu⟩ := huniq _ _ _ hS
    have e1 := hu l1 ⟨h1.2.1, h1.2.2, rfl, rfl, rfl⟩
    have e2 := hu l2 ⟨h2.2.1, h2.2.2, (congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm,
      h2.1.trans h1.1.symm⟩
    rw [e1, e2]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨l0, ⟨hl1, hl2, hx, hy, hz⟩, _⟩ := huniq _ _ _ hp
    refine ⟨l0, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hz, hl1, hl2⟩
    · exact Prod.ext hx hy
  · intro lam _
    rfl

def fh_w {m N : ℕ} (v : V N) : V (m + N + 1) := fun j =>
  if h : j.val < N then v ⟨j.val, h⟩ else if j.val = N then 1 else 0

theorem fh_two : (2 : ZMod 2) = 0 := by decide

theorem fh_sum_split {m N : ℕ} (a : Fin N → ZMod 2) (b : ZMod 2) :
    (∑ j : Fin (m + N + 1),
      (if h : j.val < N then a ⟨j.val, h⟩ else if j.val = N then b else 0)) =
      ∑ j, a j + b := by
  have hD : N + 1 + m = m + N + 1 := by omega
  rw [← Equiv.sum_comp (finCongr hD)]
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  have h3 : (∑ x : Fin m, (if h : (finCongr hD (Fin.natAdd (N + 1) x)).val < N then
      a ⟨(finCongr hD (Fin.natAdd (N + 1) x)).val, h⟩
      else if (finCongr hD (Fin.natAdd (N + 1) x)).val = N then b else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    have e : (finCongr hD (Fin.natAdd (N + 1) x)).val = N + 1 + x.val := rfl
    rw [dif_neg (by rw [e]; omega), if_neg (by rw [e]; omega)]
  rw [h3, add_zero]
  congr 1
  · apply Finset.sum_congr rfl
    intro x _
    have e : (finCongr hD (Fin.castAdd m (Fin.castSucc x))).val = x.val := rfl
    rw [dif_pos (by rw [e]; exact x.isLt)]
    exact congrArg a (Fin.ext e)
  · have e : (finCongr hD (Fin.castAdd m (Fin.last N))).val = N := rfl
    rw [dif_neg (by rw [e]; omega), if_pos e]

theorem fh_mulVec_w {m N : ℕ} (X : Matrix (Fin (m + N + 1)) (Fin (m + N + 1)) (ZMod 2))
    (v : V N) (i : Fin (m + N + 1)) :
    X.mulVec (fh_w v) i = ∑ p : Fin N, X i (cl m p) * v p + X i (rc m N) := by
  rw [← fh_sum_split (m := m) (fun p => X i (cl m p) * v p) (X i (rc m N))]
  unfold Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro j _
  unfold fh_w
  split_ifs with h1 h2
  · rfl
  · have : j = rc m N := Fin.ext h2
    rw [this, mul_one]
  · rw [mul_zero]

theorem fh_bit (x : ZMod 2) : (if decide (x ≠ 0) = true then (1 : ZMod 2) else 0) = x := by
  revert x; decide

theorem fh_sys_cl {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (i : Fin (m + N + 1))
    (p : Fin N) :
    mat (sysBits Hf rhs) i (cl m p) = if hi : i.val < m then Hf ⟨i.val, hi⟩ p else 0 := by
  unfold mat sysBits
  by_cases hi : i.val < m
  · have hp : (cl m p).val < N := p.isLt
    simp only [dif_pos hi, dif_pos hp]
    exact fh_bit _
  · simp only [dif_neg hi]
    rfl

theorem fh_sys_rc {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (i : Fin (m + N + 1)) :
    mat (sysBits Hf rhs) i (rc m N) = if hi : i.val < m then rhs ⟨i.val, hi⟩ else 0 := by
  unfold mat sysBits
  by_cases hi : i.val < m
  · have hp : ¬ (rc m N).val < N := by show ¬ N < N; omega
    have hp2 : (rc m N).val = N := rfl
    simp only [dif_pos hi, dif_neg hp, if_pos hp2]
    exact fh_bit _
  · simp only [dif_neg hi]
    rfl

theorem fh_sys_hi {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (i j : Fin (m + N + 1)) (hj : N < j.val) : mat (sysBits Hf rhs) i j = 0 := by
  unfold mat sysBits
  by_cases hi : i.val < m
  · simp only [dif_pos hi, dif_neg (show ¬ j.val < N by omega),
      if_neg (show ¬ j.val = N by omega)]
    rfl
  · simp only [dif_neg hi]
    rfl

theorem fh_sys_iff {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) (v : V N) :
    (∀ i, Hf i ⬝ᵥ v = rhs i) ↔ (mat (sysBits Hf rhs)).mulVec (fh_w v) = 0 := by
  constructor
  · intro h
    funext i
    rw [fh_mulVec_w]
    simp only [fh_sys_cl, fh_sys_rc]
    by_cases hi : i.val < m
    · simp only [dif_pos hi]
      have := h ⟨i.val, hi⟩
      unfold dotProduct at this
      rw [this]
      show rhs ⟨i.val, hi⟩ + rhs ⟨i.val, hi⟩ = 0
      linear_combination rhs ⟨i.val, hi⟩ * fh_two
    · simp only [dif_neg hi, zero_mul, Finset.sum_const_zero, add_zero]
      rfl
  · intro h i
    have := congrFun h ⟨i.val, by omega⟩
    rw [fh_mulVec_w] at this
    simp only [fh_sys_cl, fh_sys_rc, dif_pos i.isLt] at this
    unfold dotProduct
    have e : (∑ x, Hf i x * v x) + rhs i = 0 := this
    linear_combination e - rhs i * fh_two

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
  apply Finset.sum_eq_zero
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
  rw [Finset.sum_congr rfl (fun q _ => hpt q), Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_univ p)]

theorem fh_Rsol {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (hpc : ∀ p, R (p, p) = true → ∀ i, R (i, p) = decide (i = p))
    (hzr : ∀ q, R (q, q) = false → ∀ j, R (q, j) = false)
    (hhi : ∀ i j : Fin (m + N + 1), N < j.val → R (i, j) = false)
    (hcons : R (rc m N, rc m N) = false) (v : V N) :
    (mat R).mulVec (fh_w v) = 0 ↔
      ∀ p : Fin N, pv R p = true → v p = mat R (cl m p) (rc m N) +
        ∑ q, if pv R q = false then mat R (cl m p) (cl m q) * v q else 0 := by
  constructor
  · intro h p hp
    have := congrFun h (cl m p)
    rw [fh_mulVec_w, fh_row_split R hpc p hp] at this
    have e : v p + (∑ q, if pv R q = false then mat R (cl m p) (cl m q) * v q else 0) +
        mat R (cl m p) (rc m N) = 0 := this
    linear_combination e - (mat R (cl m p) (rc m N) +
      ∑ q, if pv R q = false then mat R (cl m p) (cl m q) * v q else 0) * fh_two
  · intro h
    funext i
    rw [fh_mulVec_w]
    by_cases hi : R (i, i) = true
    · have h1 : ¬ N < i.val := by
        intro hlt
        have := hhi i i hlt
        rw [hi] at this
        exact Bool.noConfusion this
      have h2 : i.val ≠ N := by
        intro he
        have : i = rc m N := Fin.ext he
        rw [this, hcons] at hi
        exact Bool.noConfusion hi
      have h3 : i.val < N := by omega
      have h4 : i = cl m (⟨i.val, h3⟩ : Fin N) := Fin.ext rfl
      have hp : pv R (⟨i.val, h3⟩ : Fin N) = true := by
        show R (cl m ⟨i.val, h3⟩, cl m ⟨i.val, h3⟩) = true
        rw [← h4]; exact hi
      rw [h4, fh_row_split R hpc _ hp, h _ hp]
      show _ = (0 : ZMod 2)
      linear_combination (mat R (cl m (⟨i.val, h3⟩ : Fin N)) (rc m N) +
        ∑ q, if pv R q = false then mat R (cl m (⟨i.val, h3⟩ : Fin N)) (cl m q) * v q else 0) *
          fh_two
    · have hz := hzr i (by simpa using hi)
      rw [fh_mat_false R _ _ (hz _)]
      rw [Finset.sum_eq_zero (fun q _ => by rw [fh_mat_false R _ _ (hz _), zero_mul]), add_zero]
      rfl

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
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h1, h2⟩
    exact ⟨h1.trans h, h2⟩

theorem fh_cnt_lt_total {N : ℕ} (P : Fin N → Prop) [DecidablePred P] (p : Fin N) (hp : P p) :
    (Finset.univ.filter (fun q : Fin N => q < p ∧ P q)).card <
      (Finset.univ.filter (fun q : Fin N => P q)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨p, by simp [hp], by simp⟩
  · intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨h1, h2⟩
    exact h2

theorem fh_cnt_inj {N : ℕ} (P : Fin N → Prop) [DecidablePred P] (p p' : Fin N)
    (hp : P p) (hp' : P p')
    (h : (Finset.univ.filter (fun q : Fin N => q < p ∧ P q)).card =
      (Finset.univ.filter (fun q : Fin N => q < p' ∧ P q)).card) : p = p' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have := fh_cnt_lt P p p' h1 hp; omega
  · have := fh_cnt_lt P p' p h1 hp'; omega

theorem fh_cntP_inj {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p p' : Fin N)
    (hp : pv R p = true) (hp' : pv R p' = true) (h : cntP R p = cntP R p') : p = p' :=
  fh_cnt_inj (fun q => pv R q = true) p p' hp hp' h

theorem fh_cntN_inj {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p p' : Fin N)
    (hp : pv R p = false) (hp' : pv R p' = false) (h : cntN R p = cntN R p') : p = p' :=
  fh_cnt_inj (fun q => pv R q = false) p p' hp hp' h

theorem fh_cntP_lt {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N)
    (hp : pv R p = true) : cntP R p < rkOf R :=
  fh_cnt_lt_total (fun q => pv R q = true) p hp

theorem fh_cntN_lt {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N)
    (hp : pv R p = false) : cntN R p < N - rkOf R := by
  have h1 := fh_cnt_lt_total (fun q => pv R q = false) p hp
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun q : Fin N => pv R q = true)
  have h3 : (Finset.univ.filter (fun q : Fin N => ¬ pv R q = true)) =
      (Finset.univ.filter (fun q : Fin N => pv R q = false)) := by
    apply Finset.filter_congr
    intro q _
    simp
  rw [h3, Finset.card_univ, Fintype.card_fin] at h2
  unfold cntN rkOf
  omega

theorem fh_rowSlot_eq {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (p : Fin N) (hp : pv R p = true) (s : Fin K) (hs : cntP R p = s.val)
    (j : Fin (m + N + 1)) : rowSlot K R s j = R (cl m p, j) := by
  unfold rowSlot
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨p', hp', hc, hr⟩
    have := fh_cntP_inj R p' p hp' hp (hc.trans hs.symm)
    subst this
    exact hr
  · intro hr
    exact ⟨p, hp, hs, hr⟩

theorem fh_rowSlot_none {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (s : Fin K) (hs : ¬ ∃ p : Fin N, pv R p = true ∧ cntP R p = s.val)
    (j : Fin (m + N + 1)) : rowSlot K R s j = false := by
  unfold rowSlot
  rw [decide_eq_false_iff_not]
  rintro ⟨p, h1, h2, _⟩
  exact hs ⟨p, h1, h2⟩

theorem la_rank {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range Hf)) =
      rkOf (gj _ (sysBits Hf rhs)) := by
  obtain ⟨U, U', h1, h2⟩ := gj_equiv (sysBits Hf rhs)
  have hb : ∃ b : {p : Fin N // pv (gj _ (sysBits Hf rhs)) p = true} → V N,
      b = fun p q => mat (gj _ (sysBits Hf rhs)) (cl m p.1) (cl m q) := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ := hb
  have hrho : ∀ k : Fin (m + N + 1),
      (fun q : Fin N => mat (gj _ (sysBits Hf rhs)) k (cl m q)) ∈
        Submodule.span (ZMod 2) (Set.range b) := by
    intro k
    by_cases hk : k.val < N ∧ gj _ (sysBits Hf rhs) (k, k) = true
    · apply Submodule.subset_span
      refine ⟨⟨⟨k.val, hk.1⟩, hk.2⟩, ?_⟩
      rw [hbdef]
      rfl
    · have hz : (fun q : Fin N => mat (gj _ (sysBits Hf rhs)) k (cl m q)) = 0 := by
        funext q
        apply fh_mat_false
        by_cases hkk : gj _ (sysBits Hf rhs) (k, k) = true
        · apply gj_upper
          have : ¬ k.val < N := fun h => hk ⟨h, hkk⟩
          show q.val < k.val
          have := q.isLt
          omega
        · exact gj_zerorow _ k (by simpa using hkk) _
      rw [hz]
      exact Submodule.zero_mem _
  have hmu : ∀ k : Fin (m + N + 1),
      (fun q : Fin N => mat (sysBits Hf rhs) k (cl m q)) ∈
        Submodule.span (ZMod 2) (Set.range Hf) := by
    intro k
    by_cases hk : k.val < m
    · apply Submodule.subset_span
      refine ⟨⟨k.val, hk⟩, ?_⟩
      funext q
      rw [fh_sys_cl, dif_pos hk]
    · have hz : (fun q : Fin N => mat (sysBits Hf rhs) k (cl m q)) = 0 := by
        funext q
        rw [fh_sys_cl, dif_neg hk]
        rfl
      rw [hz]
      exact Submodule.zero_mem _
  have hspan : Submodule.span (ZMod 2) (Set.range Hf) =
      Submodule.span (ZMod 2) (Set.range b) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have e : Hf i = ∑ k, U' ⟨i.val, by omega⟩ k •
          (fun q : Fin N => mat (gj _ (sysBits Hf rhs)) k (cl m q)) := by
        funext q
        have := congrFun (congrFun h2 ⟨i.val, by omega⟩) (cl m q)
        rw [fh_sys_cl, dif_pos i.isLt, Matrix.mul_apply] at this
        rw [Finset.sum_apply]
        exact this
      rw [e]
      exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hrho k))
    · apply Submodule.span_le.mpr
      rintro _ ⟨p, rfl⟩
      have e : b p = ∑ k, U (cl m p.1) k •
          (fun q : Fin N => mat (sysBits Hf rhs) k (cl m q)) := by
        funext q
        have := congrFun (congrFun h1 (cl m p.1)) (cl m q)
        rw [Matrix.mul_apply] at this
        rw [Finset.sum_apply, hbdef]
        exact this
      rw [e]
      exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (hmu k))
  have hli : LinearIndependent (ZMod 2) b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have key : ∀ x : {p : Fin N // pv (gj _ (sysBits Hf rhs)) p = true},
        b x i.1 = if x = i then 1 else 0 := by
      intro x
      rw [hbdef]
      show mat (gj _ (sysBits Hf rhs)) (cl m x.1) (cl m i.1) = _
      have hpc := gj_pivcol (sysBits Hf rhs) (cl m i.1) i.2 (cl m x.1)
      by_cases hx : x = i
      · subst hx
        rw [if_pos rfl]
        exact fh_mat_true _ _ _ x.2
      · rw [if_neg hx]
        have hne : cl m x.1 ≠ cl m i.1 := by
          intro h
          apply hx
          apply Subtype.ext
          apply Fin.ext
          have h' : (cl m x.1).val = (cl m i.1).val := congrArg Fin.val h
          exact h'
        rw [decide_eq_false hne] at hpc
        exact fh_mat_false _ _ _ hpc
    have := congrFun hg i.1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, key, Pi.zero_apply] at this
    simp at this
    exact this
  rw [hspan, finrank_span_eq_card hli, Fintype.card_subtype]
  rfl

theorem la_incons {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits Hf rhs) (rc m N, rc m N) = true) (v : V N) :
    ¬ ∀ i, Hf i ⬝ᵥ v = rhs i := by
  rw [fh_sys_iff, fh_R_iff]
  intro h0
  have := congrFun h0 (rc m N)
  rw [fh_mulVec_w, fh_mat_true _ _ _ h] at this
  rw [Finset.sum_eq_zero] at this
  · rw [zero_add] at this
    exact one_ne_zero this
  · intro q _
    have : gj _ (sysBits Hf rhs) (rc m N, cl m q) = false := by
      apply gj_upper
      show q.val < N
      exact q.isLt
    rw [fh_mat_false _ _ _ this, zero_mul]

theorem la_rows {m N : ℕ} (K : ℕ) (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits Hf rhs) (rc m N, rc m N) = false)
    (hr : rkOf (gj _ (sysBits Hf rhs)) ≤ K) (v : V N) :
    (∀ s : Fin K,
      (∑ j : Fin N, (if rowSlot K (gj _ (sysBits Hf rhs)) s (cl m j) then (1 : ZMod 2) else 0) * v j)
        = (if rowSlot K (gj _ (sysBits Hf rhs)) s (rc m N) then 1 else 0)) ↔
      ∀ i, Hf i ⬝ᵥ v = rhs i := by
  rw [fh_main_iff Hf rhs h]
  have hpc : ∀ p, gj _ (sysBits Hf rhs) (p, p) = true →
      ∀ i, gj _ (sysBits Hf rhs) (i, p) = decide (i = p) := fun p hp i => gj_pivcol _ p hp i
  constructor
  · intro hs p hp
    have hlt : cntP (gj _ (sysBits Hf rhs)) p < K := (fh_cntP_lt _ p hp).trans_le hr
    have e := hs ⟨cntP (gj _ (sysBits Hf rhs)) p, hlt⟩
    simp only [fh_rowSlot_eq K _ p hp ⟨_, hlt⟩ rfl] at e
    have e' : ∑ j, mat (gj _ (sysBits Hf rhs)) (cl m p) (cl m j) * v j =
        mat (gj _ (sysBits Hf rhs)) (cl m p) (rc m N) := e
    rw [fh_row_split _ hpc p hp] at e'
    linear_combination e' - (∑ q, if pv (gj _ (sysBits Hf rhs)) q = false then
      mat (gj _ (sysBits Hf rhs)) (cl m p) (cl m q) * v q else 0) * fh_two
  · intro hs s
    by_cases hex : ∃ p : Fin N, pv (gj _ (sysBits Hf rhs)) p = true ∧
        cntP (gj _ (sysBits Hf rhs)) p = s.val
    · obtain ⟨p, hp, hc⟩ := hex
      simp only [fh_rowSlot_eq K _ p hp s hc]
      show ∑ j, mat (gj _ (sysBits Hf rhs)) (cl m p) (cl m j) * v j =
        mat (gj _ (sysBits Hf rhs)) (cl m p) (rc m N)
      rw [fh_row_split _ hpc p hp, hs p hp]
      linear_combination (∑ q, if pv (gj _ (sysBits Hf rhs)) q = false then
        mat (gj _ (sysBits Hf rhs)) (cl m p) (cl m q) * v q else 0) * fh_two
    · simp only [fh_rowSlot_none K _ s hex]
      simp

def fh_E {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (q j : Fin N) : ZMod 2 :=
  (if j = q then 1 else 0) + mat R (cl m j) (cl m q)

def fh_mu {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (lam : V K)
    (q : Fin N) : ZMod 2 :=
  ∑ s : Fin K, if s.val = cntN R q then lam s else 0

theorem fh_xor_val (x y : Bool) :
    (if xor x y = true then (1 : ZMod 2) else 0) =
      (if x = true then 1 else 0) + (if y = true then 1 else 0) := by
  revert x y; decide

theorem fh_kerSlot_val {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (s : Fin K) (j : Fin N) :
    (if kerSlot K R s j = true then (1 : ZMod 2) else 0) =
      ∑ q : Fin N, if (pv R q = false ∧ cntN R q = s.val) then fh_E R q j else 0 := by
  by_cases hex : ∃ q0 : Fin N, pv R q0 = false ∧ cntN R q0 = s.val
  · obtain ⟨q0, h0, hc⟩ := hex
    rw [Finset.sum_eq_single q0]
    · rw [if_pos (show pv R q0 = false ∧ cntN R q0 = s.val from ⟨h0, hc⟩)]
      have : kerSlot K R s j = xor (decide (j = q0)) (R (cl m j, cl m q0)) := by
        unfold kerSlot
        rw [Bool.eq_iff_iff]
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨q, hq, hcq, hx⟩
          have := fh_cntN_inj R q q0 hq h0 (hcq.trans hc.symm)
          subst this
          exact hx
        · intro hx
          exact ⟨q0, h0, hc, hx⟩
      rw [this, fh_xor_val]
      unfold fh_E mat
      simp only [decide_eq_true_eq]
    · intro q _ hq
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hq (fh_cntN_inj R q q0 h1 h0 (h2.trans hc.symm))
    · intro hn
      exact absurd (Finset.mem_univ q0) hn
  · have : kerSlot K R s j = false := by
      unfold kerSlot
      rw [decide_eq_false_iff_not]
      rintro ⟨q, h1, h2, _⟩
      exact hex ⟨q, h1, h2⟩
    rw [this, if_neg (by simp)]
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hex ⟨q, h1, h2⟩

theorem fh_kerPt_eq {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (lam : V K) (j : Fin N) :
    kerPt K R lam j = mat R (cl m j) (rc m N) +
      ∑ q : Fin N, if pv R q = false then fh_mu K R lam q * fh_E R q j else 0 := by
  unfold kerPt
  show mat R (cl m j) (rc m N) + _ = _
  congr 1
  simp only [fh_kerSlot_val, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : pv R q = false
  · rw [if_pos hq]
    unfold fh_mu
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : s.val = cntN R q
    · rw [if_pos ⟨hq, h.symm⟩, if_pos h]
    · rw [if_neg (fun hh => h hh.2.symm), if_neg h, mul_zero, zero_mul]
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro s _
    rw [if_neg (fun hh => hq hh.1), mul_zero]

theorem fh_ker_np {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (hzr : ∀ q, R (q, q) = false → ∀ j, R (q, j) = false)
    (lam : V K) (j : Fin N) (hj : pv R j = false) :
    kerPt K R lam j = fh_mu K R lam j := by
  rw [fh_kerPt_eq, fh_mat_false R _ _ (hzr (cl m j) hj _), zero_add]
  rw [Finset.sum_eq_single j]
  · rw [if_pos hj]
    unfold fh_E
    rw [if_pos rfl, fh_mat_false R _ _ (hzr (cl m j) hj _), add_zero, mul_one]
  · intro q _ hq
    by_cases hv : pv R q = false
    · rw [if_pos hv]
      unfold fh_E
      rw [if_neg (fun h => hq h.symm), fh_mat_false R _ _ (hzr (cl m j) hj _), add_zero, mul_zero]
    · rw [if_neg hv]
  · intro hn
    exact absurd (Finset.mem_univ j) hn

theorem fh_ker_pv {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (lam : V K) (j : Fin N) (hj : pv R j = true) :
    kerPt K R lam j = mat R (cl m j) (rc m N) +
      ∑ q, if pv R q = false then mat R (cl m j) (cl m q) * fh_mu K R lam q else 0 := by
  rw [fh_kerPt_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  by_cases hv : pv R q = false
  · rw [if_pos hv, if_pos hv]
    unfold fh_E
    have hne : ¬ j = q := by
      intro h
      rw [h, hv] at hj
      exact Bool.noConfusion hj
    rw [if_neg hne, zero_add, mul_comm]
  · rw [if_neg hv, if_neg hv]

theorem fh_mu_slot {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (lam : V K) (q : Fin N) (s : Fin K) (hs : cntN R q = s.val) : fh_mu K R lam q = lam s := by
  unfold fh_mu
  rw [Finset.sum_eq_single s]
  · rw [if_pos hs.symm]
  · intro s' _ hne
    rw [if_neg]
    intro h
    apply hne
    apply Fin.ext
    exact h.trans hs
  · intro hn
    exact absurd (Finset.mem_univ s) hn

theorem la_ker_sol {m N : ℕ} (K : ℕ) (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits Hf rhs) (rc m N, rc m N) = false) (lam : V K) :
    ∀ i, Hf i ⬝ᵥ kerPt K (gj _ (sysBits Hf rhs)) lam = rhs i := by
  rw [fh_main_iff Hf rhs h]
  intro p hp
  rw [fh_ker_pv K _ lam p hp]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : pv (gj _ (sysBits Hf rhs)) q = false
  · rw [if_pos hq, if_pos hq, fh_ker_np K _ (fun q hq j => gj_zerorow _ q hq j) lam q hq]
  · rw [if_neg hq, if_neg hq]

theorem la_ker_uniq {m N : ℕ} (K : ℕ) (Hf : Fin m → V N) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits Hf rhs) (rc m N, rc m N) = false)
    (hk : N - rkOf (gj _ (sysBits Hf rhs)) ≤ K) (v : V N) (hv : ∀ i, Hf i ⬝ᵥ v = rhs i) :
    ∃! lam : V K, (∀ s, deadSlot K (gj _ (sysBits Hf rhs)) s = true → lam s = 0) ∧
      kerPt K (gj _ (sysBits Hf rhs)) lam = v := by
  have hzr : ∀ q, gj _ (sysBits Hf rhs) (q, q) = false →
      ∀ j, gj _ (sysBits Hf rhs) (q, j) = false := fun q hq j => gj_zerorow _ q hq j
  have hv' := (fh_main_iff Hf rhs h v).mp hv
  have hl : ∃ lam0 : V K, lam0 = fun s => ∑ q : Fin N,
      if (pv (gj _ (sysBits Hf rhs)) q = false ∧ cntN (gj _ (sysBits Hf rhs)) q = s.val)
        then v q else 0 := ⟨_, rfl⟩
  obtain ⟨lam0, hlam0⟩ := hl
  have hdead : ∀ (lam : V K) (s : Fin K),
      (¬ ∃ q : Fin N, pv (gj _ (sysBits Hf rhs)) q = false ∧
        cntN (gj _ (sysBits Hf rhs)) q = s.val) →
      deadSlot K (gj _ (sysBits Hf rhs)) s = true := by
    intro lam s hs
    unfold deadSlot
    rw [decide_eq_true_eq]
    exact hs
  have hmask0 : ∀ s, deadSlot K (gj _ (sysBits Hf rhs)) s = true → lam0 s = 0 := by
    intro s hs
    unfold deadSlot at hs
    rw [decide_eq_true_eq] at hs
    rw [hlam0]
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hs ⟨q, h1, h2⟩
  have hmu0 : ∀ q : Fin N, pv (gj _ (sysBits Hf rhs)) q = false →
      fh_mu K (gj _ (sysBits Hf rhs)) lam0 q = v q := by
    intro q hq
    have hlt : cntN (gj _ (sysBits Hf rhs)) q < K := (fh_cntN_lt _ q hq).trans_le hk
    rw [fh_mu_slot K _ lam0 q ⟨_, hlt⟩ rfl, hlam0]
    show (∑ q' : Fin N, if (pv (gj _ (sysBits Hf rhs)) q' = false ∧
      cntN (gj _ (sysBits Hf rhs)) q' = cntN (gj _ (sysBits Hf rhs)) q) then v q' else 0) = v q
    rw [Finset.sum_eq_single q]
    · rw [if_pos ⟨hq, rfl⟩]
    · intro q' _ hne
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hne (fh_cntN_inj _ q' q h1 hq h2)
    · intro hn
      exact absurd (Finset.mem_univ q) hn
  have hpt0 : kerPt K (gj _ (sysBits Hf rhs)) lam0 = v := by
    funext j
    by_cases hj : pv (gj _ (sysBits Hf rhs)) j = true
    · rw [fh_ker_pv K _ lam0 j hj, hv' j hj]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : pv (gj _ (sysBits Hf rhs)) q = false
      · rw [if_pos hq, if_pos hq, hmu0 q hq]
      · rw [if_neg hq, if_neg hq]
    · have hj' : pv (gj _ (sysBits Hf rhs)) j = false := by simpa using hj
      rw [fh_ker_np K _ hzr lam0 j hj', hmu0 j hj']
  refine ⟨lam0, ⟨hmask0, hpt0⟩, ?_⟩
  rintro lam ⟨hm, hp⟩
  funext s
  by_cases hex : ∃ q : Fin N, pv (gj _ (sysBits Hf rhs)) q = false ∧
      cntN (gj _ (sysBits Hf rhs)) q = s.val
  · obtain ⟨q, hq, hc⟩ := hex
    rw [← fh_mu_slot K _ lam q s hc, ← fh_mu_slot K _ lam0 q s hc, hmu0 q hq,
      ← fh_ker_np K _ hzr lam q hq, hp]
  · rw [hm s (hdead lam s hex), hmask0 s (hdead lam s hex)]

theorem ft_sum3 {a b c : ℕ} (F : Fin (a + b + c) → ZMod 2) :
    ∑ j : Fin (a + b + c), F j =
      ∑ j : Fin a, F (nx j) + ∑ j : Fin b, F (ny j) + ∑ j : Fin c, F (nz j) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  rfl

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

theorem ft_ext {a b c : ℕ} (u w : V (a + b + c))
    (hx : ∀ j : Fin a, u (nx j) = w (nx j)) (hy : ∀ j : Fin b, u (ny j) = w (ny j))
    (hz : ∀ j : Fin c, u (nz j) = w (nz j)) : u = w := by
  funext j
  by_cases h1 : j.val < a
  · have := hx ⟨j.val, h1⟩
    have e : (nx ⟨j.val, h1⟩ : Fin (a + b + c)) = j := Fin.ext rfl
    rwa [e] at this
  · by_cases h2 : j.val < a + b
    · have := hy ⟨j.val - a, by omega⟩
      have e : (ny ⟨j.val - a, by omega⟩ : Fin (a + b + c)) = j := Fin.ext (by simp [ny]; omega)
      rwa [e] at this
    · have := hz ⟨j.val - (a + b), by omega⟩
      have e : (nz ⟨j.val - (a + b), by omega⟩ : Fin (a + b + c)) = j :=
        Fin.ext (by simp [nz]; omega)
      rwa [e] at this

theorem ft_dot {a b c : ℕ} (h : V a × V b × V c) (x : V a) (y : V b) (z : V c) :
    join3 h ⬝ᵥ join3 (x, y, z) = h.1 ⬝ᵥ x + h.2.1 ⬝ᵥ y + h.2.2 ⬝ᵥ z := by
  unfold dotProduct
  rw [ft_sum3]
  simp only [ft_join_nx, ft_join_ny, ft_join_nz]

theorem ft_eqn {a b c m : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (x : V a) (y : V b) (z : V c) :
    (∀ i, (fun i => join3 (H i)) i ⬝ᵥ join3 (x, y, z) = rhs i) ↔
      ∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i := by
  constructor
  · intro h i
    rw [← ft_dot]
    exact h i
  · intro h i
    show join3 (H i) ⬝ᵥ join3 (x, y, z) = rhs i
    rw [ft_dot]
    exact h i

theorem ft_mulVec {m N d : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (e : Fin d → Fin N) (lam : V (K + 1)) (hl : lam (Fin.last K) = 1) (j : Fin d) :
    (mat (LnBits K R e)).mulVec lam j = kerPt K R (fun s => lam s.castSucc) (e j) := by
  unfold Matrix.mulVec dotProduct kerPt
  rw [Fin.sum_univ_castSucc, add_comm]
  congr 1
  · simp [mat, LnBits, hl]
  · apply Finset.sum_congr rfl
    intro s _
    simp [mat, LnBits, mul_comm]

theorem ft_kerPt {a b c m : ℕ} (K : ℕ)
    (R : Fin (m + (a + b + c) + 1) × Fin (m + (a + b + c) + 1) → Bool)
    (lam : V (K + 1)) (hl : lam (Fin.last K) = 1) :
    kerPt K R (fun s => lam s.castSucc) =
      join3 ((mat (LnBits K R (nx (b := b) (c := c)))).mulVec lam,
        (mat (LnBits K R (ny (a := a) (c := c)))).mulVec lam,
        (mat (LnBits K R (nz (a := a) (b := b)))).mulVec lam) := by
  apply ft_ext
  · intro j; rw [ft_join_nx]; exact (ft_mulVec K R _ lam hl j).symm
  · intro j; rw [ft_join_ny]; exact (ft_mulVec K R _ lam hl j).symm
  · intro j; rw [ft_join_nz]; exact (ft_mulVec K R _ lam hl j).symm

theorem ft_join_inj {a b c : ℕ} (h h' : V a × V b × V c) (e : join3 h = join3 h') : h = h' := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext j; rw [← ft_join_nx h, ← ft_join_nx h', e]
  · funext j; rw [← ft_join_ny h, ← ft_join_ny h', e]
  · funext j; rw [← ft_join_nz h, ← ft_join_nz h', e]

theorem tr_rank {a b c m : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)) =
      rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) := by
  rw [← la_rank]
  let e : (V a × V b × V c) →ₗ[ZMod 2] V (a + b + c) :=
    { toFun := join3
      map_add' := by
        intro u w
        apply ft_ext
        · intro j; simp [ft_join_nx]
        · intro j; simp [ft_join_ny]
        · intro j; simp [ft_join_nz]
      map_smul' := by
        intro r u
        apply ft_ext
        · intro j; simp [ft_join_nx]
        · intro j; simp [ft_join_ny]
        · intro j; simp [ft_join_nz] }
  have hinj : Function.Injective e := fun h h' he => ft_join_inj h h' he
  have hr : Set.range (fun i => join3 (H i)) = e '' Set.range H := by
    rw [← Set.range_comp]; rfl
  rw [hr, ← Submodule.map_span]
  exact (Submodule.equivMapOfInjective e hinj _).finrank_eq

theorem tr_incons {a b c m : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = true)
    (x : V a) (y : V b) (z : V c) :
    ¬ ∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i := by
  intro hh
  exact la_incons _ rhs h (join3 (x, y, z)) ((ft_eqn H rhs x y z).2 hh)

theorem ft_lr {m N d : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool)
    (e : Fin d → Fin N) (j : Fin d) (s : Fin K) :
    mat (LrBits K R e) j s.castSucc = if rowSlot K R s (cl m (e j)) then 1 else 0 := by
  simp [mat, LrBits]

theorem tr_rows {a b c m : ℕ} (K : ℕ) (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = false)
    (hr : rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ K)
    (x : V a) (y : V b) (z : V c) :
    (∀ s : Fin K,
      (∑ j, mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c))) j s.castSucc * x j) +
      (∑ j, mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c))) j s.castSucc * y j) +
      (∑ j, mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b))) j s.castSucc * z j)
        = (if rowSlot K (gj _ (sysBits (fun i => join3 (H i)) rhs)) s (rc m (a + b + c)) then 1 else 0)) ↔
      ∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i := by
  rw [← ft_eqn H rhs x y z, ← la_rows K _ rhs h hr (join3 (x, y, z))]
  apply forall_congr'
  intro s
  rw [ft_sum3]
  simp only [ft_join_nx, ft_join_ny, ft_join_nz, ft_lr]

theorem tr_ker_sol {a b c m : ℕ} (K : ℕ) (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = false)
    (lam : V (K + 1)) (hl : lam (Fin.last K) = 1) :
    ∀ i, (H i).1 ⬝ᵥ ((mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c)))).mulVec lam) +
      (H i).2.1 ⬝ᵥ ((mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c)))).mulVec lam) +
      (H i).2.2 ⬝ᵥ ((mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b)))).mulVec lam)
        = rhs i := by
  have := la_ker_sol K (fun i => join3 (H i)) rhs h (fun s => lam s.castSucc)
  rw [ft_kerPt K _ lam hl] at this
  exact (ft_eqn H rhs _ _ _).1 this

theorem tr_ker_uniq {a b c m : ℕ} (K : ℕ) (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (h : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = false)
    (hk : a + b + c - rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ K)
    (x : V a) (y : V b) (z : V c)
    (hsol : ∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i) :
    ∃! lam : V (K + 1), lam (Fin.last K) = 1 ∧
      (∀ s : Fin K, deadSlot K (gj _ (sysBits (fun i => join3 (H i)) rhs)) s = true →
        lam s.castSucc = 0) ∧
      (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c)))).mulVec lam = x ∧
      (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c)))).mulVec lam = y ∧
      (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b)))).mulVec lam = z := by
  obtain ⟨lam', ⟨hm, hp⟩, hu⟩ := la_ker_uniq K (fun i => join3 (H i)) rhs h hk (join3 (x, y, z))
    ((ft_eqn H rhs x y z).2 hsol)
  refine ⟨Fin.snoc lam' 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp
  · intro s hs
    simpa using hm s hs
  · have hl : (Fin.snoc lam' (1 : ZMod 2) : V (K + 1)) (Fin.last K) = 1 := by simp
    have hc : (fun s : Fin K => (Fin.snoc lam' (1 : ZMod 2) : V (K + 1)) s.castSucc) = lam' := by
      funext s; simp
    have hj := ft_kerPt (a := a) (b := b) (c := c) K
      (gj _ (sysBits (fun i => join3 (H i)) rhs)) (Fin.snoc lam' 1) hl
    rw [hc, hp] at hj
    have := ft_join_inj _ _ hj
    have h1 := congrArg Prod.fst this
    have h2 := congrArg (fun q => q.2.1) this
    have h3 := congrArg (fun q => q.2.2) this
    exact ⟨h1.symm, h2.symm, h3.symm⟩
  · rintro lam2 ⟨hl, hm2, hx, hy, hz⟩
    have hj := ft_kerPt (a := a) (b := b) (c := c) K
      (gj _ (sysBits (fun i => join3 (H i)) rhs)) lam2 hl
    rw [hx, hy, hz] at hj
    have he := hu (fun s => lam2 s.castSucc) ⟨hm2, hj⟩
    funext s
    refine Fin.lastCases ?_ (fun s => ?_) s
    · simp [hl]
    · simp [← he]

theorem fi_bound {i n j L : ℕ} (hi : i < n) (hj : j < L) : i * L + j < n * L := by
  have h1 : (i + 1) * L ≤ n * L := Nat.mul_le_mul_right L hi
  have h2 : (i + 1) * L = i * L + L := by ring
  omega

theorem fi_flat {α β : Type} (d : α) (blk : β → List α) (L : ℕ) :
    ∀ (l : List β), (∀ x ∈ l, (blk x).length = L) →
      (l.flatMap blk).length = l.length * L ∧
      ∀ (i : ℕ) (hi : i < l.length) (j : ℕ), j < L →
        (l.flatMap blk).getD (i * L + j) d = (blk l[i]).getD j d := by
  intro l
  induction l with
  | nil => intro _; refine ⟨by simp, ?_⟩; intro i hi; simp at hi
  | cons x l ih =>
    intro h
    have hx : (blk x).length = L := h x (by simp)
    obtain ⟨ih1, ih2⟩ := ih (fun y hy => h y (by simp [hy]))
    refine ⟨?_, ?_⟩
    · rw [List.flatMap_cons, List.length_append, ih1, hx, List.length_cons]; ring
    · intro i hi j hj
      rw [List.flatMap_cons]
      cases i with
      | zero =>
        simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left (by omega)]
      | succ i =>
        have e : (i + 1) * L + j = (blk x).length + (i * L + j) := by rw [hx]; ring
        rw [List.getD_eq_getElem?_getD, e, List.getElem?_append_right (by omega),
          Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
        simp only [List.getElem_cons_succ]
        exact ih2 i (by simpa using hi) j hj

theorem fi_fin {α : Type} (d : α) (n L : ℕ) (blk : Fin n → List α)
    (h : ∀ i, (blk i).length = L) :
    ((List.finRange n).flatMap blk).length = n * L ∧
    ∀ (i : Fin n) (j : ℕ), j < L →
      ((List.finRange n).flatMap blk).getD (i.val * L + j) d = (blk i).getD j d := by
  obtain ⟨h1, h2⟩ := fi_flat d blk L (List.finRange n) (fun x _ => h x)
  refine ⟨by simpa using h1, ?_⟩
  intro i j hj
  have := h2 i.val (by simp) j hj
  simpa using this

theorem fi_getD_left {α : Type} (d : α) (A B : List α) (k : ℕ) (hk : k < A.length) :
    (A ++ B).getD k d = A.getD k d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem fi_getD_right {α : Type} (d : α) (A B : List α) (n k : ℕ) (hn : A.length = n) :
    (A ++ B).getD (n + k) d = B.getD k d := by
  subst hn
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem fi_block {a b c : ℕ} (h : V a × V b × V c) (r : Bool) (j : ℕ) (hj : j < a + b + c + 1) :
    (List.ofFn (fun j : Fin a => decide (h.1 j ≠ 0)) ++
      List.ofFn (fun j : Fin b => decide (h.2.1 j ≠ 0)) ++
      List.ofFn (fun j : Fin c => decide (h.2.2 j ≠ 0)) ++ [r]).getD j false =
      if hh : j < a + b + c then decide (join3 h ⟨j, hh⟩ ≠ 0) else r := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h1 : j < a
  · have hh : j < a + b + c := by omega
    rw [dif_pos hh, List.append_assoc, List.append_assoc,
      List.getElem?_append_left (by simpa using h1)]
    simp [join3, h1]
  · by_cases h2 : j < a + b
    · have hh : j < a + b + c := by omega
      rw [dif_pos hh, List.append_assoc, List.append_assoc,
        List.getElem?_append_right (by simpa using h1),
        List.getElem?_append_left (by simp; omega)]
      have : j - a < b := by omega
      simp [join3, h1, h2, this]
    · by_cases h3 : j < a + b + c
      · rw [dif_pos h3, List.append_assoc, List.append_assoc,
          List.getElem?_append_right (by simpa using h1),
          List.getElem?_append_right (by simp; omega),
          List.getElem?_append_left (by simp; omega)]
        have e : j - a - b = j - (a + b) := by omega
        have h4 : j - (a + b) < c := by omega
        simp [join3, h1, h2, e, h4]
      · have e : j = a + b + c := by omega
        subst e
        rw [dif_neg h3, List.getElem?_append_right (by simp; omega)]
        have e : a + b + c - (a + (b + c)) = 0 := by omega
        simp [e]

theorem input_layout (a b c m t : ℕ) (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (bits : List Bool)
    (hbits : bits = (List.finRange m).flatMap (fun i =>
        List.ofFn (fun j : Fin a => decide ((H i).1 j ≠ 0)) ++
        List.ofFn (fun j : Fin b => decide ((H i).2.1 j ≠ 0)) ++
        List.ofFn (fun j : Fin c => decide ((H i).2.2 j ≠ 0)) ++ [decide (rhs i ≠ 0)]) ++
        (List.finRange (2 ^ a)).flatMap (fun ix =>
          List.ofFn (fun j : Fin t => (f ix).val.testBit j.val)) ++
        (List.finRange (2 ^ b)).flatMap (fun iy =>
          List.ofFn (fun j : Fin t => (g iy).val.testBit j.val))) :
    bits.length = m * (a + b + c + 1) + (2 ^ a + 2 ^ b) * t ∧
    (∀ (i : Fin m) (j : Fin (a + b + c + 1)),
      bits.getD (i.val * (a + b + c + 1) + j.val) false =
        if h : j.val < a + b + c then decide (join3 (H i) ⟨j.val, h⟩ ≠ 0)
        else decide (rhs i ≠ 0)) ∧
    (∀ (ix : Fin (2 ^ a)) (j : Fin t),
      bits.getD (m * (a + b + c + 1) + ix.val * t + j.val) false = (f ix).val.testBit j.val) ∧
    (∀ (iy : Fin (2 ^ b)) (j : Fin t),
      bits.getD (m * (a + b + c + 1) + 2 ^ a * t + iy.val * t + j.val) false =
        (g iy).val.testBit j.val) := by
  obtain ⟨hA1, hA2⟩ := fi_fin false m (a + b + c + 1) (fun i =>
        List.ofFn (fun j : Fin a => decide ((H i).1 j ≠ 0)) ++
        List.ofFn (fun j : Fin b => decide ((H i).2.1 j ≠ 0)) ++
        List.ofFn (fun j : Fin c => decide ((H i).2.2 j ≠ 0)) ++ [decide (rhs i ≠ 0)])
        (fun i => by simp; omega)
  obtain ⟨hB1, hB2⟩ := fi_fin false (2 ^ a) t (fun ix =>
          List.ofFn (fun j : Fin t => (f ix).val.testBit j.val)) (fun i => by simp)
  obtain ⟨hC1, hC2⟩ := fi_fin false (2 ^ b) t (fun iy =>
          List.ofFn (fun j : Fin t => (g iy).val.testBit j.val)) (fun i => by simp)
  subst hbits
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.length_append, List.length_append, hA1, hB1, hC1]; ring
  · intro i j
    rw [List.append_assoc, fi_getD_left _ _ _ _ (by rw [hA1]; exact fi_bound i.2 j.2),
      hA2 i j.val j.2]
    exact fi_block (H i) _ j.val j.2
  · intro ix j
    rw [List.append_assoc, Nat.add_assoc, fi_getD_right _ _ _ _ _ hA1,
      fi_getD_left _ _ _ _ (by rw [hB1]; exact fi_bound ix.2 j.2), hB2 ix j.val j.2]
    simp [List.getD_eq_getElem?_getD]
  · intro iy j
    have e : m * (a + b + c + 1) + 2 ^ a * t + iy.val * t + j.val =
        (m * (a + b + c + 1) + 2 ^ a * t) + (iy.val * t + j.val) := by ring
    rw [e, fi_getD_right _ _ _ _ _ (by rw [List.length_append, hA1, hB1]), hC2 iy j.val j.2]
    simp [List.getD_eq_getElem?_getD]

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
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
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
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
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
    (if v (Sum.inl ⟨i, hi⟩) = true then
      (if hs : 0 < s.val then v (Sum.inr ⟨s.val - 1, by omega⟩) else false)
     else v (Sum.inr s))
  else v (Sum.inr s)

theorem cntG_cb (N K i : ℕ) (s : Fin (K + 1)) :
    Cb (Fin N ⊕ Fin (K + 1)) 6 (fun v => cntG N K i v s) := by
  by_cases hi : i < N
  · by_cases hs : 0 < s.val
    · refine ((Cb.mux (Cb.var (Sum.inl ⟨i, hi⟩)) (Cb.var (Sum.inr ⟨s.val - 1, by omega⟩))
        (Cb.var (Sum.inr s))).mono (by norm_num)).congr ?_
      intro v; simp [cntG, hi, hs]
    · refine ((Cb.mux (Cb.var (Sum.inl ⟨i, hi⟩)) (Cb.const false)
        (Cb.var (Sum.inr s))).mono (by norm_num)).congr ?_
      intro v; simp [cntG, hi, hs]
  · refine ((Cb.var (Sum.inr s)).mono (by norm_num)).congr ?_
    intro v; simp [cntG, hi]

theorem cmp_counter (N K : ℕ) :
    Cmp (Fin N) (Fin (N + 1) × Fin (K + 1)) ((N + 1) * ((K + 1) * 6))
      (fun fl p => decide (cnt fl p.1.val = p.2.val)) := by
  refine Cmp.chain N ((K + 1) * 6) (fun i fl s => decide (cnt fl i = s.val)) (cntG N K) ?_ ?_ ?_
  · have := Cmp.ofBits (ι := Fin N) (κ := Fin (K + 1)) (s := 6)
      (F := fun fl s => decide (cnt fl 0 = s.val)) (fun s => by
        refine ((Cb.const (decide (0 = s.val))).mono (by norm_num)).congr ?_
        intro v; simp [cnt_zero])
    rw [Fintype.card_fin] at this
    exact this
  · intro i _
    have := Cmp.ofBits (ι := Fin N ⊕ Fin (K + 1)) (κ := Fin (K + 1)) (s := 6)
      (F := cntG N K i) (fun s => cntG_cb N K i s)
    rw [Fintype.card_fin] at this
    exact this
  · intro i hi v
    funext s
    simp only [cntG, dif_pos hi, Sum.elim_inl, Sum.elim_inr, cnt_succ v i hi]
    by_cases hv : v ⟨i, hi⟩ = true
    · by_cases hs : 0 < s.val
      · simp [hv, hs]; omega
      · simp [hv, hs]; omega
    · simp [hv]

theorem cnt_le {N : ℕ} (fl : Fin N → Bool) (i : ℕ) : cnt fl i ≤ N := by
  unfold cnt
  calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = N := by simp

theorem cnt_compl {N : ℕ} (fl : Fin N → Bool) :
    cnt (fun q => !fl q) N = N - cnt fl N := by
  have h : cnt fl N + cnt (fun q => !fl q) N = N := by
    unfold cnt
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (fun q : Fin N => fl q = true)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have e1 : (Finset.univ.filter (fun q : Fin N => q.val < N ∧ fl q = true)) =
        Finset.univ.filter (fun q : Fin N => fl q = true) := by
      ext q; simp
    have e2 : (Finset.univ.filter (fun q : Fin N => q.val < N ∧ (!fl q) = true)) =
        Finset.univ.filter (fun q : Fin N => ¬ fl q = true) := by
      ext q; simp
    rw [e1, e2]; exact this
  omega

def gjCost (D : ℕ) : ℕ := 32 * (D + 1) ^ 4

def laC (N K : ℕ) : ℕ := 2 ^ 7 * (N + 2) ^ 2 * (K + 2)

theorem fz2_gjbit {D : ℕ} (e : Bool × Fin D × Fin D) (p : Fin D × Fin D) :
    Cb (Fin D × Fin D) 11 (fun M => gjStep e M p) := by
  have h := Cmp.sel (ι := Fin D × Fin D)
    (fun j : (Fin D × Fin D) ⊕ Empty => Sum.elim id (fun x => x.elim) j)
    (fd_bit (τ := Empty) e p)
  exact h

theorem cmp_gj (D : ℕ) : Cmp (Fin D × Fin D) (Fin D × Fin D) (gjCost D) (gj D) := by
  have h := Cmp.foldl (ι := Fin D × Fin D) (s := Fintype.card (Fin D × Fin D) * 11) (sched D)
    (fun e M => gjStep e M) (fun e _ => Cmp.ofBits (fun p => fz2_gjbit e p))
  refine Cmp.mono h ?_
  have h1 := fd_sched_len D
  have h2 : Fintype.card (Fin D × Fin D) = D * D := by simp
  rw [h2]
  unfold gjCost
  have h3 : D ^ 4 ≤ (D + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h4 : 2 * (D * D) * (D * D * 11) = 22 * D ^ 4 := by ring
  calc (sched D).length * (D * D * 11) ≤ 2 * (D * D) * (D * D * 11) :=
        Nat.mul_le_mul_right _ h1
    _ ≤ 32 * (D + 1) ^ 4 := by omega

abbrev fz2_B (m N K : ℕ) : Type :=
  (Fin (m + N + 1) × Fin (m + N + 1)) ⊕ ((Fin (N + 1) × Fin (K + 1)) ⊕ (Fin (N + 1) × Fin (K + 1)))

def fz2_blk {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) :
    fz2_B m N K → Bool :=
  Sum.elim R (Sum.elim (fun p => decide (cnt (pv R) p.1.val = p.2.val))
    (fun p => decide (cnt (fun q => !pv R q) p.1.val = p.2.val)))

theorem fz2_cmp_blk (m N K : ℕ) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (fz2_B m N K) (13 * ((N + 1) * (K + 1)))
      (fz2_blk K) := by
  have hP := Cmp.comp (Cmp.wire (ι := Fin (m + N + 1) × Fin (m + N + 1))
    (fun p : Fin N => (cl m p, cl m p))) (cmp_counter N K)
  have hn : Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (Fin N) (Fintype.card (Fin N) * (0 + 1))
      (fun R q => !R (cl m q, cl m q)) :=
    Cmp.ofBits (fun q => Cb.not (Cb.var (cl m q, cl m q)))
  have hN := Cmp.comp hn (cmp_counter N K)
  have h := Cmp.pair (Cmp.wire (ι := Fin (m + N + 1) × Fin (m + N + 1)) id) (Cmp.pair hP hN)
  refine Cmp.mono (Cmp.congr h ?_) ?_
  · intro R k
    rcases k with k | k | k <;> rfl
  · rw [Fintype.card_fin]
    have h1 : N ≤ (N + 1) * (K + 1) := by nlinarith
    have e : (N + 1) * ((K + 1) * 6) = 6 * ((N + 1) * (K + 1)) := by ring
    omega

theorem fz2_laC (N K : ℕ) : 13 * ((N + 1) * (K + 1)) + (K + 2) ≤ laC N K := by
  unfold laC
  have h1 : (N + 1) * (K + 1) ≤ (N + 2) ^ 2 * (K + 2) :=
    Nat.mul_le_mul (by nlinarith) (by omega)
  have h2 : K + 2 ≤ (N + 2) ^ 2 * (K + 2) := Nat.le_mul_of_pos_left _ (by positivity)
  have e : 2 ^ 7 * (N + 2) ^ 2 * (K + 2) = 128 * ((N + 2) ^ 2 * (K + 2)) := by ring
  omega

theorem fz2_cntP {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) :
    cntP R p = cnt (pv R) p.val := by
  unfold cntP cnt
  congr 1

theorem fz2_cntN {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) (p : Fin N) :
    cntN R p = cnt (fun q => !pv R q) p.val := by
  unfold cntN cnt
  congr 1

theorem fz2_rk {m N : ℕ} (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) :
    rkOf R = cnt (pv R) N := by
  unfold rkOf cnt
  congr 1
  ext q
  simp

theorem fz2_row (m N K : ℕ) (s : Fin K) (j : Fin (m + N + 1)) :
    ∃ φ : (fz2_B m N K → Bool) → Bool, Cb (fz2_B m N K) (N * 3 + 1) φ ∧
      ∀ R, rowSlot K R s j = φ (fz2_blk K R) := by
  refine ⟨fun w => decide (∃ p : Fin N, (w (Sum.inl (cl m p, cl m p)) &&
    w (Sum.inr (Sum.inl (⟨p.val, by omega⟩, ⟨s.val, by omega⟩))) &&
    w (Sum.inl (cl m p, j))) = true), ?_, ?_⟩
  · have := Cb.bigOr (ι := fz2_B m N K) (I := Fin N)
      (φ := fun p w => (w (Sum.inl (cl m p, cl m p)) &&
        w (Sum.inr (Sum.inl (⟨p.val, by omega⟩, ⟨s.val, by omega⟩))) &&
        w (Sum.inl (cl m p, j))))
      (fun p => (Cb.and (Cb.and (Cb.var _) (Cb.var _)) (Cb.var _)))
    rw [Fintype.card_fin] at this
    exact (this.mono (by norm_num)).congr (fun w => decide_eq_decide.mpr Iff.rfl)
  · intro R
    unfold rowSlot
    refine decide_eq_decide.mpr (exists_congr fun p => ?_)
    rw [fz2_cntP]
    simp [fz2_blk, pv, and_assoc]

theorem fz2_xbit (m N K : ℕ) (j q : Fin N) :
    Cb (fz2_B m N K) 1 (fun w => xor (decide (j = q)) (w (Sum.inl (cl m j, cl m q)))) := by
  by_cases h : j = q
  · refine ((Cb.not (Cb.var (Sum.inl (cl m j, cl m q)))).mono (by norm_num)).congr ?_
    intro w; simp [h]
  · refine ((Cb.var (Sum.inl (cl m j, cl m q))).mono (by norm_num)).congr ?_
    intro w; simp [h]

theorem fz2_ker (m N K : ℕ) (s : Fin K) (j : Fin N) :
    ∃ φ : (fz2_B m N K → Bool) → Bool, Cb (fz2_B m N K) (N * 5 + 1) φ ∧
      ∀ R, kerSlot K R s j = φ (fz2_blk K R) := by
  refine ⟨fun w => decide (∃ q : Fin N, ((!w (Sum.inl (cl m q, cl m q))) &&
    w (Sum.inr (Sum.inr (⟨q.val, by omega⟩, ⟨s.val, by omega⟩))) &&
    xor (decide (j = q)) (w (Sum.inl (cl m j, cl m q)))) = true), ?_, ?_⟩
  · have := Cb.bigOr (ι := fz2_B m N K) (I := Fin N)
      (φ := fun q w => ((!w (Sum.inl (cl m q, cl m q))) &&
        w (Sum.inr (Sum.inr (⟨q.val, by omega⟩, ⟨s.val, by omega⟩))) &&
        xor (decide (j = q)) (w (Sum.inl (cl m j, cl m q)))))
      (fun q => (Cb.and (Cb.and (Cb.not (Cb.var _)) (Cb.var _)) (fz2_xbit m N K j q)))
    rw [Fintype.card_fin] at this
    exact (this.mono (by norm_num)).congr (fun w => decide_eq_decide.mpr Iff.rfl)
  · intro R
    unfold kerSlot
    refine decide_eq_decide.mpr (exists_congr fun q => ?_)
    rw [fz2_cntN]
    simp only [fz2_blk, pv, Sum.elim_inl, Sum.elim_inr, Bool.and_eq_true, Bool.not_eq_true',
      and_assoc]
    exact and_congr Iff.rfl (and_congr decide_eq_true_iff.symm Iff.rfl)

theorem fz2_dead (m N K : ℕ) (s : Fin K) :
    ∃ φ : (fz2_B m N K → Bool) → Bool, Cb (fz2_B m N K) (N * 3 + 2) φ ∧
      ∀ R, deadSlot K R s = φ (fz2_blk K R) := by
  refine ⟨fun w => !decide (∃ q : Fin N, ((!w (Sum.inl (cl m q, cl m q))) &&
    w (Sum.inr (Sum.inr (⟨q.val, by omega⟩, ⟨s.val, by omega⟩)))) = true), ?_, ?_⟩
  · have := Cb.not (Cb.bigOr (ι := fz2_B m N K) (I := Fin N)
      (φ := fun q w => ((!w (Sum.inl (cl m q, cl m q))) &&
        w (Sum.inr (Sum.inr (⟨q.val, by omega⟩, ⟨s.val, by omega⟩)))))
      (fun q => (Cb.and (Cb.not (Cb.var _)) (Cb.var _))))
    rw [Fintype.card_fin] at this
    exact (this.mono (by norm_num)).congr
      (fun w => congrArg (fun b => !b) (decide_eq_decide.mpr Iff.rfl))
  · intro R
    unfold deadSlot
    rw [decide_not]
    refine congrArg (fun b => !b) (decide_eq_decide.mpr (exists_congr fun q => ?_))
    rw [fz2_cntN]
    simp only [fz2_blk, pv, Sum.elim_inl, Sum.elim_inr, Bool.and_eq_true, Bool.not_eq_true',
      ]
    exact and_congr Iff.rfl decide_eq_true_iff.symm

theorem fz2_piece {m N K : ℕ} {κ : Type} [Fintype κ]
    (Q : (Fin (m + N + 1) × Fin (m + N + 1) → Bool) → κ → Bool) (s : ℕ)
    (h : ∀ k, ∃ φ : (fz2_B m N K → Bool) → Bool, Cb (fz2_B m N K) s φ ∧
      ∀ R, Q R k = φ (fz2_blk K R)) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) κ (13 * ((N + 1) * (K + 1)) + Fintype.card κ * s)
      Q := by
  choose φ hφ hQ using h
  have := Cmp.comp (fz2_cmp_blk m N K) (Cmp.ofBits (F := fun w k => φ k w) hφ)
  exact Cmp.congr this (fun R k => (hQ k R).symm)

theorem cmp_LrBits (m N d K : ℕ) (e : Fin d → Fin N) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (Fin d × Fin (K + 1))
      (laC N K + d * (K + 1) * (8 * N + 8)) (fun R => LrBits K R e) := by
  have h := fz2_piece (m := m) (N := N) (K := K) (fun R => LrBits K R e) (8 * N + 8) (by
    intro k
    by_cases hk : k.2.val < K
    · obtain ⟨φ, h1, h2⟩ := fz2_row m N K ⟨k.2.val, hk⟩ (cl m (e k.1))
      refine ⟨φ, h1.mono (by omega), fun R => ?_⟩
      rw [← h2 R]
      simp [LrBits, hk]
    · refine ⟨fun _ => false, (Cb.const false).mono (by omega), fun R => ?_⟩
      simp [LrBits, hk])
  refine Cmp.mono h ?_
  have := fz2_laC N K
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

theorem cmp_LnBits (m N d K : ℕ) (e : Fin d → Fin N) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (Fin d × Fin (K + 1))
      (laC N K + d * (K + 1) * (8 * N + 8)) (fun R => LnBits K R e) := by
  have h := fz2_piece (m := m) (N := N) (K := K) (fun R => LnBits K R e) (8 * N + 8) (by
    intro k
    by_cases hk : k.2.val < K
    · obtain ⟨φ, h1, h2⟩ := fz2_ker m N K ⟨k.2.val, hk⟩ (e k.1)
      refine ⟨φ, h1.mono (by omega), fun R => ?_⟩
      rw [← h2 R]
      simp [LnBits, hk]
    · refine ⟨fun w => w (Sum.inl (cl m (e k.1), rc m N)),
        (Cb.var _).mono (by omega), fun R => ?_⟩
      simp [LnBits, hk, fz2_blk])
  refine Cmp.mono h ?_
  have := fz2_laC N K
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

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

theorem fz2_cardV (K : ℕ) : Fintype.card (V (K + 1)) = 2 ^ (K + 1) := by
  simp [V, ZMod.card]

theorem fz2_wcost (N K : ℕ) :
    13 * ((N + 1) * (K + 1)) + 2 ^ (K + 1) * ((K + 1) * (8 * N + 8)) ≤
      laC N K + 2 ^ (K + 1) * ((K + 1) * (8 * N + 8)) := by
  have := fz2_laC N K
  omega

theorem cmp_wnR (m N K : ℕ) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (V (K + 1))
      (laC N K + 2 ^ (K + 1) * ((K + 1) * (8 * N + 8)))
      (fun R lam => decide ((∑ s : Fin K, lam s.castSucc *
        (if rowSlot K R s (rc m N) = true then (1 : ZMod 2) else 0)) ≠ 0)) := by
  choose ρφ hρ hρQ using fun s : Fin K => fz2_row m N K s (rc m N)
  have h := fz2_piece (m := m) (N := N) (K := K) (κ := V (K + 1))
    (fun R lam => decide ((∑ s : Fin K, lam s.castSucc *
        (if rowSlot K R s (rc m N) = true then (1 : ZMod 2) else 0)) ≠ 0))
    ((K + 1) * (8 * N + 8)) (by
    intro lam
    refine ⟨fun w => decide ((Finset.univ.filter (fun s : Fin K =>
      (decide (lam s.castSucc ≠ 0) && ρφ s w) = true)).card % 2 = 1), ?_, ?_⟩
    · have := Cb.bigXor (ι := fz2_B m N K) (I := Fin K) (s := N * 3 + 1)
        (φ := fun s w => (decide (lam s.castSucc ≠ 0) && ρφ s w)) (fun s => by
          by_cases hl : lam s.castSucc ≠ 0
          · refine (hρ s).congr ?_
            intro w; simp [hl]
          · refine ((Cb.const false).mono (by omega)).congr ?_
            intro w; simp [hl])
      rw [Fintype.card_fin] at this
      refine this.mono ?_
      nlinarith
    · intro R
      refine decide_eq_decide.mpr ?_
      rw [fz2_zsum]
      simp only [hρQ])
  rw [fz2_cardV] at h
  exact Cmp.mono h (fz2_wcost N K)

theorem cmp_wzN (m N K : ℕ) :
    Cmp (Fin (m + N + 1) × Fin (m + N + 1)) (V (K + 1))
      (laC N K + 2 ^ (K + 1) * ((K + 1) * (8 * N + 8)))
      (fun R lam => decide (lam (Fin.last K) = 0 ∨
        ∃ s : Fin K, deadSlot K R s = true ∧ lam s.castSucc ≠ 0)) := by
  choose δ hδ hδQ using fun s : Fin K => fz2_dead m N K s
  have h := fz2_piece (m := m) (N := N) (K := K) (κ := V (K + 1))
    (fun R lam => decide (lam (Fin.last K) = 0 ∨
        ∃ s : Fin K, deadSlot K R s = true ∧ lam s.castSucc ≠ 0))
    ((K + 1) * (8 * N + 8)) (by
    intro lam
    by_cases h0 : lam (Fin.last K) = 0
    · refine ⟨fun _ => true, (Cb.const true).mono (by nlinarith), fun R => ?_⟩
      simp [h0]
    · refine ⟨fun w => decide (∃ s : Fin K,
        (decide (lam s.castSucc ≠ 0) && δ s w) = true), ?_, ?_⟩
      · have := Cb.bigOr (ι := fz2_B m N K) (I := Fin K) (s := N * 3 + 2)
          (φ := fun s w => (decide (lam s.castSucc ≠ 0) && δ s w)) (fun s => by
            by_cases hl : lam s.castSucc ≠ 0
            · refine (hδ s).congr ?_
              intro w; simp [hl]
            · refine ((Cb.const false).mono (by omega)).congr ?_
              intro w; simp [hl])
        rw [Fintype.card_fin] at this
        refine (this.mono ?_).congr (fun w => decide_eq_decide.mpr Iff.rfl)
        nlinarith
      · intro R
        refine decide_eq_decide.mpr ?_
        simp only [h0, false_or, hδQ, Bool.and_eq_true, decide_eq_true_eq]
        exact exists_congr fun s => and_comm)
  rw [fz2_cardV] at h
  exact Cmp.mono h (fz2_wcost N K)

theorem fz2_last (m N K : ℕ) (g : (Fin (N + 1) × Fin (K + 1)) → fz2_B m N K) :
    Cb (fz2_B m N K) ((K + 1) * (0 + 1) + 1)
      (fun w => decide (∃ s : Fin (K + 1), w (g (Fin.last N, s)) = true)) := by
  have := Cb.bigOr (ι := fz2_B m N K) (I := Fin (K + 1)) (s := 0)
    (φ := fun s w => w (g (Fin.last N, s))) (fun s => Cb.var _)
  rw [Fintype.card_fin] at this
  exact this.congr (fun w => decide_eq_decide.mpr Iff.rfl)

theorem fz2_exle (c K : ℕ) : (∃ s : Fin (K + 1), c = s.val) ↔ c ≤ K := by
  constructor
  · rintro ⟨s, hs⟩
    have := s.isLt
    omega
  · intro h
    exact ⟨⟨c, by omega⟩, rfl⟩

theorem cb_okr (m N K : ℕ) :
    Cb (Fin (m + N + 1) × Fin (m + N + 1)) (laC N K) (fun R => decide (rkOf R ≤ K)) := by
  have h := Cb.comp (fz2_cmp_blk m N K) (fz2_last m N K (fun p => Sum.inr (Sum.inl p)))
  refine (h.mono ?_).congr ?_
  · have := fz2_laC N K
    omega
  · intro R
    refine decide_eq_decide.mpr ?_
    rw [fz2_rk, ← fz2_exle]
    simp [fz2_blk]

theorem cb_okn (m N K : ℕ) :
    Cb (Fin (m + N + 1) × Fin (m + N + 1)) (laC N K) (fun R => decide (N - rkOf R ≤ K)) := by
  have h := Cb.comp (fz2_cmp_blk m N K) (fz2_last m N K (fun p => Sum.inr (Sum.inr p)))
  refine (h.mono ?_).congr ?_
  · have := fz2_laC N K
    omega
  · intro R
    refine decide_eq_decide.mpr ?_
    rw [fz2_rk, ← cnt_compl, ← fz2_exle]
    simp [fz2_blk]

def coreSem {a b c K W : ℕ} (F : V a × Fin W → Bool) (G : V b × Fin W → Bool)
    (Lx : Fin a × Fin (K + 1) → Bool) (Ly : Fin b × Fin (K + 1) → Bool)
    (Lz : Fin c × Fin (K + 1) → Bool) (wz wn : V (K + 1) → Bool) : V c → BitVec W :=
  fun z => ∑ lam : V (K + 1), if (mat Lz).mulVec lam = z then
    (if wz lam = true then 0
     else if wn lam = true then
       -(tab F ((mat Lx).mulVec lam) * tab G ((mat Ly).mulVec lam))
     else tab F ((mat Lx).mulVec lam) * tab G ((mat Ly).mulVec lam))
    else 0

def coreCost (a b c K W : ℕ) : ℕ :=
  tcost a (K + 1) W + tcost b (K + 1) W + tcost c (K + 1) W + 2 ^ (K + 1) * (60 * (W + 1) ^ 2)

theorem fz3_pull {ι : Type} {d k W S S' : ℕ} {L : (ι → Bool) → Fin d × Fin k → Bool}
    {T : (ι → Bool) → V d × Fin W → Bool} (hL : Cmp ι (Fin d × Fin k) S L)
    (hT : Cmp ι (V d × Fin W) S' T) :
    Cmp ι (V k × Fin W) (S + S' + tcost d k W)
      (fun v => untab (fun lam : V k => tab (T v) ((mat (L v)).mulVec lam))) :=
  Cmp.congr (Cmp.comp (Cmp.pair hL hT) (cmp_pull d k W)) (fun _ _ => rfl)

theorem fz3_push {ι : Type} {d k W S S' : ℕ} {L : (ι → Bool) → Fin d × Fin k → Bool}
    {T : (ι → Bool) → V k × Fin W → Bool} (hL : Cmp ι (Fin d × Fin k) S L)
    (hT : Cmp ι (V k × Fin W) S' T) :
    Cmp ι (V d × Fin W) (S + S' + tcost d k W)
      (fun v => untab (fun z : V d =>
        ∑ lam : V k, if (mat (L v)).mulVec lam = z then tab (T v) lam else 0)) :=
  Cmp.congr (Cmp.comp (Cmp.pair hL hT) (cmp_push d k W)) (fun _ _ => rfl)

theorem fz3_card (k : ℕ) : Fintype.card (V k) = 2 ^ k := by
  simp [V, ZMod.card]

theorem fz3_prod {ι : Type} {k W SA SB S6 S7 : ℕ} {A B : (ι → Bool) → V k × Fin W → Bool}
    {WZ WN : (ι → Bool) → V k → Bool}
    (hA : Cmp ι (V k × Fin W) SA A) (hB : Cmp ι (V k × Fin W) SB B)
    (hwz : Cmp ι (V k) S6 WZ) (hwn : Cmp ι (V k) S7 WN) :
    Cmp ι (V k × Fin W) (SA + SB + S6 + S7 + 2 ^ k * (60 * (W + 1) ^ 2))
      (fun v => untab (fun lam : V k => if WZ v lam = true then 0
        else if WN v lam = true then -(tab (A v) lam * tab (B v) lam)
        else tab (A v) lam * tab (B v) lam)) := by
  have hb := Cmp.pair (Cmp.pair hA hB) (Cmp.pair hwz hwn)
  have hw : ∀ lam : V k, Cw (((V k × Fin W) ⊕ (V k × Fin W)) ⊕ (V k ⊕ V k)) W (60 * (W + 1) ^ 2)
      (fun v => if v (Sum.inr (Sum.inl lam)) = true then 0
        else if v (Sum.inr (Sum.inr lam)) = true then
          -(tab (fun p => v (Sum.inl (Sum.inl p))) lam * tab (fun p => v (Sum.inl (Sum.inr p))) lam)
        else tab (fun p => v (Sum.inl (Sum.inl p))) lam *
          tab (fun p => v (Sum.inl (Sum.inr p))) lam) := by
    intro lam
    have hAv : Cw (((V k × Fin W) ⊕ (V k × Fin W)) ⊕ (V k ⊕ V k)) W 0
        (fun v => tab (fun p => v (Sum.inl (Sum.inl p))) lam) :=
      Cw.var (fun i => Sum.inl (Sum.inl (lam, i)))
    have hBv : Cw (((V k × Fin W) ⊕ (V k × Fin W)) ⊕ (V k ⊕ V k)) W 0
        (fun v => tab (fun p => v (Sum.inl (Sum.inr p))) lam) :=
      Cw.var (fun i => Sum.inl (Sum.inr (lam, i)))
    have h1 := Cw.mux (Cb.var (Sum.inr (Sum.inr lam))) (Cw.neg hAv) hAv
    have h2 := Cw.mul h1 hBv
    have h3 := Cw.mux (Cb.var (Sum.inr (Sum.inl lam))) (Cw.const 0) h2
    refine (h3.mono ?_).congr ?_
    · nlinarith [Nat.zero_le W]
    · intro v
      by_cases h1 : v (Sum.inr (Sum.inl lam)) = true
      · simp [h1]
      · by_cases h2 : v (Sum.inr (Sum.inr lam)) = true
        · simp [h1, h2]
        · simp [h1, h2]
  have h := Cmp.comp hb (Cmp.ofWords hw)
  rw [fz3_card] at h
  exact Cmp.congr (h.mono (by omega)) (fun _ _ => rfl)

theorem Cmp.core {ι : Type} {a b c K W S1 S2 S3 S4 S5 S6 S7 : ℕ}
    {FF : (ι → Bool) → V a × Fin W → Bool} {GG : (ι → Bool) → V b × Fin W → Bool}
    {LX : (ι → Bool) → Fin a × Fin (K + 1) → Bool} {LY : (ι → Bool) → Fin b × Fin (K + 1) → Bool}
    {LZ : (ι → Bool) → Fin c × Fin (K + 1) → Bool} {WZ WN : (ι → Bool) → V (K + 1) → Bool}
    (hF : Cmp ι (V a × Fin W) S1 FF) (hG : Cmp ι (V b × Fin W) S2 GG)
    (hX : Cmp ι (Fin a × Fin (K + 1)) S3 LX) (hY : Cmp ι (Fin b × Fin (K + 1)) S4 LY)
    (hZ : Cmp ι (Fin c × Fin (K + 1)) S5 LZ) (hwz : Cmp ι (V (K + 1)) S6 WZ)
    (hwn : Cmp ι (V (K + 1)) S7 WN) :
    Cmp ι (V c × Fin W) (S1 + S2 + S3 + S4 + S5 + S6 + S7 + coreCost a b c K W)
      (fun v => untab (coreSem (FF v) (GG v) (LX v) (LY v) (LZ v) (WZ v) (WN v))) := by
  have h := fz3_push hZ (fz3_prod (fz3_pull hX hF) (fz3_pull hY hG) hwz hwn)
  refine (h.mono ?_).congr ?_
  · unfold coreCost
    generalize 2 ^ (K + 1) * (60 * (W + 1) ^ 2) = q
    omega
  · intro v k
    simp only [tab_untab]
    rfl

abbrev In0 (a b c m t : ℕ) : Type :=
  (Fin m × Fin (a + b + c + 1)) ⊕ ((Fin (2 ^ a) × Fin t) ⊕ (Fin (2 ^ b) × Fin t))

def Mb (a b c m t : ℕ) (v : In0 a b c m t → Bool) :
    Fin (m + (a + b + c) + 1) × Fin (m + (a + b + c) + 1) → Bool := fun p =>
  if hi : p.1.val < m then
    (if hj : p.2.val < a + b + c + 1 then v (Sum.inl (⟨p.1.val, hi⟩, ⟨p.2.val, hj⟩)) else false)
  else false

def Rb (a b c m t : ℕ) (v : In0 a b c m t → Bool) :
    Fin (m + (a + b + c) + 1) × Fin (m + (a + b + c) + 1) → Bool :=
  gj _ (Mb a b c m t v)

def fTab (a b c m t W : ℕ) (ea : Fin (2 ^ a) ≃ V a) (v : In0 a b c m t → Bool) :
    V a × Fin W → Bool := fun p =>
  if h : p.2.val < t then v (Sum.inr (Sum.inl (ea.symm p.1, ⟨p.2.val, h⟩))) else false

def gTab (a b c m t W : ℕ) (eb : Fin (2 ^ b) ≃ V b) (v : In0 a b c m t → Bool) :
    V b × Fin W → Bool := fun p =>
  if h : p.2.val < t then v (Sum.inr (Sum.inr (eb.symm p.1, ⟨p.2.val, h⟩))) else false

def whtF {d W : ℕ} (T : V d × Fin W → Bool) : V d × Fin W → Bool :=
  untab (fun xi : V d => ∑ x : V d, sgn (xi ⬝ᵥ x) * tab T x)

def Kof (a b c u : ℕ) : ℕ := min (a + b + c) u

def Wof (a b c t u : ℕ) : ℕ := a + b + 2 * t + 1 + Kof a b c u

def wzRf (K : ℕ) : V (K + 1) → Bool := fun lam => decide (lam (Fin.last K) ≠ 0)

def wnRf {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) : V (K + 1) → Bool :=
  fun lam => decide ((∑ s : Fin K, lam s.castSucc *
    (if rowSlot K R s (rc m N) = true then (1 : ZMod 2) else 0)) ≠ 0)

def wzNf {m N : ℕ} (K : ℕ) (R : Fin (m + N + 1) × Fin (m + N + 1) → Bool) : V (K + 1) → Bool :=
  fun lam => decide (lam (Fin.last K) = 0 ∨
    ∃ s : Fin K, deadSlot K R s = true ∧ lam s.castSucc ≠ 0)

def ansR (a b c m t u : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (v : In0 a b c m t → Bool) : V c × Fin (Wof a b c t u) → Bool :=
  whtF (untab (coreSem (whtF (fTab a b c m t (Wof a b c t u) ea v))
    (whtF (gTab a b c m t (Wof a b c t u) eb v))
    (LrBits (Kof a b c u) (Rb a b c m t v) (nx (b := b) (c := c)))
    (LrBits (Kof a b c u) (Rb a b c m t v) (ny (a := a) (c := c)))
    (LrBits (Kof a b c u) (Rb a b c m t v) (nz (a := a) (b := b)))
    (wzRf (Kof a b c u)) (wnRf (Kof a b c u) (Rb a b c m t v))))

def ansN (a b c m t u : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (v : In0 a b c m t → Bool) : V c × Fin (Wof a b c t u) → Bool :=
  untab (coreSem (fTab a b c m t (Wof a b c t u) ea v)
    (gTab a b c m t (Wof a b c t u) eb v)
    (LnBits (Kof a b c u) (Rb a b c m t v) (nx (b := b) (c := c)))
    (LnBits (Kof a b c u) (Rb a b c m t v) (ny (a := a) (c := c)))
    (LnBits (Kof a b c u) (Rb a b c m t v) (nz (a := a) (b := b)))
    (wzNf (Kof a b c u) (Rb a b c m t v)) (fun _ => false))

def okR (a b c m t u : ℕ) (v : In0 a b c m t → Bool) : Bool :=
  decide (rkOf (Rb a b c m t v) ≤ Kof a b c u)

def okN (a b c m t u : ℕ) (v : In0 a b c m t → Bool) : Bool :=
  decide (a + b + c - rkOf (Rb a b c m t v) ≤ Kof a b c u)

def consB (a b c m t : ℕ) (v : In0 a b c m t → Bool) : Bool :=
  !(Rb a b c m t v) (rc m (a + b + c), rc m (a + b + c))

def topF (a b c m t u : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (ec : Fin (2 ^ c) ≃ V c) (v : In0 a b c m t → Bool) :
    Unit ⊕ (Fin (2 ^ c) × Fin (a + b + 2 * t + 1)) → Bool :=
  Sum.elim (fun _ => okR a b c m t u v || okN a b c m t u v)
    (fun p => (okR a b c m t u v || okN a b c m t u v) && consB a b c m t v &&
      (if okR a b c m t u v = true then
        ansR a b c m t u ea eb v (ec p.1, ⟨Kof a b c u + p.2.val, by unfold Wof; omega⟩)
       else ansN a b c m t u ea eb v (ec p.1, ⟨p.2.val, by unfold Wof; omega⟩)))

def inpOf {a b c m t : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) : In0 a b c m t → Bool :=
  Sum.elim (fun p => if h : p.2.val < a + b + c then decide (join3 (H p.1) ⟨p.2.val, h⟩ ≠ 0)
      else decide (rhs p.1 ≠ 0))
    (Sum.elim (fun p => (f p.1).val.testBit p.2.val) (fun p => (g p.1).val.testBit p.2.val))

def topSum (a b c m t u : ℕ) : ℕ :=
  gjCost (m + (a + b + c) + 1) + (m + (a + b + c) + 1) ^ 2 +
  (2 ^ a + 2 ^ b) * (Wof a b c t u + 1) +
  whtCost a (Wof a b c t u) + whtCost b (Wof a b c t u) + whtCost c (Wof a b c t u) +
  laC (a + b + c) (Kof a b c u) +
  (a + b + c) * (Kof a b c u + 1) * (8 * (a + b + c) + 8) +
  2 ^ (Kof a b c u + 1) * ((Kof a b c u + 1) * (8 * (a + b + c) + 8)) +
  coreCost a b c (Kof a b c u) (Wof a b c t u) + 2 ^ (Kof a b c u + 1) +
  2 ^ c * (a + b + 2 * t + 1) * 16 + 16

def topCost (a b c m t u : ℕ) : ℕ := 16 * topSum a b c m t u

theorem fz4_cardV (d : ℕ) : Fintype.card (V d) = 2 ^ d := by
  simp [V]

theorem fz4_Mb (a b c m t : ℕ) :
    Cmp (In0 a b c m t) (Fin (m + (a + b + c) + 1) × Fin (m + (a + b + c) + 1))
      ((m + (a + b + c) + 1) ^ 2) (Mb a b c m t) := by
  refine (Cmp.ofBits (s := 1) (F := Mb a b c m t) (fun p => ?_)).mono (by simp [sq])
  by_cases hi : p.1.val < m
  · by_cases hj : p.2.val < a + b + c + 1
    · refine ((Cb.var (Sum.inl (⟨p.1.val, hi⟩, ⟨p.2.val, hj⟩))).mono (by norm_num)).congr ?_
      intro v; simp [Mb, hi, hj]
    · refine (Cb.const false).congr ?_
      intro v; simp [Mb, hi, hj]
  · refine (Cb.const false).congr ?_
    intro v; simp [Mb, hi]

theorem fz4_fTab (a b c m t W : ℕ) (ea : Fin (2 ^ a) ≃ V a) :
    Cmp (In0 a b c m t) (V a × Fin W) (2 ^ a * W) (fTab a b c m t W ea) := by
  refine (Cmp.ofBits (s := 1) (F := fTab a b c m t W ea) (fun p => ?_)).mono
    (by simp)
  by_cases h : p.2.val < t
  · refine ((Cb.var (Sum.inr (Sum.inl (ea.symm p.1, ⟨p.2.val, h⟩)))).mono (by norm_num)).congr ?_
    intro v; simp [fTab, h]
  · refine (Cb.const false).congr ?_
    intro v; simp [fTab, h]

theorem fz4_gTab (a b c m t W : ℕ) (eb : Fin (2 ^ b) ≃ V b) :
    Cmp (In0 a b c m t) (V b × Fin W) (2 ^ b * W) (gTab a b c m t W eb) := by
  refine (Cmp.ofBits (s := 1) (F := gTab a b c m t W eb) (fun p => ?_)).mono
    (by simp)
  by_cases h : p.2.val < t
  · refine ((Cb.var (Sum.inr (Sum.inr (eb.symm p.1, ⟨p.2.val, h⟩)))).mono (by norm_num)).congr ?_
    intro v; simp [gTab, h]
  · refine (Cb.const false).congr ?_
    intro v; simp [gTab, h]

theorem fz4_const (ι : Type) (K : ℕ) (w : V (K + 1) → Bool) :
    Cmp ι (V (K + 1)) (2 ^ (K + 1)) (fun _ => w) :=
  (Cmp.ofBits (s := 1) (F := fun _ => w) (fun k => Cb.const (w k))).mono
    (by simp)

def fz4_fin (a b c t u : ℕ) (ec : Fin (2 ^ c) ≃ V c)
    (w : ((Unit ⊕ Unit) ⊕ Unit) ⊕
      ((V c × Fin (Wof a b c t u)) ⊕ (V c × Fin (Wof a b c t u))) → Bool) :
    Unit ⊕ (Fin (2 ^ c) × Fin (a + b + 2 * t + 1)) → Bool :=
  Sum.elim (fun _ => w (Sum.inl (Sum.inl (Sum.inl ()))) || w (Sum.inl (Sum.inl (Sum.inr ()))))
    (fun p => (w (Sum.inl (Sum.inl (Sum.inl ()))) || w (Sum.inl (Sum.inl (Sum.inr ())))) &&
      w (Sum.inl (Sum.inr ())) &&
      (if w (Sum.inl (Sum.inl (Sum.inl ()))) = true then
        w (Sum.inr (Sum.inl (ec p.1, ⟨Kof a b c u + p.2.val, by unfold Wof; omega⟩)))
       else w (Sum.inr (Sum.inr (ec p.1, ⟨p.2.val, by unfold Wof; omega⟩)))))

theorem fz4_fin_cmp (a b c t u : ℕ) (ec : Fin (2 ^ c) ≃ V c) :
    Cmp (((Unit ⊕ Unit) ⊕ Unit) ⊕
      ((V c × Fin (Wof a b c t u)) ⊕ (V c × Fin (Wof a b c t u))))
      (Unit ⊕ (Fin (2 ^ c) × Fin (a + b + 2 * t + 1)))
      ((1 + 2 ^ c * (a + b + 2 * t + 1)) * 7) (fz4_fin a b c t u ec) := by
  refine (Cmp.ofBits (s := 7) (F := fz4_fin a b c t u ec) (fun k => ?_)).mono (by simp)
  rcases k with k | p
  · exact (Cb.or (Cb.var (Sum.inl (Sum.inl (Sum.inl ()))))
      (Cb.var (Sum.inl (Sum.inl (Sum.inr ()))))).mono (by norm_num)
  · exact (Cb.and (Cb.and (Cb.or (Cb.var (Sum.inl (Sum.inl (Sum.inl ()))))
      (Cb.var (Sum.inl (Sum.inl (Sum.inr ()))))) (Cb.var (Sum.inl (Sum.inr ()))))
      (Cb.mux (Cb.var (Sum.inl (Sum.inl (Sum.inl ()))))
        (Cb.var (Sum.inr (Sum.inl (ec p.1,
          (⟨Kof a b c u + p.2.val, by unfold Wof; omega⟩ : Fin (Wof a b c t u))))))
        (Cb.var (Sum.inr (Sum.inr (ec p.1,
          (⟨p.2.val, by unfold Wof; omega⟩ : Fin (Wof a b c t u)))))))).mono
      (by norm_num)

theorem cmp_top (a b c m t u : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (ec : Fin (2 ^ c) ≃ V c) :
    Cmp (In0 a b c m t) (Unit ⊕ (Fin (2 ^ c) × Fin (a + b + 2 * t + 1))) (topCost a b c m t u)
      (topF a b c m t u ea eb ec) := by
  have hR : Cmp (In0 a b c m t) (Fin (m + (a + b + c) + 1) × Fin (m + (a + b + c) + 1))
      ((m + (a + b + c) + 1) ^ 2 + gjCost (m + (a + b + c) + 1)) (Rb a b c m t) := by
    have h0 := Cmp.comp (fz4_Mb a b c m t) (cmp_gj (m + (a + b + c) + 1))
    exact h0
  have hf := fz4_fTab a b c m t (Wof a b c t u) ea
  have hg := fz4_gTab a b c m t (Wof a b c t u) eb
  have hwf : Cmp (In0 a b c m t) _ _ (fun v => whtF (fTab a b c m t (Wof a b c t u) ea v)) :=
    Cmp.comp hf (cmp_wht a (Wof a b c t u))
  have hwg : Cmp (In0 a b c m t) _ _ (fun v => whtF (gTab a b c m t (Wof a b c t u) eb v)) :=
    Cmp.comp hg (cmp_wht b (Wof a b c t u))
  have hrx := Cmp.comp hR (cmp_LrBits m (a + b + c) a (Kof a b c u) (nx (b := b) (c := c)))
  have hry := Cmp.comp hR (cmp_LrBits m (a + b + c) b (Kof a b c u) (ny (a := a) (c := c)))
  have hrz := Cmp.comp hR (cmp_LrBits m (a + b + c) c (Kof a b c u) (nz (a := a) (b := b)))
  have hnx := Cmp.comp hR (cmp_LnBits m (a + b + c) a (Kof a b c u) (nx (b := b) (c := c)))
  have hny := Cmp.comp hR (cmp_LnBits m (a + b + c) b (Kof a b c u) (ny (a := a) (c := c)))
  have hnz := Cmp.comp hR (cmp_LnBits m (a + b + c) c (Kof a b c u) (nz (a := a) (b := b)))
  have hwnR : Cmp (In0 a b c m t) _ _ (fun v => wnRf (Kof a b c u) (Rb a b c m t v)) :=
    Cmp.comp hR (cmp_wnR m (a + b + c) (Kof a b c u))
  have hwzN : Cmp (In0 a b c m t) _ _ (fun v => wzNf (Kof a b c u) (Rb a b c m t v)) :=
    Cmp.comp hR (cmp_wzN m (a + b + c) (Kof a b c u))
  have hwzR := fz4_const (In0 a b c m t) (Kof a b c u) (wzRf (Kof a b c u))
  have hwnN := fz4_const (In0 a b c m t) (Kof a b c u) (fun _ => false)
  have hcR := Cmp.core hwf hwg hrx hry hrz hwzR hwnR
  have hansR0 := Cmp.comp hcR (cmp_wht c (Wof a b c t u))
  have hansR : Cmp (In0 a b c m t) _ _ (ansR a b c m t u ea eb) := hansR0
  have hansN : Cmp (In0 a b c m t) _ _ (ansN a b c m t u ea eb) :=
    Cmp.core hf hg hnx hny hnz hwzN hwnN
  have hokR0 := Cb.comp hR (cb_okr m (a + b + c) (Kof a b c u))
  have hokR : Cb (In0 a b c m t) _ (okR a b c m t u) := hokR0
  have hokN0 := Cb.comp hR (cb_okn m (a + b + c) (Kof a b c u))
  have hokN : Cb (In0 a b c m t) _ (okN a b c m t u) := hokN0
  have hcons0 := Cb.comp hR (Cb.not (Cb.var (rc m (a + b + c), rc m (a + b + c))))
  have hcons : Cb (In0 a b c m t) _ (consB a b c m t) := hcons0
  have hb := Cmp.pair (Cmp.pair (Cmp.pair hokR hokN) hcons) (Cmp.pair hansR hansN)
  have htop := Cmp.comp hb (fz4_fin_cmp a b c t u ec)
  refine Cmp.mono (Cmp.congr htop ?_) ?_
  · intro v k
    rcases k with k | p
    · rfl
    · rfl
  · unfold topCost topSum coreCost
    have e1 : a * (Kof a b c u + 1) * (8 * (a + b + c) + 8) ≤
        (a + b + c) * (Kof a b c u + 1) * (8 * (a + b + c) + 8) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have e2 : b * (Kof a b c u + 1) * (8 * (a + b + c) + 8) ≤
        (a + b + c) * (Kof a b c u + 1) * (8 * (a + b + c) + 8) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have e3 : c * (Kof a b c u + 1) * (8 * (a + b + c) + 8) ≤
        (a + b + c) * (Kof a b c u + 1) * (8 * (a + b + c) + 8) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have e4 : (2 ^ a + 2 ^ b) * (Wof a b c t u + 1) =
        2 ^ a * Wof a b c t u + 2 ^ b * Wof a b c t u + 2 ^ a + 2 ^ b := by ring
    have p1 := Nat.zero_le (2 ^ Kof a b c u)
    have p2 := Nat.zero_le (2 ^ a)
    have p3 := Nat.zero_le (2 ^ b)
    omega

theorem fz5_Mb {a b c m t : ℕ} (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) :
    Mb a b c m t (inpOf H rhs f g) = sysBits (fun i => join3 (H i)) rhs := by
  funext p
  unfold Mb sysBits inpOf
  by_cases hi : p.1.val < m
  · by_cases hj : p.2.val < a + b + c
    · have hj' : p.2.val < a + b + c + 1 := by omega
      simp [hi, hj, hj']
    · by_cases hj2 : p.2.val = a + b + c
      · have hj' : p.2.val < a + b + c + 1 := by omega
        simp [hi, hj, hj', hj2]
      · have hj' : ¬ p.2.val < a + b + c + 1 := by omega
        simp [hi, hj, hj', hj2]
  · simp [hi]

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

theorem fz5_total {a b c m t : ℕ} (W : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (z : V c) :
    (∑ x : V a, ∑ y : V b,
      if (∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i) then
        BitVec.ofNat W (f (ea.symm x)).val * BitVec.ofNat W (g (eb.symm y)).val else 0) =
    BitVec.ofNat W (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ z = rhs i) then
        (f ix).val * (g iy).val else 0) := by
  rw [← Equiv.sum_comp ea]
  have : ∀ ix : Fin (2 ^ a), (∑ y : V b,
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i) then
        BitVec.ofNat W (f (ea.symm (ea ix))).val * BitVec.ofNat W (g (eb.symm y)).val else 0) =
      ∑ iy : Fin (2 ^ b),
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ z = rhs i) then
        ((f ix).val : BitVec W) * ((g iy).val : BitVec W) else 0 := by
    intro ix
    rw [← Equiv.sum_comp eb]
    apply Finset.sum_congr rfl
    intro iy _
    simp only [Equiv.symm_apply_apply, BitVec.natCast_eq_ofNat]
  rw [Finset.sum_congr rfl (fun ix _ => this ix)]
  rw [← BitVec.natCast_eq_ofNat]
  push_cast
  rfl

theorem fz5_two (W K n : ℕ) : (2 : BitVec W) ^ K * BitVec.ofNat W n = BitVec.ofNat W (2 ^ K * n) := by
  rw [← BitVec.natCast_eq_ofNat, ← BitVec.natCast_eq_ofNat]
  push_cast
  rfl

theorem fz5_R {a b c m t : ℕ} (K W : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (z : V c)
    (hc : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = false)
    (hr : rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ K) :
    (∑ ζ : V c, sgn (z ⬝ᵥ ζ) *
      coreSem (whtF (fTab a b c m t W ea (inpOf H rhs f g)))
        (whtF (gTab a b c m t W eb (inpOf H rhs f g)))
        (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c)))
        (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c)))
        (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b)))
        (wzRf K) (wnRf K (gj _ (sysBits (fun i => join3 (H i)) rhs))) ζ) =
    BitVec.ofNat W (2 ^ K * ∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ z = rhs i) then
        (f ix).val * (g iy).val else 0) := by
  have key := fourier_id K a b c W (fun x => BitVec.ofNat W (f (ea.symm x)).val)
    (fun y => BitVec.ofNat W (g (eb.symm y)).val)
    (mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c))))
    (mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c))))
    (mat (LrBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b))))
    (fun s => if rowSlot K (gj _ (sysBits (fun i => join3 (H i)) rhs)) s (rc m (a + b + c)) = true
      then 1 else 0) z
  rw [← fz5_two, ← fz5_total]
  refine Eq.trans ?_ (key.trans ?_)
  · apply Finset.sum_congr rfl
    intro ζ _
    rw [dotProduct_comm z ζ]
    congr 1
    unfold coreSem
    apply Finset.sum_congr rfl
    intro lam _
    simp only [whtF, tab_untab, wzRf, wnRf, decide_eq_true_eq, fz5_tabf, fz5_tabg]
  · congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    exact if_congr (tr_rows K H rhs hc hr x y z) rfl rfl

theorem fz5_N {a b c m t : ℕ} (K W : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) (z : V c)
    (hc : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = false)
    (hk : a + b + c - rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ K) :
    coreSem (fTab a b c m t W ea (inpOf H rhs f g))
        (gTab a b c m t W eb (inpOf H rhs f g))
        (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c)))
        (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c)))
        (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b)))
        (wzNf K (gj _ (sysBits (fun i => join3 (H i)) rhs))) (fun _ => false) z =
    BitVec.ofNat W (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
      if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ z = rhs i) then
        (f ix).val * (g iy).val else 0) := by
  have key := kernel_id K a b c W (fun x => BitVec.ofNat W (f (ea.symm x)).val)
    (fun y => BitVec.ofNat W (g (eb.symm y)).val)
    (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nx (b := b) (c := c))))
    (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (ny (a := a) (c := c))))
    (mat (LnBits K (gj _ (sysBits (fun i => join3 (H i)) rhs)) (nz (a := a) (b := b))))
    (deadSlot K (gj _ (sysBits (fun i => join3 (H i)) rhs)))
    (fun x y z => ∀ i, (H i).1 ⬝ᵥ x + (H i).2.1 ⬝ᵥ y + (H i).2.2 ⬝ᵥ z = rhs i)
    (fun lam hl => tr_ker_sol K H rhs hc lam hl)
    (fun x y z hs => tr_ker_uniq K H rhs hc hk x y z hs) z
  rw [← fz5_total]
  refine Eq.trans ?_ key
  unfold coreSem
  apply Finset.sum_congr rfl
  intro lam _
  simp only [wzNf, decide_eq_true_eq, fz5_tabf, fz5_tabg, Bool.false_eq_true, if_false]

theorem top_sem (a b c m t u : ℕ) (ea : Fin (2 ^ a) ≃ V a) (eb : Fin (2 ^ b) ≃ V b)
    (ec : Fin (2 ^ c) ≃ V c)
    (hea : ∀ ix j, ea ix j = if ix.val.testBit j.val then 1 else 0)
    (heb : ∀ ix j, eb ix j = if ix.val.testBit j.val then 1 else 0)
    (hec : ∀ ix j, ec ix j = if ix.val.testBit j.val then 1 else 0)
    (H : Fin m → V a × V b × V c) (rhs : Fin m → ZMod 2)
    (f : Fin (2 ^ a) → Fin (2 ^ t)) (g : Fin (2 ^ b) → Fin (2 ^ t)) :
    (topF a b c m t u ea eb ec (inpOf H rhs f g) (Sum.inl ()) = true ↔
      min (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)))
        (a + b + c - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H))) ≤ u) ∧
    ∀ (iz : Fin (2 ^ c)) (j : Fin (a + b + 2 * t + 1)),
      topF a b c m t u ea eb ec (inpOf H rhs f g) (Sum.inr (iz, j)) =
        (if topF a b c m t u ea eb ec (inpOf H rhs f g) (Sum.inl ()) = true then
          (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
            if ∀ i, (H i).1 ⬝ᵥ (fun j : Fin a => if ix.val.testBit j.val then (1 : ZMod 2) else 0) +
                (H i).2.1 ⬝ᵥ (fun j : Fin b => if iy.val.testBit j.val then (1 : ZMod 2) else 0) +
                (H i).2.2 ⬝ᵥ (fun j : Fin c => if iz.val.testBit j.val then (1 : ZMod 2) else 0) =
                rhs i
            then (f ix).val * (g iy).val else 0)
         else 0).testBit j.val := by
  have hea' : ∀ ix, ea ix = (fun j : Fin a => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
    fun ix => funext (hea ix)
  have heb' : ∀ ix, eb ix = (fun j : Fin b => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
    fun ix => funext (heb ix)
  have hec' : ∀ ix, ec ix = (fun j : Fin c => if ix.val.testBit j.val then (1 : ZMod 2) else 0) :=
    fun ix => funext (hec ix)
  have hRb : Rb a b c m t (inpOf H rhs f g) = gj _ (sysBits (fun i => join3 (H i)) rhs) := by
    unfold Rb; rw [fz5_Mb]
  have hrk := tr_rank H rhs
  have hle : rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ a + b + c := by
    unfold rkOf
    calc _ ≤ (Finset.univ : Finset (Fin (a + b + c))).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = a + b + c := by simp
  have hok : (okR a b c m t u (inpOf H rhs f g) || okN a b c m t u (inpOf H rhs f g)) = true ↔
      min (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)))
        (a + b + c - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H))) ≤ u := by
    unfold okR okN Kof
    rw [hRb, hrk]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    omega
  refine ⟨hok, ?_⟩
  intro iz j
  have htot : (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
            if ∀ i, (H i).1 ⬝ᵥ (fun j : Fin a => if ix.val.testBit j.val then (1 : ZMod 2) else 0) +
                (H i).2.1 ⬝ᵥ (fun j : Fin b => if iy.val.testBit j.val then (1 : ZMod 2) else 0) +
                (H i).2.2 ⬝ᵥ (fun j : Fin c => if iz.val.testBit j.val then (1 : ZMod 2) else 0) =
                rhs i
            then (f ix).val * (g iy).val else 0) =
      ∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
        if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ ec iz = rhs i) then
          (f ix).val * (g iy).val else 0 := by
    simp only [hea', heb', hec']
  rw [htot]
  have hK : Kof a b c u + j.val < Wof a b c t u := by unfold Wof; omega
  have hj : j.val < Wof a b c t u := by unfold Wof; omega
  show ((okR a b c m t u (inpOf H rhs f g) || okN a b c m t u (inpOf H rhs f g)) &&
      consB a b c m t (inpOf H rhs f g) &&
      (if okR a b c m t u (inpOf H rhs f g) = true then
        ansR a b c m t u ea eb (inpOf H rhs f g) (ec iz, ⟨Kof a b c u + j.val, hK⟩)
       else ansN a b c m t u ea eb (inpOf H rhs f g) (ec iz, ⟨j.val, hj⟩))) =
    (if (okR a b c m t u (inpOf H rhs f g) || okN a b c m t u (inpOf H rhs f g)) = true then _
      else 0).testBit j.val
  by_cases hO : (okR a b c m t u (inpOf H rhs f g) || okN a b c m t u (inpOf H rhs f g)) = true
  swap
  · rw [if_neg hO]
    rw [Bool.not_eq_true] at hO
    rw [hO]
    simp
  rw [if_pos hO, hO, Bool.true_and]
  by_cases hC : gj _ (sysBits (fun i => join3 (H i)) rhs) (rc m (a + b + c), rc m (a + b + c)) = true
  · have h0 : (∑ ix : Fin (2 ^ a), ∑ iy : Fin (2 ^ b),
        if (∀ i, (H i).1 ⬝ᵥ ea ix + (H i).2.1 ⬝ᵥ eb iy + (H i).2.2 ⬝ᵥ ec iz = rhs i) then
          (f ix).val * (g iy).val else 0) = 0 := by
      apply Finset.sum_eq_zero; intro ix _
      apply Finset.sum_eq_zero; intro iy _
      exact if_neg (tr_incons H rhs hC _ _ _)
    rw [h0]
    have : consB a b c m t (inpOf H rhs f g) = false := by
      unfold consB; rw [hRb, hC]; rfl
    rw [this]; simp
  rw [Bool.not_eq_true] at hC
  have hcons : consB a b c m t (inpOf H rhs f g) = true := by
    unfold consB; rw [hRb, hC]; rfl
  rw [hcons, Bool.true_and]
  by_cases hR : okR a b c m t u (inpOf H rhs f g) = true
  · rw [if_pos hR]
    have hr : rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ Kof a b c u := by
      have := hR; unfold okR at this; rw [hRb] at this; exact of_decide_eq_true this
    have e1 : ansR a b c m t u ea eb (inpOf H rhs f g) (ec iz, ⟨Kof a b c u + j.val, hK⟩) =
        (∑ ζ : V c, sgn (ec iz ⬝ᵥ ζ) *
          tab (untab (coreSem (whtF (fTab a b c m t (Wof a b c t u) ea (inpOf H rhs f g)))
            (whtF (gTab a b c m t (Wof a b c t u) eb (inpOf H rhs f g)))
            (LrBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (nx (b := b) (c := c)))
            (LrBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (ny (a := a) (c := c)))
            (LrBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (nz (a := a) (b := b)))
            (wzRf (Kof a b c u)) (wnRf (Kof a b c u) (Rb a b c m t (inpOf H rhs f g))))) ζ).getLsbD
          (Kof a b c u + j.val) := by
      simp only [ansR, whtF, untab]
    rw [e1, tab_untab, hRb, fz5_R (Kof a b c u) (Wof a b c t u) ea eb H rhs f g (ec iz) hC hr,
      BitVec.getLsbD_ofNat, Nat.testBit_two_pow_mul]
    simp [hK]
  · rw [if_neg hR]
    have hk : a + b + c - rkOf (gj _ (sysBits (fun i => join3 (H i)) rhs)) ≤ Kof a b c u := by
      rw [Bool.not_eq_true] at hR
      rw [hR, Bool.false_or] at hO
      unfold okN at hO; rw [hRb] at hO; exact of_decide_eq_true hO
    have e1 : ansN a b c m t u ea eb (inpOf H rhs f g) (ec iz, ⟨j.val, hj⟩) =
        (coreSem (fTab a b c m t (Wof a b c t u) ea (inpOf H rhs f g))
            (gTab a b c m t (Wof a b c t u) eb (inpOf H rhs f g))
            (LnBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (nx (b := b) (c := c)))
            (LnBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (ny (a := a) (c := c)))
            (LnBits (Kof a b c u) (Rb a b c m t (inpOf H rhs f g)) (nz (a := a) (b := b)))
            (wzNf (Kof a b c u) (Rb a b c m t (inpOf H rhs f g))) (fun _ => false) (ec iz)).getLsbD
          j.val := by
      simp only [ansN, untab]
    rw [e1, hRb, fz5_N (Kof a b c u) (Wof a b c t u) ea eb H rhs f g (ec iz) hC hk,
      BitVec.getLsbD_ofNat]
    simp [hj]

theorem fz6_low (P B i : ℕ) (hi : i ≤ 5) (hP : 1 ≤ P) (hB : 1 ≤ B) : P ^ i ≤ P ^ 5 * B := by
  calc P ^ i ≤ P ^ 5 := Nat.pow_le_pow_right hP hi
    _ = P ^ 5 * 1 := (Nat.mul_one _).symm
    _ ≤ P ^ 5 * B := Nat.mul_le_mul_left _ hB

theorem fz6_lowB (P B i : ℕ) (hi : i ≤ 5) (hP : 1 ≤ P) : P ^ i * B ≤ P ^ 5 * B :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hP hi)

theorem fz6_tc (d K W P B : ℕ) (h1 : d + (K + 1) + 2 ≤ 2 * P) (h2 : W + 1 ≤ 2 * P)
    (h3 : 2 ^ (max d (K + 1)) ≤ 2 * B) : tcost d (K + 1) W ≤ 2 ^ 15 * (P ^ 5 * B) := by
  unfold tcost
  calc 2 ^ 9 * (d + (K + 1) + 2) ^ 4 * (W + 1) * 2 ^ (max d (K + 1))
      ≤ 2 ^ 9 * (2 * P) ^ 4 * (2 * P) * (2 * B) := by gcongr
    _ = 2 ^ 15 * (P ^ 5 * B) := by ring

theorem fz6_wht (d W P B : ℕ) (h1 : d + 1 ≤ P) (h2 : W + 1 ≤ 2 * P) (h3 : 2 ^ d ≤ B)
    (hP : 1 ≤ P) : whtCost d W ≤ 2 ^ 8 * (P ^ 5 * B) := by
  unfold whtCost
  calc 2 ^ 7 * (d + 1) * (W + 1) * 2 ^ d ≤ 2 ^ 7 * P * (2 * P) * B := by gcongr
    _ = 2 ^ 8 * (P ^ 2 * B) := by ring
    _ ≤ 2 ^ 8 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 2 (by norm_num) hP)

theorem fz6_max (d K B : ℕ) (hd : 2 ^ d + 2 ^ K ≤ B) : 2 ^ (max d (K + 1)) ≤ 2 * B := by
  have hd0 : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
  have hk0 : 0 < 2 ^ K := Nat.pos_of_ne_zero (by positivity)
  rcases max_cases d (K + 1) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; omega
  · rw [h, pow_succ]; omega

theorem fz6_main (a b c m t K P B : ℕ) (hK : K ≤ a + b + c)
    (hP : P = a + b + c + m + t + 3) (hB : B = 2 ^ a + 2 ^ b + 2 ^ c + 2 ^ K) :
    gjCost (m + (a + b + c) + 1) + (m + (a + b + c) + 1) ^ 2 +
    (2 ^ a + 2 ^ b) * (a + b + 2 * t + 1 + K + 1) +
    whtCost a (a + b + 2 * t + 1 + K) + whtCost b (a + b + 2 * t + 1 + K) +
    whtCost c (a + b + 2 * t + 1 + K) +
    laC (a + b + c) K +
    (a + b + c) * (K + 1) * (8 * (a + b + c) + 8) +
    2 ^ (K + 1) * ((K + 1) * (8 * (a + b + c) + 8)) +
    (tcost a (K + 1) (a + b + 2 * t + 1 + K) + tcost b (K + 1) (a + b + 2 * t + 1 + K) +
      tcost c (K + 1) (a + b + 2 * t + 1 + K) +
      2 ^ (K + 1) * (60 * (a + b + 2 * t + 1 + K + 1) ^ 2)) + 2 ^ (K + 1) +
    2 ^ c * (a + b + 2 * t + 1) * 16 + 16 ≤ 2 ^ 17 * (P ^ 5 * B) := by
  have ha0 : 0 < 2 ^ a := Nat.pos_of_ne_zero (by positivity)
  have hb0 : 0 < 2 ^ b := Nat.pos_of_ne_zero (by positivity)
  have hc0 : 0 < 2 ^ c := Nat.pos_of_ne_zero (by positivity)
  have hk0 : 0 < 2 ^ K := Nat.pos_of_ne_zero (by positivity)
  have hP1 : 1 ≤ P := by omega
  have hB1 : 1 ≤ B := by omega
  have hW : a + b + 2 * t + 1 + K + 1 ≤ 2 * P := by omega
  have hK2 : 2 ^ (K + 1) ≤ 2 * B := by rw [pow_succ]; omega
  have e1 : gjCost (m + (a + b + c) + 1) ≤ 32 * (P ^ 5 * B) := by
    unfold gjCost
    calc 32 * (m + (a + b + c) + 1 + 1) ^ 4 ≤ 32 * P ^ 4 := by gcongr; omega
      _ ≤ 32 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_low P B 4 (by norm_num) hP1 hB1)
  have e2 : (m + (a + b + c) + 1) ^ 2 ≤ 1 * (P ^ 5 * B) := by
    calc (m + (a + b + c) + 1) ^ 2 ≤ P ^ 2 := by gcongr; omega
      _ ≤ P ^ 5 * B := fz6_low P B 2 (by norm_num) hP1 hB1
      _ = 1 * (P ^ 5 * B) := (Nat.one_mul _).symm
  have e3 : (2 ^ a + 2 ^ b) * (a + b + 2 * t + 1 + K + 1) ≤ 2 * (P ^ 5 * B) := by
    calc (2 ^ a + 2 ^ b) * (a + b + 2 * t + 1 + K + 1) ≤ B * (2 * P) := by gcongr; omega
      _ = 2 * (P ^ 1 * B) := by ring
      _ ≤ 2 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 1 (by norm_num) hP1)
  have e4 := fz6_wht a (a + b + 2 * t + 1 + K) P B (by omega) hW (by omega) hP1
  have e5 := fz6_wht b (a + b + 2 * t + 1 + K) P B (by omega) hW (by omega) hP1
  have e6 := fz6_wht c (a + b + 2 * t + 1 + K) P B (by omega) hW (by omega) hP1
  have e7 : laC (a + b + c) K ≤ 2 ^ 7 * (P ^ 5 * B) := by
    unfold laC
    calc 2 ^ 7 * (a + b + c + 2) ^ 2 * (K + 2) ≤ 2 ^ 7 * P ^ 2 * P := by gcongr <;> omega
      _ = 2 ^ 7 * P ^ 3 := by ring
      _ ≤ 2 ^ 7 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_low P B 3 (by norm_num) hP1 hB1)
  have e8 : (a + b + c) * (K + 1) * (8 * (a + b + c) + 8) ≤ 8 * (P ^ 5 * B) := by
    calc (a + b + c) * (K + 1) * (8 * (a + b + c) + 8) ≤ P * P * (8 * P) := by gcongr <;> omega
      _ = 8 * P ^ 3 := by ring
      _ ≤ 8 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_low P B 3 (by norm_num) hP1 hB1)
  have e9 : 2 ^ (K + 1) * ((K + 1) * (8 * (a + b + c) + 8)) ≤ 16 * (P ^ 5 * B) := by
    calc 2 ^ (K + 1) * ((K + 1) * (8 * (a + b + c) + 8)) ≤ (2 * B) * (P * (8 * P)) := by
          gcongr <;> omega
      _ = 16 * (P ^ 2 * B) := by ring
      _ ≤ 16 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 2 (by norm_num) hP1)
  have e10 := fz6_tc a K (a + b + 2 * t + 1 + K) P B (by omega) hW (fz6_max a K B (by omega))
  have e11 := fz6_tc b K (a + b + 2 * t + 1 + K) P B (by omega) hW (fz6_max b K B (by omega))
  have e12 := fz6_tc c K (a + b + 2 * t + 1 + K) P B (by omega) hW (fz6_max c K B (by omega))
  have e13 : 2 ^ (K + 1) * (60 * (a + b + 2 * t + 1 + K + 1) ^ 2) ≤ 480 * (P ^ 5 * B) := by
    calc 2 ^ (K + 1) * (60 * (a + b + 2 * t + 1 + K + 1) ^ 2) ≤ (2 * B) * (60 * (2 * P) ^ 2) := by
          gcongr
      _ = 480 * (P ^ 2 * B) := by ring
      _ ≤ 480 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 2 (by norm_num) hP1)
  have e14 : 2 ^ (K + 1) ≤ 2 * (P ^ 5 * B) := by
    calc 2 ^ (K + 1) ≤ 2 * (P ^ 0 * B) := by simpa using hK2
      _ ≤ 2 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 0 (by norm_num) hP1)
  have e15 : 2 ^ c * (a + b + 2 * t + 1) * 16 ≤ 32 * (P ^ 5 * B) := by
    calc 2 ^ c * (a + b + 2 * t + 1) * 16 ≤ B * (2 * P) * 16 := by gcongr <;> omega
      _ = 32 * (P ^ 1 * B) := by ring
      _ ≤ 32 * (P ^ 5 * B) := Nat.mul_le_mul_left _ (fz6_lowB P B 1 (by norm_num) hP1)
  have e16 : 16 ≤ 16 * (P ^ 5 * B) :=
    Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.pos_of_ne_zero (by positivity)) hB1)
  norm_num at e4 e5 e6 e7 e10 e11 e12 ⊢
  omega

theorem topCost_le (a b c m t u : ℕ) :
    topCost a b c m t u + 1 ≤
      2 ^ 24 * (a + b + c + m + t + 3) ^ 12 * (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ (min (a + b + c) u)) := by
  have hK : Kof a b c u ≤ a + b + c := Nat.min_le_left _ _
  have hKd : min (a + b + c) u = Kof a b c u := rfl
  rw [hKd]
  have hm := fz6_main a b c m t (Kof a b c u) _ _ hK rfl rfl
  have hk0 : 0 < 2 ^ (Kof a b c u) := Nat.pos_of_ne_zero (by positivity)
  have hX : (a + b + c + m + t + 3) ^ 5 * (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ Kof a b c u) ≤
      (a + b + c + m + t + 3) ^ 12 * (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ Kof a b c u) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hX1 : 1 ≤ (a + b + c + m + t + 3) ^ 5 * (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ Kof a b c u) :=
    Nat.mul_pos (Nat.pos_of_ne_zero (by positivity)) (Nat.pos_of_ne_zero (by positivity))
  have hT : topSum a b c m t u ≤
      2 ^ 17 * ((a + b + c + m + t + 3) ^ 5 * (2 ^ a + 2 ^ b + 2 ^ c + 2 ^ Kof a b c u)) := by
    unfold topSum coreCost Wof
    exact hm
  unfold topCost
  rw [Nat.mul_assoc]
  norm_num at hT ⊢
  omega

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
  fun j => b2z (o (Sum.inr (Sum.inl j))) + ∑ t : Fin β, b2z (o (Sum.inl (j, t))) * x t

def glOk {N2 β : ℕ} (o : GlOut N2 β → Bool) (x : Fin β → ZMod 2) : Prop :=
  ∀ t : Fin β, o (Sum.inr (Sum.inr (Sum.inl t))) = false → x t = 0

def GlSpec (M N1 N2 β : ℕ)
    (F : (Fin M × Fin (N1+N2+1) → Bool) → GlOut N2 β → Bool)
    (nf : (Fin M × Fin (N1+N2+1) → Bool) → ℕ) : Prop :=
  ∀ Hb : Fin M × Fin (N1+N2+1) → Bool,
    (F Hb (Sum.inr (Sum.inr (Sum.inr ()))) = false → ∀ e, ¬ glSol M N1 N2 Hb e) ∧
    (F Hb (Sum.inr (Sum.inr (Sum.inr ()))) = true →
      Nat.card {e : Fin N2 → ZMod 2 // glSol M N1 N2 Hb e} = 2^(nf Hb) ∧
      (∀ t : Fin β, F Hb (Sum.inr (Sum.inr (Sum.inl t))) = true ↔ t.val < nf Hb) ∧
      (nf Hb ≤ β →
        (∀ x, glOk (F Hb) x → glSol M N1 N2 Hb (glPt (F Hb) x)) ∧
        (∀ e, glSol M N1 N2 Hb e → ∃ x, glOk (F Hb) x ∧ glPt (F Hb) x = e) ∧
        (∀ x x', glOk (F Hb) x → glOk (F Hb) x' → glPt (F Hb) x = glPt (F Hb) x' → x = x')))

def gl_P {n : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (e : Fin n → ZMod 2) : Prop :=
  ∀ j, fl j = false → e j = b2z (a j) + ∑ q, if fl q = true then b2z (G (j, q)) * e q else 0

def gl_A {n : ℕ} (β : ℕ) (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool) :
    GlOut n β → Bool :=
  Sum.elim (fun p => decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = p.2.val ∧
      xor (decide (p.1 = q)) (G (p.1, q)) = true))
    (Sum.elim a (Sum.elim (fun t => decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = t.val))
      (fun _ => c)))

def gl_xs {n β : ℕ} (fl : Fin n → Bool) (x : Fin β → ZMod 2) (q : Fin n) : ZMod 2 :=
  if h : cnt fl q.val < β then x ⟨_, h⟩ else 0

theorem gl_cnt_mono {n : ℕ} (fl : Fin n → Bool) (i i' : ℕ) (h : i ≤ i') : cnt fl i ≤ cnt fl i' := by
  unfold cnt
  apply Finset.card_le_card
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨h1, h2⟩
  exact ⟨by omega, h2⟩

theorem gl_cnt_lt {n : ℕ} (fl : Fin n → Bool) (q : Fin n) (hq : fl q = true) :
    cnt fl q.val < cnt fl n := by
  have h1 := cnt_succ fl q.val q.isLt
  rw [if_pos hq] at h1
  have h2 := gl_cnt_mono fl (q.val + 1) n q.isLt
  omega

theorem gl_cnt_inj {n : ℕ} (fl : Fin n → Bool) (q q' : Fin n) (hq : fl q = true)
    (hq' : fl q' = true) (h : cnt fl q.val = cnt fl q'.val) : q = q' := by
  by_contra hne
  have key : ∀ a b : Fin n, a < b → fl a = true → cnt fl a.val < cnt fl b.val := by
    intro a b hab ha
    have h1 := cnt_succ fl a.val a.isLt
    rw [if_pos ha] at h1
    have h2 := gl_cnt_mono fl (a.val + 1) b.val hab
    omega
  rcases lt_or_gt_of_ne hne with h1 | h1
  · have := key q q' h1 hq; omega
  · have := key q' q h1 hq'; omega

theorem gl_cnt_surj {n : ℕ} (fl : Fin n → Bool) : ∀ i, i ≤ n → ∀ t, t < cnt fl i →
    ∃ q : Fin n, q.val < i ∧ fl q = true ∧ cnt fl q.val = t := by
  intro i
  induction i with
  | zero => intro _ t ht; rw [cnt_zero] at ht; omega
  | succ i ih =>
    intro hi t ht
    rw [cnt_succ fl i hi] at ht
    by_cases h : t < cnt fl i
    · obtain ⟨q, h1, h2, h3⟩ := ih (by omega) t h
      exact ⟨q, by omega, h2, h3⟩
    · by_cases hf : fl ⟨i, hi⟩ = true
      · rw [if_pos hf] at ht
        exact ⟨⟨i, hi⟩, by simp, hf, by simp; omega⟩
      · rw [if_neg hf] at ht; omega

theorem gl_b2z_ex {n : ℕ} (fl : Fin n → Bool) (t : ℕ) (c : Fin n → Bool) :
    b2z (decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = t ∧ c q = true)) =
      ∑ q : Fin n, if (fl q = true ∧ cnt fl q.val = t) then b2z (c q) else 0 := by
  by_cases h : ∃ q : Fin n, fl q = true ∧ cnt fl q.val = t
  · obtain ⟨q0, h1, h2⟩ := h
    rw [Finset.sum_eq_single q0]
    · rw [if_pos ⟨h1, h2⟩]
      cases hc : c q0
      · have : ¬ ∃ q : Fin n, fl q = true ∧ cnt fl q.val = t ∧ c q = true := by
          rintro ⟨q, a1, a2, a3⟩
          have := gl_cnt_inj fl q q0 a1 h1 (a2.trans h2.symm)
          subst this
          rw [hc] at a3; exact Bool.false_ne_true a3
        simp [this, b2z]
      · have : ∃ q : Fin n, fl q = true ∧ cnt fl q.val = t ∧ c q = true := ⟨q0, h1, h2, hc⟩
        simp [this, b2z]
    · intro q _ hq
      rw [if_neg]
      rintro ⟨a1, a2⟩
      exact hq (gl_cnt_inj fl q q0 a1 h1 (a2.trans h2.symm))
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · have h' : ¬ ∃ q : Fin n, fl q = true ∧ cnt fl q.val = t ∧ c q = true := by
      rintro ⟨q, a1, a2, _⟩; exact h ⟨q, a1, a2⟩
    rw [decide_eq_false h']
    symm
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨a1, a2⟩; exact h ⟨q, a1, a2⟩

theorem gl_pt {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) (j : Fin n) :
    glPt (gl_A β fl a G c) x j = b2z (a j) +
      ∑ q, if fl q = true then b2z (xor (decide (j = q)) (G (j, q))) * gl_xs fl x q else 0 := by
  unfold glPt
  simp only [gl_A, Sum.elim_inl, Sum.elim_inr]
  congr 1
  have e1 : ∀ t : Fin β, b2z (decide (∃ q : Fin n, fl q = true ∧ cnt fl q.val = t.val ∧
      xor (decide (j = q)) (G (j, q)) = true)) * x t =
      ∑ q : Fin n, (if (fl q = true ∧ cnt fl q.val = t.val) then
        b2z (xor (decide (j = q)) (G (j, q))) else 0) * x t := by
    intro t
    rw [gl_b2z_ex fl t.val (fun q => xor (decide (j = q)) (G (j, q))), Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun t _ => e1 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : fl q = true
  · rw [if_pos hq]
    have hlt : cnt fl q.val < β := lt_of_lt_of_le (gl_cnt_lt fl q hq) hβ
    rw [Finset.sum_eq_single (⟨cnt fl q.val, hlt⟩ : Fin β)]
    · rw [if_pos ⟨hq, rfl⟩]
      simp [gl_xs, hlt]
    · intro t _ ht
      rw [if_neg, zero_mul]
      rintro ⟨_, a2⟩
      exact ht (Fin.ext a2.symm)
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [if_neg hq]
    apply Finset.sum_eq_zero
    intro t _
    rw [if_neg (fun hh => hq hh.1), zero_mul]

theorem gl_pt_free {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) (j : Fin n) (hj : fl j = true) :
    glPt (gl_A β fl a G c) x j = gl_xs fl x j := by
  rw [gl_pt fl a G c hβ x j, (hz j hj).1]
  rw [Finset.sum_eq_single j]
  · rw [if_pos hj, (hz j hj).2 j]
    simp [b2z]
  · intro q _ hq
    by_cases hf : fl q = true
    · rw [if_pos hf, (hz j hj).2 q]
      have : decide (j = q) = false := decide_eq_false (fun h => hq h.symm)
      simp [this, b2z]
    · rw [if_neg hf]
  · intro hh; exact absurd (Finset.mem_univ _) hh

theorem gl_pt_piv {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hβ : cnt fl n ≤ β) (x : Fin β → ZMod 2) (j : Fin n) (hj : fl j = false) :
    glPt (gl_A β fl a G c) x j = b2z (a j) +
      ∑ q, if fl q = true then b2z (G (j, q)) * gl_xs fl x q else 0 := by
  rw [gl_pt fl a G c hβ x j]
  congr 1
  apply Finset.sum_congr rfl
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
  apply Finset.sum_congr rfl
  intro q _
  by_cases hf : fl q = true
  · rw [if_pos hf, if_pos hf, gl_pt_free fl a G c hz hβ x q hf]
  · rw [if_neg hf, if_neg hf]

theorem gl_A_inj {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (x x' : Fin β → ZMod 2)
    (hx : glOk (gl_A β fl a G c) x) (hx' : glOk (gl_A β fl a G c) x')
    (h : glPt (gl_A β fl a G c) x = glPt (gl_A β fl a G c) x') : x = x' := by
  funext t
  by_cases hu : ∃ q : Fin n, fl q = true ∧ cnt fl q.val = t.val
  · obtain ⟨q, h1, h2⟩ := hu
    have e1 := gl_pt_free fl a G c hz hβ x q h1
    have e2 := gl_pt_free fl a G c hz hβ x' q h1
    rw [h] at e1
    have e3 : gl_xs fl x q = gl_xs fl x' q := e1.symm.trans e2
    have hlt : cnt fl q.val < β := by rw [h2]; exact t.isLt
    have ht : (⟨cnt fl q.val, hlt⟩ : Fin β) = t := Fin.ext h2
    simpa [gl_xs, hlt, ht] using e3
  · have u : gl_A β fl a G c (Sum.inr (Sum.inr (Sum.inl t))) = false := by
      simp only [gl_A, Sum.elim_inr, Sum.elim_inl]
      exact decide_eq_false hu
    rw [hx t u, hx' t u]

theorem gl_A_surj {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (hz : ∀ q, fl q = true → a q = false ∧ ∀ q', G (q, q') = false)
    (hβ : cnt fl n ≤ β) (e : Fin n → ZMod 2) (he : gl_P fl a G e) :
    ∃ x, glOk (gl_A β fl a G c) x ∧ glPt (gl_A β fl a G c) x = e := by
  refine ⟨fun t => ∑ q : Fin n, if (fl q = true ∧ cnt fl q.val = t.val) then e q else 0, ?_, ?_⟩
  · intro t ht
    simp only [gl_A, Sum.elim_inr, Sum.elim_inl, decide_eq_false_iff_not] at ht
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    rintro ⟨a1, a2⟩; exact ht ⟨q, a1, a2⟩
  · have hxs : ∀ q, fl q = true → gl_xs fl (fun t : Fin β => ∑ q : Fin n,
        if (fl q = true ∧ cnt fl q.val = t.val) then e q else 0) q = e q := by
      intro q hq
      have hlt : cnt fl q.val < β := lt_of_lt_of_le (gl_cnt_lt fl q hq) hβ
      simp only [gl_xs, hlt, dif_pos]
      rw [Finset.sum_eq_single q]
      · rw [if_pos ⟨hq, rfl⟩]
      · intro q' _ hne
        rw [if_neg]
        rintro ⟨a1, a2⟩
        exact hne (gl_cnt_inj fl q' q a1 hq a2)
      · intro hh; exact absurd (Finset.mem_univ _) hh
    funext j
    by_cases hj : fl j = true
    · rw [gl_pt_free fl a G c hz hβ _ j hj, hxs j hj]
    · have hj' : fl j = false := by simpa using hj
      rw [gl_pt_piv fl a G c hβ _ j hj', he j hj']
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      by_cases hf : fl q = true
      · rw [if_pos hf, if_pos hf, hxs q hf]
      · rw [if_neg hf, if_neg hf]

theorem gl_A_used {n β : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) (c : Bool)
    (t : Fin β) : gl_A β fl a G c (Sum.inr (Sum.inr (Sum.inl t))) = true ↔ t.val < cnt fl n := by
  simp only [gl_A, Sum.elim_inr, Sum.elim_inl, decide_eq_true_eq]
  constructor
  · rintro ⟨q, h1, h2⟩
    rw [← h2]; exact gl_cnt_lt fl q h1
  · intro h
    obtain ⟨q, _, h2, h3⟩ := gl_cnt_surj fl n le_rfl t.val h
    exact ⟨q, h2, h3⟩

theorem gl_P_card {n : ℕ} (fl a : Fin n → Bool) (G : Fin n × Fin n → Bool) :
    Nat.card {e : Fin n → ZMod 2 // gl_P fl a G e} = 2 ^ (cnt fl n) := by
  have hcard : Fintype.card {q : Fin n // fl q = true} = cnt fl n := by
    rw [Fintype.card_subtype]; unfold cnt; congr 1; ext q; simp
  have hext : ∀ g : {q : Fin n // fl q = true} → ZMod 2, gl_P fl a G (fun j =>
      if h : fl j = true then g ⟨j, h⟩ else b2z (a j) +
        ∑ q, if h : fl q = true then b2z (G (j, q)) * g ⟨q, h⟩ else 0) := by
    intro g j hj
    have hj' : ¬ fl j = true := by rw [hj]; exact Bool.false_ne_true
    simp only [dif_neg hj']
    congr 1
    apply Finset.sum_congr rfl
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
            apply Finset.sum_congr rfl
            intro q _
            by_cases hf : fl q = true
            · rw [if_pos hf, dif_pos hf]
            · rw [if_neg hf, dif_neg hf])
      right_inv := by
        intro g
        funext q
        simp only [dif_pos q.2] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, hcard]

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
    apply Finset.sum_eq_zero
    intro q _
    by_cases h : pv R (Fin.castAdd N2 q) = false
    · rw [if_pos h, Fin.append_left]
      rcases hc0 q h with h0 | h0
      · rw [h0, mul_zero]
      · simp [mat, h0]
    · rw [if_neg h]
  rw [h1, zero_add]
  apply Finset.sum_congr rfl
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
  Sum.elim R (fun p => decide (cnt (gl_fl R) p.1.val = p.2.val))

def gl_Psi {M N1 N2 : ℕ} (β : ℕ) (w : gl_B M N1 N2 β → Bool) : GlOut N2 β → Bool :=
  Sum.elim (fun p => decide (∃ q : Fin N2, ((!w (Sum.inl (gl_vc M N1 q, gl_vc M N1 q))) &&
      w (Sum.inr (⟨q.val, by omega⟩, ⟨p.2.val, by omega⟩)) &&
      xor (decide (p.1 = q)) (w (Sum.inl (gl_vc M N1 p.1, gl_vc M N1 q)))) = true))
    (Sum.elim (fun j => w (Sum.inl (gl_vc M N1 j, rc M (N1+N2))))
      (Sum.elim (fun t => decide (∃ q : Fin N2, ((!w (Sum.inl (gl_vc M N1 q, gl_vc M N1 q))) &&
        w (Sum.inr (⟨q.val, by omega⟩, ⟨t.val, by omega⟩))) = true))
      (fun _ => !w (Sum.inl (rc M (N1+N2), rc M (N1+N2))))))

theorem gl_Psi_eq {M N1 N2 : ℕ} (β : ℕ)
    (R : Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1) → Bool) :
    gl_Psi β (gl_blk β R) = gl_O β R := by
  funext k
  rcases k with p | j | t | u
  · simp only [gl_Psi, gl_blk, gl_O, gl_A, Sum.elim_inl, Sum.elim_inr]
    refine decide_eq_decide.mpr (exists_congr fun q => ?_)
    simp [gl_fl, and_assoc]
  · rfl
  · simp only [gl_Psi, gl_blk, gl_O, gl_A, Sum.elim_inl, Sum.elim_inr]
    refine decide_eq_decide.mpr (exists_congr fun q => ?_)
    simp [gl_fl]
  · rfl

theorem gl_xbit (M N1 N2 β : ℕ) (j q : Fin N2) :
    Cb (gl_B M N1 N2 β) 1
      (fun w => xor (decide (j = q)) (w (Sum.inl (gl_vc M N1 j, gl_vc M N1 q)))) := by
  by_cases h : j = q
  · refine ((Cb.not (Cb.var (Sum.inl (gl_vc M N1 j, gl_vc M N1 q)))).mono (by norm_num)).congr ?_
    intro w; simp [h]
  · refine ((Cb.var (Sum.inl (gl_vc M N1 j, gl_vc M N1 q))).mono (by norm_num)).congr ?_
    intro w; simp [h]

theorem gl_Psi_cb (M N1 N2 β : ℕ) (k : GlOut N2 β) :
    Cb (gl_B M N1 N2 β) (N2 * 5 + 1) (fun w => gl_Psi β w k) := by
  rcases k with p | j | t | u
  · have := Cb.bigOr (ι := gl_B M N1 N2 β) (I := Fin N2)
      (φ := fun q w => ((!w (Sum.inl (gl_vc M N1 q, gl_vc M N1 q))) &&
        w (Sum.inr (⟨q.val, by omega⟩, ⟨p.2.val, by omega⟩)) &&
        xor (decide (p.1 = q)) (w (Sum.inl (gl_vc M N1 p.1, gl_vc M N1 q)))))
      (fun q => (Cb.and (Cb.and (Cb.not (Cb.var _)) (Cb.var _)) (gl_xbit M N1 N2 β p.1 q)))
    rw [Fintype.card_fin] at this
    exact (this.mono (by norm_num)).congr (fun w => decide_eq_decide.mpr Iff.rfl)
  · exact (Cb.var (Sum.inl (gl_vc M N1 j, rc M (N1+N2)))).mono (by omega)
  · have := Cb.bigOr (ι := gl_B M N1 N2 β) (I := Fin N2)
      (φ := fun q w => ((!w (Sum.inl (gl_vc M N1 q, gl_vc M N1 q))) &&
        w (Sum.inr (⟨q.val, by omega⟩, ⟨t.val, by omega⟩))))
      (fun q => (Cb.and (Cb.not (Cb.var _)) (Cb.var _)))
    rw [Fintype.card_fin] at this
    exact (this.mono (by omega)).congr (fun w => decide_eq_decide.mpr Iff.rfl)
  · exact (Cb.not (Cb.var (Sum.inl (rc M (N1+N2), rc M (N1+N2))))).mono (by omega)

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
        (Fintype.card (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) * 1) gl_mat :=
      Cmp.ofBits (fun p => gl_mat_cb M N1 N2 p)
    have c2 := cmp_gj (M + (N1+N2) + 1)
    have hn : Cmp (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) (Fin N2)
        (Fintype.card (Fin N2) * (0 + 1)) (fun R q => gl_fl R q) :=
      Cmp.ofBits (fun q => Cb.not (Cb.var (gl_vc M N1 q, gl_vc M N1 q)))
    have c3 := Cmp.pair (Cmp.wire (ι := Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) id)
      (Cmp.comp hn (cmp_counter N2 β))
    have c3' : Cmp (Fin (M + (N1+N2) + 1) × Fin (M + (N1+N2) + 1)) (gl_B M N1 N2 β) _
        (gl_blk β) := Cmp.congr c3 (by intro R k; rcases k with k | k <;> rfl)
    have c4 : Cmp (gl_B M N1 N2 β) (GlOut N2 β) (Fintype.card (GlOut N2 β) * (N2 * 5 + 1))
        (gl_Psi β) := Cmp.ofBits (fun k => gl_Psi_cb M N1 N2 β k)
    have call := ((c1.comp c2).comp c3').comp c4
    refine Cmp.mono (Cmp.congr call ?_) ?_
    · intro Hb k
      show gl_Psi β (gl_blk β (gj _ (gl_mat Hb))) k = _
      rw [gl_Psi_eq]
    · simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
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
    (∑ j : ι1, b2z (Hb (i, Sum.inl j)) * c j) +
    (∑ j : ι2, b2z (Hb (i, Sum.inr (Sum.inl j))) * e j) = b2z (Hb (i, Sum.inr (Sum.inr ())))

abbrev SOut (ι2 : Type) (β : ℕ) : Type := (ι2 × Fin β) ⊕ (ι2 ⊕ (Fin β ⊕ Unit))

def sPt {ι2 : Type} {β : ℕ} (o : SOut ι2 β → Bool) (x : Fin β → ZMod 2) : ι2 → ZMod 2 :=
  fun j => b2z (o (Sum.inr (Sum.inl j))) + ∑ t : Fin β, b2z (o (Sum.inl (j, t))) * x t

def sOk {ι2 : Type} {β : ℕ} (o : SOut ι2 β → Bool) (x : Fin β → ZMod 2) : Prop :=
  ∀ t : Fin β, o (Sum.inr (Sum.inr (Sum.inl t))) = false → x t = 0

def SSpec (ρ ι1 ι2 : Type) [Fintype ι1] [Fintype ι2] (β : ℕ)
    (F : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → SOut ι2 β → Bool)
    (nf : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → ℕ) : Prop :=
  ∀ Hb : ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool,
    (F Hb (Sum.inr (Sum.inr (Sum.inr ()))) = false → ∀ e, ¬ solS Hb e) ∧
    (F Hb (Sum.inr (Sum.inr (Sum.inr ()))) = true →
      Nat.card {e : ι2 → ZMod 2 // solS Hb e} = 2^(nf Hb) ∧
      (∀ t : Fin β, F Hb (Sum.inr (Sum.inr (Sum.inl t))) = true ↔ t.val < nf Hb) ∧
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

theorem st_count {m N : ℕ} (Hf : Fin m → V N) (rhs : Fin m → ZMod 2) :
    Nat.card {v : V N // ∀ i, Hf i ⬝ᵥ v = rhs i} =
      (if (!(gj _ (sysBits Hf rhs) (rc m N, rc m N))) = true then
        2 ^ (Finset.univ.filter (fun p : Fin N =>
          (!(gj _ (sysBits Hf rhs) (cl m p, cl m p))) = true)).card else 0) := by
  by_cases hc : gj _ (sysBits Hf rhs) (rc m N, rc m N) = true
  · have : IsEmpty {v : V N // ∀ i, Hf i ⬝ᵥ v = rhs i} :=
      ⟨fun v => la_incons Hf rhs hc v.1 v.2⟩
    rw [Nat.card_of_isEmpty, hc]; simp
  · have hc' : gj _ (sysBits Hf rhs) (rc m N, rc m N) = false := by simpa using hc
    have key := fh_main_iff Hf rhs hc'
    rw [hc']
    simp only [Bool.not_false, if_true]
    generalize gj _ (sysBits Hf rhs) = R at key
    let e : {v : V N // ∀ i, Hf i ⬝ᵥ v = rhs i} ≃ ({q : Fin N // pv R q = false} → ZMod 2) :=
      { toFun := fun v q => v.1 q.1
        invFun := fun f => ⟨fun p => if h : pv R p = false then f ⟨p, h⟩ else
            mat R (cl m p) (rc m N) +
              ∑ q, if h : pv R q = false then mat R (cl m p) (cl m q) * f ⟨q, h⟩ else 0, by
          rw [key]; intro p hp
          rw [dif_neg (by simp [hp])]
          congr 1
          apply Finset.sum_congr rfl; intro q _
          by_cases hq : pv R q = false
          · rw [dif_pos hq, if_pos hq, dif_pos hq]
          · rw [dif_neg hq, if_neg hq]⟩
        left_inv := by
          intro v; apply Subtype.ext; funext p
          by_cases hp : pv R p = false
          · simp [hp]
          · have := (key v.1).1 v.2 p (by simpa using hp)
            show (if h : pv R p = false then _ else _) = v.1 p
            rw [dif_neg hp]
            refine Eq.trans ?_ this.symm
            congr 1
        right_inv := by intro f; funext q; simp [q.2] }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_subtype]
    congr 2

theorem st_hom_rank {m N : ℕ} (Hf : Fin m → V N) :
    Nat.card {v : V N // ∀ i, Hf i ⬝ᵥ v = 0} =
      2 ^ (N - rkOf (gj _ (sysBits Hf (fun _ => 0)))) := by
  have sc := st_count Hf (fun _ => 0)
  have hc : gj _ (sysBits Hf (fun _ => 0)) (rc m N, rc m N) = false := by
    by_contra h
    exact la_incons Hf (fun _ => 0) (by simpa using h) 0 (fun i => by simp)
  rw [hc] at sc
  simp only [Bool.not_false, if_true] at sc
  rw [sc]
  congr 1
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun q : Fin N => pv (gj _ (sysBits Hf (fun _ => 0))) q = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have e : (Finset.univ.filter (fun p : Fin N =>
      (!(gj _ (sysBits Hf (fun _ => 0)) (cl m p, cl m p))) = true)) =
      (Finset.univ.filter (fun q : Fin N => ¬ pv (gj _ (sysBits Hf (fun _ => 0))) q = true)) := by
    apply Finset.filter_congr
    intro q _
    simp [pv]
  rw [e]
  unfold rkOf
  omega

theorem glS (ρ ι1 ι2 : Type) [Fintype ρ] [Fintype ι1] [Fintype ι2] (β : ℕ) :
    ∃ (F : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → SOut ι2 β → Bool)
      (nf : (ρ × (ι1 ⊕ (ι2 ⊕ Unit)) → Bool) → ℕ),
      Cmp (ρ × (ι1 ⊕ (ι2 ⊕ Unit))) (SOut ι2 β)
        (glCost (Fintype.card ρ) (Fintype.card ι1) (Fintype.card ι2) β) F ∧
      SSpec ρ ι1 ι2 β F nf := by
  classical
  obtain ⟨F0, nf0, hC, hS⟩ :=
    gl_main (Fintype.card ρ) (Fintype.card ι1) (Fintype.card ι2) β
  let eρ := Fintype.equivFin ρ
  let e1 := Fintype.equivFin ι1
  let e2 := Fintype.equivFin ι2
  let col : Fin (Fintype.card ι1 + Fintype.card ι2 + 1) → ι1 ⊕ (ι2 ⊕ Unit) := fun j =>
    if h : j.val < Fintype.card ι1 then Sum.inl (e1.symm ⟨j.val, h⟩)
    else if h2 : j.val < Fintype.card ι1 + Fintype.card ι2 then
      Sum.inr (Sum.inl (e2.symm ⟨j.val - Fintype.card ι1, by omega⟩))
    else Sum.inr (Sum.inr ())
  let σ : Fin (Fintype.card ρ) × Fin (Fintype.card ι1 + Fintype.card ι2 + 1) →
      ρ × (ι1 ⊕ (ι2 ⊕ Unit)) := fun p => (eρ.symm p.1, col p.2)
  let om : SOut ι2 β → GlOut (Fintype.card ι2) β :=
    Sum.elim (fun p => Sum.inl (e2 p.1, p.2))
      (Sum.elim (fun j => Sum.inr (Sum.inl (e2 j))) (fun x => Sum.inr (Sum.inr x)))
  have hcol1 : ∀ (j : Fin (Fintype.card ι1)) (h : j.val < Fintype.card ι1 + Fintype.card ι2 + 1),
      col ⟨j.val, h⟩ = Sum.inl (e1.symm j) := by
    intro j h
    simp [col, j.isLt]
  have hcol2 : ∀ (j : Fin (Fintype.card ι2))
      (h : Fintype.card ι1 + j.val < Fintype.card ι1 + Fintype.card ι2 + 1),
      col ⟨Fintype.card ι1 + j.val, h⟩ = Sum.inr (Sum.inl (e2.symm j)) := by
    intro j h
    simp [col, j.isLt]
  have hcol3 : ∀ (h : Fintype.card ι1 + Fintype.card ι2 < Fintype.card ι1 + Fintype.card ι2 + 1),
      col ⟨Fintype.card ι1 + Fintype.card ι2, h⟩ = Sum.inr (Sum.inr ()) := by
    intro h
    simp [col]
  refine ⟨fun Hb o => F0 (fun p => Hb (σ p)) (om o), fun Hb => nf0 (fun p => Hb (σ p)), ?_, ?_⟩
  · exact (Cmp.comp (Cmp.sel σ hC) (Cmp.wire om)).mono (by omega)
  · intro Hb
    have hs1 : ∀ (i : Fin (Fintype.card ρ)) (c' : Fin (Fintype.card ι1) → ZMod 2),
        (∑ j : ι1, b2z (Hb (eρ.symm i, Sum.inl j)) * c' (e1 j)) =
        ∑ j : Fin (Fintype.card ι1), b2z (Hb (σ (i, ⟨j.val, by omega⟩))) * c' j := by
      intro i c'
      rw [← Equiv.sum_comp e1 (fun j : Fin (Fintype.card ι1) =>
        b2z (Hb (σ (i, ⟨j.val, by omega⟩))) * c' j)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [σ]
      rw [hcol1]
      simp
    have hs2 : ∀ (i : Fin (Fintype.card ρ)) (e' : Fin (Fintype.card ι2) → ZMod 2),
        (∑ j : ι2, b2z (Hb (eρ.symm i, Sum.inr (Sum.inl j))) * e' (e2 j)) =
        ∑ j : Fin (Fintype.card ι2),
          b2z (Hb (σ (i, ⟨Fintype.card ι1 + j.val, by omega⟩))) * e' j := by
      intro i e'
      rw [← Equiv.sum_comp e2 (fun j : Fin (Fintype.card ι2) =>
        b2z (Hb (σ (i, ⟨Fintype.card ι1 + j.val, by omega⟩))) * e' j)]
      apply Finset.sum_congr rfl
      intro j _
      simp only [σ]
      rw [hcol2]
      simp
    have hs3 : ∀ (i : Fin (Fintype.card ρ)),
        b2z (Hb (σ (i, ⟨Fintype.card ι1 + Fintype.card ι2, by omega⟩))) =
          b2z (Hb (eρ.symm i, Sum.inr (Sum.inr ()))) := by
      intro i
      simp only [σ]
      rw [hcol3]
    have key : ∀ e' : Fin (Fintype.card ι2) → ZMod 2,
        solS Hb (fun j => e' (e2 j)) ↔
          glSol (Fintype.card ρ) (Fintype.card ι1) (Fintype.card ι2) (fun p => Hb (σ p)) e' := by
      intro e'
      constructor
      · rintro ⟨c, hc⟩
        refine ⟨fun j => c (e1.symm j), fun i => ?_⟩
        have h := hc (eρ.symm i)
        rw [← hs1 i (fun j => c (e1.symm j)), ← hs2 i e', hs3]
        simpa using h
      · rintro ⟨c', hc⟩
        refine ⟨fun j => c' (e1 j), fun i => ?_⟩
        have h := hc (eρ i)
        rw [← hs1, ← hs2, hs3] at h
        simpa using h
    have key2 : ∀ e : ι2 → ZMod 2,
        solS Hb e ↔ glSol (Fintype.card ρ) (Fintype.card ι1) (Fintype.card ι2)
          (fun p => Hb (σ p)) (fun j => e (e2.symm j)) := by
      intro e
      rw [← key]
      simp
    have hpt : ∀ x : Fin β → ZMod 2,
        sPt (fun o => F0 (fun p => Hb (σ p)) (om o)) x =
          fun j => glPt (F0 (fun p => Hb (σ p))) x (e2 j) := by
      intro x
      rfl
    have hok : ∀ x : Fin β → ZMod 2,
        sOk (fun o => F0 (fun p => Hb (σ p)) (om o)) x ↔ glOk (F0 (fun p => Hb (σ p))) x := by
      intro x
      exact Iff.rfl
    obtain ⟨g1, g2⟩ := hS (fun p => Hb (σ p))
    refine ⟨?_, ?_⟩
    · intro h e he
      exact g1 h _ ((key2 e).1 he)
    · intro h
      obtain ⟨c1, c2, c3⟩ := g2 h
      refine ⟨?_, c2, ?_⟩
      · rw [← c1]
        refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr e2 (Equiv.refl _)) ?_)
        intro e
        exact key2 e
      · intro hnf
        obtain ⟨d1, d2, d3⟩ := c3 hnf
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          rw [hpt]
          exact (key _).2 (d1 x ((hok x).1 hx))
        · intro e he
          obtain ⟨x, hx, hxe⟩ := d2 _ ((key2 e).1 he)
          refine ⟨x, (hok x).2 hx, ?_⟩
          rw [hpt, hxe]
          funext j
          simp
        · intro x x' hx hx' hxx
          apply d3 x x' ((hok x).1 hx) ((hok x').1 hx')
          rw [hpt, hpt] at hxx
          funext j
          have := congrFun hxx (e2.symm j)
          simpa using this

abbrev JIn (ρ : Type) (a bb c t : ℕ) : Type :=
  (ρ × (Fin a ⊕ (Fin bb ⊕ (Fin c ⊕ Unit)))) ⊕ ((Fin (2^a) × Fin t) ⊕ (Fin (2^bb) × Fin t))

def jSat {ρ : Type} {a bb c t : ℕ} (v : JIn ρ a bb c t → Bool)
    (x : Fin a → ZMod 2) (y : Fin bb → ZMod 2) (z : Fin c → ZMod 2) : Prop :=
  ∀ i : ρ, (∑ j : Fin a, b2z (v (Sum.inl (i, Sum.inl j))) * x j) +
    (∑ j : Fin bb, b2z (v (Sum.inl (i, Sum.inr (Sum.inl j)))) * y j) +
    (∑ j : Fin c, b2z (v (Sum.inl (i, Sum.inr (Sum.inr (Sum.inl j))))) * z j) =
      b2z (v (Sum.inl (i, Sum.inr (Sum.inr (Sum.inr ())))))

def jHom {ρ : Type} {a bb c t : ℕ} (v : JIn ρ a bb c t → Bool)
    (x : Fin a → ZMod 2) (y : Fin bb → ZMod 2) (z : Fin c → ZMod 2) : Prop :=
  ∀ i : ρ, (∑ j : Fin a, b2z (v (Sum.inl (i, Sum.inl j))) * x j) +
    (∑ j : Fin bb, b2z (v (Sum.inl (i, Sum.inr (Sum.inl j)))) * y j) +
    (∑ j : Fin c, b2z (v (Sum.inl (i, Sum.inr (Sum.inr (Sum.inl j))))) * z j) = 0

noncomputable def jTot {ρ : Type} {a bb c t : ℕ} (v : JIn ρ a bb c t → Bool)
    (iz : Fin (2^c)) : ℕ :=
  ∑ ix : Fin (2^a), ∑ iy : Fin (2^bb),
    @ite ℕ (jSat v (vecN a ix.val) (vecN bb iy.val) (vecN c iz.val)) (Classical.propDecidable _)
      (tabN (fun j => v (Sum.inr (Sum.inl (ix, j)))) * tabN (fun j => v (Sum.inr (Sum.inr (iy, j)))))
      0


theorem joinAll (ρ : Type) [Fintype ρ] (a bb c t : ℕ) :
    let u := (a + bb + c) / 2
    ∃ F : (JIn ρ a bb c t → Bool) → (Fin (2^c) × Fin t → Bool),
      Cmp (JIn ρ a bb c t) (Fin (2^c) × Fin t) (topCost a bb c (Fintype.card ρ) t u) F ∧
      ∀ v : JIn ρ a bb c t → Bool,
        ∀ (iz : Fin (2^c)) (j : Fin t), F v (iz, j) = (jTot v iz).testBit j.val := by
  intro u
  classical
  let eρ := Fintype.equivFin ρ
  obtain ⟨ea, hea⟩ := vecEquiv_exists a
  obtain ⟨eb, heb⟩ := vecEquiv_exists bb
  obtain ⟨ec, hec⟩ := vecEquiv_exists c
  let colJ : Fin (a + bb + c + 1) → Fin a ⊕ (Fin bb ⊕ (Fin c ⊕ Unit)) := fun j =>
    if h : j.val < a then Sum.inl ⟨j.val, h⟩
    else if h2 : j.val < a + bb then Sum.inr (Sum.inl ⟨j.val - a, by omega⟩)
    else if h3 : j.val < a + bb + c then Sum.inr (Sum.inr (Sum.inl ⟨j.val - (a + bb), by omega⟩))
    else Sum.inr (Sum.inr (Sum.inr ()))
  let σ : In0 a bb c (Fintype.card ρ) t → JIn ρ a bb c t :=
    Sum.elim (fun p => Sum.inl (eρ.symm p.1, colJ p.2)) Sum.inr
  let om : Fin (2^c) × Fin t → Unit ⊕ (Fin (2^c) × Fin (a + bb + 2 * t + 1)) :=
    fun p => Sum.inr (p.1, ⟨p.2.val, by have := p.2.isLt; omega⟩)
  refine ⟨fun v p => topF a bb c (Fintype.card ρ) t u ea eb ec (fun j => v (σ j)) (om p), ?_, ?_⟩
  · exact (Cmp.comp (Cmp.sel σ (cmp_top a bb c (Fintype.card ρ) t u ea eb ec))
      (Cmp.wire om)).mono (by omega)
  · intro v iz j
    let H : Fin (Fintype.card ρ) → V a × V bb × V c := fun i =>
      (fun j => b2z (v (Sum.inl (eρ.symm i, Sum.inl j))),
       fun j => b2z (v (Sum.inl (eρ.symm i, Sum.inr (Sum.inl j)))),
       fun j => b2z (v (Sum.inl (eρ.symm i, Sum.inr (Sum.inr (Sum.inl j))))))
    let rhs : Fin (Fintype.card ρ) → ZMod 2 := fun i =>
      b2z (v (Sum.inl (eρ.symm i, Sum.inr (Sum.inr (Sum.inr ())))))
    let f : Fin (2^a) → Fin (2^t) := fun ix =>
      ⟨tabN (fun j => v (Sum.inr (Sum.inl (ix, j)))), st_tabN_lt _⟩
    let g : Fin (2^bb) → Fin (2^t) := fun iy =>
      ⟨tabN (fun j => v (Sum.inr (Sum.inr (iy, j)))), st_tabN_lt _⟩
    have hin : (fun j => v (σ j)) = inpOf H rhs f g := by
      funext q
      rcases q with p | p | p
      · show v (Sum.inl (eρ.symm p.1, colJ p.2)) =
          if h : p.2.val < a + bb + c then decide (join3 (H p.1) ⟨p.2.val, h⟩ ≠ 0)
          else decide (rhs p.1 ≠ 0)
        by_cases h1 : p.2.val < a
        · have h : p.2.val < a + bb + c := by omega
          rw [dif_pos h]
          have e1 : colJ p.2 = Sum.inl ⟨p.2.val, h1⟩ := by simp [colJ, h1]
          have e2 : join3 (H p.1) ⟨p.2.val, h⟩ = (H p.1).1 ⟨p.2.val, h1⟩ := by
            simp [join3, h1]
          rw [e1, e2, st_dec_b2z]
        · by_cases h2 : p.2.val < a + bb
          · have h : p.2.val < a + bb + c := by omega
            rw [dif_pos h]
            have e1 : colJ p.2 = Sum.inr (Sum.inl ⟨p.2.val - a, by omega⟩) := by
              simp [colJ, h1, h2]
            have e2 : join3 (H p.1) ⟨p.2.val, h⟩ = (H p.1).2.1 ⟨p.2.val - a, by omega⟩ := by
              simp [join3, h1, h2]
            rw [e1, e2, st_dec_b2z]
          · by_cases h3 : p.2.val < a + bb + c
            · rw [dif_pos h3]
              have e1 : colJ p.2 =
                  Sum.inr (Sum.inr (Sum.inl ⟨p.2.val - (a + bb), by omega⟩)) := by
                simp [colJ, h1, h2, h3]
              have e2 : join3 (H p.1) ⟨p.2.val, h3⟩ =
                  (H p.1).2.2 ⟨p.2.val - (a + bb), by omega⟩ := by
                simp [join3, h1, h2]
              rw [e1, e2, st_dec_b2z]
            · rw [dif_neg h3]
              have e1 : colJ p.2 = Sum.inr (Sum.inr (Sum.inr ())) := by
                simp [colJ, h1, h2, h3]
              rw [e1, st_dec_b2z]
      · show v (Sum.inr (Sum.inl p)) = (f p.1).val.testBit p.2.val
        exact (st_tabN_testBit (fun j => v (Sum.inr (Sum.inl (p.1, j)))) p.2).symm
      · show v (Sum.inr (Sum.inr p)) = (g p.1).val.testBit p.2.val
        exact (st_tabN_testBit (fun j => v (Sum.inr (Sum.inr (p.1, j)))) p.2).symm
    obtain ⟨k1, k2⟩ := top_sem a bb c (Fintype.card ρ) t u ea eb ec hea heb hec H rhs f g
    have hguard : min (Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H)))
        (a + bb + c - Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range H))) ≤ u := by
      dsimp [u]
      omega
    have hflag := k1.2 hguard
    show topF a bb c (Fintype.card ρ) t u ea eb ec (fun j => v (σ j))
      (Sum.inr (iz, ⟨j.val, _⟩)) = _
    rw [hin, k2 iz ⟨j.val, by have := j.isLt; omega⟩, if_pos hflag]
    congr 1
    unfold jTot
    apply Finset.sum_congr rfl
    intro ix _
    apply Finset.sum_congr rfl
    intro iy _
    have hiff : (∀ i, (H i).1 ⬝ᵥ (fun j : Fin a => if ix.val.testBit j.val then (1 : ZMod 2) else 0) +
        (H i).2.1 ⬝ᵥ (fun j : Fin bb => if iy.val.testBit j.val then (1 : ZMod 2) else 0) +
        (H i).2.2 ⬝ᵥ (fun j : Fin c => if iz.val.testBit j.val then (1 : ZMod 2) else 0) = rhs i) ↔
        jSat v (vecN a ix.val) (vecN bb iy.val) (vecN c iz.val) := by
      constructor
      · intro h i
        have := h (eρ i)
        simp only [H, rhs, dotProduct, Equiv.symm_apply_apply] at this
        exact this
      · intro h i
        exact h (eρ.symm i)
    by_cases hs : jSat v (vecN a ix.val) (vecN bb iy.val) (vecN c iz.val)
    · rw [if_pos (hiff.2 hs), if_pos hs]
    · rw [if_neg (fun h => hs (hiff.1 h)), if_neg hs]

end PEqualNP.Outside.L_meta_29751.Donor


namespace PEqualNP.Outside.L_meta_29751

open Donor

abbrev ProjIn (ρ α β : Type) := ρ × (α ⊕ (β ⊕ Unit))

def zbit (a : F) : Bool := decide (a ≠ 0)

lemma zbit_decode (a : F) : b2z (zbit a) = a := by
  rcases ffCases a with rfl | rfl <;> decide

lemma zbit_zero : zbit 0 = false := rfl
lemma zbit_one : zbit 1 = true := by decide

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
  refine Finset.sum_congr rfl fun t _ => ?_
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
    Submodule.span F (Set.range (column o)) = K := by
  have h0 : offset o ∈ K := by simpa only [project_point_zero] using hproj.1 0 (project_zero o)
  apply le_antisymm
  · apply Submodule.span_le.mpr
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
        rw [Finset.sum_eq_single t]
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
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

lemma projected_submodule {ρ α J : Type} [Fintype α] [Fintype J]
    {β : ℕ} (o : (ProjIn ρ α J → Bool) → SOut J β → Bool) (nf : (ProjIn ρ α J → Bool) → ℕ)
    (h : SSpec ρ α J β o nf) (v : ProjIn ρ α J → Bool)
    (K : Submodule F (J → F)) (hk : ∀ x, solS v x ↔ x ∈ K) :
    successful (o v) = true ∧ Module.finrank F K = nf v ∧
    (nf v ≤ β → Submodule.span F (Set.range (column (o v))) = K) := by
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
  have hp : 2 ^ Module.finrank F K = 2 ^ (nf v) := by
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
  exact (Submodule.mem_span_range_iff_exists_fun F).symm

lemma intersectionSys_spec {J U : Type} [Fintype J] [Fintype U] [DecidableEq U]
    (R : J → U → F) (p : J → Bool) (x : U → F) :
    solS (intersectSys R p) x ↔ x ∈ selectedSpan R p ⊓ selectedSpan R (fun j => !p j) := by
  have hd (a : Bool × J → F) (b : Bool) (u : U) :
      (∑ y : Bool × J, b2z (intersectSys R p ((b,u), .inl y)) * a y) =
        ∑ j : J, a (b,j) * (if p j == b then R j u else 0) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
    · refine Finset.sum_congr rfl fun j _ => ?_
      cases hb : (p j == b)
      · simp [intersectSys, hb, b2z]
      · simp only [intersectSys, beq_self_eq_true, Bool.true_and, hb, ite_true, zbit_decode]
        exact mul_comm _ _
    · intro b' _ hb'
      refine Finset.sum_eq_zero fun j _ => ?_
      cases b <;> cases b' <;> simp_all [intersectSys, b2z]
    · simp
  have hs (a : J → F) (b : Bool) (u : U) :
      (∑ j : J, a j • (if p j == b then R j else 0)) u =
        ∑ j : J, a j * (if p j == b then R j u else 0) := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by cases h : (p j == b) <;> rfl
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

lemma relation_equations {J U : Type} [Fintype J] [DecidableEq J]
    (R : J → U → F) {β : ℕ} (o : SOut J β → Bool)
    (h : Submodule.span F (Set.range (column o)) = LinearMap.ker (Fintype.linearCombination F R))
    (x : J → F) :
    (∀ i, dotProduct (column o i) x = 0) ↔ ∃ g : Dual (U → F), ∀ j, g (R j) = x j := by
  rw [evalRange]
  let L : (J → F) →ₗ[F] F := dotProductEquiv F J x
  have hz (a : J → F) : L a = dotProduct x a := rfl
  have hspan (a : J → F) : a ∈ Submodule.span F (Set.range (column o)) ↔
      (∑ j, a j • R j) = 0 := by
    rw [h, LinearMap.mem_ker, Fintype.linearCombination_apply]
  constructor
  · intro hg a ha
    have hle : Submodule.span F (Set.range (column o)) ≤ LinearMap.ker L := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change L (column o i) = 0
      rw [hz, dotProduct_comm]
      exact hg i
    exact hle ((hspan a).mpr ha)
  · intro hg i
    rw [dotProduct_comm]
    apply hg
    exact (hspan (column o i)).mp (Submodule.subset_span ⟨i, rfl⟩)

lemma joinCost_cap {d N m P : ℕ} (hd : d ≤ N) (hN : N + 1 ≤ P ^ 2)
    (hm : m ≤ 3 * d) (hP : 1 ≤ P) :
    topCost d d d m (N + 1) ((3 * d) / 2) + 1 ≤
      2 ^ 62 * P ^ 24 * 2 ^ ((3 * d) / 2) := by
  have hbase : d + d + d + m + (N + 1) + 3 ≤ 8 * P ^ 2 := by omega
  have hd' : d ≤ 3 * d / 2 := by omega
  have hexp : 2 ^ d ≤ (2 : ℕ) ^ (3 * d / 2) := Nat.pow_le_pow_right (by decide) hd'
  have hsum : 2 ^ d + 2 ^ d + 2 ^ d + 2 ^ min (d + d + d) (3 * d / 2) ≤
      4 * (2 : ℕ) ^ (3 * d / 2) := by
    have hmin : (2 : ℕ) ^ min (d + d + d) (3 * d / 2) ≤
        2 ^ (3 * d / 2) := Nat.pow_le_pow_right (by decide) (min_le_right ..)
    omega
  calc
    _ ≤ _ := topCost_le d d d m (N + 1) (3 * d / 2)
    _ ≤ 2 ^ 24 * (8 * P ^ 2) ^ 12 * (4 * 2 ^ (3 * d / 2)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 12)) hsum
    _ = _ := by ring

end PEqualNP.Outside.L_meta_29751


namespace PEqualNP.Outside.L_meta_29751.PackedTape

-- Insert after the ambient F, Word, Tape and Leaf abbreviations.
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

private def obsRow (i : Fin q) : List (InputSlot k r q n) :=
  List.ofFn (obsKeySlot i) ++ sides (fun b => lane (obsTapeSlot i b)) ++ [rhsSlot i]

private def bagRow (v : Fin n) : List (InputSlot k r q n) :=
  List.ofFn (fun j => bagSlot v (.inl j)) ++ sides (fun b => lane (fun t j => bagSlot v (.inr (b, t, j))))

def slots (k r q n : ℕ) : List (InputSlot k r q n) :=
  sides (fun b => List.ofFn (nameSlot b)) ++ sides (fun b => lane (cSlot b)) ++
    rows obsRow ++ rows bagRow

private theorem obsRow_length (i : Fin q) :
    (obsRow (k := k) (r := r) (n := n) i).length = tapeSize k r + 1 := by
  simp only [obsRow, sides, List.length_append, List.length_ofFn, length_lane,
    List.length_cons, List.length_nil, tapeSize]
  ring

private theorem bagRow_length (v : Fin n) :
    (bagRow (k := k) (r := r) (q := q) v).length = (2 * r + 1) * k := by
  simp only [bagRow, sides, List.length_append, List.length_ofFn, length_lane]
  ring

theorem slots_length (k r q n : ℕ) : (slots k r q n).length = inputs k r q n := by
  have ho := length_rows (obsRow (k := k) (r := r) (q := q) (n := n))
    (tapeSize k r + 1) (fun i => obsRow_length i)
  have hb := length_rows (bagRow (k := k) (r := r) (q := q) (n := n))
    ((2 * r + 1) * k) (fun v => bagRow_length v)
  simp only [slots, sides, List.length_append, List.length_ofFn, length_lane, ho, hb, inputs]
  ring

theorem card_inputSlot (k r q n : ℕ) : Fintype.card (InputSlot k r q n) = inputs k r q n := by
  simp only [InputSlot, ObsSlot, Leaf, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_unit, inputs, tapeSize]
  ring

theorem mem_slots (s : InputSlot k r q n) : s ∈ slots k r q n := by
  unfold slots
  rcases s with ⟨b, j⟩ | (⟨b, t, j⟩ | (⟨i, u⟩ | ⟨v, l⟩))
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact mem_sides b (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact mem_sides b (mem_lane (cSlot b) t j)
  · apply List.mem_append_left
    apply List.mem_append_right
    apply mem_rows i
    unfold obsRow
    rcases u with j | (⟨b, t, j⟩ | ⟨⟩)
    · apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_ofFn.mpr ⟨j, rfl⟩
    · apply List.mem_append_left
      apply List.mem_append_right
      exact mem_sides b (mem_lane (obsTapeSlot i b) t j)
    · exact List.mem_append_right _ List.mem_cons_self
  · apply List.mem_append_right
    apply mem_rows v
    unfold bagRow
    rcases l with j | ⟨b, t, j⟩
    · exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
    · apply List.mem_append_right
      exact mem_sides b (mem_lane (fun t j => bagSlot v (.inr (b, t, j))) t j)

noncomputable def slotIx (s : InputSlot k r q n) : Fin (inputs k r q n) := by
  classical
  letI : BEq (InputSlot k r q n) := instBEqOfDecidableEq
  exact ⟨(slots k r q n).idxOf s,
    slots_length k r q n ▸ List.idxOf_lt_length_of_mem (mem_slots s)⟩

def slotAt (i : Fin (inputs k r q n)) : InputSlot k r q n :=
  (slots k r q n)[i.val]'(by rw [slots_length]; exact i.isLt)

@[simp] theorem slotAt_slotIx (s : InputSlot k r q n) : slotAt (slotIx s) = s := by
  classical
  letI : BEq (InputSlot k r q n) := instBEqOfDecidableEq
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (mem_slots s))

theorem slotIx_bijective (k r q n : ℕ) : Function.Bijective (slotIx (k := k) (r := r) (q := q) (n := n)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨Function.LeftInverse.injective slotAt_slotIx, by rw [card_inputSlot, Fintype.card_fin]⟩

noncomputable def wireIx (s : InputSlot k r q n) : ℕ := (slotIx s).val

theorem wireIx_lt (s : InputSlot k r q n) : wireIx s < inputs k r q n := (slotIx s).isLt

theorem wireIx_lt_succ (s : InputSlot k r q n) : wireIx s < inputs k r q n + 1 :=
  Nat.lt_succ_of_lt (wireIx_lt s)

def wordBits (v : Word k) : List Bool := List.ofFn (fun j : Fin k => decide (v j ≠ 0))
def obsLaneBits (side : Bool) (tape : Tape k r) : List Bool :=
  (List.finRange (r + 1)).flatMap (fun j => wordBits (tape.2 side j))
def leafBits (p : Leaf k r → Bool) : List Bool :=
  List.ofFn (fun j : Fin k => p (.inl j)) ++
    [false, true].flatMap (fun b => (List.finRange r).flatMap (fun t =>
      List.ofFn (fun j : Fin k => p (.inr (b, t, j)))))

def bits (name : Bool → Word k) (c : Bool → Fin r → Word k) (obs : Fin q → Tape k r)
    (rhs : Fin q → F) (bag : Fin n → Leaf k r → Bool) : List Bool :=
  wordBits (name false) ++ wordBits (name true) ++
    [false, true].flatMap (fun b => (List.finRange r).flatMap (fun t => wordBits (c b t))) ++
    (List.finRange q).flatMap (fun i => wordBits (obs i).1 ++ obsLaneBits false (obs i) ++
      obsLaneBits true (obs i) ++ [decide (rhs i ≠ 0)]) ++
    (List.finRange n).flatMap (fun v => leafBits (bag v))

def slotBit (name : Bool → Word k) (c : Bool → Fin r → Word k) (obs : Fin q → Tape k r)
    (rhs : Fin q → F) (bag : Fin n → Leaf k r → Bool) : InputSlot k r q n → Bool
  | .inl (b, j) => decide (name b j ≠ 0)
  | .inr (.inl (b, t, j)) => decide (c b t j ≠ 0)
  | .inr (.inr (.inl (i, .inl j))) => decide ((obs i).1 j ≠ 0)
  | .inr (.inr (.inl (i, .inr (.inl (b, t, j))))) => decide ((obs i).2 b t j ≠ 0)
  | .inr (.inr (.inl (i, .inr (.inr ())))) => decide (rhs i ≠ 0)
  | .inr (.inr (.inr (v, l))) => bag v l

section
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

theorem map_slots :
    (slots k r q n).map (slotBit name c obs rhs bag) = bits name c obs rhs bag := by
  simp only [slots, obsRow, bagRow, sides, rows, lane, bits, wordBits, obsLaneBits, leafBits,
    List.map_append, List.map_flatMap, List.map_ofFn, Function.comp_def, List.map_cons,
    List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
    slotBit_name, slotBit_c, slotBit_obsKey, slotBit_obsTape, slotBit_rhs, slotBit_bag]

theorem bits_length : (bits name c obs rhs bag).length = inputs k r q n := by
  rw [← map_slots name c obs rhs bag, List.length_map, slots_length]

def vector (i : Fin (inputs k r q n)) : Bool := slotBit name c obs rhs bag (slotAt i)

@[simp] theorem vector_slotIx (s : InputSlot k r q n) :
    vector name c obs rhs bag (slotIx s) = slotBit name c obs rhs bag s := by
  simp only [vector, slotAt_slotIx]

theorem ofFn_vector : List.ofFn (vector name c obs rhs bag) = bits name c obs rhs bag := by
  rw [← map_slots name c obs rhs bag]
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, slots_length]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, vector, slotAt]

-- This is exactly the function supplied to the output semantics of Cmp.extract.
theorem read_bits (s : InputSlot k r q n) :
    ((bits name c obs rhs bag) ++ [false]).getD (wireIx s) false = slotBit name c obs rhs bag s := by
  have hi : wireIx s < (bits name c obs rhs bag).length := by
    rw [bits_length]
    exact wireIx_lt s
  rw [List.getD_append _ _ _ _ hi, ← ofFn_vector name c obs rhs bag]
  have h : wireIx s < (List.ofFn (vector name c obs rhs bag)).length := by
    rw [List.length_ofFn]
    exact wireIx_lt s
  rw [List.getD_eq_getElem _ _ h, List.getElem_ofFn]
  exact vector_slotIx name c obs rhs bag s

end
end PEqualNP.Outside.L_meta_29751.PackedTape


namespace PEqualNP.Outside.L_meta_29751.Greedy

-- Descending initial segments from L_meta_33648.lean (04168edab39014e515fbb09f71ba0651b69367a8),
-- ta_arg–ta_top_sem. Uses only the transferred Donor Cmp/Cb combinators.
open PEqualNP.Outside.L_meta_29751.Donor
open scoped BigOperators

abbrev Bits (k : ℕ) := Fin k → Bool
-- Input wires are data, mask, then values. A true mask bit fixes the corresponding key bit.
abbrev Input (ι : Type) (k : ℕ) := ι ⊕ (Fin k ⊕ Fin k)
abbrev Reply (k : ℕ) := Unit ⊕ Fin (k + 1)
abbrev Output (k : ℕ) := Reply k ⊕ Fin k

def input {ι : Type} {k : ℕ} (d : ι → Bool) (m p : Bits k) : Input ι k → Bool :=
  Sum.elim d (Sum.elim m p)

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
    simp [Nat.card_eq_fintype_card, Fintype.card_fun]
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

private def base {ι : Type} (d : ι → Bool) : Base ι → Bool := Sum.elim d id
private def reply {ι : Type} {k : ℕ} (v : State ι k → Bool) (s : Reply k) : Bool := v (.inr (.inl s))
private def keys {ι : Type} {k : ℕ} (v : State ι k → Bool) (j : Fin k) : Bool := v (.inr (.inr j))
private def positive {k : ℕ} (v : Reply k → Bool) : Bool := someBit k (fun i => v (.inr i))

private def emptyRoute {ι : Type} {k : ℕ} : Input ι k → Base ι :=
  Sum.elim Sum.inl (Sum.elim (fun _ => .inr false) (fun _ => .inr false))

private def start {ι : Type} {k : ℕ} (F : (Input ι k → Bool) → Reply k → Bool)
    (v : Base ι → Bool) : State ι k → Bool :=
  Sum.elim v (Sum.elim (F (fun a => v (emptyRoute a))) (fun _ => v (.inr false)))

private def probeRoute {ι : Type} {k : ℕ} (i : Fin k) : Input ι k → State ι k
  | .inl a => .inl (.inl a)
  | .inr (.inl j) => .inl (.inr (decide (i.val ≤ j.val)))
  | .inr (.inr j) => if j = i then .inl (.inr false) else .inr (.inr j)

private def put {k : ℕ} (p : Bits k) (i : Fin k) (b : Bool) : Bits k :=
  fun j => if j = i then b else p j

private def advance {ι : Type} {k : ℕ} (F : (Input ι k → Bool) → Reply k → Bool)
    (i : Fin k) (v : State ι k → Bool) : State ι k → Bool :=
  Sum.elim (fun b => v (.inl b))
    (Sum.elim (reply v) (put (keys v) i (!positive (F (fun a => v (probeRoute i a))))))

private def loop {ι : Type} {k : ℕ} (F : (Input ι k → Bool) → Reply k → Bool) :
    ℕ → (State ι k → Bool) → State ι k → Bool
  | 0, v => v
  | q + 1, v => if hq : q < k then loop F q (advance F ⟨q, hq⟩ v) else v

private def finish {ι : Type} {k : ℕ} (v : State ι k → Bool) : Output k → Bool :=
  Sum.elim (reply v) (fun j => positive (reply v) && keys v j)

def wrap {ι : Type} {k : ℕ} (F : (Input ι k → Bool) → Reply k → Bool)
    (d : ι → Bool) : Output k → Bool := finish (loop F k (start F (base d)))

private theorem base_cmp (ι : Type) : Cmp ι (Base ι) 2 base := by
  let route : Base ι → ι ⊕ (Unit ⊕ Unit) :=
    Sum.elim Sum.inl (fun b => .inr (if b then .inr () else .inl ()))
  refine Cmp.congr (Cmp.comp (Cmp.keep (Cmp.pair (Cb.const false) (Cb.const true))) (Cmp.wire route)) ?_
  intro v a
  rcases a with a | b
  · rfl
  · cases b <;> rfl

private theorem start_cmp {ι : Type} {k S : ℕ} {F : (Input ι k → Bool) → Reply k → Bool}
    (hc : Cmp (Input ι k) (Reply k) S F) : Cmp (Base ι) (State ι k) S (start F) := by
  let route : State ι k → Base ι ⊕ Reply k :=
    Sum.elim Sum.inl (Sum.elim Sum.inr (fun _ => .inl (.inr false)))
  refine Cmp.congr (Cmp.comp (Cmp.keep (Cmp.sel emptyRoute hc)) (Cmp.wire route)) ?_
  intro v a
  rcases a with a | s | j <;> rfl

private theorem advance_cmp {ι : Type} {k S : ℕ} {F : (Input ι k → Bool) → Reply k → Bool}
    (hc : Cmp (Input ι k) (Reply k) S F) (i : Fin k) :
    Cmp (State ι k) (State ι k) (S + k + 1) (advance F i) := by
  have hpos : Cb (Reply k) k positive := someBit_cb k Sum.inr
  have hbit := Cb.comp (Cmp.sel (probeRoute i) hc) (Cb.not hpos)
  let route : State ι k → State ι k ⊕ Unit :=
    Sum.elim (fun b => .inl (.inl b)) (Sum.elim (fun s => .inl (.inr (.inl s)))
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
    simpa only [Fintype.card_fin, Nat.mul_one] using h
  have hr := Cmp.wire (fun s : Reply k => (Sum.inl (.inr (.inl s)) : State ι k ⊕ Unit))
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

end PEqualNP.Outside.L_meta_29751.Greedy


namespace PEqualNP.Outside.L_meta_29751.TreeSchedule

open PEqualNP.Outside.L_meta_29751.Donor

abbrev State (D T : Type) (n : ℕ) := D ⊕ (Fin n × T)
abbrev Candidate (J : Type) (n : ℕ) := J ⊕ (Fin n × Fin n)

abbrev LeafFn (D J T : Type) := J → (D → Bool) → T → Bool
abbrev JoinFn (D T : Type) (n : ℕ) :=
  Fin n → Fin n → Fin n → (D ⊕ (T ⊕ T) → Bool) → T → Bool
abbrev GuardFn (D J : Type) (n : ℕ) := Fin n → Candidate J n → (D → Bool) → Bool

abbrev data {D T : Type} {n : ℕ} (s : State D T n → Bool) : D → Bool := s ∘ Sum.inl
abbrev table {D T : Type} {n : ℕ} (s : State D T n → Bool) (i : Fin n) : T → Bool :=
  fun t => s (.inr (i,t))

def joinInputs {D T : Type} {n : ℕ} (l h : Fin n) (s : State D T n → Bool) :
    D ⊕ (T ⊕ T) → Bool := Sum.elim (data s) (Sum.elim (table s l) (table s h))

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
  (List.finRange n).foldl (fun s i => step leaf join guard i s) (Sum.elim x (fun _ => false))

def stepCost (D J T : Type) [Fintype D] [Fintype J] [Fintype T] (n sTable sFlag : ℕ) : ℕ :=
  Fintype.card (Candidate J n) * (sTable + sFlag + 2) +
    Fintype.card (State D T n) * (2 * Fintype.card (Candidate J n) + 1)

private theorem decision_eq (p : Prop) (a b : Decidable p) : @decide p a = @decide p b :=
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
    Sum.elim (fun ct => getCand leaf join v s ct.1 ct.2) (fun c => validCand guard v s c.1)
  have ha : Cmp S (C × T) (Fintype.card C * sTable) (fun s p => getCand leaf join v s p.1 p.2) := by
    refine Cmp.piU (F := fun c s t => getCand leaf join v s c t) ?_
    rintro (i | ⟨l,h⟩)
    · exact Cmp.sel Sum.inl (hLeaf i)
    · refine Cmp.congr (Cmp.sel (Sum.elim Sum.inl (Sum.elim (fun t => .inr (l,t)) (fun t => .inr (h,t))))
        (hJoin v l h)) ?_
      intro s t
      change join v l h _ t = join v l h _ t
      congr 2
      funext j
      rcases j with d | u | u <;> rfl
  have hb : Cmp S (C × Unit) (Fintype.card C * (sFlag + 2))
      (fun s p => validCand guard v s p.1) := by
    refine Cmp.piU (F := fun c s (_ : Unit) => validCand guard v s c) ?_
    intro p
    cases p with
    | inl i => exact (Cmp.sel Sum.inl (hGuard v (.inl i))).mono (by omega)
    | inr p =>
      rcases p with ⟨l,h⟩
      have hv : Cb S sFlag (fun s => guard v (.inr (l,h)) (data s)) :=
        Cmp.sel Sum.inl (hGuard v (.inr (l,h)))
      exact Cb.mono (Cb.and (Cb.const (decide (l < v ∧ h < v))) hv) (by omega)
  have hA : Cmp S (Sum (C × T) (C × Unit))
      (Fintype.card C * (sTable + sFlag + 2)) stageA := by
    simpa [stageA, Nat.mul_add, Nat.add_assoc] using Cmp.pair ha hb
  let Z := S ⊕ Sum (C × T) (C × Unit)
  let stageB : (S ⊕ Sum (C × T) (C × Unit) → Bool) → S → Bool := fun z s =>
    match s with
    | .inl d => z (.inl (.inl d))
    | .inr (i,t) => if i = v then decide (∃ c : C, z (.inr (.inr (c, ()))) = true ∧
        z (.inr (.inl (c,t))) = true) else z (.inl (.inr (i,t)))
  have hB : Cmp (S ⊕ Sum (C × T) (C × Unit)) S
      (Fintype.card S * (2 * Fintype.card C + 1)) stageB := by
    apply Cmp.ofBits
    rintro (d | ⟨i,t⟩)
    · exact (Cb.var (ι := Z) (.inl (.inl d))).mono (Nat.zero_le _)
    · by_cases h : i = v
      · simpa [stageB, h, Bool.and_eq_true, Nat.mul_comm] using
          (Cb.bigOr (I := C) fun c => Cb.and (Cb.var (ι := Z) (.inr (.inr (c, ()))))
            (Cb.var (ι := Z) (.inr (.inl (c,t)))))
      · simpa only [stageB, ite_eq_right h] using
          (Cb.var (ι := S ⊕ Sum (C × T) (C × Unit)) (.inl (.inr (i,t)))).mono
            (Nat.zero_le (2 * Fintype.card C + 1))
  have hF := Cmp.comp (Cmp.keep hA) hB
  refine Cmp.congr hF (fun z s => ?_)
  rcases s with d | ⟨i,t⟩
  · rfl
  · by_cases hi : i = v <;>
      simp only [step, stageA, stageB, table, Sum.elim_inl, Sum.elim_inr, hi, ite_true, ite_false]
    exact decision_eq _ _ _

theorem run_cmp {D J T : Type} [Fintype D] [Fintype J] [Fintype T]
    {n sTable sFlag : ℕ} (leaf : LeafFn D J T) (join : JoinFn D T n)
    (guard : GuardFn D J n)
    (hLeaf : ∀ i, Cmp D T sTable (leaf i))
    (hJoin : ∀ i l h, Cmp (D ⊕ (T ⊕ T)) T sTable (join i l h))
    (hGuard : ∀ i c, Cb D sFlag (guard i c)) :
    Cmp D (State D T n) (Fintype.card (Fin n × T) + n * stepCost D J T n sTable sFlag)
      (run leaf join guard) := by
  have h0 : Cmp D (State D T n) (Fintype.card (Fin n × T))
      (fun x => Sum.elim x (fun _ => false)) := by
    simpa using Cmp.pair (Cmp.wire (fun i : D => i))
      (Cmp.ofBits (κ := Fin n × T) fun _ => Cb.const (ι := D) false)
  have h1 := Cmp.foldl (List.finRange n) (step leaf join guard)
    (fun i _ => step_cmp leaf join guard hLeaf hJoin hGuard i)
  have h := Cmp.comp h0 h1
  rw [List.length_finRange] at h
  exact h

theorem run_sem {D J T : Type} {n : ℕ} (leaf : LeafFn D J T) (join : JoinFn D T n)
    (guard : GuardFn D J n) (x : D → Bool) (A : Fin n → T → Bool)
    (hAvail : ∀ v, ∃ c, validCand guard v (Sum.elim x (fun _ => false) : State D T n → Bool) c = true)
    (hLeaf : ∀ v i, guard v (.inl i) x = true → leaf i x = A v)
    (hJoin : ∀ v l h, l < v → h < v → guard v (.inr (l,h)) x = true →
      join v l h (Sum.elim x (Sum.elim (A l) (A h))) = A v) :
    ∀ v, table (run leaf join guard x) v = A v := by
  classical
  let S := State D T n
  let st (p : ℕ) : S → Bool := ((List.finRange n).take p).foldl
    (fun s i => step leaf join guard i s) (Sum.elim x (fun _ => false))
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
            have he : joinInputs l u (st p) = Sum.elim x (Sum.elim (A l) (A u)) := by
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

end PEqualNP.Outside.L_meta_29751.TreeSchedule


namespace PEqualNP.Outside.L_meta_29751

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
    [AddCommGroup U] [Module F U] (T : V →ₗ[F] U) (ht : Function.Injective T)
    (rows : J → V) (bag : J → Bool) :
    Module.finrank F (selectedSpan (fun j => T (rows j)) bag ⊓
      selectedSpan (fun j => T (rows j)) (fun j => !bag j) : Submodule F U) =
    Module.finrank F (selectedSpan rows bag ⊓ selectedSpan rows (fun j => !bag j) : Submodule F V) := by
  let C : Submodule F V := selectedSpan rows bag ⊓ selectedSpan rows (fun j => !bag j)
  rw [← selectedSpan_map, ← selectedSpan_map, ← Submodule.map_inf T ht]
  exact (Submodule.equivMapOfInjective T ht C).finrank_eq.symm

def precompose {A B : Type*} (f : A → B) : (B → F) →ₗ[F] (A → F) where
  toFun g := g ∘ f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma precompose_injective {A B : Type*} (f : A → B) (hf : Function.Surjective f) :
    Function.Injective (precompose f) := by
  intro a b h
  funext y
  obtain ⟨x,rfl⟩ := hf y
  exact congrFun h x

def dotFunctions (A : Type*) [Fintype A] : (A → F) →ₗ[F] ((A → F) → F) where
  toFun a := dotProduct a
  map_add' _ _ := funext fun b => add_dotProduct _ _ _
  map_smul' c a := funext fun b => smul_dotProduct c a b

lemma dotFunctions_injective (A : Type*) [Fintype A] [DecidableEq A] :
    Function.Injective (dotFunctions A) := by
  intro a b h
  funext i
  simpa [dotFunctions] using congrFun h (Pi.single i 1)

lemma width_coordinates {J A B : Type*} [Fintype A] [DecidableEq A]
    (f : J → B → F) (rows : J → A → F) (toDirection : (A → F) → B)
    (hsurj : Function.Surjective toDirection)
    (hrepr : ∀ i v, f i (toDirection v) = dotProduct (rows i) v) (bag : J → Bool) :
    Module.finrank F (selectedSpan rows bag ⊓ selectedSpan rows (fun j => !bag j) : Submodule F (A → F)) =
    Module.finrank F (selectedSpan f bag ⊓ selectedSpan f (fun j => !bag j) : Submodule F (B → F)) := by
  have hc : (fun i => precompose toDirection (f i)) = fun i => dotFunctions A (rows i) := by
    funext i v
    exact hrepr i v
  rw [← width_map (precompose toDirection) (precompose_injective _ hsurj) f bag,
    hc, width_map (dotFunctions A) (dotFunctions_injective A) rows bag]

lemma selectedSpan_union {J V : Type*} [AddCommGroup V] [Module F V]
    (rows : J → V) (p q : J → Bool) :
    selectedSpan rows (fun j => p j || q j) = selectedSpan rows p ⊔ selectedSpan rows q := by
  unfold selectedSpan
  rw [← Submodule.span_union]
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

lemma selectedSpan_congr {J V : Type*} [AddCommGroup V] [Module F V]
    (rows : J → V) {a b : J → Bool} (hab : ∀ j, a j = b j) :
    selectedSpan rows a = selectedSpan rows b := congrArg (selectedSpan rows) (funext hab)

lemma restPartition {J : Type*} (L H : J → Bool) (hd : ∀ j, L j = true → H j = false) :
    (∀ j, (H j || !(L j || H j)) = !L j) ∧
    (∀ j, (L j || !(L j || H j)) = !H j) := by
  constructor <;> intro j <;> have hh := hd j <;> cases hL : L j <;> cases hH : H j <;> simp_all

lemma rootEval_exists {J V : Type*} [AddCommGroup V] [Module F V]
    (rows : J → V) (g : Dual (selectedSpan rows (fun _ => true))) :
    ∃ u : Dual V, u.comp (selectedSpan rows (fun _ => true)).subtype = g :=
  LinearMap.dualMap_surjective_of_injective (selectedSpan rows (fun _ => true)).injective_subtype g

lemma selectedSpan_ext {J V : Type*} [AddCommGroup V] [Module F V]
    {rows : J → V} {bag : J → Bool} {a b : Dual V}
    (h : ∀ j, bag j = true → a (rows j) = b (rows j)) :
    a.comp (selectedSpan rows bag).subtype = b.comp (selectedSpan rows bag).subtype := by
  have hl : selectedSpan rows bag ≤ LinearMap.ker (a - b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,hj,rfl⟩
    change a (rows j) - b (rows j) = 0
    rw [h j hj, sub_self]
  apply LinearMap.ext
  intro v
  exact sub_eq_zero.mp (hl v.prop)

end PEqualNP.Outside.L_meta_29751

namespace PEqualNP.Outside.L_meta_29751

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
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
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

end PEqualNP.Outside.L_meta_29751


namespace PEqualNP.Outside.L_meta_29751

open Donor

abbrev WidthIn (J U : Type) := (J × U) ⊕ J
abbrev WidthOut (U : Type) (d : ℕ) := (U × Fin d) ⊕ Unit

def widthInRows {J U : Type} (x : WidthIn J U → Bool) : J → U → F := fun j u => b2z (x (.inl (j,u)))
def widthInMask {J U : Type} (x : WidthIn J U → Bool) : J → Bool := fun j => x (.inr j)

def widthOutGen {U : Type} {d : ℕ} (x : WidthOut U d → Bool) : Fin d → U → F :=
  fun t u => b2z (x (.inl (u,t)))

def widthPrepCost (J U : Type) [Fintype J] [Fintype U] (d : ℕ) : ℕ :=
  Fintype.card (ProjIn (Bool × U) (Bool × J) U) * 4 +
  glCost (Fintype.card (Bool × U)) (Fintype.card (Bool × J)) (Fintype.card U) (d+1) +
  Fintype.card (WidthOut U d) * 2

theorem widthPrep {J U : Type} [Fintype J] [Fintype U] [DecidableEq U] (d : ℕ) :
    ∃ P : (WidthIn J U → Bool) → WidthOut U d → Bool,
      Cmp (WidthIn J U) (WidthOut U d) (widthPrepCost J U d) P ∧
      ∀ x : WidthIn J U → Bool,
        let K := selectedSpan (widthInRows x) (widthInMask x) ⊓
          selectedSpan (widthInRows x) (fun j => !(widthInMask x j))
        (P x (.inr ()) = true ↔ Module.finrank F K ≤ d) ∧
        (P x (.inr ()) = true → Submodule.span F (Set.range (widthOutGen (P x))) = K) := by
  classical
  let L := ProjIn (Bool × U) (Bool × J) U
  let O := SOut U (d+1)
  let A (x : WidthIn J U → Bool) : L → Bool := intersectSys (widthInRows x) (widthInMask x)
  have hA : Cmp (WidthIn J U) L (Fintype.card L * 4) A := by
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
  let B (v : O → Bool) : WidthOut U d → Bool := Sum.elim
    (fun p => enabled v p.2.castSucc && v (.inl (p.1,p.2.castSucc)))
    (fun _ => !(enabled v (Fin.last d)))
  have hB : Cmp O (WidthOut U d) (Fintype.card (WidthOut U d) * 2) B := by
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
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact Submodule.subset_span ⟨t.castSucc, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨t,rfl⟩
    refine Fin.lastCases ?_ (fun j => ?_) t
    · rw [hz]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨j, rfl⟩

abbrev NullIn (J U : Type) := J × U
abbrev NullOut (J : Type) (d : ℕ) := J × Fin d

def nullDecoded {J U : Type} (x : NullIn J U → Bool) : J → U → F := fun j u => b2z (x (j,u))
def nullOutGen {J : Type} {d : ℕ} (x : NullOut J d → Bool) : Fin d → J → F :=
  fun t j => b2z (x (j,t))

def nullPrepCost (J U : Type) [Fintype J] [Fintype U] (d : ℕ) : ℕ :=
  Fintype.card (ProjIn U Empty J) + glCost (Fintype.card U) 0 (Fintype.card J) d +
  Fintype.card (NullOut J d)

theorem nullPrep {J U : Type} [Fintype J] [Fintype U] (d : ℕ) (hd : Fintype.card J ≤ d) :
    ∃ P : (NullIn J U → Bool) → NullOut J d → Bool,
      Cmp (NullIn J U) (NullOut J d) (nullPrepCost J U d) P ∧
      ∀ x, Submodule.span F (Set.range (nullOutGen (P x))) =
        LinearMap.ker (Fintype.linearCombination F (nullDecoded x)) := by
  classical
  let L := ProjIn U Empty J
  let A (x : NullIn J U → Bool) : L → Bool := system (fun u j => nullDecoded x j u) (fun _ => 0)
  have hA : Cmp (NullIn J U) L (Fintype.card L) A := by
    rw [← Nat.mul_one (Fintype.card L)]
    apply Cmp.ofBits
    rintro ⟨u, (b | j | ⟨⟩)⟩
    · exact b.elim
    · exact ((Cb.var (ι := NullIn J U) (j,u)).mono (by decide : 0 ≤ 1)).congr
        (fun x => (st_dec_b2z (x (j,u))).symm)
    · exact Cb.const false
  obtain ⟨S, nf, hS, hs⟩ := glS U Empty J d
  have hS' : Cmp L (SOut J d) (glCost (Fintype.card U) 0 (Fintype.card J) d) S := by simpa using hS
  let B (v : SOut J d → Bool) (it : NullOut J d) := enabled v it.2 && v (.inl it)
  have hB : Cmp (SOut J d) (NullOut J d) (Fintype.card (NullOut J d)) B := by
    rw [← Nat.mul_one (Fintype.card (NullOut J d))]
    apply Cmp.ofBits
    intro p
    exact Cb.and (Cb.var (ι := SOut J d) (.inr (.inr (.inl p.2))))
      (Cb.var (ι := SOut J d) (.inl p))
  refine ⟨fun x => B (S (A x)), Cmp.comp (Cmp.comp hA hS') hB, ?_⟩
  intro x
  let K := LinearMap.ker (Fintype.linearCombination F (nullDecoded x))
  obtain ⟨_, hr, hb⟩ := projected_submodule S nf hs (A x) K (null_iff (nullDecoded x))
  have hk : Module.finrank F K ≤ d := (Submodule.finrank_le K).trans (by simpa using hd)
  exact hb (hr ▸ hk)

end PEqualNP.Outside.L_meta_29751


namespace PEqualNP.Outside.L_meta_29751

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

lemma coord_card (k r : ℕ) : Fintype.card (Coord k r) = tapeSize k r := by
  simp [Coord, tapeSize]
  ring

def latticeMap (hk : 0 < k) (obs : Fin q → Tape k r) :
    (Coord k r → F) →ₗ[F] (EqRow k q → F) :=
  LinearMap.pi fun i =>
    { toFun := dotProduct (row hk obs i)
      map_add' := fun u v => dotProduct_add _ _ _
      map_smul' := fun c u => dotProduct_smul c _ u }

lemma latticeMap_apply (hk : 0 < k) (obs : Fin q → Tape k r) (z : Coord k r → F) (i : EqRow k q) :
    latticeMap hk obs z i = dotProduct (row hk obs i) z := rfl

abbrev TapeOut (k r : ℕ) := (Coord k r × (Param k r ⊕ Unit)) ⊕ Unit

def tapePrepGen (out : TapeOut k r → Bool) : Param k r → Coord k r → F :=
  fun t j => b2z (out (.inl (j, .inl t)))
def tapePrepPoint (out : TapeOut k r → Bool) : Coord k r → F :=
  fun j => b2z (out (.inl (j, .inr ())))

def tapePrepSysCost (k r q : ℕ) := Fintype.card (ProjIn (EqRow k q) Empty (Coord k r))
def tapePrepCost (k r q : ℕ) : ℕ :=
  2 * (tapePrepSysCost k r q + glCost (Fintype.card (EqRow k q)) 0 (tapeSize k r) (tapeSize k r)) +
    Fintype.card (TapeOut k r)

lemma latticeSys_cmp (hk : 0 < k) (hom : Bool) :
    Cmp (Raw k r q n) (ProjIn (EqRow k q) Empty (Coord k r)) (tapePrepSysCost k r q)
      (fun v => system (row hk (readObs v)) (if hom then 0 else rowTarget (readName v) (readRhs v))) := by
  classical
  rw [tapePrepSysCost, ← Nat.mul_one (Fintype.card (ProjIn (EqRow k q) Empty (Coord k r)))]
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
        Submodule.span F (Set.range (tapePrepGen (P x))) = LinearMap.ker (latticeMap hk (readObs x)) ∧
        (P x (.inr ()) = true →
          latticeMap hk (readObs x) (tapePrepPoint (P x)) = rowTarget (readName x) (readRhs x)) := by
  classical
  let D := Raw k r q n
  let M := Fintype.card (EqRow k q)
  let N := tapeSize k r
  let I := ProjIn (EqRow k q) Empty (Coord k r)
  let O := SOut (Coord k r) N
  obtain ⟨S, nf, hS, hsem⟩ := glS (EqRow k q) Empty (Coord k r) N
  have hS' : Cmp I O (glCost M 0 N N) S := by
    simpa only [Fintype.card_empty, coord_card] using hS
  let A (x : D → Bool) (b : Bool) : I → Bool :=
    system (row hk (readObs x)) (if b then 0 else rowTarget (readName x) (readRhs x))
  have hA (b : Bool) : Cmp D O (tapePrepSysCost k r q + glCost M 0 N N) (fun x => S (A x b)) :=
    Cmp.comp (latticeSys_cmp hk b) hS'
  let B (v : O ⊕ O → Bool) : TapeOut k r → Bool :=
    Sum.elim (fun (j, p) => Sum.elim
      (fun t => v (.inl (.inr (.inr (.inl t)))) && v (.inl (.inl (j,t))))
      (fun _ => v (.inr (.inr (.inl j)))) p)
      (fun _ => v (.inr (.inr (.inr (.inr ())))))
  have hB : Cmp (O ⊕ O) (TapeOut k r) (Fintype.card (TapeOut k r)) B := by
    rw [← Nat.mul_one (Fintype.card (TapeOut k r))]
    apply Cmp.ofBits
    rintro (⟨j, (t | ⟨⟩)⟩ | ⟨⟩)
    · exact Cb.and (Cb.var (ι := O ⊕ O) (.inl (.inr (.inr (.inl t)))))
        (Cb.var (ι := O ⊕ O) (.inl (.inl (j,t))))
    · exact (Cb.var (ι := O ⊕ O) (.inr (.inr (.inl j)))).mono (by decide)
    · exact (Cb.var (ι := O ⊕ O) (.inr (.inr (.inr (.inr ()))))).mono (by decide)
  let P (x : D → Bool) : TapeOut k r → Bool := B (Sum.elim (S (A x true)) (S (A x false)))
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
  have hwidth : Module.finrank F K ≤ N := by
    simpa only [Module.finrank_fintype_fun_eq_card, coord_card] using Submodule.finrank_le K
  have hg' : Submodule.span F (Set.range (tapePrepGen (P x))) = K := by
    exact hg (hdim ▸ hwidth)
  let b := rowTarget (readName x) (readRhs x)
  have haff (z : Coord k r → F) : solS (A x false) z ↔ latticeMap hk (readObs x) z = b := by
    rw [show A x false = system (row hk (readObs x)) b from rfl, system_iff]
    exact ⟨fun h => funext h, fun h => congrFun h⟩
  obtain ⟨hbad, hok⟩ := hsem (A x false)
  have hpoint (h : P x (.inr ()) = true) : latticeMap hk (readObs x) (tapePrepPoint (P x)) = b := by
    obtain ⟨hc, _, hp⟩ := hok h
    have hcard : Nat.card (Coord k r → F) = 2 ^ N := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, coord_card]
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

end PEqualNP.Outside.L_meta_29751


namespace PEqualNP.Outside.L_meta_29751

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
    Cmp (TapeOut k r) (FormData k r) (Fintype.card (FormData k r) * 21) (evalForms hk) := by
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
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  exact congrArg (fun b => a t * b) (linearRows_eq hk x i t)

end PEqualNP.Outside.L_meta_29751


namespace PEqualNP.Outside.L_meta_29751.LayoutGuard

open PEqualNP.Outside.L_meta_29751.Donor

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

theorem guard_split_sets [DecidableEq J] (idx : Fin n × J → D)
    (v l h : Fin n) (x : D → Bool) (hg : guard idx v (.inr (l,h)) x = true) :
    Disjoint {j | mask idx x l j = true} {j | mask idx x h j = true} ∧
    {j | mask idx x v j = true} = {j | mask idx x l j = true} ∪ {j | mask idx x h j = true} := by
  obtain ⟨hd, hu⟩ := (guard_split_true idx v l h x).mp hg
  refine ⟨Set.disjoint_left.mpr ?_, ?_⟩
  · intro j hl hh
    have hf := hd j hl
    exact Bool.noConfusion (hh.symm.trans hf)
  · ext j
    change mask idx x v j = true ↔ mask idx x l j = true ∨ mask idx x h j = true
    rw [hu j, Bool.or_eq_true]

/-- Validity adds the scheduler's static predecessor check to the local guard. -/
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

def rootCost (J : Type) [Fintype J] : ℕ := Fintype.card J + 1

def guardCost (J : Type) [Fintype J] : ℕ := Fintype.card J * 10 + 1

def hasRootCost (J : Type) [Fintype J] (n : ℕ) : ℕ := n * (rootCost J + 1) + 1

def nodeCost (J : Type) [Fintype J] (n : ℕ) : ℕ :=
  (Fintype.card J + n * n) * (guardCost J + 1) + 1

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
  simpa only [hasRootCost, Fintype.card_fin] using h

theorem valid_cb [Fintype J] [DecidableEq J] (idx : Fin n × J → D) (v : Fin n)
    (c : TreeSchedule.Candidate J n) : Cb D (guardCost J) (valid idx v c) := by
  rcases c with one | ⟨l,h⟩
  · exact guard_cb idx v (.inl one)
  · by_cases hp : l < v ∧ h < v
    · exact (guard_cb idx v (.inr (l,h))).congr (fun x => by simp [valid, hp])
    · exact ((Cb.const (ι := D) false).mono
        (Nat.succ_le_succ (Nat.zero_le (Fintype.card J * 10)))).congr
        (fun x => by simp [valid, hp])

theorem node_cb [Fintype J] [DecidableEq J] (idx : Fin n × J → D) (v : Fin n) :
    Cb D (nodeCost J n) (node idx v) := by
  have h := (Cb.bigOr (valid_cb idx v)).congr (φ' := node idx v) (fun x => by
    rw [Bool.eq_iff_iff]
    simp only [node, decide_eq_true_eq])
  simpa only [nodeCost, TreeSchedule.Candidate, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using h

theorem layout_cb [Fintype J] [DecidableEq J] (idx : Fin n × J → D) :
    Cb D (layoutCost J n) (layout idx) := by
  have h := (Cb.and (hasRoot_cb idx) (Cb.bigAnd (node_cb idx))).congr (φ' := layout idx)
    (fun x => by
      rw [Bool.eq_iff_iff]
      simp only [layout, Bool.and_eq_true, decide_eq_true_eq])
  simpa only [layoutCost, Fintype.card_fin] using h

theorem roots_cmp [Fintype J] (idx : Fin n × J → D) :
    Cmp D (Fin n) (n * rootCost J) (fun x v => root idx v x) := by
  simpa using (Cmp.ofBits (root_cb idx))

/-- Read one common result from all roots; no priority choice is needed. -/
noncomputable def readRoots {T : Type} (idx : Fin n × J → D)
    (s : TreeSchedule.State D T n → Bool) (t : T) : Bool := by
  classical
  exact decide (∃ v, (root idx v (TreeSchedule.data s) && TreeSchedule.table s v t) = true)

theorem readRoots_cmp [Fintype J] {T : Type} [Fintype T] (idx : Fin n × J → D) :
    Cmp (TreeSchedule.State D T n) T (Fintype.card T * (n * (rootCost J + 2) + 1))
      (readRoots idx) := by
  apply Cmp.ofBits
  intro t
  have hv (v : Fin n) : Cb (TreeSchedule.State D T n) (rootCost J + 1)
      (fun s => root idx v (TreeSchedule.data s) && TreeSchedule.table s v t) := by
    have hr : Cb (TreeSchedule.State D T n) (rootCost J)
        (fun s => root idx v (TreeSchedule.data s)) :=
      Cmp.sel (ι := TreeSchedule.State D T n) Sum.inl (root_cb idx v)
    have h := Cb.and hr (Cb.var (ι := TreeSchedule.State D T n) (.inr (v,t)))
    simpa only [Nat.add_zero] using h
  have hc := (Cb.bigOr hv).congr (φ' := fun s => readRoots idx s t)
    (fun s => by
      rw [Bool.eq_iff_iff]
      simp only [readRoots, decide_eq_true_eq])
  simpa only [Fintype.card_fin, Nat.add_assoc] using hc

theorem readRoots_eq {T : Type} (idx : Fin n × J → D)
    (s : TreeSchedule.State D T n → Bool) (a : T → Bool)
    (he : ∃ v, root idx v (TreeSchedule.data s) = true)
    (ha : ∀ v, root idx v (TreeSchedule.data s) = true → TreeSchedule.table s v = a) :
    readRoots idx s = a := by
  classical
  funext t
  rw [Bool.eq_iff_iff]
  simp only [readRoots, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ⟨v,hv,ht⟩
    rwa [ha v hv] at ht
  · intro ht
    obtain ⟨v,hv⟩ := he
    exact ⟨v,hv,by rwa [ha v hv]⟩

end PEqualNP.Outside.L_meta_29751.LayoutGuard


namespace PEqualNP.Outside.L_meta_29751.LeafTable

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
  simp only [Fintype.card_fin] at hc
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
  simp only [Fintype.card_fin] at h
  refine Cb.congr (Cb.mono (Cb.and h (localC gate u)) (by
    change m * (5 * (d + 3) + 3) + 1 + 32 + 1 ≤ _
    omega)) (fun x => ?_)
  rw [Bool.eq_iff_iff]
  simp only [accept, Bool.and_eq_true, decide_eq_true_eq]

private noncomputable def pop (v : Forms → Bool) : ℕ :=
  (Finset.univ.filter (fun u => v u = true)).card

private theorem forms_card : Fintype.card Forms = 8 := by
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
    have hc : Fintype.card (Forms → Bool) = 256 := by
      rw [Fintype.card_fun, forms_card, Fintype.card_bool]
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
  simpa only [Fintype.card_fin, Nat.mul_comm t 5121] using Cmp.ofBits h

private theorem count_eq_pop {m d : ℕ} (gate : Bool) (a : Fin (2 ^ d)) (x : Input m d → Bool) :
    count gate x a = pop (accept gate a x) := by
  classical
  unfold count pop
  apply congrArg Finset.card
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, accept_correct]

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
  simpa only [budget, Fintype.card_fin] using Cmp.piU h

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
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold count
  apply congrArg Finset.card
  ext u
  simp

theorem fieldTableC (m d t : ℕ) (gate : Bool) :
    Cmp (Input m d) (Fin (2 ^ d) × Fin t) (budget m d t)
      (fun x p => (Nat.card {u : Fin 3 → ZMod 2 // fieldValid gate x p.1 u}).testBit p.2.val) := by
  refine Cmp.congr (tableC m d t gate) (fun x p => ?_)
  rw [count_eq_fieldCard]

end PEqualNP.Outside.L_meta_29751.LeafTable


namespace PEqualNP.Outside.L_meta_29751

abbrev Predicates (J : Type*) := J → (Fin 3 → F) → Prop

def FormSpan {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (p : J → Bool) : Submodule F V := selectedSpan R (fun i => p i.1)

def CutSpan {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (p : J → Bool) : Submodule F V := FormSpan R p ⊓ FormSpan R (fun j => !p j)

lemma row_mem {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (p : J → Bool) {j : J} (hj : p j = true) (e : Fin 3) :
    R (j,e) ∈ FormSpan R p := Submodule.subset_span ⟨(j,e), hj, rfl⟩

def localGood {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (P : Predicates J) (p : J → Bool) (f : Dual (FormSpan R p)) : Prop :=
  ∀ j (hj : p j = true), P j (fun e => f ⟨R (j,e), row_mem R p hj e⟩)

lemma localGood_extension {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (P : Predicates J) (p : J → Bool) (v : Dual V) :
    localGood R P p (v.comp (FormSpan R p).subtype) ↔ ∀ j, p j = true → P j (fun e => v (R (j,e))) :=
  Iff.rfl

def genMembers {ι V : Type*} [AddCommGroup V] [Module F V]
    (S : Submodule F V) (A : ι → V) (hA : Submodule.span F (Set.range A) = S) (i : ι) : S :=
  ⟨A i, hA ▸ Submodule.subset_span ⟨i,rfl⟩⟩

lemma genMembers_span {ι V : Type*} [AddCommGroup V] [Module F V]
    (S : Submodule F V) (A : ι → V) (hA : Submodule.span F (Set.range A) = S) :
    Submodule.span F (Set.range (genMembers S A hA)) = ⊤ := by
  let T := Submodule.span F (Set.range (genMembers S A hA))
  have hmap : T.map S.subtype = S := by
    rw [show T = Submodule.span F (Set.range (genMembers S A hA)) from rfl, Submodule.map_span, ← Set.range_comp]
    exact hA
  ext a
  constructor
  · intro _; trivial
  · intro _
    have ha : (a : V) ∈ T.map S.subtype := hmap.symm ▸ a.prop
    obtain ⟨b,hb,he⟩ := ha
    exact (S.injective_subtype he) ▸ hb

def genValue {ι V : Type*} [AddCommGroup V] [Module F V]
    {S : Submodule F V} {A : ι → V} (hA : Submodule.span F (Set.range A) = S)
    (f : Dual S) : ι → F := fun i => f (genMembers S A hA i)

lemma genValue_injective {ι V : Type*} [AddCommGroup V] [Module F V]
    {S : Submodule F V} {A : ι → V} (hA : Submodule.span F (Set.range A) = S) :
    Function.Injective (genValue hA) := by
  intro f g h
  exact LinearMap.ext_on_range (genMembers_span S A hA) fun i => congrFun h i

def address {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (p : J → Bool) {d : ℕ} (A : Fin d → V)
    (hA : Submodule.span F (Set.range A) = CutSpan R p) (f : Dual (FormSpan R p)) : Fin d → F :=
  genValue hA (restr inf_le_left f)

noncomputable def tableCount {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (P : Predicates J) (p : J → Bool) {d : ℕ} (A : Fin d → V)
    (hA : Submodule.span F (Set.range A) = CutSpan R p) (addr : Fin d → F) : ℕ :=
  Nat.card {f : Dual (FormSpan R p) // localGood R P p f ∧ address R p A hA f = addr}

lemma address_extension {J V : Type*} [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (p : J → Bool) {d : ℕ} (A : Fin d → V)
    (hA : Submodule.span F (Set.range A) = CutSpan R p) (f : Dual V) :
    address R p A hA (f.comp (FormSpan R p).subtype) = fun i => f (A i) := rfl

lemma leaf_span {J V : Type*} [DecidableEq J] [AddCommGroup V] [Module F V]
    (R : J × Fin 3 → V) (j : J) :
    Submodule.span F (Set.range fun e => R (j,e)) = FormSpan R (fun a => decide (a = j)) := by
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
    (hA : Submodule.span F (Set.range A) = CutSpan R (fun a => decide (a = j)))
    (x : Fin d → F) :
    tableCount R P (fun a => decide (a = j)) A hA x = Nat.card {y : Fin 3 → F // P j y ∧
      ∃ u : Dual V, (∀ t, u (A t) = x t) ∧ ∀ e, u (R (j,e)) = y e} := by
  let b : J → Bool := fun a => decide (a = j)
  let S := FormSpan R b
  let m : Dual S → (Fin 3 → F) := genValue (leaf_span R j)
  have hm : Function.Injective m := genValue_injective _
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
    (hA : Submodule.span F (Set.range A) = LeftBoundary L H E)
    (hB : Submodule.span F (Set.range B) = RightBoundary L H E)
    (hC : Submodule.span F (Set.range C) = ParentBoundary L H E)
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
    (hA : Submodule.span F (Set.range A) = LeftBoundary L H E)
    (hB : Submodule.span F (Set.range B) = RightBoundary L H E)
    (hC : Submodule.span F (Set.range C) = ParentBoundary L H E)
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
    (hA : Submodule.span F (Set.range A) = CutSpan R l)
    (hB : Submodule.span F (Set.range B) = CutSpan R h)
    (hC : Submodule.span F (Set.range C) = CutSpan R (fun j => l j || h j)) (z : Fin d → F) :
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
  apply Finset.sum_congr
  · exact congrArg (fun i => @Finset.univ (Fin d → F) i) (Subsingleton.elim _ _)
  intro x _
  apply Finset.sum_congr
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

end PEqualNP.Outside.L_meta_29751


namespace PEqualNP.Outside.L_meta_29751

open Donor PackedTape

variable {k r q n : ℕ}

abbrev In (k r q n : ℕ) := Greedy.Input (Raw k r q n) k
abbrev PreMid (k r q n : ℕ) := In k r q n ⊕ (Unit ⊕ FormData k r)
abbrev BasisIx (k r n : ℕ) := Fin n ⊕ Leaf k r
abbrev Pre (k r q n d : ℕ) := PreMid k r q n ⊕ (BasisIx k r n × WidthOut (Param k r) d)

def preIn {d : ℕ} (x : Pre k r q n d → Bool) : In k r q n → Bool := x ∘ Sum.inl ∘ Sum.inl
def preRaw {d : ℕ} (x : Pre k r q n d → Bool) : Raw k r q n → Bool := preIn x ∘ Sum.inl
def preForms {d : ℕ} (x : Pre k r q n d → Bool) : FormData k r → Bool :=
  fun i => x (.inl (.inr (.inr i)))
def preAffine {d : ℕ} (x : Pre k r q n d → Bool) : Bool := x (.inl (.inr (.inl ())))
def preBasis {d : ℕ} (x : Pre k r q n d → Bool) (p : BasisIx k r n) : WidthOut (Param k r) d → Bool :=
  fun j => x (.inr (p,j))
def preBags {d : ℕ} (x : Pre k r q n d → Bool) : Fin n × Leaf k r → Bool :=
  fun (i,j) => preRaw x (bagSlot i j)
def preBagIx [DecidableEq (Leaf k r)] (x : Raw k r q n → Bool) (i : BasisIx k r n) : Leaf k r → Bool :=
  i.elim (readBag x) (fun j a => decide (a = j))

def preWidth {d : ℕ} (x : Pre k r q n d → Bool) (p : BasisIx k r n) : Bool := preBasis x p (.inr ())
def preGen {d : ℕ} (x : Pre k r q n d → Bool) (p : BasisIx k r n) : Fin d → Param k r → F :=
  widthOutGen (preBasis x p)

def basisInput [DecidableEq (Leaf k r)] (i : BasisIx k r n) (x : PreMid k r q n → Bool) :
    WidthIn (FormIx k r) (Param k r) → Bool :=
  Sum.elim (fun (j,t) => x (.inr (.inr (j, .inl t))))
    (fun j => preBagIx (fun a => x (.inl (.inl a))) i j.1)

lemma basisInput_cmp [DecidableEq (Leaf k r)] (i : BasisIx k r n) :
    Cmp (PreMid k r q n) (WidthIn (FormIx k r) (Param k r))
      (Fintype.card (WidthIn (FormIx k r) (Param k r))) (basisInput i) := by
  rw [← Nat.mul_one (Fintype.card (WidthIn (FormIx k r) (Param k r)))]
  apply Cmp.ofBits
  rintro (⟨j,t⟩ | j)
  · exact (Cb.var (ι := PreMid k r q n) (.inr (.inr (j, .inl t)))).mono (by decide)
  · cases i with
    | inl u => exact (Cb.var (ι := PreMid k r q n) (.inl (.inl (bagSlot u j.1)))).mono (by decide)
    | inr u => exact Cb.const (decide (j.1 = u))

def preCost (k r q n d : ℕ) : ℕ :=
  tapePrepCost k r q + (Fintype.card (FormData k r) * 21) +
  Fintype.card (BasisIx k r n) *
    (Fintype.card (WidthIn (FormIx k r) (Param k r)) + widthPrepCost (FormIx k r) (Param k r) d)

set_option maxHeartbeats 1000000 in
theorem preprocess [DecidableEq (Leaf k r)] [DecidableEq (Param k r)] (hk : 0 < k) (d : ℕ) :
    ∃ T : (In k r q n → Bool) → Pre k r q n d → Bool,
      Cmp (In k r q n) (Pre k r q n d) (preCost k r q n d) T ∧
      ∃ S : (Raw k r q n → Bool) → TapeOut k r → Bool,
      (∀ x,
        (S x (.inr ()) = true ↔ ∃ u, latticeMap hk (readObs x) u = rowTarget (readName x) (readRhs x)) ∧
        Submodule.span F (Set.range (tapePrepGen (S x))) = LinearMap.ker (latticeMap hk (readObs x)) ∧
        (S x (.inr ()) = true →
          latticeMap hk (readObs x) (tapePrepPoint (S x)) = rowTarget (readName x) (readRhs x))) ∧
        ∀ x : In k r q n → Bool,
          preIn (T x) = x ∧ preAffine (T x) = S (x ∘ Sum.inl) (.inr ()) ∧
          preForms (T x) = evalForms hk (S (x ∘ Sum.inl)) ∧
          (∀ p,
            (preWidth (T x) p = true ↔ Module.finrank F
              (CutSpan (linearRows (preForms (T x))) (preBagIx (preRaw (T x)) p)) ≤ d) ∧
            (preWidth (T x) p = true → Submodule.span F (Set.range (preGen (T x) p)) =
              CutSpan (linearRows (preForms (T x))) (preBagIx (preRaw (T x)) p))) ∧
          ∀ v j, (∀ a, readBag (preRaw (T x)) v a = decide (a = j)) →
            preBasis (T x) (.inl v) = preBasis (T x) (.inr j) := by
  classical
  obtain ⟨S,hS,hSsem⟩ := tapePrep (k:=k) (r:=r) (q:=q) (n:=n) hk
  obtain ⟨B,hB,hBsem⟩ := widthPrep (J:=FormIx k r) (U:=Param k r) d
  let A (x : In k r q n → Bool) : PreMid k r q n → Bool :=
    Sum.elim x (Sum.elim (fun _ => S (x ∘ Sum.inl) (.inr ())) (evalForms hk (S (x ∘ Sum.inl))))
  have hextra : Cmp (TapeOut k r) (Unit ⊕ FormData k r) (Fintype.card (FormData k r) * 21)
      (fun v => Sum.elim (fun _ => v (.inr ())) (evalForms hk v)) := by
    have h := Cmp.pair (Cmp.wire (fun _ : Unit => (Sum.inr () : TapeOut k r))) (evalFormsCmp (r:=r) hk)
    simpa only [Nat.zero_add] using h
  have hA : Cmp (In k r q n) (PreMid k r q n) (tapePrepCost k r q + Fintype.card (FormData k r) * 21) A :=
    Cmp.keep (Cmp.comp (Cmp.sel Sum.inl hS) hextra)
  let T (x : In k r q n → Bool) : Pre k r q n d → Bool :=
    Sum.elim (A x) (fun (i,j) => B (basisInput i (A x)) j)
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

end PEqualNP.Outside.L_meta_29751


namespace PEqualNP.Outside.L_meta_29751

open Donor

variable {k r q : ℕ}

abbrev Direction (hk : 0 < k) (obs : Fin q → Tape k r) :=
  {z : Tape k r // (∀ b, z.2 b 0 = rot hk (start b) z.1) ∧ ∀ i, pair (obs i) z = 0}

def paramMap (o : TapeOut k r → Bool) : (Param k r → F) →ₗ[F] (Coord k r → F) :=
  Fintype.linearCombination F (tapePrepGen o)

lemma paramMap_range (hk : 0 < k) (obs : Fin q → Tape k r) (o : TapeOut k r → Bool)
    (h : Submodule.span F (Set.range (tapePrepGen o)) = LinearMap.ker (latticeMap hk obs)) :
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
    (h : Submodule.span F (Set.range (tapePrepGen o)) = LinearMap.ker (latticeMap hk obs))
    (a : Param k r → F) : Direction hk obs :=
  ⟨flatten.symm (paramMap o a), (direction_iff hk obs _).mpr (by
    rw [LinearEquiv.apply_symm_apply]
    have hx : paramMap o a ∈ LinearMap.range (paramMap o) := ⟨a,rfl⟩
    rw [paramMap_range hk obs o h] at hx
    exact hx)⟩

lemma paramDirection_surj (hk : 0 < k) (obs : Fin q → Tape k r) (o : TapeOut k r → Bool)
    (h : Submodule.span F (Set.range (tapePrepGen o)) = LinearMap.ker (latticeMap hk obs)) :
    Function.Surjective (paramDirection hk obs o h) := by
  intro z
  have hz : flatten z.val ∈ LinearMap.ker (latticeMap hk obs) := (direction_iff hk obs z.val).mp z.prop
  rw [← paramMap_range hk obs o h] at hz
  obtain ⟨a,ha⟩ := hz
  refine ⟨a, Subtype.ext ?_⟩
  change flatten.symm (paramMap o a) = z.val
  rw [ha, LinearEquiv.symm_apply_apply]

lemma post_width_eq (hk : 0 < k) (obs : Fin q → Tape k r) (o : TapeOut k r → Bool)
    (h : Submodule.span F (Set.range (tapePrepGen o)) = LinearMap.ker (latticeMap hk obs))
    (p : Leaf k r → Bool) :
    Module.finrank F (CutSpan (linearRows (evalForms hk o)) p) =
      let D := Direction hk obs
      let sp := fun bag => Submodule.span F {f : D → F |
        ∃ (j : Leaf k r) (e : Fin 3), bag j = true ∧ f = fun z => form hk j e z.val}
      Module.finrank F (sp p ⊓ sp (fun j => !p j) : Submodule F (D → F)) := by
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
        Submodule.span F {u : Direction hk obs → F | ∃ (j : Leaf k r) (e : Fin 3),
          b j = true ∧ u = fun z => form hk j e z.val} := by
    unfold selectedSpan
    apply congrArg (Submodule.span F)
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
  · simp only [gatePred, h, localCheck, Sum.elim_inl]
  · simp only [gatePred, h, localCheck, Sum.elim_inr]

end PEqualNP.Outside.L_meta_29751

namespace PEqualNP.Outside.L_meta_29751

open Donor

variable {k r q : ℕ}

theorem root_tableCount (hk : 0 < k) (name : Bool → Word k) (c : Bool → Fin r → Word k)
    (obs : Fin q → Tape k r) (rhs : Fin q → F) (pref : Fin k → Option F)
    (o : TapeOut k r → Bool)
    (hgen : Submodule.span F (Set.range (tapePrepGen o)) = LinearMap.ker (latticeMap hk obs))
    (hpoint : latticeMap hk obs (tapePrepPoint o) = rowTarget name rhs)
    {d : ℕ} (A : Fin d → Param k r → F)
    (hA : Submodule.span F (Set.range A) = CutSpan (linearRows (evalForms hk o)) (fun _ => true)) :
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
  have hzSurj : Function.Surjective z := by
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

end PEqualNP.Outside.L_meta_29751


namespace PEqualNP.Outside.L_meta_29751

open Donor PackedTape

variable {k r q n d : ℕ}

abbrev Addr (d : ℕ) := Fin (2^d)
abbrev TableIx (k r d : ℕ) := Addr d × Fin (tapeSize k r + 1)
abbrev JoinState (k r q n d : ℕ) := Pre k r q n d ⊕ (TableIx k r d ⊕ TableIx k r d)
abbrev JoinIx (d : ℕ) := Fin d ⊕ (Fin d ⊕ Fin d)

abbrev JInput (k r d : ℕ) := JIn (Fin (3*d)) d d d (tapeSize k r + 1)
def joinLocalCost (k r d : ℕ) : ℕ :=
  nullPrepCost (JoinIx d) (Param k r) (3*d) + Fintype.card (JInput k r d) +
    topCost d d d (3*d) (tapeSize k r + 1) ((3*d)/2)

open Classical in
set_option maxHeartbeats 1200000 in
lemma joinLocal_cmp (v l h : Fin n) :
    ∃ FJ : (JoinState k r q n d → Bool) → TableIx k r d → Bool,
      Cmp (JoinState k r q n d) (TableIx k r d) (joinLocalCost k r d) FJ ∧
      ∀ (x : Pre k r q n d → Bool) (f g : TableIx k r d → Bool) (a : Addr d)
        (j : Fin (tapeSize k r + 1)),
        FJ (Sum.elim x (Sum.elim f g)) (a,j) =
          (∑ b : Addr d, ∑ c : Addr d, if TripleRelation
            (preGen x (.inl l)) (preGen x (.inl h)) (preGen x (.inl v))
            (vecN d b.val) (vecN d c.val) (vecN d a.val) then
            tabN (fun e => f (b,e)) * tabN (fun e => g (c,e)) else 0).testBit j.val := by
  classical
  let Q := JoinState k r q n d
  let U := Param k r
  let M := Fin (3*d)
  let I := JoinIx d
  let route : NullIn I U → Q := fun (i,t) => match i with
    | .inl u => .inl (.inr (.inl l, .inl (t,u)))
    | .inr (.inl u) => .inl (.inr (.inl h, .inl (t,u)))
    | .inr (.inr u) => .inl (.inr (.inl v, .inl (t,u)))
  have hc : Fintype.card I ≤ 3*d := by simp [I, JoinIx]; omega
  obtain ⟨S,hS,hsem⟩ := nullPrep (J:=I) (U:=U) (3*d) hc
  obtain ⟨J,hJ,hJsem⟩ := joinAll M d d d (tapeSize k r + 1)
  let A (x : Q → Bool) : NullOut I (3*d) → Bool := S (x ∘ route)
  let D := Q ⊕ NullOut I (3*d)
  let B (z : D → Bool) : JInput k r d → Bool := Sum.elim
    (fun (i,x) => match x with
      | .inl j => z (.inr (.inl j,i))
      | .inr (.inl j) => z (.inr (.inr (.inl j),i))
      | .inr (.inr (.inl j)) => z (.inr (.inr (.inr j),i))
      | .inr (.inr (.inr ())) => false)
    (fun x => z (.inl (.inr x)))
  have hB : Cmp D (JInput k r d) (Fintype.card (JInput k r d)) B := by
    rw [← Nat.mul_one (Fintype.card (JInput k r d))]
    apply Cmp.ofBits
    rintro (⟨i,(a | a | a | ⟨⟩)⟩ | z)
    · exact (Cb.var (ι:=D) (.inr (.inl a,i))).mono (by decide)
    · exact (Cb.var (ι:=D) (.inr (.inr (.inl a),i))).mono (by decide)
    · exact (Cb.var (ι:=D) (.inr (.inr (.inr a),i))).mono (by decide)
    · exact Cb.const false
    · exact (Cb.var (ι:=D) (.inl (.inr z))).mono (by decide)
  have hJ' : Cmp (JInput k r d) (TableIx k r d)
      (topCost d d d (3*d) (tapeSize k r+1) ((3*d)/2)) J := by
    have hd : (d+d+d)/2 = (3*d)/2 := by omega
    have hcost := congrArg₂ (fun m u => topCost d d d m (tapeSize k r+1) u)
      (Fintype.card_fin (3*d)) hd
    exact hJ.mono hcost.le
  refine ⟨fun x => J (B (Sum.elim x (A x))),
    Cmp.comp (Cmp.comp (Cmp.keep (Cmp.sel route hS)) hB) hJ', ?_⟩
  intro x f g a j
  let y : Q → Bool := Sum.elim x (Sum.elim f g)
  let R : I → U → F := nullDecoded (y ∘ route)
  have hR : R = Sum.elim (preGen x (.inl l)) (Sum.elim (preGen x (.inl h)) (preGen x (.inl v))) := by
    funext i u
    rcases i with t | t | t <;> rfl
  have hr := hsem (y ∘ route)
  let E := S (y ∘ route)
  have hEq (xL xH xP : Fin d → F) :
      jSat (B (Sum.elim y E)) xL xH xP ↔
      TripleRelation (preGen x (.inl l)) (preGen x (.inl h)) (preGen x (.inl v)) xL xH xP := by
    have hsp := hr
    let U0 : I → F := Sum.elim xL (Sum.elim xH xP)
    have hEval : (∃ g : Dual (U → F), ∀ j, g (R j) = U0 j) ↔
        TripleRelation (preGen x (.inl l)) (preGen x (.inl h)) (preGen x (.inl v)) xL xH xP := by
      rw [hR]
      constructor
      · rintro ⟨g,hg⟩
        exact ⟨g, fun j => hg (.inl j), fun j => hg (.inr (.inl j)), fun j => hg (.inr (.inr j))⟩
      · rintro ⟨g,hl,hh,hp⟩
        exact ⟨g, fun t => match t with | .inl i => hl i | .inr (.inl i) => hh i | .inr (.inr i) => hp i⟩
    have he : (∀ i, dotProduct (nullOutGen E i) U0 = 0) ↔ (∃ g : Dual (U → F), ∀ j, g (R j) = U0 j) := by
      rw [evalRange]
      have hspan : ∀ w : I → F, w ∈ Submodule.span F (Set.range (nullOutGen E)) ↔
          (∑ j, w j • R j) = 0 := by
        intro w
        rw [hsp, LinearMap.mem_ker, Fintype.linearCombination_apply]
      constructor
      · intro hb w hw
        let L : (I → F) →ₗ[F] F := dotProductEquiv F I U0
        have hs : Submodule.span F (Set.range (nullOutGen E)) ≤ LinearMap.ker L := by
          apply Submodule.span_le.mpr
          rintro _ ⟨t,rfl⟩
          change dotProduct U0 (nullOutGen E t) = 0
          rw [dotProduct_comm]
          exact hb t
        exact hs ((hspan w).mpr hw)
      · intro hb i
        rw [dotProduct_comm]
        exact hb _ ((hspan _).mp (Submodule.subset_span ⟨i,rfl⟩))
    refine (Iff.trans ?_ he).trans hEval
    unfold jSat
    apply forall_congr'
    intro i
    have hs (f : JoinIx d → F) :
        ∑ j, f j = (∑ j : Fin d, f (.inl j)) +
          (∑ j : Fin d, f (.inr (.inl j))) + (∑ j : Fin d, f (.inr (.inr j))) := by
      simp only [JoinIx, Fintype.sum_sum_type, add_assoc]
    rw [dotProduct, hs]
    rfl
  change J (B (Sum.elim y E)) (a,j) = _
  rw [hJsem]
  congr 1
  unfold jTot
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  by_cases hh : TripleRelation (preGen x (.inl l)) (preGen x (.inl h)) (preGen x (.inl v))
      (vecN d b.val) (vecN d c.val) (vecN d a.val)
  · rw [ite_eq_left hh, ite_eq_left ((hEq _ _ _).mpr hh)]
    rfl
  · rw [ite_eq_right hh, ite_eq_right (fun e => hh ((hEq _ _ _).mp e))]

end PEqualNP.Outside.L_meta_29751

namespace PEqualNP.Outside.L_meta_29751

open Donor PackedTape

variable {k r q n d : ℕ}

def prefixMask (x : In k r q n → Bool) (j : Fin k) : Bool := x (.inr (.inl j))
def prefixValue (x : In k r q n → Bool) (j : Fin k) : Bool := x (.inr (.inr j))
def readPref (x : In k r q n → Bool) (j : Fin k) : Option F :=
  if prefixMask x j then some (b2z (prefixValue x j)) else none

def isGate : Leaf k r → Bool := Sum.elim (fun _ => false) (fun _ => true)

abbrev LInput (d : ℕ) := LeafTable.Input (d+3) d

def leafLocalCost (k r d : ℕ) : ℕ := nullPrepCost (Fin (d+3)) (Param k r) (d+3) +
  Fintype.card (LInput d) + LeafTable.budget (d+3) d (tapeSize k r + 1)

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
  let B (v : D ⊕ NullOut I (d+3) → Bool) : LInput d → Bool := Sum.elim
    (fun (i,t) => v (.inr (t,i)))
    (Sum.elim (fun e => v (.inl (.inl (.inr (.inr ((j,e), .inr ()))))))
      (Sum.elim (fun _ => match j with
          | .inl j => v (.inl (.inl (.inl (.inr (.inl j)))))
          | .inr _ => false)
        (Sum.elim (fun _ => match j with
            | .inl j => v (.inl (.inl (.inl (.inr (.inr j)))))
            | .inr _ => false)
          (fun _ => match j with
            | .inl _ => false
            | .inr (b,t,i) => v (.inl (.inl (.inl (.inl (cSlot b t i)))))))))
  have hB : Cmp (D ⊕ NullOut I (d+3)) (LInput d) (Fintype.card (LInput d)) B := by
    rw [← Nat.mul_one (Fintype.card (LInput d))]
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
  let w := B (Sum.elim x (A x))
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
    have hspan : ∀ v : I → F, v ∈ Submodule.span F (Set.range (nullOutGen (A x))) ↔
        (∑ i, v i • R i) = 0 := by
      intro v
      rw [hR, LinearMap.mem_ker, Fintype.linearCombination_apply]
    constructor
    · intro ht v hv
      let f : (I → F) →ₗ[F] F := dotProductEquiv F I z
      have hc : Submodule.span F (Set.range (nullOutGen (A x))) ≤ LinearMap.ker f := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change dotProduct z (nullOutGen (A x) i) = 0
        rw [dotProduct_comm]
        exact ht i
      exact hc ((hspan v).mpr hv)
    · intro hv i
      rw [dotProduct_comm]
      exact hv _ ((hspan _).mp (Submodule.subset_span ⟨i,rfl⟩))
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

end PEqualNP.Outside.L_meta_29751


namespace PEqualNP.Outside.L_meta_29751

open Donor PackedTape

variable {k r q n d : ℕ}

def bagRoute : Fin n × Leaf k r → Pre k r q n d := fun (v,j) => .inl (.inl (.inl (bagSlot v j)))

def inputHit (hk : 0 < k) (x : Raw k r q n → Bool) (key : Fin k → Bool) : Prop :=
  ∀ i, pair (readObs x i) ((fun j => b2z (key j)),
    actual hk (readName x) (readC x) (fun j => b2z (key j))) = readRhs x i

noncomputable def inputGood (hk : 0 < k) (w : ℕ) (x : Raw k r q n → Bool) : Bool := by
  classical
  let D := Direction hk (readObs x)
  let sp := fun b : Leaf k r → Bool => Submodule.span F {f : D → F |
    ∃ (j : Leaf k r) (e : Fin 3), b j = true ∧ f = fun z => form hk j e z.val}
  exact decide (LayoutGuard.layout (fun (v,j) => bagSlot v j) x = true ∧
    ∀ v : Fin n, Module.finrank F ((sp (readBag x v) ⊓ sp (fun j => !(readBag x v j))) : Submodule F (D → F)) ≤ w)

lemma tableCount_congr {J V : Type*} [AddCommGroup V] [Module F V] {d : ℕ}
    (R : J × Fin 3 → V) (P : Predicates J) {p p' : J → Bool} (hp : p = p')
    {A A' : Fin d → V} (he : A = A')
    (hA : Submodule.span F (Set.range A) = CutSpan R p)
    (hA' : Submodule.span F (Set.range A') = CutSpan R p') (x : Fin d → F) :
    tableCount R P p A hA x = tableCount R P p' A' hA' x := by
  subst p'; subst A'; rfl

lemma tableCount_bound {J U : Type*} [Fintype U] {d : ℕ}
    (R : J × Fin 3 → (U → F)) (P : Predicates J) (p : J → Bool) (A : Fin d → U → F)
    (hA : Submodule.span F (Set.range A) = CutSpan R p) (x : Fin d → F) :
    tableCount R P p A hA x < 2 ^ (Fintype.card U + 1) := by
  let S := FormSpan R p
  have h0 : Module.finrank F (Dual S) ≤ Fintype.card U := by
    rw [Subspace.dual_finrank_eq, ← Module.finrank_pi (R := F)]
    exact Submodule.finrank_le S
  have hNat : Nat.card F = 2 := by simp [Nat.card_eq_fintype_card, ZMod.card]
  have h1 : Nat.card (Dual S) ≤ 2 ^ Fintype.card U := by
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

def scheduleBudget (k r q n d : ℕ) : ℕ :=
  Fintype.card (Fin n × TableIx k r d) + n * TreeSchedule.stepCost (Pre k r q n d)
    (Leaf k r) (TableIx k r d) n (max (leafLocalCost k r d) (joinLocalCost k r d))
    (LayoutGuard.guardCost (Leaf k r))

def finalCountBudget (k r n : ℕ) : ℕ := (k+2) *
  (LayoutGuard.layoutCost (Leaf k r) n + (n+1) + n * (LayoutGuard.rootCost (Leaf k r) + 2) + 4)

def oracleCost (k r q n d : ℕ) := preCost k r q n d + scheduleBudget k r q n d + finalCountBudget k r n

abbrev TreeState (k r q n d : ℕ) := TreeSchedule.State (Pre k r q n d) (TableIx k r d) n

def zeroAddr (d : ℕ) : Addr d := ⟨0, Nat.two_pow_pos d⟩

noncomputable def fitSignal (x : Pre k r q n d → Bool) : Bool := by
  classical
  exact LayoutGuard.layout bagRoute x && decide (∀ v : Fin n, preWidth x (.inl v) = true)

def widenCount (k r : ℕ) (j : Fin (k+1)) : Fin (tapeSize k r + 1) :=
  ⟨j.val, j.isLt.trans_le (by change k+1 ≤ (2*r+3)*k+1; nlinarith)⟩

noncomputable def finishCount (s : TreeState k r q n d → Bool) : Greedy.Reply k → Bool :=
  Sum.elim (fun _ => fitSignal (TreeSchedule.data s)) (fun j =>
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
      simp only [Fintype.card_fin, Nat.zero_add, Nat.mul_one] at h
      refine h.congr fun s => ?_
      exact TreeSchedule.decision_eq _ _ _
    exact Cb.and (Cmp.sel Sum.inl (LayoutGuard.layout_cb (bagRoute (k:=k) (r:=r) (q:=q) (n:=n) (d:=d)))) hwidth
  have hRead (t : TableIx k r d) : Cb D (n*(a+2)+1) (fun s => LayoutGuard.readRoots bagRoute s t) := by
    have hv (v : Fin n) : Cb D (a+1) (fun s => (LayoutGuard.root bagRoute v (TreeSchedule.data s) &&
        TreeSchedule.table s v t)) := by
      have h : Cb D a (fun s => LayoutGuard.root bagRoute v (TreeSchedule.data s)) :=
        Cmp.sel Sum.inl (LayoutGuard.root_cb bagRoute v)
      simpa only [Nat.add_zero] using Cb.and h (Cb.var (ι:=D) (.inr (v,t)))
    have h := (Cb.bigOr hv).congr (φ' := fun s => LayoutGuard.readRoots bagRoute s t)
      (fun z => by
        rw [Bool.eq_iff_iff]
        simp only [LayoutGuard.readRoots, decide_eq_true_eq])
    simpa only [Fintype.card_fin, Nat.add_assoc] using h
  rw [show finalCountBudget k r n =
      Fintype.card (Greedy.Reply k) * (l+(n+1)+n*(a+2)+4) by
    unfold finalCountBudget Greedy.Reply
    simp [l,a,Nat.add_comm,Nat.add_assoc] <;> omega]
  apply Cmp.ofBits
  rintro (⟨⟩ | i)
  · exact hg.mono (by omega)
  · apply Cb.mono (Cb.and (Cb.and hg (Cb.var (ι:=D) (.inl (.inl (.inr (.inl ())))))) (hRead _))
    omega

end PEqualNP.Outside.L_meta_29751

namespace PEqualNP.Outside.L_meta_29751

open Donor PackedTape

variable {k r q n : ℕ}

set_option maxHeartbeats 2500000 in
theorem countOracle (hk : 0 < k) (w : ℕ) :
    let d := min (tapeSize k r) w
    ∃ O : (In k r q n → Bool) → Greedy.Reply k → Bool,
      Cmp (In k r q n) (Greedy.Reply k) (oracleCost k r q n d) O ∧
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
  choose FJ hFJ hJsem using fun v l h : Fin n => joinLocal_cmp (k:=k) (r:=r) (q:=q) (n:=n) (d:=d) v l h
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
  have hx : preRaw z = x := congrArg (fun f => f ∘ Sum.inl) hIn
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
    have hh : Module.finrank F (CutSpan rowForm (bg v)) ≤ N :=
      (Submodule.finrank_le _).trans (by simp [N, Param])
    have hw := post_width_eq hk (readObs x) (S x) hTape.2.1 (bg v)
    have heq := congrArg (fun R => Module.finrank F (CutSpan R (bg v))) (congrArg linearRows hForm)
    have hw' := heq.trans hw
    change Module.finrank F (CutSpan rowForm (bg v)) ≤ d ↔ _
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
    have hspan (v : Fin n) : Submodule.span F (Set.range (preGen z (.inl v))) = CutSpan rowForm (bg v) := by
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
        have hs : Submodule.span F (Set.range (preGen z (.inr i))) = CutSpan rowForm (fun t => decide (t=i)) := by
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
          FJ v l h (Sum.elim z (Sum.elim (bits l) (bits h))) = bits v := by
        obtain ⟨hdis, hUnion⟩ := (LayoutGuard.guard_split_true bagRoute v l h z).mp hv
        have hd' : ∀ i, bg l i = true → bg h i = false := by
          simpa only [LayoutGuard.mask, hmask] using hdis
        have hp : bg v = fun j => bg l j || bg h j := by
          funext i
          simpa only [LayoutGuard.mask, hmask] using hUnion i
        have hs : Submodule.span F (Set.range (preGen z (.inl v))) = CutSpan rowForm (fun j => bg l j || bg h j) := hp ▸ hspan v
        funext j
        rcases j with ⟨a,i⟩
        have hCnt := tableCount_congr rowForm good hp rfl (hspan v) hs (vecN d a.val)
        rw [splitTableCount rowForm good (bg l) (bg h) hd' _ _ _ (hspan l) (hspan h) hs] at hCnt
        obtain ⟨ev,hev⟩ := vecEquiv_exists d
        have hvec (b : Addr d) : ev b = vecN d b.val := funext (hev b)
        rw [hJsem]
        change _ = (C v a).testBit i.val
        congr 1
        rw [show C v a = _ from hCnt]
        rw [← Equiv.sum_comp ev]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Equiv.sum_comp ev, hvec]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hvec]
        have hl' : tabN (fun e => bits l (x,e)) = C l x := tabN_recover (hb l x)
        have hh' : tabN (fun e => bits h (y,e)) = C h y := tabN_recover (hb h y)
        rw [hl', hh']
      have hRun := TreeSchedule.run_sem FL FJ gr z bits (hAvail (Sum.elim z (fun _ => false)) rfl) hleaf hjoin
      have hzero : vecN d (zeroAddr d).val = 0 := by funext i; simp [vecN, zeroAddr]
      let amt := Greedy.cardinal (Greedy.matched (inputHit hk x) m p)
      have hRootCounts (v : Fin n) (hv : LayoutGuard.root bagRoute v z = true) : C v (zeroAddr d) = amt := by
        have hfull : bg v = fun _ => true := by
          funext i
          simpa only [LayoutGuard.mask, hmask] using (LayoutGuard.root_true bagRoute v z).mp hv i
        have hS' : Submodule.span F (Set.range (preGen z (.inl v))) = CutSpan rowForm (fun _ => true) :=
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

end PEqualNP.Outside.L_meta_29751


namespace PEqualNP.Outside.L_meta_29751

open Donor PackedTape

theorem le_mono_pow {P i j : ℕ} (hP : 1 ≤ P) (h : i ≤ j) : P ^ i ≤ P ^ j :=
  Nat.pow_le_pow_right hP h

lemma leaf_card (k r : ℕ) : Fintype.card (Leaf k r) = (2*r+1)*k := by
  simp [Leaf]
  ring

set_option maxHeartbeats 3500000 in
set_option maxRecDepth 1800 in
theorem full_size (k r q n w : ℕ) :
    let N := tapeSize k r
    let d := min N w
    let P := k+r+q+n+5
    (k+1)*oracleCost k r q n d + k*k+3*k+2+1 ≤ 2^(90+(3*d)/2)*P^40 := by
  intro N d P
  let A := P^2
  let B := 2 ^ (3*d/2)
  have hP : 5 ≤ P := by dsimp [P]; omega
  have hA : 1 ≤ A := Nat.pow_pos (by omega : 0 < P)
  have hA2 : 4 ≤ A := by
    have h := Nat.pow_le_pow_left (show 2 ≤ P by omega) 2
    exact h
  have hB : 1 ≤ B := Nat.two_pow_pos _
  have hP' : P ≤ A := by
    simpa only [pow_one] using (le_mono_pow (show 1 ≤ P by omega) (show 1 ≤ 2 by decide))
  have hk : k+2 ≤ A := (by dsimp [P]; omega : k+2 ≤ P).trans hP'
  have hn : n ≤ A := (by dsimp [P]; omega : n ≤ P).trans hP'
  have hN : N+1 ≤ A := by
    have h : (2*r+3)*k+1 ≤ (k+r+2)^2 := by
      nlinarith only [Nat.zero_le k, Nat.zero_le r, Nat.zero_le (k*k), Nat.zero_le (r*r)]
    exact h.trans (Nat.pow_le_pow_left (show k+r+2 ≤ P by dsimp [P]; omega) 2)
  have hd : d ≤ N := min_le_left ..
  have hde : 2^d ≤ B := Nat.pow_le_pow_right (by decide) (by omega)
  let L := Fintype.card (Leaf k r)
  let R := Fintype.card (EqRow k q)
  have hL : L ≤ A := by
    change Fintype.card (Leaf k r) ≤ A
    rw [leaf_card]
    exact (Nat.mul_le_mul_right k (show 2*r+1 ≤ 2*r+3 by omega)).trans
      ((Nat.le_succ N).trans hN)
  have hR : R ≤ 2*A := by
    simp only [R, EqRow, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    have h : 2*k+q ≤ 2*P := by dsimp [P]; omega
    exact h.trans (Nat.mul_le_mul_left _ hP')
  have hgl {a b c e : ℕ} (h : a+b+c+e+2 ≤ 16*A) : glCost a b c e ≤ 2^36*A^6 := by
    calc
      glCost a b c e ≤ 2^12 * (16*A)^6 :=
        Nat.mul_le_mul_left (2^12) (Nat.pow_le_pow_left h 6)
      _ = 2^12 * (16^6 * A^6) := by rw [mul_pow]
      _ = 2^36 * A^6 := by rw [← mul_assoc, show (2 : ℕ)^12 * 16^6 = 2^36 by decide]
  have hpow (i j : ℕ) (h : i ≤ j) := le_mono_pow hA h
  have hQ (i : ℕ) : 1 ≤ A^i := Nat.pow_pos hA
  have hAP : A ≤ A^2 := by simpa only [pow_one] using hpow 1 2 (by decide)
  have hAP3 : A^2 ≤ A^3 := hpow 2 3 (by decide)
  have hParam : Fintype.card (Param k r) = N := Fintype.card_fin _
  have hFormIx : Fintype.card (FormIx k r) = L * 3 := by
    unfold FormIx
    rw [Fintype.card_prod, Fintype.card_fin]
  have hFormData : Fintype.card (FormData k r) = L * 3 * (N+1) := by
    unfold FormData
    rw [Fintype.card_prod, hFormIx, Fintype.card_sum, hParam, Fintype.card_unit]
  have hBasis : Fintype.card (BasisIx k r n) = n + L := by
    unfold BasisIx
    rw [Fintype.card_sum, Fintype.card_fin]
  have hWidthOut : Fintype.card (WidthOut (Param k r) d) = N*d+1 := by
    unfold WidthOut
    rw [Fintype.card_sum, Fintype.card_prod, hParam, Fintype.card_fin, Fintype.card_unit]
  have hTP : tapePrepCost k r q ≤ 2^39*A^6 := by
    have hSys : tapePrepSysCost k r q = R*(N+1) := by
      unfold tapePrepSysCost ProjIn
      rw [Fintype.card_prod, Fintype.card_sum (α := Empty), Fintype.card_empty, Nat.zero_add,
        Fintype.card_sum (α := Coord k r) (β := Unit), coord_card, Fintype.card_unit]
    have hOut : Fintype.card (TapeOut k r) = N*(N+1)+1 := by
      unfold TapeOut
      rw [Fintype.card_sum, Fintype.card_prod, coord_card, Fintype.card_sum, hParam, Fintype.card_unit]
    unfold tapePrepCost
    rw [hSys, hOut]
    change 2 * (R * (N + 1) + glCost R 0 N N) + (N * (N + 1) + 1) ≤ _
    have g := hgl (a:=R) (b:=0) (c:=N) (e:=N) (by omega)
    have a := Nat.mul_le_mul hR hN
    have b := Nat.mul_le_mul (show N ≤ A by omega) hN
    nlinarith only [g, a, b, hpow 2 6 (by decide), hQ 6]
  have hf : Fintype.card (FormData k r) * 21 ≤ 64*A^2 := by
    rw [hFormData]
    have h := Nat.mul_le_mul hL hN
    nlinarith only [h, hQ 2]
  have hWP : Fintype.card (WidthIn (FormIx k r) (Param k r)) +
      widthPrepCost (FormIx k r) (Param k r) d ≤ 2^38*A^6 := by
    have hIn : Fintype.card (WidthIn (FormIx k r) (Param k r)) = L*3*N + L*3 := by
      unfold WidthIn
      rw [Fintype.card_sum, Fintype.card_prod, hFormIx, hParam]
    have hU : Fintype.card (Bool × Param k r) = 2*N := by
      rw [Fintype.card_prod, Fintype.card_bool, hParam]
    have hJ : Fintype.card (Bool × FormIx k r) = 2*(L*3) := by
      rw [Fintype.card_prod, Fintype.card_bool, hFormIx]
    have hProj : Fintype.card (ProjIn (Bool × Param k r) (Bool × FormIx k r) (Param k r)) =
        2*N*(2*(L*3)+(N+1)) := by
      unfold ProjIn
      rw [Fintype.card_prod, hU, Fintype.card_sum, hJ, Fintype.card_sum, hParam,
        Fintype.card_unit]
    unfold widthPrepCost
    rw [hIn, hProj, hU, hJ, hParam, hWidthOut]
    change L*3*N + L*3 + (2*N*(2*(L*3)+(N+1))*4 + glCost (2*N) (2*(L*3)) N (d+1) +
      (N*d+1)*2) ≤ _
    have g := hgl (a:=2*N) (b:=2*(L*3)) (c:=N) (e:=d+1) (by omega)
    have a := Nat.mul_le_mul hL (show N ≤ A by omega)
    have b := Nat.mul_le_mul (show N ≤ A by omega) (show d ≤ A by omega)
    have c := Nat.mul_le_mul (show 2*N ≤ 2*A by omega) (show 2*(L*3)+(N+1) ≤ 7*A by omega)
    nlinarith only [g, a, b, c, hL, hpow 2 6 (by decide), hAP, hQ 6]
  have hPre : preCost k r q n d ≤ 2^41*A^7 := by
    rw [preCost, hBasis]
    have h := Nat.mul_le_mul (show n+L ≤ 2*A by omega) hWP
    nlinarith only [hTP, hf, hpow 2 7 (by decide), hpow 6 7 (by decide), h]
  have hNull {m : ℕ} (hm : m ≤ 3*A) :
      N*(m+1) + glCost N 0 m m + m*m ≤ 2^38*A^6 := by
    have g := hgl (a:=N) (b:=0) (c:=m) (e:=m) (by omega)
    have a := Nat.mul_le_mul (show N ≤ A by omega) (show m+1 ≤ 4*A by omega)
    have b := Nat.mul_le_mul hm hm
    nlinarith only [g, a, b, hpow 2 6 (by decide), hQ 6]
  have hNullCost (J : Type) [Fintype J] (m : ℕ) (hc : Fintype.card J = m)
      (hm : m ≤ 3*A) : nullPrepCost J (Param k r) m ≤ 2^38*A^6 := by
    unfold nullPrepCost ProjIn NullOut
    rw [Fintype.card_prod, hParam, Fintype.card_sum, Fintype.card_empty, Nat.zero_add,
      Fintype.card_sum, Fintype.card_unit, Fintype.card_prod, hc, Fintype.card_fin]
    exact hNull hm
  have hLocal : max (leafLocalCost k r d) (joinLocalCost k r d) ≤ 2^64*A^12*B := by
    apply max_le
    · unfold leafLocalCost
      have hm : d+3 ≤ 3*A := by omega
      have hnul : nullPrepCost (Fin (d+3)) (Param k r) (d+3) ≤ 2^38*A^6 := by
        exact hNullCost (Fin (d+3)) (d+3) (Fintype.card_fin _) hm
      have hIn : Fintype.card (LInput d) ≤ 16*A^2 := by
        simp only [LInput, LeafTable.Input, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin,
          Fintype.card_unit]
        have a := Nat.mul_le_mul hm hm
        nlinarith only [a, hQ 2]
      have hLeaf : LeafTable.budget (d+3) d (N+1) ≤ 2^20*A^2*B := by
        unfold LeafTable.budget
        have a := Nat.mul_le_mul hm (show 5*(d+3)+3 ≤ 16*A by omega)
        have harg : 8*((d+3)*(5*(d+3)+3)+34)+5121*(N+1) ≤ 2^20*A^2 := by
          nlinarith only [a, hN, hQ 2, hAP]
        calc _ ≤ B*(2^20*A^2) := Nat.mul_le_mul hde harg
             _ = _ := by ring
      have c1 := Nat.mul_le_mul (hpow 6 12 (by decide)) hB
      have c2 := Nat.mul_le_mul (hpow 2 12 (by decide)) hB
      have c3 := Nat.mul_le_mul_right B (hpow 2 12 (by decide))
      nlinarith only [hnul, hIn, hLeaf, c1, c2, c3, hQ 12]
    · unfold joinLocalCost
      have hc : Fintype.card (JoinIx d) = 3*d := by simp [JoinIx]; omega
      have hnul : nullPrepCost (JoinIx d) (Param k r) (3*d) ≤ 2^38*A^6 := by
        exact hNullCost (JoinIx d) (3*d) hc (by omega)
      have hIn : Fintype.card (JInput k r d) ≤ 20*A^2*B := by
        simp only [JInput, JIn, Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
        change 3*d*(d+(d+(d+1))) + (2^d*(N+1)+2^d*(N+1)) ≤ _
        have a := Nat.mul_le_mul (show 3*d≤3*A by omega) (show d+(d+(d+1))≤4*A by omega)
        have b := Nat.mul_le_mul hde hN
        have c := Nat.mul_le_mul_right B hAP
        have e := Nat.mul_le_mul (le_refl (A^2)) hB
        nlinarith only [a, b, c, e]
      have hJ := joinCost_cap (d:=d) (N:=N) (m:=3*d) (P:=P) hd hN le_rfl (by omega)
      have hpow' : P^24 = A^12 := by dsimp [A]; rw [← pow_mul]
      rw [hpow'] at hJ
      have c1 := Nat.mul_le_mul (hpow 6 12 (by decide)) hB
      have c2 := Nat.mul_le_mul_right B (hpow 2 12 (by decide))
      change topCost d d d (3*d) (N+1) ((3*d)/2) + 1 ≤ 2^62*A^12*B at hJ
      change nullPrepCost (JoinIx d) (Param k r) (3*d) + Fintype.card (JInput k r d) +
        topCost d d d (3*d) (N+1) ((3*d)/2) ≤ _
      nlinarith only [hnul, hIn, hJ, c1, c2, Nat.zero_le (A^12*B)]
  have hTbl : Fintype.card (TableIx k r d) ≤ A*B := by
    simp only [TableIx, Addr, Fintype.card_prod, Fintype.card_fin]
    exact (Nat.mul_le_mul hde hN).trans_eq (Nat.mul_comm ..)
  have hPreType : Fintype.card (Pre k r q n d) ≤ 16*A^3 := by
    have hRaw : Fintype.card (Raw k r q n) =
        (2+2*r)*k+q*(N+1)+n*((2*r+1)*k) := card_inputSlot k r q n
    have hIn : Fintype.card (In k r q n) = Fintype.card (Raw k r q n) + (k+k) := by
      unfold In Greedy.Input
      rw [Fintype.card_sum, Fintype.card_sum (α := Fin k) (β := Fin k),
        Fintype.card_fin]
    have hMid : Fintype.card (PreMid k r q n) =
        Fintype.card (In k r q n) + (1+L*3*(N+1)) := by
      unfold PreMid
      rw [Fintype.card_sum, Fintype.card_sum (α := Unit), Fintype.card_unit, hFormData]
    unfold Pre
    rw [Fintype.card_sum, hMid, hIn, hRaw, Fintype.card_prod, hBasis, hWidthOut]
    have ha : (2+2*r)*k ≤ A :=
      (Nat.mul_le_mul_right k (show 2+2*r ≤ 2*r+3 by omega)).trans
        ((Nat.le_succ N).trans hN)
    have hq : q ≤ A := (by dsimp [P]; omega : q ≤ P).trans hP'
    have a := Nat.mul_le_mul hq hN
    have a' : (2*r+1)*k ≤ A := by simpa only [L, leaf_card] using hL
    have b := Nat.mul_le_mul hn a'
    have c := Nat.mul_le_mul hL hN
    have e := Nat.mul_le_mul (show N ≤ A by omega) (show d ≤ A by omega)
    have er : N*d+1 ≤ 2*A^2 := by nlinarith only [e, hQ 2]
    have f := Nat.mul_le_mul (show n+L ≤ 2*A by omega) er
    have hkk : k ≤ A := by omega
    nlinarith only [ha, hkk, a, b, c, f, hAP, hAP3, hQ 3]
  have hSched : scheduleBudget k r q n d ≤ 2^68*A^15*B := by
    have hc : Fintype.card (TreeSchedule.Candidate (Leaf k r) n) = L+n*n := by
      unfold TreeSchedule.Candidate
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    have ht' : Fintype.card (Fin n × TableIx k r d) = n * Fintype.card (TableIx k r d) := by
      rw [Fintype.card_prod, Fintype.card_fin]
    have hs : Fintype.card (TreeSchedule.State (Pre k r q n d) (TableIx k r d) n) =
        Fintype.card (Pre k r q n d) + n * Fintype.card (TableIx k r d) := by
      unfold TreeSchedule.State
      rw [Fintype.card_sum, ht']
    rw [scheduleBudget, TreeSchedule.stepCost, hc, hs, ht']
    have ht := Nat.mul_le_mul hn hTbl
    have hState : Fintype.card (Pre k r q n d) + n * Fintype.card (TableIx k r d) ≤ 18*A^3*B := by
      nlinarith only [hPreType, ht, Nat.mul_le_mul (le_refl (A^3)) hB, Nat.mul_le_mul_right B hAP3]
    have hCand : L + n*n ≤ 2*A^2 := by
      have h := Nat.mul_le_mul hn hn
      nlinarith only [h, hL, hAP]
    have harg : max (leafLocalCost k r d) (joinLocalCost k r d) + LayoutGuard.guardCost (Leaf k r) + 2 ≤
        2^65*A^12*B := by
      unfold LayoutGuard.guardCost
      have h := Nat.mul_le_mul (hpow 1 12 (by decide)) hB
      have h' := Nat.mul_le_mul (hQ 12) hB
      nlinarith only [hLocal, hL, h, h']
    have h1 := Nat.mul_le_mul hCand harg
    have h2 := Nat.mul_le_mul hState (show 2*(L+n*n)+1 ≤ 5*A^2 by nlinarith only [hCand, hQ 2])
    have hStep : (L+n*n) * (max (leafLocalCost k r d) (joinLocalCost k r d) + LayoutGuard.guardCost (Leaf k r) + 2) +
        (Fintype.card (Pre k r q n d) + n*Fintype.card (TableIx k r d))*(2*(L+n*n)+1) ≤ 2^67*A^14*B := by
      nlinarith only [h1,h2,Nat.mul_le_mul_right B (hpow 5 14 (by decide)), Nat.zero_le (A^14*B)]
    have h := Nat.mul_le_mul hn hStep
    nlinarith only [h, ht, Nat.mul_le_mul_right B (hpow 2 15 (by decide)), Nat.zero_le (A^15*B)]
  have hFinal : finalCountBudget k r n ≤ 2^10*A^5 := by
    unfold finalCountBudget LayoutGuard.layoutCost LayoutGuard.hasRootCost LayoutGuard.nodeCost
      LayoutGuard.rootCost LayoutGuard.guardCost
    change (k+2)*(n*(L+1+1)+1+(n*((L+n*n)*(L*10+1+1)+1+1)+1)+1+(n+1)+n*(L+1+2)+4) ≤ _
    have f1 := Nat.mul_le_mul hn hn
    have f2 := Nat.mul_le_mul hn (show L+1+2 ≤ 2*A by omega)
    have f3 := Nat.mul_le_mul (show L+n*n ≤ 2*A^2 by nlinarith only [f1, hL, hAP])
      (show L*10+1+1 ≤ 11*A by omega)
    have f4 := Nat.mul_le_mul hn (show (L+n*n)*(L*10+1+1)+1+1 ≤ 24*A^3 by
      nlinarith only [f3, hQ 3])
    have f5 : n*(L+1+1)+1+(n*((L+n*n)*(L*10+1+1)+1+1)+1)+1+(n+1)+n*(L+1+2)+4 ≤
        64*A^4 := by
      have f6 := Nat.mul_le_mul hn (show L+1+1≤2*A by omega)
      nlinarith only [f2, f4, f6, hn, hpow 2 4 (by decide), hpow 1 4 (by decide), hQ 4]
    have f6 := Nat.mul_le_mul hk f5
    nlinarith only [f6, hQ 5]
  have hOr : oracleCost k r q n d ≤ 2^69*A^15*B := by
    unfold oracleCost
    nlinarith only [hPre, hSched, hFinal, Nat.mul_le_mul (hpow 7 15 (by decide)) hB,
      Nat.mul_le_mul (hpow 5 15 (by decide)) hB]
  have hm := Nat.mul_le_mul (show k+1 ≤ A by omega) hOr
  have hl := Nat.mul_le_mul (show k≤A by omega) (show k≤A by omega)
  have hbudget : (k+1)*oracleCost k r q n d + k*k+3*k+2+1 ≤ 2^70*A^16*B := by
    have hk' : k ≤ A := by omega
    nlinarith only [hm,hl,hk',Nat.mul_le_mul (hpow 2 16 (by decide)) hB,
      Nat.mul_le_mul (hpow 1 16 (by decide)) hB,Nat.mul_le_mul (hQ 16) hB]
  refine hbudget.trans ?_
  rw [pow_add, show A^16 = P^32 by dsimp [A]; rw [← pow_mul]]
  change 2^70*P^32*B ≤ 2^90*B*P^40
  rw [mul_right_comm (2^90) B (P^40)]
  exact Nat.mul_le_mul_right B (Nat.mul_le_mul (by decide) (le_mono_pow (by omega) (by decide)))

end PEqualNP.Outside.L_meta_29751



open PEqualNP.Outside.L_meta_29751
open PEqualNP.Outside.L_meta_29751.Donor
open PEqualNP.Outside.L_meta_29751.PackedTape

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_29751 :
∀ (k r q n w : Nat) (hk : 0 < k),
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
  let inputs := (2+2*r)*k+q*(N+1)+n*((2*r+1)*k)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (ok : Fin (inputs+C.size))
    (countWire : Fin (k+1) → Fin (inputs+C.size)) (keyWire : Fin k → Fin (inputs+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.output = ok.val ∧ C.size ≤ 2^(90+(3*min N w)/2)*(k+r+q+n+5)^40 ∧
    ∀ (name : Bool → W) (c : Bool → Fin r → W) (obs : Fin q → X) (rhs : Fin q → F)
      (bag : Fin n → I → Bool),
      let pack := fun v : W => List.ofFn (fun j : Fin k => decide (v j ≠ 0))
      let lanes := fun (side : Bool) (tape : X) => (List.finRange (r+1)).flatMap (fun j => pack (tape.2 side j))
      let leafBits := fun (p : I → Bool) => List.ofFn (fun j : Fin k => p (.inl j)) ++
        [false,true].flatMap (fun b => (List.finRange r).flatMap (fun t =>
          List.ofFn (fun j : Fin k => p (.inr (b,t,j)))))
      let bits := pack (name false) ++ pack (name true) ++
        [false,true].flatMap (fun b => (List.finRange r).flatMap (fun t => pack (c b t))) ++
        (List.finRange q).flatMap (fun i => pack (obs i).1 ++ lanes false (obs i) ++ lanes true (obs i) ++
          [decide (rhs i ≠ 0)]) ++ (List.finRange n).flatMap (fun v => leafBits (bag v))
      let wire := fun i : Fin (inputs+C.size) => (C.wires bits).getD i.val false
      let D := {z : X // (∀ b, z.2 b 0 = rot (start b) z.1) ∧ ∀ i, pair (obs i) z = 0}
      let span := fun (p : I → Bool) => Submodule.span F
        {f : D → F | ∃ (j : I) (e : Fin 3), p j = true ∧ f = fun z : D => form j e z.val}
      let layout := (∃ root : Fin n, ∀ j, bag root j = true) ∧
        ∀ v : Fin n, (∃ one : I, ∀ j, bag v j = decide (j = one)) ∨
          ∃ l h : Fin n, l < v ∧ h < v ∧ (∀ j, bag l j = true → bag h j = false) ∧
            ∀ j, bag v j = (bag l j || bag h j)
      let fits := layout ∧ ∀ v : Fin n,
        Module.finrank F ((span (bag v) ⊓ span (fun j => !(bag v j))) : Submodule F (D → F)) ≤ w
      let actual := fun (key : W) (b : Bool) (time : Fin (r+1)) =>
        ((List.finRange r).take time.val).foldl (fun prev tick =>
          let y := mix b prev
          fun j : Fin k => y j + (1+y (ix (j.val+1)))*y (ix (j.val+2)) +
            rot (feed b tick.val) key j + c b tick j) (rot (start b) key + name b)
      let hit := fun key : W => ∀ i, pair (obs i) (key,actual key) = rhs i
      let cnt := Nat.card {key : W // hit key}
      let out := fun j => (if wire (keyWire j) then 1 else 0 : F)
      let code : W → Nat := fun v => ∑ j : Fin k, if v j = 0 then 0 else 2^j.val
      (wire ok = true ↔ fits) ∧ (∀ s, wire (countWire s) = (if wire ok then cnt else 0).testBit s.val) ∧
        (wire ok = true → 0 < cnt → hit out ∧ ∀ key, hit key → code out ≤ code key) ∧
        ((wire ok = false ∨ cnt = 0) → out = 0) := by
  classical
  intro k r q n w hk F W X G I N ix rot start feed mix pair form inputs
  have h := countOracle (k:=k) (r:=r) (q:=q) (n:=n) hk w
  obtain ⟨O,hO,hsem⟩ := h
  have hWrap := Greedy.wrap_cmp hO
  obtain ⟨gs, alloc, hfan, hback, hlen, halloc, hval⟩ := hWrap.extract inputs
    (wireIx (k:=k) (r:=r) (q:=q) (n:=n)) wireIx_lt_succ
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs, alloc (.inl (.inl ()))⟩
  let ok : Fin (inputs + C.size) := ⟨alloc (.inl (.inl ())), halloc _⟩
  let countWire (s : Fin (k+1)) : Fin (inputs + C.size) := ⟨alloc (.inl (.inr s)),halloc _⟩
  let keyWire (j : Fin k) : Fin (inputs + C.size) := ⟨alloc (.inr j),halloc _⟩
  refine ⟨C,ok,countWire,keyWire,hfan,hback _,rfl,?_,?_⟩
  · exact hlen.trans (by simpa only [pow_two] using full_size k r q n w)
  intro name c obs rhs bags pack lanes leafBits bits wire D span layout fits actual hit cnt out code
  let a := slotBit name c obs rhs bags
  have hx : (fun i => (bits++[false]).getD (wireIx i) false) = a :=
    funext (read_bits name c obs rhs bags)
  have hb : bits.length = inputs := bits_length name c obs rhs bags
  have hw (o : Greedy.Output k) : (C.wires bits).getD (alloc o) false = Greedy.wrap O a o := by
    rw [← hx]
    exact hval C.output bits hb o
  have hn : readName a = name := by
    funext b j
    exact zbit_decode (name b j)
  have hc : readC a = c := by
    funext b t j
    exact zbit_decode (c b t j)
  have ho : readObs a = obs := by
    funext i
    apply Prod.ext
    · funext j; exact zbit_decode ((obs i).1 j)
    · funext b t j; exact zbit_decode ((obs i).2 b t j)
  have hr : readRhs a = rhs := by
    funext i
    exact zbit_decode (rhs i)
  have hfit : inputGood hk w a = true ↔ fits := by
    let width (o : Fin q → Tape k r) : Prop :=
      let S (b : Leaf k r → Bool) := Submodule.span F {f : Direction hk o → F |
        ∃ (j : Leaf k r) (e : Fin 3), b j = true ∧ f = fun z => L_meta_29751.form hk j e z.val}
      ∀ v : Fin n, Module.finrank F
        ((S (bags v) ⊓ S (fun j => !bags v j)) : Submodule F (Direction hk o → F)) ≤ w
    unfold inputGood
    rw [decide_eq_true_eq, LayoutGuard.layout_true]
    change (layout ∧ width (readObs a)) ↔ layout ∧ width obs
    rw [ho]
  let dec (x : Fin k → Bool) : W := fun j => b2z (x j)
  let enc (x : W) : Fin k → Bool := fun j => zbit (x j)
  have he (x : W) : dec (enc x) = x := funext fun j => zbit_decode (x j)
  have hd (x : Fin k → Bool) : enc (dec x) = x := funext fun j => st_dec_b2z (x j)
  have hh (x : Fin k → Bool) : inputHit hk a x ↔ hit (dec x) := by
    unfold inputHit
    rw [hn,hc,ho,hr]
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
  have hOkWire : wire ok = inputGood hk w a := (hw (.inl (.inl ()))).trans hOk
  have hout : out = dec (fun j => Greedy.wrap O a (.inr j)) := by
    funext j
    exact congrArg b2z (hw (.inr j))
  refine ⟨hOkWire.symm ▸ hfit, ?_, ?_, ?_⟩
  · intro s
    exact (hw (.inl (.inr s))).trans (by rw [hCount s, hcnt, hOkWire])
  · intro hOK hp
    obtain ⟨hu,hmin⟩ := hMin (hOkWire.symm.trans hOK) (hcnt.symm ▸ hp)
    rw [hout]
    refine ⟨(hh _).mp hu, fun y hy => ?_⟩
    have ha := hmin (enc y) ((hh _).mpr ((he y).symm ▸ hy))
    rw [← hcode, ← hcode, he] at ha
    exact ha
  · intro hz
    have hz' : inputGood hk w a = false ∨ Greedy.cardinal (inputHit hk a) = 0 := by
      simpa only [← hOkWire,hcnt] using hz
    rw [hout, hZero hz']
    rfl
