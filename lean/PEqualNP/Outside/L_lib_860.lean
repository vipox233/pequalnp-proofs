import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_860_aux

theorem rn {d : ℕ} (O B : Submodule (ZMod 2) (Fin d → ZMod 2)) :
    Module.finrank (ZMod 2) ↥(B.map O.mkQ) + Module.finrank (ZMod 2) ↥(O ⊓ B) =
      Module.finrank (ZMod 2) ↥B := by
  have h := LinearMap.finrank_range_add_finrank_ker (O.mkQ ∘ₗ B.subtype)
  have h1 : LinearMap.range (O.mkQ ∘ₗ B.subtype) = B.map O.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have e : LinearMap.ker (O.mkQ ∘ₗ B.subtype) = (O ⊓ B).comap B.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  have h2 : Module.finrank (ZMod 2) ↥(LinearMap.ker (O.mkQ ∘ₗ B.subtype)) =
      Module.finrank (ZMod 2) ↥(O ⊓ B) := by
    rw [e]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_right)
  rw [h1, h2] at h
  exact h

theorem lb {d : ℕ} (O A C : Submodule (ZMod 2) (Fin d → ZMod 2)) :
    Module.finrank (ZMod 2) ↥(A ⊓ C) ≤
      Module.finrank (ZMod 2) ↥((A.map O.mkQ) ⊓ (C.map O.mkQ)) +
        Module.finrank (ZMod 2) ↥(O ⊓ (A ⊓ C)) := by
  have h := rn O (A ⊓ C)
  have hle : (A ⊓ C).map O.mkQ ≤ (A.map O.mkQ) ⊓ (C.map O.mkQ) := Submodule.map_inf_le _
  have := Submodule.finrank_mono hle
  omega

theorem eqA {d : ℕ} (O A C : Submodule (ZMod 2) (Fin d → ZMod 2)) (hO : O ≤ A) :
    Module.finrank (ZMod 2) ↥((A.map O.mkQ) ⊓ (C.map O.mkQ)) +
      Module.finrank (ZMod 2) ↥(O ⊓ (A ⊓ C)) = Module.finrank (ZMod 2) ↥(A ⊓ C) := by
  have hle : (A.map O.mkQ) ⊓ (C.map O.mkQ) = (A ⊓ C).map O.mkQ := by
    apply le_antisymm _ (Submodule.map_inf_le _)
    rintro z ⟨⟨a, ha, rfl⟩, ⟨c, hc, hca⟩⟩
    have hd : c - a ∈ O := by
      have h0 : O.mkQ (c - a) = 0 := by rw [map_sub, hca, sub_self]
      exact (Submodule.Quotient.mk_eq_zero O).mp h0
    have hcA : c ∈ A := by
      have : c = (c - a) + a := by abel
      rw [this]
      exact A.add_mem (hO hd) ha
    exact ⟨c, ⟨hcA, hc⟩, hca⟩
  rw [hle]
  exact rn O (A ⊓ C)

theorem eqC {d : ℕ} (O A C : Submodule (ZMod 2) (Fin d → ZMod 2)) (hO : O ≤ C) :
    Module.finrank (ZMod 2) ↥((A.map O.mkQ) ⊓ (C.map O.mkQ)) +
      Module.finrank (ZMod 2) ↥(O ⊓ (A ⊓ C)) = Module.finrank (ZMod 2) ↥(A ⊓ C) := by
  have h := eqA O C A hO
  rw [inf_comm (C.map O.mkQ), inf_comm C A] at h
  exact h

theorem bot_profile {d : ℕ} (A C : Submodule (ZMod 2) (Fin d → ZMod 2)) :
    Module.finrank (ZMod 2) ↥((A.map (⊥ : Submodule (ZMod 2) (Fin d → ZMod 2)).mkQ) ⊓
      (C.map (⊥ : Submodule (ZMod 2) (Fin d → ZMod 2)).mkQ)) = Module.finrank (ZMod 2) ↥(A ⊓ C) := by
  have h := eqA ⊥ A C bot_le
  have h0 : Module.finrank (ZMod 2) ↥((⊥ : Submodule (ZMod 2) (Fin d → ZMod 2)) ⊓ (A ⊓ C)) = 0 := by
    rw [bot_inf_eq]
    exact finrank_bot _ _
  omega


def side {d l h e : ℕ} (leaf : Fin l → Submodule (ZMod 2) (Fin d → ZMod 2))
    (cut : Fin h → Fin e → Fin l → Bool) (t : Fin h) (j : Fin e) (c : Bool) :
    Submodule (ZMod 2) (Fin d → ZMod 2) :=
  Submodule.span (ZMod 2) {v : Fin d → ZMod 2 | ∃ i : Fin l, cut t j i = c ∧ v ∈ leaf i}

noncomputable def prof {d l h e : ℕ} (leaf : Fin l → Submodule (ZMod 2) (Fin d → ZMod 2))
    (cut : Fin h → Fin e → Fin l → Bool) (O : Submodule (ZMod 2) (Fin d → ZMod 2))
    (t : Fin h) (j : Fin e) : ℕ :=
  Module.finrank (ZMod 2) ↥(((side leaf cut t j true).map O.mkQ) ⊓ ((side leaf cut t j false).map O.mkQ))

noncomputable def pk {d l h e : ℕ} (leaf : Fin l → Submodule (ZMod 2) (Fin d → ZMod 2))
    (cut : Fin h → Fin e → Fin l → Bool) (O : Submodule (ZMod 2) (Fin d → ZMod 2))
    (t : Fin h) : ℕ :=
  (Finset.univ : Finset (Fin e)).sup (prof leaf cut O t)

theorem prof_lb {d l h e : ℕ} (leaf : Fin l → Submodule (ZMod 2) (Fin d → ZMod 2))
    (cut : Fin h → Fin e → Fin l → Bool) (O : Submodule (ZMod 2) (Fin d → ZMod 2))
    (t : Fin h) (j : Fin e) :
    Module.finrank (ZMod 2) ↥(side leaf cut t j true ⊓ side leaf cut t j false) ≤
      prof leaf cut O t j +
        Module.finrank (ZMod 2) ↥(O ⊓ (side leaf cut t j true ⊓ side leaf cut t j false)) :=
  lb O _ _

theorem prof_bot {d l h e : ℕ} (leaf : Fin l → Submodule (ZMod 2) (Fin d → ZMod 2))
    (cut : Fin h → Fin e → Fin l → Bool) (t : Fin h) (j : Fin e) :
    prof leaf cut ⊥ t j =
      Module.finrank (ZMod 2) ↥(side leaf cut t j true ⊓ side leaf cut t j false) :=
  bot_profile _ _

theorem pk_bot_le {d l h e : ℕ} (leaf : Fin l → Submodule (ZMod 2) (Fin d → ZMod 2))
    (cut : Fin h → Fin e → Fin l → Bool) (O : Submodule (ZMod 2) (Fin d → ZMod 2)) (t : Fin h) :
    pk leaf cut ⊥ t ≤ pk leaf cut O t + Module.finrank (ZMod 2) ↥O := by
  apply Finset.sup_le
  intro j _
  rw [prof_bot]
  have h1 := prof_lb leaf cut O t j
  have h2 : Module.finrank (ZMod 2) ↥(O ⊓ (side leaf cut t j true ⊓ side leaf cut t j false)) ≤
      Module.finrank (ZMod 2) ↥O := Submodule.finrank_mono inf_le_left
  have h3 : prof leaf cut O t j ≤ pk leaf cut O t :=
    Finset.le_sup (f := prof leaf cut O t) (Finset.mem_univ j)
  omega

theorem side_mono {d l h e : ℕ} (leaf : Fin l → Submodule (ZMod 2) (Fin d → ZMod 2))
    (cut : Fin h → Fin e → Fin l → Bool) (t : Fin h) (i j : Fin e) (a b : Bool)
    (hab : ∀ u : Fin l, cut t i u = a → cut t j u = b) :
    side leaf cut t i a ≤ side leaf cut t j b := by
  apply Submodule.span_mono
  rintro v ⟨u, hu, hv⟩
  exact ⟨u, hab u hu, hv⟩

theorem prof_exact {d l h e : ℕ} (leaf : Fin l → Submodule (ZMod 2) (Fin d → ZMod 2))
    (cut : Fin h → Fin e → Fin l → Bool) (O : Submodule (ZMod 2) (Fin d → ZMod 2))
    (t : Fin h) (j : Fin e) (b : Bool) (hO : O ≤ side leaf cut t j b) :
    prof leaf cut O t j +
        Module.finrank (ZMod 2) ↥(O ⊓ (side leaf cut t j true ⊓ side leaf cut t j false)) =
      Module.finrank (ZMod 2) ↥(side leaf cut t j true ⊓ side leaf cut t j false) := by
  cases b with
  | true => exact eqA O _ _ hO
  | false => exact eqC O _ _ hO

theorem main {d l h e : ℕ} (leaf : Fin l → Submodule (ZMod 2) (Fin d → ZMod 2))
    (cut : Fin h → Fin e → Fin l → Bool)
    (hlam : ∀ (t : Fin h) (i j : Fin e), ∃ a b : Bool, ∀ u : Fin l, cut t i u = a → cut t j u = b)
    (w : ℕ) (hw : IsLeast {z : ℕ | ∃ t : Fin h, pk leaf cut ⊥ t = z} w)
    (O : Submodule (ZMod 2) (Fin d → ZMod 2))
    (hs : 0 < Module.finrank (ZMod 2) ↥O) (hsw : Module.finrank (ZMod 2) ↥O ≤ w) :
    IsLeast {z : ℕ | ∃ t : Fin h, pk leaf cut O t = z} (w - Module.finrank (ZMod 2) ↥O) ↔
      ∃ t : Fin h, pk leaf cut ⊥ t = w ∧ ∀ j : Fin e,
        Module.finrank (ZMod 2) ↥O +
            Module.finrank (ZMod 2) ↥(side leaf cut t j true ⊓ side leaf cut t j false) ≤
          w + Module.finrank (ZMod 2) ↥(O ⊓ (side leaf cut t j true ⊓ side leaf cut t j false)) := by
  have hwle : ∀ t : Fin h, w ≤ pk leaf cut ⊥ t := fun t => hw.2 ⟨t, rfl⟩
  have hlow : ∀ t : Fin h, w - Module.finrank (ZMod 2) ↥O ≤ pk leaf cut O t := fun t => by
    have h1 := pk_bot_le leaf cut O t
    have h2 := hwle t
    omega
  constructor
  · intro hL
    obtain ⟨t0, ht0⟩ := hL.1
    refine ⟨t0, ?_, fun j => ?_⟩
    · have h1 := pk_bot_le leaf cut O t0
      have h2 := hwle t0
      omega
    · have h1 := prof_lb leaf cut O t0 j
      have h3 : prof leaf cut O t0 j ≤ pk leaf cut O t0 :=
        Finset.le_sup (f := prof leaf cut O t0) (Finset.mem_univ j)
      omega
  · rintro ⟨t, hpk, hcond⟩
    refine ⟨⟨t, le_antisymm ?_ (hlow t)⟩, ?_⟩
    · have hwpos : 0 < w := by omega
      have hex : ∃ j0 : Fin e, prof leaf cut ⊥ t j0 = w := by
        rcases Nat.eq_zero_or_pos e with he | he
        · subst he
          have h0 : pk leaf cut ⊥ t = 0 := by
            unfold pk
            rw [Finset.univ_eq_empty, Finset.sup_empty]
            rfl
          omega
        · have hne : (Finset.univ : Finset (Fin e)).Nonempty := ⟨⟨0, he⟩, Finset.mem_univ _⟩
          obtain ⟨j0, _, hj0⟩ := Finset.exists_mem_eq_sup _ hne (prof leaf cut ⊥ t)
          refine ⟨j0, ?_⟩
          rw [← hj0]
          exact hpk
      obtain ⟨j0, hj0⟩ := hex
      rw [prof_bot] at hj0
      have hc0 := hcond j0
      have hOB : O ⊓ (side leaf cut t j0 true ⊓ side leaf cut t j0 false) = O :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      have hOle : O ≤ side leaf cut t j0 true ⊓ side leaf cut t j0 false := inf_eq_left.mp hOB
      have hOside : ∀ a : Bool, O ≤ side leaf cut t j0 a := fun a => by
        cases a with
        | true => exact le_trans hOle inf_le_left
        | false => exact le_trans hOle inf_le_right
      apply Finset.sup_le
      intro j _
      obtain ⟨a, b, hab⟩ := hlam t j0 j
      have hOj : O ≤ side leaf cut t j b := le_trans (hOside a) (side_mono leaf cut t j0 j a b hab)
      have h1 := prof_exact leaf cut O t j b hOj
      have h2 := hcond j
      omega
    · rintro z ⟨t', rfl⟩
      exact hlow t'

end PEqualNP.Outside.L_lib_860_aux

theorem PEqualNP.Outside.L_lib_860 : (∀ (d l h e : Nat),
  let F := ZMod 2
  let W := Fin d → F
  ∀ (leaf : Fin l → Submodule F W) (cut : Fin h → Fin e → Fin l → Bool),
    let side := fun (t : Fin h) (j : Fin e) (c : Bool) =>
      Submodule.span F {v : W | ∃ i : Fin l, cut t j i = c ∧ v ∈ leaf i}
    let boundary := fun (t : Fin h) (j : Fin e) => side t j true ⊓ side t j false
    let profile := fun (O : Submodule F W) (t : Fin h) (j : Fin e) =>
      Module.finrank F (((side t j true).map O.mkQ) ⊓ ((side t j false).map O.mkQ) : Submodule F (W ⧸ O))
    let peak := fun (O : Submodule F W) (t : Fin h) =>
      (Finset.univ : Finset (Fin e)).sup (profile O t)
    (∀ (t : Fin h) (i j : Fin e), ∃ a b : Bool,
      ∀ u : Fin l, cut t i u = a → cut t j u = b) →
    ∀ (w : Nat), IsLeast {z : Nat | ∃ t : Fin h, peak ⊥ t = z} w →
    ∀ O : Submodule F W, let s := Module.finrank F O
    0 < s → s ≤ w →
      (IsLeast {z : Nat | ∃ t : Fin h, peak O t = z} (w-s) ↔
        ∃ t : Fin h, peak ⊥ t = w ∧ ∀ j : Fin e,
          s + Module.finrank F (boundary t j) ≤ w + Module.finrank F ((O ⊓ boundary t j) : Submodule F W))) := by
  intro d l h e
  dsimp only
  intro leaf cut hlam w hw O hs hsw
  exact PEqualNP.Outside.L_lib_860_aux.main leaf cut hlam w hw O hs hsw
