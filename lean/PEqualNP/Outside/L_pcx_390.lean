import PEqualNP.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace PEqualNP.Outside.L_pcx_390_aux

private lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_ne_iff_eq_add_one (a b : ZMod 2) : a ≠ b ↔ a = b + 1 := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

private lemma zmod2_decide_eq (a b : ZMod 2) (t : Bool) :
    decide (a = b) = t ↔ a = (if t then b else b + 1) := by
  cases t <;> simp [zmod2_ne_iff_eq_add_one]

private def boolToF (t : Bool) : ZMod 2 := if t then 1 else 0

private lemma zmod2_decide_eq_one (a : ZMod 2) (t : Bool) :
    decide (a = 1) = t ↔ a = boolToF t := by
  rcases zmod2_cases a with rfl | rfl <;> cases t <;> decide

private lemma card_submodule_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (W : Submodule (ZMod 2) V) [Fintype W] :
    Fintype.card W = 2 ^ Module.finrank (ZMod 2) W := by
  have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
  simp only [Nat.card_eq_fintype_card, ZMod.card] at h1
  exact h1

private lemma exists_leaf_of_tree (N J : Finset (List Bool))
    (hroot : [] ∈ N)
    (hchildren : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    (f : List Bool → Bool) :
    ∃ p ∈ N \ J, ∀ j : Fin p.length, f (p.take j.val) = p.get j := by
  let M := N.sup List.length
  have hstep : ∀ (r : ℕ) (p : List Bool), p ∈ N →
      (∀ j : Fin p.length, f (p.take j.val) = p.get j) →
      M - p.length ≤ r →
      ∃ q ∈ N \ J, ∀ j : Fin q.length, f (q.take j.val) = q.get j := by
    intro r
    induction r with
    | zero =>
      intro p hp hinv hle
      by_cases hpJ : p ∈ J
      · exfalso
        have hch := (hchildren p hpJ).1
        have hlen : (p ++ [false]).length ≤ M := Finset.le_sup (f := List.length) hch
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        omega
      · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpJ⟩, hinv⟩
    | succ r ih =>
      intro p hp hinv hle
      by_cases hpJ : p ∈ J
      · let t := f p
        have hp' : p ++ [t] ∈ N := by
          cases ht : t
          · exact (hchildren p hpJ).1
          · exact (hchildren p hpJ).2
        have hlen : (p ++ [t]).length ≤ M := Finset.le_sup (f := List.length) hp'
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen
        have hinv' : ∀ j : Fin (p ++ [t]).length,
            f ((p ++ [t]).take j.val) = (p ++ [t]).get j := by
          intro j
          have hjlen : j.val < p.length + 1 := by simpa using j.isLt
          by_cases hlt : j.val < p.length
          · rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
            have hget : (p ++ [t]).get j = p.get ⟨j.val, hlt⟩ := by
              simp [List.getElem_append_left hlt]
            rw [hget]
            exact hinv ⟨j.val, hlt⟩
          · have heq : j.val = p.length := by omega
            have htake : (p ++ [t]).take j.val = p := by
              rw [heq]; exact List.take_left
            have hget : (p ++ [t]).get j = t := by
              simp [heq]
            rw [htake, hget]
        apply ih (p ++ [t]) hp' hinv'
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpJ⟩, hinv⟩
  exact hstep M [] hroot (fun j => Fin.elim0 j) (by simp)

private lemma second_diff_target {n m : ℕ} (u v : Fin m → Fin n)
    (z₀ d₁ d₂ : (Fin n → ZMod 2) × (Fin m → ZMod 2)) (e : Fin m) :
    let target := fun (z : (Fin n → ZMod 2) × (Fin m → ZMod 2)) (e : Fin m) =>
      z.2 e + z.1 (u e) * z.1 (v e)
    ((target (z₀ + (d₁ + d₂)) - target z₀) - (target (z₀ + d₁) - target z₀) -
      (target (z₀ + d₂) - target z₀)) e =
      d₁.1 (u e) * d₂.1 (v e) + d₂.1 (u e) * d₁.1 (v e) := by
  dsimp only [Pi.sub_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  ring

private lemma exists_coord_basis {n : ℕ} (H : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    ∃ A : Finset (Fin n), A.card = Module.finrank (ZMod 2) H ∧
      ∀ a ∈ A, ∃ x : H, ∀ a' ∈ A, x.1 a' = if a' = a then 1 else 0 := by
  let F := ZMod 2
  let ev : Fin n → Module.Dual F H := fun i => (LinearMap.proj i).comp H.subtype
  have hspan : Submodule.span F (Set.range ev) = ⊤ := by
    obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective H.subtype (Submodule.ker_subtype H)
    rw [eq_top_iff]
    intro f _
    have hfeq : f = ∑ i : Fin n, (f (L (Pi.single i 1))) • ev i := by
      ext x
      have hx : H.subtype x = ∑ i : Fin n, x.1 i • Pi.single i (1 : F) := by
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      have hLx : L (H.subtype x) = x := LinearMap.congr_fun hL x
      calc f x = f (L (H.subtype x)) := by rw [hLx]
        _ = f (L (∑ i : Fin n, x.1 i • Pi.single i (1 : F))) := by rw [hx]
        _ = ∑ i : Fin n, x.1 i * f (L (Pi.single i 1)) := by
            simp [map_sum, map_smul, smul_eq_mul]
        _ = (∑ i : Fin n, (f (L (Pi.single i 1))) • ev i) x := by
            simp [ev, LinearMap.sum_apply, smul_eq_mul, mul_comm]
    rw [hfeq]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i)))
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent F (Set.range ev)
  rw [hspan] at hs_span
  have hs_fin : s.Finite := (Set.finite_range ev).subset hs_sub
  letI : Fintype s := hs_fin.fintype
  have hs_range : ⊤ ≤ Submodule.span F (Set.range ((↑) : s → Module.Dual F H)) := by
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hs_span]
  let b : Module.Basis s F (Module.Dual F H) := Module.Basis.mk hs_li hs_range
  let pick : s → Fin n := fun g => Classical.choose (hs_sub g.2)
  have hpick_spec : ∀ g : s, ev (pick g) = g.1 := fun g => Classical.choose_spec (hs_sub g.2)
  have hpick_inj : Function.Injective pick := by
    intro g₁ g₂ h
    apply Subtype.ext
    rw [← hpick_spec g₁, ← hpick_spec g₂, h]
  let A : Finset (Fin n) := Finset.univ.image pick
  have hAcard : A.card = Module.finrank F H := by
    rw [Finset.card_image_of_injective _ hpick_inj, Finset.card_univ,
      ← Module.finrank_eq_card_basis b, Subspace.dual_finrank_eq]
  let res : H →ₗ[F] (A → F) :=
    { toFun := fun x a => x.1 a.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hres_inj : Function.Injective res := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hbx : ∀ g : s, b g x = 0 := by
      intro g
      have hmem : pick g ∈ A := Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
      have h0 : res x ⟨pick g, hmem⟩ = 0 := congr_fun hx ⟨pick g, hmem⟩
      change x.1 (pick g) = 0 at h0
      have hbg : b g = ev (pick g) := by simp [b, hpick_spec g]
      rw [hbg]
      exact h0
    have hfx : ∀ f : Module.Dual F H, f x = 0 := by
      intro f
      have hf : f = ∑ g : s, (b.repr f g) • b g := (b.sum_repr f).symm
      have hf' : f x = (∑ g : s, (b.repr f g) • b g) x := by rw [← hf]
      rw [hf', LinearMap.sum_apply]
      simp [hbx]
    apply Subtype.ext
    ext i
    exact hfx (ev i)
  have hfr_eq : Module.finrank F H = Module.finrank F (A → F) := by
    rw [← hAcard, Module.finrank_pi, Fintype.card_coe]
  have hres_surj : Function.Surjective res :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr_eq).mp hres_inj
  refine ⟨A, hAcard, ?_⟩
  intro a ha
  obtain ⟨x, hx⟩ := hres_surj (Pi.single ⟨a, ha⟩ (1 : F))
  refine ⟨x, ?_⟩
  intro a' ha'
  have h := congr_fun hx ⟨a', ha'⟩
  simpa [res, Pi.single_apply, Subtype.mk.injEq] using h

private lemma flat_finrank_le {n m : ℕ}
    (u v : Fin m → Fin n) (huv : ∀ e, u e < v e)
    (hinj : Function.Injective (fun e : Fin m => (u e, v e)))
    (k : ℕ)
    (R : Submodule (ZMod 2) (Fin m → ZMod 2)) (hRk : Module.finrank (ZMod 2) R ≤ k)
    (c : Fin m → ZMod 2)
    (W : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin m → ZMod 2)))
    (z₀ : (Fin n → ZMod 2) × (Fin m → ZMod 2))
    (hflat : ∀ d ∈ W,
      (fun e => (z₀ + d).2 e + (z₀ + d).1 (u e) * (z₀ + d).1 (v e)) - c ∈ R) :
    Module.finrank (ZMod 2) W ≤
      k + (Finset.univ.filter (fun A : Finset (Fin n) =>
        (Finset.univ.filter (fun e : Fin m => u e ∈ A ∧ v e ∈ A)).card ≤ k)).sup Finset.card := by
  let F := ZMod 2
  let X := Fin n → F
  let Y := Fin m → F
  let target : (X × Y) → Y := fun z e => z.2 e + z.1 (u e) * z.1 (v e)
  have hdiff : ∀ d ∈ W, target (z₀ + d) - target z₀ ∈ R := by
    intro d hd
    have h0 : target z₀ - c ∈ R := by
      have := hflat 0 W.zero_mem
      simpa [target] using this
    have h1 : target (z₀ + d) - c ∈ R := hflat d hd
    have heq : target (z₀ + d) - target z₀ = (target (z₀ + d) - c) - (target z₀ - c) := by
      ext e; simp
    rw [heq]
    exact R.sub_mem h1 h0
  let φ : W →ₗ[F] X := (LinearMap.fst F X Y).domRestrict W
  have hrank : Module.finrank F (LinearMap.range φ) + Module.finrank F (LinearMap.ker φ) =
      Module.finrank F W := LinearMap.finrank_range_add_finrank_ker φ
  have hker_le : Module.finrank F (LinearMap.ker φ) ≤ k := by
    have hmemR : ∀ w : LinearMap.ker φ, w.1.1.2 ∈ R := by
      intro w
      have hw1 : w.1.1.1 = 0 := w.2
      have hd := hdiff w.1.1 w.1.2
      have heq : target (z₀ + w.1.1) - target z₀ = w.1.1.2 := by
        ext e
        change (z₀.2 e + w.1.1.2 e + (z₀.1 (u e) + w.1.1.1 (u e)) * (z₀.1 (v e) + w.1.1.1 (v e))) -
          (z₀.2 e + z₀.1 (u e) * z₀.1 (v e)) = w.1.1.2 e
        rw [hw1]
        simp only [Pi.zero_apply, add_zero]
        ring
      rwa [heq] at hd
    let ψ : LinearMap.ker φ →ₗ[F] R :=
      { toFun := fun w => ⟨w.1.1.2, hmemR w⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hψ_inj : Function.Injective ψ := by
      intro w₁ w₂ h
      apply Subtype.ext; apply Subtype.ext; apply Prod.ext
      · have h1 : w₁.1.1.1 = 0 := w₁.2
        have h2 : w₂.1.1.1 = 0 := w₂.2
        rw [h1, h2]
      · exact congr_arg Subtype.val h
    exact le_trans (LinearMap.finrank_le_finrank_of_injective hψ_inj) hRk
  let H : Submodule F X := LinearMap.range φ
  obtain ⟨A, hAcard, hAbasis⟩ := exists_coord_basis H
  have hlift : ∀ a ∈ A, ∃ d : W, ∀ a' ∈ A, d.1.1 a' = if a' = a then 1 else 0 := by
    intro a ha
    obtain ⟨x, hx⟩ := hAbasis a ha
    obtain ⟨d, hd⟩ := x.2
    refine ⟨d, ?_⟩
    intro a' ha'
    have hxeq : d.1.1 = x.1 := hd
    rw [hxeq]
    exact hx a' ha'
  let EA : Finset (Fin m) := Finset.univ.filter (fun e => u e ∈ A ∧ v e ∈ A)
  have hEA_le : EA.card ≤ k := by
    let da : (a : A) → W := fun a => Classical.choose (hlift a.1 a.2)
    have hda : ∀ (a : A) (a' : A), (da a).1.1 a'.1 = if a'.1 = a.1 then 1 else 0 :=
      fun a a' => Classical.choose_spec (hlift a.1 a.2) a'.1 a'.2
    let vec : EA → R := fun e₀ =>
      let a₀ : A := ⟨u e₀.1, (Finset.mem_filter.mp e₀.2).2.1⟩
      let b₀ : A := ⟨v e₀.1, (Finset.mem_filter.mp e₀.2).2.2⟩
      ⟨(target (z₀ + ((da a₀).1 + (da b₀).1)) - target z₀) -
        (target (z₀ + (da a₀).1) - target z₀) -
        (target (z₀ + (da b₀).1) - target z₀),
        R.sub_mem (R.sub_mem (hdiff _ (W.add_mem (da a₀).2 (da b₀).2)) (hdiff _ (da a₀).2))
          (hdiff _ (da b₀).2)⟩
    have hvec_eval : ∀ (e₀ e₁ : EA), (vec e₀).1 e₁.1 = if e₁ = e₀ then 1 else 0 := by
      intro e₀ e₁
      let a₀ : A := ⟨u e₀.1, (Finset.mem_filter.mp e₀.2).2.1⟩
      let b₀ : A := ⟨v e₀.1, (Finset.mem_filter.mp e₀.2).2.2⟩
      let a₁ : A := ⟨u e₁.1, (Finset.mem_filter.mp e₁.2).2.1⟩
      let b₁ : A := ⟨v e₁.1, (Finset.mem_filter.mp e₁.2).2.2⟩
      have hsd := second_diff_target u v z₀ (da a₀).1 (da b₀).1 e₁.1
      change ((target (z₀ + ((da a₀).1 + (da b₀).1)) - target z₀) -
        (target (z₀ + (da a₀).1) - target z₀) -
        (target (z₀ + (da b₀).1) - target z₀)) e₁.1 = _
      rw [hsd]
      have h1 := hda a₀ a₁
      have h2 := hda b₀ b₁
      have h3 := hda b₀ a₁
      have h4 := hda a₀ b₁
      dsimp only [a₀, b₀, a₁, b₁] at h1 h2 h3 h4
      rw [h1, h2, h3, h4]
      have hswap : ¬(u e₁.1 = v e₀.1 ∧ v e₁.1 = u e₀.1) := by
        rintro ⟨hu1, hv1⟩
        have hlt1 := huv e₁.1
        have hlt0 := huv e₀.1
        rw [hu1, hv1] at hlt1
        exact lt_asymm hlt0 hlt1
      have hterm1 : (if u e₁.1 = u e₀.1 then (1 : F) else 0) * (if v e₁.1 = v e₀.1 then 1 else 0) =
          if e₁ = e₀ then 1 else 0 := by
        by_cases heq : e₁ = e₀
        · subst heq; simp
        · have hpne : ¬(u e₁.1 = u e₀.1 ∧ v e₁.1 = v e₀.1) := by
            rintro ⟨hu, hv⟩; exact heq (Subtype.ext (hinj (Prod.ext hu hv)))
          simp only [heq, ↓reduceIte]
          by_cases hA : u e₁.1 = u e₀.1
          · have hB : v e₁.1 ≠ v e₀.1 := fun hB => hpne ⟨hA, hB⟩
            simp [hA, hB]
          · simp [hA]
      have hterm2 : (if u e₁.1 = v e₀.1 then (1 : F) else 0) * (if v e₁.1 = u e₀.1 then 1 else 0) = 0 := by
        by_cases hA : u e₁.1 = v e₀.1
        · have hB : v e₁.1 ≠ u e₀.1 := fun hB => hswap ⟨hA, hB⟩
          simp [hA, hB]
        · simp [hA]
      rw [hterm1, hterm2, add_zero]
    have hli : LinearIndependent F vec := by
      rw [Fintype.linearIndependent_iff]
      intro g hg e₁
      have h0 := congr_fun (congr_arg Subtype.val hg) e₁.1
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply] at h0
      simp_rw [hvec_eval] at h0
      simpa using h0
    have hcard := LinearIndependent.fintype_card_le_finrank hli
    rw [Fintype.card_coe] at hcard
    exact le_trans hcard hRk
  have hH_le : Module.finrank (ZMod 2) H ≤
      (Finset.univ.filter (fun A : Finset (Fin n) =>
        (Finset.univ.filter (fun e : Fin m => u e ∈ A ∧ v e ∈ A)).card ≤ k)).sup Finset.card := by
    rw [← hAcard]
    exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_univ A, hEA_le⟩)
  have hrank' : Module.finrank (ZMod 2) H + Module.finrank (ZMod 2) (LinearMap.ker φ) =
      Module.finrank (ZMod 2) W := hrank
  have hker_le' : Module.finrank (ZMod 2) (LinearMap.ker φ) ≤ k := hker_le
  omega

private def allBoolLists : ℕ → Finset (List Bool)
  | 0 => {[]}
  | r + 1 => (allBoolLists r).biUnion (fun p => {p ++ [false], p ++ [true]})

private lemma mem_allBoolLists (r : ℕ) (p : List Bool) :
    p ∈ allBoolLists r ↔ p.length = r := by
  induction r generalizing p with
  | zero =>
    simp [allBoolLists]
  | succ r ih =>
    simp only [allBoolLists, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, ih]
    constructor
    · rintro ⟨q, hq, rfl | rfl⟩ <;> simp [hq]
    · intro hlen
      have hne : p ≠ [] := by intro h; simp [h] at hlen
      refine ⟨p.dropLast, by rw [List.length_dropLast, hlen]; omega, ?_⟩
      cases ht : p.getLast hne
      · left; simpa [ht] using (List.dropLast_append_getLast hne).symm
      · right; simpa [ht] using (List.dropLast_append_getLast hne).symm

private lemma card_allBoolLists (r : ℕ) : (allBoolLists r).card = 2 ^ r := by
  induction r with
  | zero => simp [allBoolLists]
  | succ r ih =>
    have hdisj : Set.PairwiseDisjoint (↑(allBoolLists r) : Set (List Bool))
        (fun p => ({p ++ [false], p ++ [true]} : Finset (List Bool))) := by
      intro p₁ _ p₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
      rcases hx1 with rfl | rfl <;> rcases hx2 with h | h <;>
        have := List.append_inj_left' h rfl <;> exact hne this
    rw [allBoolLists, Finset.card_biUnion hdisj]
    have h2 : ∀ p ∈ allBoolLists r, ({p ++ [false], p ++ [true]} : Finset (List Bool)).card = 2 := by
      intro p _
      rw [Finset.card_pair]
      intro h
      have := List.append_inj_right' h rfl
      simp at this
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, ih, pow_succ]

end PEqualNP.Outside.L_pcx_390_aux

open PEqualNP.Outside.L_pcx_390_aux in
theorem PEqualNP.Outside.L_pcx_390 : (∀ (n m : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  let Y := Fin m → F
  let tree := fun (target : (X × Y) → Y) (allowed : Set (Set Y)) (K : ℕ) =>
    ∃ (N J : Finset (List Bool)) (query : List Bool → (X × Y) →ₗ[F] F)
      (bias : List Bool → F) (out : List Bool → Set Y),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ K ∧ ∀ p ∈ N \ J, out p ∈ allowed ∧
        ∀ z : X × Y, (∀ j : Fin p.length,
          decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) → target z ∈ out p
  ∀ (u v : Fin m → Fin n) (_ : ∀ e, u e < v e)
    (_ : Function.Injective (fun e : Fin m => (u e, v e))) (k : ℕ) (_ : k ≤ m) (K : ℕ),
    let target := fun (z : X × Y) (e : Fin m) => z.2 e + z.1 (u e) * z.1 (v e)
    let allowed := {L : Set Y | ∃ (R : Submodule F Y) (c : Y),
      Module.finrank F R ≤ k ∧ L = {w : Y | w-c ∈ R}}
    let h := (Finset.univ.filter (fun A : Finset (Fin n) =>
      (Finset.univ.filter (fun e : Fin m => u e ∈ A ∧ v e ∈ A)).card ≤ k)).sup Finset.card
    tree target allowed K ↔ 2^(n+m-(k+h)) ≤ K) := by
  intro n m F X Y tree u v huv hinj k hkm K target allowed h
  have hle_n : h ≤ n := by
    apply Finset.sup_le
    intro A _
    exact le_trans (Finset.card_le_univ A) (by simp)
  constructor
  · rintro ⟨N, J, query, bias, out, hroot, hJN, hpar, hch, hcardK, hleaves⟩
    let cell : List Bool → Finset (X × Y) := fun p =>
      Finset.univ.filter (fun z : X × Y =>
        ∀ j : Fin p.length, decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j)
    have hcover : (Finset.univ : Finset (X × Y)) ⊆ (N \ J).biUnion cell := by
      intro z _
      obtain ⟨p, hp, hpath⟩ := exists_leaf_of_tree N J hroot hch
        (fun q => decide (query q z = bias q))
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hpath⟩⟩
    have hcell_le : ∀ p ∈ N \ J, (cell p).card ≤ 2 ^ (k + h) := by
      intro p hp
      by_cases hne : (cell p).Nonempty
      · obtain ⟨z₀, hz₀⟩ := hne
        have hz₀_path := (Finset.mem_filter.mp hz₀).2
        let W : Submodule F (X × Y) :=
          ⨅ j : Fin p.length, LinearMap.ker (query (p.take j.val))
        letI : Fintype W := Fintype.ofFinite W
        have hmem_iff : ∀ z : X × Y, z ∈ cell p ↔ z - z₀ ∈ W := by
          intro z
          simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and, W, Submodule.mem_iInf,
            LinearMap.mem_ker, map_sub, sub_eq_zero]
          constructor
          · intro hz j
            have h1 := (zmod2_decide_eq _ _ _).mp (hz j)
            have h2 := (zmod2_decide_eq _ _ _).mp (hz₀_path j)
            rw [h1, h2]
          · intro hz j
            rw [zmod2_decide_eq, hz j]
            exact (zmod2_decide_eq _ _ _).mp (hz₀_path j)
        have hcard_eq : (cell p).card = Fintype.card W := by
          have heq : (cell p).card = Fintype.card (cell p) := (Fintype.card_coe _).symm
          rw [heq]
          apply Fintype.card_congr
          refine
            { toFun := fun z => ⟨z.1 - z₀, (hmem_iff z.1).mp z.2⟩
              invFun := fun d => ⟨z₀ + d.1, (hmem_iff (z₀ + d.1)).mpr (by simpa using d.2)⟩
              left_inv := fun z => by apply Subtype.ext; exact add_sub_cancel z₀ z.1
              right_inv := fun d => by apply Subtype.ext; exact add_sub_cancel_left z₀ d.1 }
        obtain ⟨hallow, hout_p⟩ := hleaves p hp
        rcases hallow with ⟨R, c, hRk, hout_eq⟩
        have hflat : ∀ d ∈ W,
            (fun e => (z₀ + d).2 e + (z₀ + d).1 (u e) * (z₀ + d).1 (v e)) - c ∈ R := by
          intro d hd
          have hmem : z₀ + d ∈ cell p := (hmem_iff (z₀ + d)).mpr (by simpa using hd)
          have hpath := (Finset.mem_filter.mp hmem).2
          have ht := hout_p (z₀ + d) hpath
          rw [hout_eq] at ht
          exact ht
        have hfr := flat_finrank_le u v huv hinj k R hRk c W z₀ hflat
        rw [hcard_eq, card_submodule_zmod2]
        exact Nat.pow_le_pow_right (by omega) hfr
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
        exact Nat.zero_le _
    have htotal : Fintype.card (X × Y) ≤ (N \ J).card * 2 ^ (k + h) := by
      calc Fintype.card (X × Y) = (Finset.univ : Finset (X × Y)).card := rfl
        _ ≤ ((N \ J).biUnion cell).card := Finset.card_le_card hcover
        _ ≤ ∑ p ∈ N \ J, (cell p).card := Finset.card_biUnion_le
        _ ≤ ∑ _p ∈ N \ J, 2 ^ (k + h) := Finset.sum_le_sum hcell_le
        _ = (N \ J).card * 2 ^ (k + h) := by simp
    have hcardXY : Fintype.card (X × Y) = 2 ^ (n + m) := by
      simp [X, Y, F, Fintype.card_prod, Fintype.card_pi, ZMod.card, pow_add]
    rw [hcardXY] at htotal
    have hle_mul : 2 ^ (n + m - (k + h)) * 2 ^ (k + h) ≤ K * 2 ^ (k + h) := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
      exact le_trans htotal (Nat.mul_le_mul_right _ hcardK)
    exact Nat.le_of_mul_le_mul_right hle_mul (by positivity)
  · intro hK
    let good : Finset (Finset (Fin n)) := Finset.univ.filter (fun A : Finset (Fin n) =>
      (Finset.univ.filter (fun e : Fin m => u e ∈ A ∧ v e ∈ A)).card ≤ k)
    have hgood_ne : good.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩⟩
    obtain ⟨A, hA_mem, hA_sup⟩ := Finset.exists_mem_eq_sup good hgood_ne Finset.card
    have hA_card : A.card = h := hA_sup.symm
    let EA : Finset (Fin m) := Finset.univ.filter (fun e : Fin m => u e ∈ A ∧ v e ∈ A)
    have hEA_le : EA.card ≤ k := (Finset.mem_filter.mp hA_mem).2
    have hrem : k - EA.card ≤ (EAᶜ).card := by
      have hsum : EA.card + (EAᶜ).card = m := by
        simp
      omega
    obtain ⟨B', hB'_sub, hB'_card⟩ := Finset.exists_subset_card_eq hrem
    let B : Finset (Fin m) := EA ∪ B'
    have hdisj : Disjoint EA B' :=
      Disjoint.mono_right hB'_sub disjoint_compl_right
    have hB_card : B.card = k := by
      rw [Finset.card_union_of_disjoint hdisj, hB'_card]; omega
    have hEA_sub_B : EA ⊆ B := Finset.subset_union_left
    let Lx : List (Fin n) := (Aᶜ).toList
    let Ly : List (Fin m) := (Bᶜ).toList
    have hLx_len : Lx.length = n - h := by
      have hsum : A.card + (Aᶜ).card = n := by simp
      simp only [Lx, Finset.length_toList]; omega
    have hLy_len : Ly.length = m - k := by
      have hsum : B.card + (Bᶜ).card = m := by simp
      simp only [Ly, Finset.length_toList]; omega
    let dx := Lx.length
    let dy := Ly.length
    let d := dx + dy
    have hd_eq : d = n + m - (k + h) := by
      dsimp only [d, dx, dy]; rw [hLx_len, hLy_len]; omega
    let N : Finset (List Bool) := (Finset.range (d + 1)).biUnion allBoolLists
    let J : Finset (List Bool) := (Finset.range d).biUnion allBoolLists
    have hmemN : ∀ p, p ∈ N ↔ p.length ≤ d := by
      intro p
      simp only [N, Finset.mem_biUnion, Finset.mem_range, mem_allBoolLists]
      constructor
      · rintro ⟨r, hr, hlen⟩; omega
      · intro hlen; exact ⟨p.length, by omega, rfl⟩
    have hmemJ : ∀ p, p ∈ J ↔ p.length < d := by
      intro p
      simp only [J, Finset.mem_biUnion, Finset.mem_range, mem_allBoolLists]
      constructor
      · rintro ⟨r, hr, hlen⟩; omega
      · intro hlen; exact ⟨p.length, hlen, rfl⟩
    have hsdiff : N \ J = allBoolLists d := by
      ext p
      simp only [Finset.mem_sdiff, hmemN, hmemJ, mem_allBoolLists]
      omega
    let valX : List Bool → Fin n → F := fun p i => boolToF (p.getD (Lx.idxOf i) false)
    let projX : Fin n → (X × Y) →ₗ[F] F := fun i => (LinearMap.proj i).comp (LinearMap.fst F X Y)
    let projY : Fin m → (X × Y) →ₗ[F] F := fun e => (LinearMap.proj e).comp (LinearMap.snd F X Y)
    let query : List Bool → (X × Y) →ₗ[F] F := fun p =>
      if h1 : p.length < dx then
        projX (Lx[p.length]'h1)
      else if h2 : p.length < dx + dy then
        let r : ℕ := p.length - dx
        have hr : r < dy := by omega
        let e : Fin m := Ly[r]'hr
        if u e ∉ A ∧ v e ∉ A then
          projY e
        else if u e ∉ A then
          projY e + valX p (u e) • projX (v e)
        else
          projY e + valX p (v e) • projX (u e)
      else
        0
    let bias : List Bool → F := fun _ => 1
    let R : Submodule F Y :=
      { carrier := {w : Y | ∀ e, e ∉ B → w e = 0}
        , add_mem' := fun {a b} ha hb e he => by
            change a e + b e = 0
            rw [ha e he, hb e he, add_zero]
        zero_mem' := fun _ _ => rfl
        smul_mem' := fun c {a} ha e he => by
            change c * a e = 0
            rw [ha e he, mul_zero] }
    have hR_fr : Module.finrank F R ≤ k := by
      let eqv : (B → F) ≃ₗ[F] R :=
        { toFun := fun f => ⟨fun e => if he : e ∈ B then f ⟨e, he⟩ else 0,
            fun e he => by simp [he]⟩
          invFun := fun w b => w.1 b.1
          map_add' := fun f g => by
            apply Subtype.ext; ext e
            change (if he : e ∈ B then f ⟨e, he⟩ + g ⟨e, he⟩ else (0 : F)) =
              (if he : e ∈ B then f ⟨e, he⟩ else 0) + (if he : e ∈ B then g ⟨e, he⟩ else 0)
            by_cases he : e ∈ B <;> simp [he]
          map_smul' := fun c f => by
            apply Subtype.ext; ext e
            change (if he : e ∈ B then c * f ⟨e, he⟩ else (0 : F)) =
              c * (if he : e ∈ B then f ⟨e, he⟩ else 0)
            by_cases he : e ∈ B <;> simp [he]
          left_inv := fun f => by ext ⟨e, he⟩; simp [he]
          right_inv := fun w => by
            apply Subtype.ext; ext e
            by_cases he : e ∈ B
            · simp [he]
            · simp [he, w.2 e he] }
      have hfr : Module.finrank F R = k := by
        rw [← eqv.finrank_eq, Module.finrank_pi, Fintype.card_coe, hB_card]
      omega
    let center : List Bool → Y := fun p e =>
      if e ∈ B then 0
      else
        let r := Ly.idxOf e
        let qval := boolToF (p.getD (dx + r) false)
        if u e ∉ A ∧ v e ∉ A then
          qval + valX p (u e) * valX p (v e)
        else
          qval
    let out : List Bool → Set Y := fun p => {w : Y | w - center p ∈ R}
    refine ⟨N, J, query, bias, out, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmemN]; simp
    · intro p hp; rw [hmemJ] at hp; rw [hmemN]; omega
    · intro p t hp; rw [hmemN] at hp; rw [hmemJ]; simp at hp; omega
    · intro p hp; rw [hmemJ] at hp; constructor <;> (rw [hmemN]; simp; omega)
    · rw [hsdiff, card_allBoolLists, hd_eq]; exact hK
    · intro p hp
      rw [hsdiff, mem_allBoolLists] at hp
      refine ⟨⟨R, center p, hR_fr, rfl⟩, ?_⟩
      intro z hpath
      change target z - center p ∈ R
      intro e heB
      have hxe : ∀ i, i ∉ A → z.1 i = valX p i := by
        intro i hiA
        have hiLx : i ∈ Lx := by simp [Lx, hiA]
        have hidx_lt : Lx.idxOf i < dx := List.idxOf_lt_length_iff.mpr hiLx
        have hidx_p : Lx.idxOf i < p.length := by omega
        have hstep := hpath ⟨Lx.idxOf i, hidx_p⟩
        have hlen_tk : (p.take (Lx.idxOf i)).length = Lx.idxOf i :=
          List.length_take_of_le (Nat.le_of_lt hidx_p)
        have hq : query (p.take (Lx.idxOf i)) z = z.1 i := by
          dsimp only [query]
          have h1 : (p.take (Lx.idxOf i)).length < dx := by omega
          rw [dif_pos h1]
          have hget : Lx[(p.take (Lx.idxOf i)).length]'h1 = i := by
            simp only [hlen_tk]
            exact List.getElem_idxOf hidx_lt
          change z.1 (Lx[(p.take (Lx.idxOf i)).length]'h1) = z.1 i
          rw [hget]
        rw [hq] at hstep
        have hval := (zmod2_decide_eq_one _ _).mp hstep
        simpa [valX, List.getD_eq_getElem?_getD, hidx_p] using hval
      have hvalX_take : ∀ (r : ℕ) (i : Fin n), i ∉ A → valX (p.take (dx + r)) i = valX p i := by
        intro r i hiA
        have hiLx : i ∈ Lx := by simp [Lx, hiA]
        have hidx_lt : Lx.idxOf i < dx := List.idxOf_lt_length_iff.mpr hiLx
        simp only [valX, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega : Lx.idxOf i < dx + r)]
      have heLy : e ∈ Ly := by simp [Ly, heB]
      have hr_lt : Ly.idxOf e < dy := List.idxOf_lt_length_iff.mpr heLy
      have hpos_p : dx + Ly.idxOf e < p.length := by omega
      have hstep := hpath ⟨dx + Ly.idxOf e, hpos_p⟩
      let pr := p.take (dx + Ly.idxOf e)
      have hpr_len : pr.length = dx + Ly.idxOf e :=
        List.length_take_of_le (Nat.le_of_lt hpos_p)
      have hnot1 : ¬(pr.length < dx) := by omega
      have h2 : pr.length < dx + dy := by omega
      have hgetE : Ly[pr.length - dx]'(by omega) = e := by
        have hsub : pr.length - dx = Ly.idxOf e := by omega
        simp only [hsub]
        exact List.getElem_idxOf hr_lt
      have hqval : query pr z = boolToF (p.getD (dx + Ly.idxOf e) false) := by
        have h := (zmod2_decide_eq_one _ _).mp hstep
        simpa [pr, List.getD_eq_getElem?_getD, hpos_p] using h
      have hnotEA : ¬(u e ∈ A ∧ v e ∈ A) := by
        intro hboth
        exact heB (hEA_sub_B (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hboth⟩))
      change target z e - center p e = 0
      dsimp only [target, center]
      rw [if_neg heB]
      by_cases hbothOut : u e ∉ A ∧ v e ∉ A
      · have hqeval : query pr z = z.2 e := by
          dsimp only [query]
          rw [dif_neg hnot1, dif_pos h2]
          simp only [hgetE]
          rw [if_pos hbothOut]
          rfl
        rw [hqeval] at hqval
        rw [if_pos hbothOut, hqval, hxe (u e) hbothOut.1, hxe (v e) hbothOut.2]
        ring
      · by_cases huOut : u e ∉ A
        · have hqeval : query pr z = z.2 e + valX pr (u e) * z.1 (v e) := by
            dsimp only [query]
            rw [dif_neg hnot1, dif_pos h2]
            simp only [hgetE]
            rw [if_neg hbothOut, if_pos huOut]
            rfl
          rw [hqeval, hvalX_take (Ly.idxOf e) (u e) huOut, ← hxe (u e) huOut] at hqval
          rw [if_neg hbothOut, hqval]
          ring
        · have hvOut : v e ∉ A := by
            intro hvA
            exact hnotEA ⟨Classical.not_not.mp huOut, hvA⟩
          have hqeval : query pr z = z.2 e + valX pr (v e) * z.1 (u e) := by
            dsimp only [query]
            rw [dif_neg hnot1, dif_pos h2]
            simp only [hgetE]
            rw [if_neg hbothOut, if_neg huOut]
            rfl
          rw [hqeval, hvalX_take (Ly.idxOf e) (v e) hvOut, ← hxe (v e) hvOut] at hqval
          rw [if_neg hbothOut, mul_comm (z.1 (u e)) (z.1 (v e)), hqval]
          ring
