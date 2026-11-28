import Mathlib
import PEqualNP.Defs

open Module

namespace PEqualNP.Outside.L_lib_1042_aux

section Abs

variable {ι : Type*} [DecidableEq ι]

def IsRk (r : Finset ι → ℕ) : Prop :=
  r ∅ = 0 ∧ (∀ A B : Finset ι, A ⊆ B → r A ≤ r B) ∧
  (∀ A B : Finset ι, r (A ∪ B) + r (A ∩ B) ≤ r A + r B) ∧ (∀ a : ι, r {a} ≤ 1)

theorem rk_insert_le {r : Finset ι → ℕ} (h : IsRk r) (a : ι) (A : Finset ι) :
    r (insert a A) ≤ r {a} + r A := by
  have := h.2.2.1 {a} A
  rw [← Finset.insert_eq] at this
  omega

theorem rk_union_le {r : Finset ι → ℕ} (h : IsRk r) (A D : Finset ι) :
    r (A ∪ D) ≤ r A + D.card := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert x D hx ih =>
    rw [Finset.union_insert, Finset.card_insert_of_notMem hx]
    have h1 := rk_insert_le h x (A ∪ D)
    have h2 := h.2.2.2 x
    omega

theorem rk_le_sum {r : Finset ι → ℕ} (h : IsRk r) (A : Finset ι) :
    r A ≤ ∑ e ∈ A, r {e} := by
  induction A using Finset.induction_on with
  | empty => simp [h.1]
  | insert x A hx ih =>
    rw [Finset.sum_insert hx]
    have h1 := rk_insert_le h x A
    omega

theorem weak {r1 r2 : Finset ι → ℕ} (h1 : IsRk r1) (h2 : IsRk r2) (S A E : Finset ι)
    (hS : S ⊆ E) (i1 : r1 S = S.card) (i2 : r2 S = S.card) :
    S.card ≤ r1 A + r2 (E \ A) := by
  have e1 : S ∩ A ∪ S \ A = S := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have e2 : S \ A ∪ S ∩ A = S := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  have a1 := rk_union_le h1 (S ∩ A) (S \ A)
  have b1 := rk_union_le h2 (S \ A) (S ∩ A)
  rw [e1] at a1
  rw [e2] at b1
  have a2 := h1.2.1 (S ∩ A) A Finset.inter_subset_right
  have b2 := h2.2.1 (S \ A) (E \ A) (Finset.sdiff_subset_sdiff hS le_rfl)
  have c := Finset.card_inter_add_card_sdiff S A
  omega

theorem contr {r : Finset ι → ℕ} (h : IsRk r) (e : ι) (he : r {e} = 1) :
    IsRk (fun A => r (insert e A) - 1) := by
  have lb : ∀ A : Finset ι, 1 ≤ r (insert e A) := fun A => by
    have := h.2.1 {e} (insert e A) (by simp)
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [he]
  · intro A B hAB
    have := h.2.1 _ _ (Finset.insert_subset_insert e hAB)
    simp only
    omega
  · intro A B
    have := h.2.2.1 (insert e A) (insert e B)
    rw [← Finset.insert_union_distrib, ← Finset.insert_inter_distrib] at this
    have := lb A
    have := lb B
    have := lb (A ∪ B)
    have := lb (A ∩ B)
    simp only
    omega
  · intro a
    have h1 := rk_insert_le h e {a}
    have h2 := h.2.2.2 a
    simp only
    omega

theorem inter (n : ℕ) : ∀ (r1 r2 : Finset ι → ℕ), IsRk r1 → IsRk r2 → ∀ E : Finset ι,
    E.card = n → ∃ S ⊆ E, ∃ C ⊆ E, r1 S = S.card ∧ r2 S = S.card ∧
      r1 C + r2 (E \ C) = S.card := by
  induction n with
  | zero =>
    intro r1 r2 h1 h2 E hE
    rw [Finset.card_eq_zero] at hE
    subst hE
    exact ⟨∅, subset_refl _, ∅, subset_refl _, by simp [h1.1, h2.1]⟩
  | succ n ih =>
    intro r1 r2 h1 h2 E hE
    by_cases hx : ∃ e ∈ E, r1 {e} = 1 ∧ r2 {e} = 1
    · obtain ⟨e, heE, he1, he2⟩ := hx
      have hcard : (E.erase e).card = n := by rw [Finset.card_erase_of_mem heE]; omega
      obtain ⟨S1, hS1, A, hA, i1, j1, c1⟩ := ih r1 r2 h1 h2 _ hcard
      obtain ⟨S2, hS2, B, hB, i2, j2, c2⟩ :=
        ih _ _ (contr h1 e he1) (contr h2 e he2) _ hcard
      obtain ⟨C, hC, hmin⟩ := Finset.exists_min_image E.powerset
        (fun C => r1 C + r2 (E \ C)) ⟨∅, Finset.empty_mem_powerset E⟩
      rw [Finset.mem_powerset] at hC
      have heS2 : e ∉ S2 := fun h => by have := hS2 h; simp at this
      have heA : e ∉ A := fun h => by have := hA h; simp at this
      have heB : e ∉ B := fun h => by have := hB h; simp at this
      have lb1 := h1.2.1 {e} (insert e S2) (by simp)
      have lb2 := h2.2.1 {e} (insert e S2) (by simp)
      have hS1E : S1 ⊆ E := hS1.trans (Finset.erase_subset e E)
      have hS2E : insert e S2 ⊆ E :=
        Finset.insert_subset heE (hS2.trans (Finset.erase_subset e E))
      have k1 : r1 (insert e S2) = (insert e S2).card := by
        rw [Finset.card_insert_of_notMem heS2]; omega
      have k2 : r2 (insert e S2) = (insert e S2).card := by
        rw [Finset.card_insert_of_notMem heS2]; omega
      by_cases hp : r1 C + r2 (E \ C) ≤ S1.card
      · refine ⟨S1, hS1E, C, hC, i1, j1, ?_⟩
        have := weak h1 h2 S1 C E hS1E i1 j1
        omega
      by_cases hq : r1 C + r2 (E \ C) ≤ S2.card + 1
      · refine ⟨insert e S2, hS2E, C, hC, k1, k2, ?_⟩
        have := weak h1 h2 _ C E hS2E k1 k2
        rw [Finset.card_insert_of_notMem heS2] at this ⊢
        omega
      exfalso
      have hAE : A ⊆ E := hA.trans (Finset.erase_subset e E)
      have hBE : insert e B ⊆ E := Finset.insert_subset heE (hB.trans (Finset.erase_subset e E))
      have s1 := h1.2.2.1 A (insert e B)
      have s2 := h2.2.2.1 ((E.erase e) \ A) (E \ B)
      have m1 := hmin (A ∩ insert e B)
        (Finset.mem_powerset.2 (Finset.inter_subset_left.trans hAE))
      have m2 := hmin (A ∪ insert e B) (Finset.mem_powerset.2 (Finset.union_subset hAE hBE))
      have q1 : (E.erase e \ A) ∪ (E \ B) = E \ (A ∩ insert e B) := by
        ext x
        by_cases hxe : x = e
        · subst hxe; simp [heA, heB, heE]
        · simp [hxe]; tauto
      have q2 : (E.erase e \ A) ∩ (E \ B) = E \ (A ∪ insert e B) := by
        ext x
        by_cases hxe : x = e
        · subst hxe; simp [heA, heB, heE]
        · simp [hxe]; tauto
      have q3 : insert e (E.erase e \ B) = E \ B := by
        ext x
        by_cases hxe : x = e
        · subst hxe; simp [heB, heE]
        · simp [hxe]
      rw [q1, q2] at s2
      rw [q3] at c2
      have lb3 := h1.2.1 {e} (insert e B) (by simp)
      have lb4 := h2.2.1 {e} (E \ B) (by simp [heE, heB])
      omega
    · simp only [not_exists, not_and] at hx
      refine ⟨∅, Finset.empty_subset _, E.filter (fun e => r1 {e} = 0),
        Finset.filter_subset _ _, by simp [h1.1], by simp [h2.1], ?_⟩
      have a := rk_le_sum h1 (E.filter (fun e => r1 {e} = 0))
      have b := rk_le_sum h2 (E \ E.filter (fun e => r1 {e} = 0))
      rw [Finset.sum_eq_zero (fun i hi => (Finset.mem_filter.1 hi).2)] at a
      rw [Finset.sum_eq_zero] at b
      · simp only [Finset.card_empty]; omega
      · intro i hi
        simp only [Finset.mem_sdiff, Finset.mem_filter, not_and] at hi
        have h3 := h1.2.2.2 i
        have h4 := h2.2.2.2 i
        have h5 := hx i hi.1
        have h6 := hi.2 hi.1
        omega

end Abs

section Lin

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
  {ι : Type*} [DecidableEq ι]

noncomputable def lrk (u : ι → V) (A : Finset ι) : ℕ :=
  finrank F (Submodule.span F (u '' (A : Set ι)))

theorem lrk_isRk [FiniteDimensional F V] (u : ι → V) : IsRk (lrk (F := F) u) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [lrk]
  · intro A B hAB
    exact Submodule.finrank_mono
      (Submodule.span_mono (Set.image_mono (Finset.coe_subset.2 hAB)))
  · intro A B
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F (u '' (A : Set ι)))
      (Submodule.span F (u '' (B : Set ι)))
    have e : Submodule.span F (u '' ((A ∪ B : Finset ι) : Set ι)) =
        Submodule.span F (u '' (A : Set ι)) ⊔ Submodule.span F (u '' (B : Set ι)) := by
      rw [Finset.coe_union, Set.image_union, Submodule.span_union]
    have hle : Submodule.span F (u '' ((A ∩ B : Finset ι) : Set ι)) ≤
        Submodule.span F (u '' (A : Set ι)) ⊓ Submodule.span F (u '' (B : Set ι)) :=
      le_inf (Submodule.span_mono (Set.image_mono (by simp)))
        (Submodule.span_mono (Set.image_mono (by simp)))
    have := Submodule.finrank_mono hle
    unfold lrk
    rw [e]
    omega
  · intro a
    unfold lrk
    rw [Finset.coe_singleton, Set.image_singleton]
    by_cases hv : u a = 0
    · rw [hv, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]; omega
    · rw [finrank_span_singleton hv]

theorem li_iff (u : ι → V) (S : Finset ι) :
    LinearIndependent F (fun i : S => u i.val) ↔ lrk (F := F) u S = S.card := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_coe]
  have : Set.range (fun i : S => u i.val) = u '' (S : Set ι) := by
    ext x; simp
  unfold Set.finrank lrk
  rw [this]
  constructor <;> intro h <;> omega

theorem surj [FiniteDimensional F V] (a : ι → Module.Dual F V) (S : Finset ι)
    (ha : LinearIndependent F (fun i : S => a i.val)) :
    Function.Surjective (LinearMap.pi (fun i : S => a i.val)) := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi (fun i : S => a i.val))
  have hk : LinearMap.ker (LinearMap.pi fun i : S => a i.val) ≤
      (Submodule.span F (a '' (S : Set ι))).dualCoannihilator := by
    intro x hx
    rw [Submodule.mem_dualCoannihilator]
    intro ψ hψ
    have : Submodule.span F (a '' (S : Set ι)) ≤ LinearMap.ker (Module.Dual.eval F V x) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      have := congrFun (LinearMap.mem_ker.1 hx) ⟨i, hi⟩
      simpa using this
    simpa using this hψ
  have h2 := Submodule.finrank_mono hk
  have h3 := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.span F (a '' (S : Set ι)))
  have h4 := (li_iff a S).1 ha
  unfold lrk at h4
  have h5 := Submodule.finrank_le (LinearMap.range (LinearMap.pi (fun i : S => a i.val)))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h5 ⊢
  omega

end Lin

section Count

theorem sum_fib {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) (k : ℕ)
    (hk : ∀ b, (Finset.univ.filter (fun x => f x = b)).card = k) (h : β → ℕ) :
    ∑ x, h (f x) = k * ∑ b, h b := by
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => h (f x)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.1 hx).2]),
    Finset.sum_const, hk, smul_eq_mul]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem fib {X : Type*} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [Fintype X]
    {ι : Type*} [DecidableEq ι] (a : ι → Module.Dual F X) (S : Finset ι)
    (ha : LinearIndependent F (fun i : S => a i.val)) :
    ∃ k, (∀ s, (Finset.univ.filter
      (fun x => (LinearMap.pi (fun i : S => a i.val) : X →ₗ[F] (S → F)) x = s)).card = k) ∧
      Fintype.card X = k * Fintype.card F ^ S.card := by
  classical
  have hs := surj a S ha
  refine ⟨(Finset.univ.filter
      (fun x => (LinearMap.pi (fun i : S => a i.val) : X →ₗ[F] (S → F)) x = 0)).card,
    fun s => ?_, ?_⟩
  · have := AddMonoidHom.card_fiber_eq_of_mem_range
      (LinearMap.pi (fun i : S => a i.val) : X →ₗ[F] (S → F)) (hs s) (hs 0)
    convert this
  · have := sum_fib (LinearMap.pi (fun i : S => a i.val) : X →ₗ[F] (S → F)) _
      (fun s => by
        have := AddMonoidHom.card_fiber_eq_of_mem_range
          (LinearMap.pi (fun i : S => a i.val) : X →ₗ[F] (S → F)) (hs s) (hs 0)
        convert this) (fun _ => 1)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at this
    rw [this, Fintype.card_fun, Fintype.card_coe]

theorem zero_pairs : Fintype.card {z : F × F // z.1 * z.2 = 0} ≤ 2 * Fintype.card F - 1 := by
  classical
  let g : {z : F × F // z.1 * z.2 = 0} → F ⊕ {u : F // u ≠ 0} := fun z =>
    if h : z.1.1 = 0 then Sum.inl z.1.2 else Sum.inr ⟨z.1.1, h⟩
  have hg : Function.Injective g := by
    rintro ⟨⟨x1, y1⟩, h1⟩ ⟨⟨x2, y2⟩, h2⟩ hxy
    simp only at h1 h2
    by_cases hx1 : x1 = 0 <;> by_cases hx2 : x2 = 0 <;>
      simp [g, hx1, hx2] at hxy
    · subst hx1; subst hx2; subst hxy; rfl
    · have hy1 : y1 = 0 := by simpa [hx1] using h1
      have hy2 : y2 = 0 := by simpa [hx2] using h2
      subst hxy hy1 hy2; rfl
  have := Fintype.card_le_of_injective g hg
  rw [Fintype.card_sum, Fintype.card_subtype_compl,
    Fintype.card_unique (α := {x : F // x = 0})] at this
  have := Fintype.card_pos (α := F)
  omega

theorem count {X Y : Type*} [AddCommGroup X] [Module F X] [FiniteDimensional F X] [Fintype X]
    [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y] [Fintype Y]
    {ι : Type*} [DecidableEq ι] (a : ι → Module.Dual F X) (b : ι → Module.Dual F Y)
    (S : Finset ι) (ha : LinearIndependent F (fun i : S => a i.val))
    (hb : LinearIndependent F (fun i : S => b i.val)) :
    Fintype.card F ^ (2 * S.card) *
      (Finset.univ.filter (fun w : X × Y => ∀ i ∈ S, a i w.1 * b i w.2 = 0)).card ≤
      (2 * Fintype.card F - 1) ^ S.card * Fintype.card X * Fintype.card Y := by
  classical
  obtain ⟨ka, hka, cX⟩ := fib a S ha
  obtain ⟨kb, hkb, cY⟩ := fib b S hb
  set φ := (LinearMap.pi (fun i : S => a i.val) : X →ₗ[F] (S → F))
  set ψ := (LinearMap.pi (fun i : S => b i.val) : Y →ₗ[F] (S → F))
  let G : (S → F) → (S → F) → Prop := fun s t => ∀ i, s i * t i = 0
  have e1 : (Finset.univ.filter (fun w : X × Y => ∀ i ∈ S, a i w.1 * b i w.2 = 0)).card =
      ∑ x, ∑ y, if G (φ x) (ψ y) then 1 else 0 := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    congr 1
    simp [G, φ, ψ]
  have e2 : ∀ x, (∑ y, if G (φ x) (ψ y) then 1 else 0) =
      kb * ∑ t, if G (φ x) t then 1 else 0 := fun x =>
    sum_fib ψ kb hkb (fun t => if G (φ x) t then 1 else 0)
  have e3 : (∑ x, ∑ t, if G (φ x) t then 1 else 0) =
      ka * ∑ s, ∑ t, if G s t then 1 else 0 :=
    sum_fib φ ka hka (fun s => ∑ t, if G s t then 1 else 0)
  have e4 : (∑ s, ∑ t, if G s t then 1 else 0) = Fintype.card {st : (S → F) × (S → F) //
      G st.1 st.2} := by
    rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have e5 : Fintype.card {st : (S → F) × (S → F) // G st.1 st.2} =
      Fintype.card {z : F × F // z.1 * z.2 = 0} ^ S.card := by
    rw [← Fintype.card_coe S, ← Fintype.card_fun]
    refine Fintype.card_congr ?_
    refine ((Equiv.arrowProdEquivProdArrow S (fun _ => F) (fun _ => F)).symm.subtypeEquiv ?_).trans
      (Equiv.subtypePiEquivPi (p := fun _ (z : F × F) => z.1 * z.2 = 0))
    intro st
    simp [G, Equiv.arrowProdEquivProdArrow]
  have hz := zero_pairs (F := F)
  have hpow := Nat.pow_le_pow_left hz S.card
  rw [e1, Finset.sum_congr rfl (fun x _ => e2 x), ← Finset.mul_sum, e3, e4, e5, cX, cY]
  have : Fintype.card F ^ (2 * S.card) = Fintype.card F ^ S.card * Fintype.card F ^ S.card := by
    rw [two_mul, pow_add]
  rw [this]
  calc Fintype.card F ^ S.card * Fintype.card F ^ S.card *
        (kb * (ka * Fintype.card {z : F × F // z.1 * z.2 = 0} ^ S.card))
      = Fintype.card {z : F × F // z.1 * z.2 = 0} ^ S.card *
        (ka * Fintype.card F ^ S.card) * (kb * Fintype.card F ^ S.card) := by ring
    _ ≤ (2 * Fintype.card F - 1) ^ S.card *
        (ka * Fintype.card F ^ S.card) * (kb * Fintype.card F ^ S.card) := by
      gcongr

end Count

end PEqualNP.Outside.L_lib_1042_aux

open PEqualNP.Outside.L_lib_1042_aux

theorem PEqualNP.Outside.L_lib_1042 : (∀ (p l r m : ℕ) [Fact p.Prime],
  let F := ZMod p
  let X := Fin l → F
  let Y := Fin r → F
  ∀ (a : Fin m → X →ₗ[F] F) (b : Fin m → Y →ₗ[F] F),
    let zero := fun (x : X) (y : Y) => ∀ i, a i x * b i y = 0
    let good := fun (U : Submodule F X) (V : Submodule F Y) => ∀ x ∈ U, ∀ y ∈ V, zero x y
    let cost := fun (U : Submodule F X) (V : Submodule F Y) =>
      (l - Module.finrank F U) + (r - Module.finrank F V)
    ∃ (S : Finset (Fin m)) (P : Submodule F X) (Q : Submodule F Y),
      LinearIndependent F (fun i : S => a i.val) ∧ LinearIndependent F (fun i : S => b i.val) ∧
      good P Q ∧ cost P Q = S.card ∧ (∀ U V, good U V → S.card ≤ cost U V) ∧
      p^(2*S.card) * Nat.card {w : X × Y // zero w.1 w.2} ≤
        (2*p-1)^S.card * Nat.card X * Nat.card Y) := by
  intro p l r m hp
  dsimp only
  intro a b
  classical
  obtain ⟨S, -, C, -, i1, i2, hc⟩ := inter (Finset.univ : Finset (Fin m)).card
    (lrk (F := ZMod p) (V := Module.Dual (ZMod p) (Fin l → ZMod p)) a)
    (lrk (F := ZMod p) (V := Module.Dual (ZMod p) (Fin r → ZMod p)) b)
    (lrk_isRk _) (lrk_isRk _) Finset.univ rfl
  have ha := (li_iff a S).2 i1
  have hb := (li_iff b S).2 i2
  refine ⟨S, (Submodule.span (ZMod p) (a '' (C : Set (Fin m)))).dualCoannihilator,
    (Submodule.span (ZMod p)
      (b '' ((Finset.univ \ C : Finset (Fin m)) : Set (Fin m)))).dualCoannihilator,
    ha, hb, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy i
    rw [Submodule.mem_dualCoannihilator] at hx hy
    by_cases hi : i ∈ C
    · rw [hx (a i) (Submodule.subset_span ⟨i, hi, rfl⟩), zero_mul]
    · rw [hy (b i) (Submodule.subset_span ⟨i, by simpa using hi, rfl⟩), mul_zero]
  · have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq
      (Submodule.span (ZMod p) (a '' (C : Set (Fin m))))
    have h2 := Subspace.finrank_add_finrank_dualCoannihilator_eq
      (Submodule.span (ZMod p) (b '' ((Finset.univ \ C : Finset (Fin m)) : Set (Fin m))))
    rw [Module.finrank_fin_fun] at h1 h2
    unfold lrk at hc
    omega
  · intro U V hg
    have key : ∀ i, (∀ x ∈ U, a i x = 0) ∨ (∀ y ∈ V, b i y = 0) := by
      intro i
      by_contra hcon
      simp only [not_or, not_forall] at hcon
      obtain ⟨⟨x, hx, hax⟩, ⟨y, hy, hby⟩⟩ := hcon
      exact mul_ne_zero hax hby (hg x hx y hy i)
    set A := Finset.univ.filter (fun i => ∀ x ∈ U, a i x = 0) with hAdef
    have w := weak (lrk_isRk (F := ZMod p) a) (lrk_isRk (F := ZMod p) b) S A Finset.univ
      (Finset.subset_univ _) i1 i2
    have hA : lrk (F := ZMod p) a A ≤ finrank (ZMod p) U.dualAnnihilator := by
      unfold lrk
      apply Submodule.finrank_mono
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
      exact (Finset.mem_filter.1 hi).2
    have hB : lrk (F := ZMod p) b (Finset.univ \ A) ≤ finrank (ZMod p) V.dualAnnihilator := by
      unfold lrk
      apply Submodule.finrank_mono
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_dualAnnihilator]
      have : ¬ ∀ x ∈ U, a i x = 0 := by simpa [hAdef] using hi
      exact (key i).resolve_left this
    have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq U
    have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq V
    rw [Module.finrank_fin_fun] at h1 h2
    omega
  · have hc := count (F := ZMod p) a b S ha hb
    rw [ZMod.card] at hc
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    refine le_trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_)) hc
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact fun i _ => hw i
