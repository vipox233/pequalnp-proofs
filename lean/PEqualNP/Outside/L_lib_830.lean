import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_830_aux
open Module

variable {E K : Type} [Field E] [Fintype E] [Field K] [Algebra E K]
    [FiniteDimensional E K] [Fintype K]

noncomputable def orth (S : Submodule E K) : Submodule E K :=
  (Algebra.traceForm E K).orthogonal S

theorem mem_orth (S : Submodule E K) (b : K) :
    b ∈ orth S ↔ ∀ s ∈ S, Algebra.trace E K (s * b) = 0 := by
  unfold orth
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  rfl

theorem finrank_orth (S : Submodule E K) :
    finrank E (orth S) = finrank E K - finrank E S := by
  unfold orth
  exact LinearMap.BilinForm.finrank_orthogonal (traceForm_nondegenerate E K) S

theorem card_sub (S : Submodule E K) :
    Nat.card S = Fintype.card E ^ finrank E S := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank

theorem trace_sq [CharP E 2] (y : K) :
    Algebra.trace E K (y ^ 2) = (Algebra.trace E K y) ^ 2 := by
  have : CharP K 2 := charP_of_injective_algebraMap' E 2
  apply (algebraMap E K).injective
  rw [(algebraMap E K).map_pow, trace_eq_sum_automorphisms, trace_eq_sum_automorphisms]
  rw [sum_pow_char]
  simp [map_pow]

theorem mem_orth_span (X : Set K) (b : K) :
    b ∈ orth (Submodule.span E X) ↔ ∀ x ∈ X, Algebra.trace E K (x * b) = 0 := by
  rw [mem_orth]
  refine ⟨fun h x hx => h x (Submodule.subset_span hx), fun h s hs => ?_⟩
  induction hs using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_mul_assoc, map_smul, hx, smul_zero]

noncomputable def sqS (L : Submodule E K) : Submodule E K :=
  Submodule.span E (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K)))

theorem mem_orth_sqS (L : Submodule E K) (b : K) :
    b ∈ orth (sqS L) ↔ ∀ s ∈ L, ∀ t ∈ L, Algebra.trace E K (s * t * b) = 0 := by
  unfold sqS
  rw [mem_orth_span]
  constructor
  · intro h s hs t ht
    exact h _ ⟨(⟨s, hs⟩, ⟨t, ht⟩), rfl⟩
  · rintro h _ ⟨⟨s, t⟩, rfl⟩
    exact h s s.2 t t.2

theorem mem_orth_sqS_ext (L : Submodule E K) (x b : K) :
    b ∈ orth (sqS (L ⊔ Submodule.span E {x})) ↔
      b ∈ orth (sqS L) ∧ (∀ l ∈ L, Algebra.trace E K (l * x * b) = 0) ∧
        Algebra.trace E K (x * x * b) = 0 := by
  simp only [mem_orth_sqS]
  have hx : x ∈ L ⊔ Submodule.span E {x} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  constructor
  · intro h
    exact ⟨fun s hs t ht => h s (Submodule.mem_sup_left hs) t (Submodule.mem_sup_left ht),
      fun l hl => h l (Submodule.mem_sup_left hl) x hx, h x hx x hx⟩
  · rintro ⟨h1, h2, h3⟩ s hs t ht
    obtain ⟨l, hl, y, hy, rfl⟩ := Submodule.mem_sup.1 hs
    obtain ⟨l', hl', y', hy', rfl⟩ := Submodule.mem_sup.1 ht
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hy'
    have e : (l + α • x) * (l' + β • x) * b =
        l * l' * b + β • (l * x * b) + α • (l' * x * b) + (α * β) • (x * x * b) := by
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [e, map_add, map_add, map_add, map_smul, map_smul, map_smul, h1 l hl l' hl',
      h2 l hl, h2 l' hl', h3]
    simp

noncomputable def Tb (L : Submodule E K) (b s : K) : Submodule E K :=
  L.map (LinearMap.mulLeft E b) ⊔ Submodule.span E {s}

theorem cond_iff [CharP E 2] (L : Submodule E K) (b s x : K) (hs : s ^ 2 = b) :
    ((∀ l ∈ L, Algebra.trace E K (l * x * b) = 0) ∧ Algebra.trace E K (x * x * b) = 0) ↔
      x ∈ orth (Tb L b s) := by
  have hsq : Algebra.trace E K (x * x * b) = (Algebra.trace E K (s * x)) ^ 2 := by
    rw [← trace_sq, ← hs]; ring_nf
  rw [hsq, pow_eq_zero_iff two_ne_zero, mem_orth]
  constructor
  · rintro ⟨h1, h2⟩ t ht
    obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.1 ht
    obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hu
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [add_mul, map_add, smul_mul_assoc, map_smul, h2, smul_zero, add_zero]
    simp only [LinearMap.mulLeft_apply]
    rw [← h1 l hl]; ring_nf
  · intro h
    refine ⟨fun l hl => ?_, h s (Submodule.mem_sup_right (Submodule.mem_span_singleton_self s))⟩
    have := h (b * l) (Submodule.mem_sup_left (Submodule.mem_map.2 ⟨l, hl, rfl⟩))
    rw [← this]; ring_nf

theorem finrank_mapMul (L : Submodule E K) (b : K) (hb : b ≠ 0) :
    finrank E (L.map (LinearMap.mulLeft E b)) = finrank E L := by
  have hinj : Function.Injective (LinearMap.mulLeft E b) := by
    intro u v h
    simpa [hb] using h
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj L)).symm

theorem finrank_Tb_mem (L : Submodule E K) (b s : K) (hb : b ≠ 0)
    (h : s ∈ L.map (LinearMap.mulLeft E b)) : finrank E (Tb L b s) = finrank E L := by
  unfold Tb
  rw [sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 h), finrank_mapMul L b hb]

theorem finrank_Tb_not_mem (L : Submodule E K) (b s : K) (hb : b ≠ 0)
    (h : s ∉ L.map (LinearMap.mulLeft E b)) : finrank E (Tb L b s) = finrank E L + 1 := by
  unfold Tb
  rw [Submodule.finrank_sup_span_singleton h, finrank_mapMul L b hb]

theorem mem_map_iff (L : Submodule E K) (b s : K) (hb : b ≠ 0) (hs : s ≠ 0) :
    s ∈ L.map (LinearMap.mulLeft E b) ↔ (b⁻¹ * s) ∈ L := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    simp only [LinearMap.mulLeft_apply]
    rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul]; exact hl
  · intro h
    refine ⟨b⁻¹ * s, h, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]

open Classical

theorem card_filter_mem (S : Submodule E K) :
    (Finset.univ.filter (fun b : K => b ∈ S)).card = Fintype.card E ^ finrank E S := by
  rw [← card_sub S, Nat.card_eq_fintype_card]
  exact (Fintype.card_of_subtype _ (by simp)).symm

theorem card_filter_ne (S : Submodule E K) :
    (Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ S)).card =
      Fintype.card E ^ finrank E S - 1 := by
  rw [← card_filter_mem S]
  have h : Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ S) =
      (Finset.univ.filter (fun b : K => b ∈ S)).erase 0 := by
    ext b; simp
  rw [h, Finset.card_erase_of_mem (by simp)]

theorem exists_sq [CharP E 2] (b : K) : ∃ s : K, s ^ 2 = b := by
  have : CharP K 2 := charP_of_injective_algebraMap' E 2
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) b
  exact ⟨r, by rw [hr, sq]⟩

variable (E) in
noncomputable def sr [CharP E 2] (b : K) : K := Classical.choose (exists_sq (E := E) b)

variable (E) in
theorem sr_spec [CharP E 2] (b : K) : sr E b ^ 2 = b :=
  Classical.choose_spec (exists_sq (E := E) b)

theorem sq_inj [CharP E 2] {x y : K} (h : x ^ 2 = y ^ 2) : x = y := by
  have : CharP K 2 := charP_of_injective_algebraMap' E 2
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h3 : (x - y) ^ 2 = 0 := by linear_combination h + (y ^ 2 - x * y) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h3)

theorem sr_ne [CharP E 2] {b : K} (hb : b ≠ 0) : sr E b ≠ 0 := by
  intro h
  have hs := sr_spec E b
  rw [h] at hs
  exact hb (by rw [← hs]; simp)

theorem term_eq [CharP E 2] (L : Submodule E K) (x : K) :
    Fintype.card E ^ (finrank E K - finrank E (sqS (L ⊔ Submodule.span E {x}))) - 1 =
      (Finset.univ.filter (fun b : K => (b ≠ 0 ∧ b ∈ orth (sqS L)) ∧
        x ∈ orth (Tb L b (sr E b)))).card := by
  rw [← finrank_orth, ← card_filter_ne]
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mem_orth_sqS_ext, cond_iff L b (sr E b) x (sr_spec E b)]
  tauto

theorem swap_sum [CharP E 2] (L : Submodule E K) :
    ∑ x : K, (Fintype.card E ^ (finrank E K -
        finrank E (sqS (L ⊔ Submodule.span E {x}))) - 1) =
      ∑ b : K, if (b ≠ 0 ∧ b ∈ orth (sqS L)) then
        Fintype.card E ^ (finrank E K - finrank E (Tb L b (sr E b))) else 0 := by
  simp_rw [term_eq, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : (b ≠ 0 ∧ b ∈ orth (sqS L))
  · simp only [and_iff_right hb]
    rw [if_pos hb, ← Finset.card_filter, card_filter_mem, finrank_orth]
  · simp [hb]

theorem per_b [CharP E 2] (L : Submodule E K) (b : K) :
    Fintype.card E ^ (finrank E L + 1) * (if (b ≠ 0 ∧ b ∈ orth (sqS L)) then
        Fintype.card E ^ (finrank E K - finrank E (Tb L b (sr E b))) else 0) =
      Fintype.card E ^ finrank E K * ((if (b ≠ 0 ∧ b ∈ orth (sqS L)) then 1 else 0) +
        (Fintype.card E - 1) *
          (if ((b ≠ 0 ∧ b ∈ orth (sqS L)) ∧ b⁻¹ * sr E b ∈ L) then 1 else 0)) := by
  rw [mul_ite, mul_zero]
  by_cases hb : (b ≠ 0 ∧ b ∈ orth (sqS L))
  · have hs : sr E b ≠ 0 := sr_ne hb.1
    have hq : 1 ≤ Fintype.card E := Fintype.card_pos
    rw [if_pos hb, if_pos hb]
    by_cases hX : b⁻¹ * sr E b ∈ L
    · rw [if_pos ⟨hb, hX⟩, finrank_Tb_mem L b _ hb.1 ((mem_map_iff L b _ hb.1 hs).2 hX)]
      have hle : finrank E L ≤ finrank E K := Submodule.finrank_le L
      rw [mul_one, Nat.add_sub_cancel' hq, ← pow_add, ← pow_succ]
      congr 1; omega
    · have hd := finrank_Tb_not_mem L b _ hb.1
        (fun h => hX ((mem_map_iff L b _ hb.1 hs).1 h))
      have hle := Submodule.finrank_le (Tb L b (sr E b))
      rw [hd] at hle
      rw [if_neg (fun h => hX h.2), hd, mul_zero, add_zero, mul_one, ← pow_add]
      congr 1; omega
  · rw [if_neg hb, if_neg hb, if_neg (fun h => hb h.1)]; simp

theorem count_bij [CharP E 2] (L : Submodule E K) :
    (Finset.univ.filter (fun b : K => (b ≠ 0 ∧ b ∈ orth (sqS L)) ∧
        b⁻¹ * sr E b ∈ L)).card =
      (Finset.univ.filter (fun a : K => a ≠ 0 ∧ a ∈ L ∧
        ∀ w ∈ sqS L, Algebra.trace E K ((a⁻¹) ^ 2 * w) = 0)).card := by
  have aux : ∀ s : K, s ≠ 0 → (s ^ 2)⁻¹ * s = s⁻¹ := by
    intro s hs
    rw [pow_two, mul_inv, mul_assoc, inv_mul_cancel₀ hs, mul_one]
  have key : ∀ b : K, b ≠ 0 → b⁻¹ * sr E b = (sr E b)⁻¹ := by
    intro b hb
    calc b⁻¹ * sr E b = ((sr E b) ^ 2)⁻¹ * sr E b := by rw [sr_spec E b]
      _ = (sr E b)⁻¹ := aux _ (sr_ne hb)
  have key2 : ∀ a : K, sr E ((a⁻¹) ^ 2) = a⁻¹ := fun a => sq_inj (E := E) (sr_spec E _)
  refine Finset.card_bij' (fun b _ => b⁻¹ * sr E b) (fun a _ => (a⁻¹) ^ 2) ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨-, ⟨hb0, hbW⟩, hbL⟩ := Finset.mem_filter.1 hb
    show b⁻¹ * sr E b ∈ Finset.filter _ _
    rw [key b hb0] at hbL ⊢
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, inv_ne_zero (sr_ne hb0), hbL, fun w hw => ?_⟩
    rw [inv_inv, sr_spec E b, mul_comm]
    exact (mem_orth _ _).1 hbW w hw
  · intro a ha
    obtain ⟨-, ha0, haL, haW⟩ := Finset.mem_filter.1 ha
    have hb0 : (a⁻¹) ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero ha0)
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨hb0, (mem_orth _ _).2 fun w hw => ?_⟩, ?_⟩
    · rw [mul_comm]; exact haW w hw
    · rw [key _ hb0, key2, inv_inv]; exact haL
  · intro b hb
    obtain ⟨-, ⟨hb0, -⟩, -⟩ := Finset.mem_filter.1 hb
    show ((b⁻¹ * sr E b)⁻¹) ^ 2 = b
    rw [key b hb0, inv_inv, sr_spec]
  · intro a ha
    obtain ⟨-, ha0, -⟩ := Finset.mem_filter.1 ha
    show ((a⁻¹) ^ 2)⁻¹ * sr E ((a⁻¹) ^ 2) = a
    rw [key _ (pow_ne_zero 2 (inv_ne_zero ha0)), key2, inv_inv]

theorem identA [CharP E 2] (L : Submodule E K) :
    Fintype.card E ^ (finrank E L + 1) * ∑ x : K, (Fintype.card E ^ (finrank E K -
        finrank E (sqS (L ⊔ Submodule.span E {x}))) - 1) =
      Fintype.card E ^ (finrank E K) * ((Fintype.card E ^ (finrank E K -
        finrank E (sqS L)) - 1) + (Fintype.card E - 1) *
          (Finset.univ.filter (fun a : K => a ≠ 0 ∧ a ∈ L ∧
            ∀ w ∈ sqS L, Algebra.trace E K ((a⁻¹) ^ 2 * w) = 0)).card) := by
  rw [swap_sum, Finset.mul_sum, Finset.sum_congr rfl (fun b _ => per_b L b),
    ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter,
    ← Finset.card_filter, card_filter_ne, finrank_orth, count_bij]

-- FRAGMENT: paste inside namespace PEqualNP.Outside.L_lib_830_aux, after s1 helpers,
-- `open Classical`, card_filter_mem and identA.

theorem mul_mem_sqS (L : Submodule E K) {a b : K} (ha : a ∈ L) (hb : b ∈ L) :
    a * b ∈ sqS L := by
  unfold sqS
  exact Submodule.subset_span ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem sqS_le_iff (L T : Submodule E K) :
    sqS L ≤ T ↔ ∀ a ∈ L, ∀ b ∈ L, a * b ∈ T := by
  constructor
  · intro h a ha b hb
    exact h (mul_mem_sqS L ha hb)
  · intro h
    unfold sqS
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact h a a.2 b b.2

theorem sqS_mono {L M : Submodule E K} (h : L ≤ M) : sqS L ≤ sqS M := by
  rw [sqS_le_iff]
  intro a ha b hb
  exact mul_mem_sqS M (h ha) (h hb)

theorem sqS_top : finrank E (sqS (⊤ : Submodule E K)) = finrank E K := by
  have h : sqS (⊤ : Submodule E K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 := mul_mem_sqS (⊤ : Submodule E K) (Submodule.mem_top : (1 : K) ∈ ⊤)
      (Submodule.mem_top : x ∈ ⊤)
    rwa [one_mul] at h1
  rw [h, finrank_top]

theorem sqS_ext_le (L : Submodule E K) (x : K) :
    finrank E (sqS (L ⊔ Submodule.span E {x})) ≤ finrank E (sqS L) + finrank E L + 1 := by
  have hle : sqS (L ⊔ Submodule.span E {x}) ≤
      (sqS L ⊔ L.map (LinearMap.mulLeft E x)) ⊔ Submodule.span E {x * x} := by
    rw [sqS_le_iff]
    intro s hs t ht
    obtain ⟨l, hl, y, hy, rfl⟩ := Submodule.mem_sup.1 hs
    obtain ⟨l', hl', y', hy', rfl⟩ := Submodule.mem_sup.1 ht
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hy'
    have e : (l + α • x) * (l' + β • x) =
        l * l' + β • (x * l) + α • (x * l') + (α * β) • (x * x) := by
      simp only [Algebra.smul_def, map_mul]
      ring
    rw [e]
    have h2 : ∀ u ∈ L, x * u ∈
        (sqS L ⊔ L.map (LinearMap.mulLeft E x)) ⊔ Submodule.span E {x * x} :=
      fun u hu => Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.mem_map.2 ⟨u, hu, rfl⟩))
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_sup_left (mul_mem_sqS L hl hl')))
      (Submodule.smul_mem _ β (h2 l hl))) (Submodule.smul_mem _ α (h2 l' hl')))
      (Submodule.smul_mem _ (α * β)
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  have h1 : finrank E (Submodule.span E {x * x}) ≤ 1 := by
    by_cases h : x * x = 0
    · rw [h, Submodule.span_zero_singleton]
      simp
    · exact (finrank_span_singleton h).le
  have h2 : finrank E (L.map (LinearMap.mulLeft E x)) ≤ finrank E L :=
    Submodule.finrank_map_le _ _
  have h3 := Submodule.finrank_add_le_finrank_add_finrank (sqS L)
    (L.map (LinearMap.mulLeft E x))
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    (sqS L ⊔ L.map (LinearMap.mulLeft E x)) (Submodule.span E {x * x})
  have h5 := Submodule.finrank_mono hle
  omega

theorem count_le (L : Submodule E K) (P : K → Prop) [DecidablePred P]
    (hP : ∀ a, P a → a ≠ 0 ∧ a ∈ L) :
    (Finset.univ.filter P).card + 1 ≤ Fintype.card E ^ finrank E L := by
  rw [← card_filter_mem L]
  have h0 : (0 : K) ∈ Finset.univ.filter (fun b : K => b ∈ L) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, L.zero_mem⟩
  have hsub : Finset.univ.filter P ⊆ (Finset.univ.filter (fun b : K => b ∈ L)).erase 0 := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_erase, Finset.mem_filter]
    exact ⟨(hP a ha.2).1, Finset.mem_univ _, (hP a ha.2).2⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem h0] at h1
  have hpos : 0 < (Finset.univ.filter (fun b : K => b ∈ L)).card :=
    Finset.card_pos.2 ⟨0, h0⟩
  omega

theorem num1 (q A C : ℕ) (hq : 2 < q) (hA : 1 ≤ A) (hC : 1 ≤ C) (hCA : C ≤ A) :
    ¬ (A * q * (q - 1) ≤ (C - 1) + (q - 1) * (A - 1)) := by
  intro h
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 3 := ⟨q - 3, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
  rw [show k + 3 - 1 = k + 2 from by omega, show a + 1 - 1 = a from by omega] at h
  have h1 : (a + 1) * (k + 3) * (k + 2) =
      (k + 2) * a * k + 3 * ((k + 2) * a) + (k + 3) * (k + 2) := by ring
  have h2 : (k + 2) * a = k * a + 2 * a := by ring
  have h3 : 0 < (k + 3) * (k + 2) := by positivity
  rw [h1] at h
  omega

theorem num2 (q A T : ℕ) (hq : 2 < q) (hA : 1 ≤ A) (hT : q ≤ T) :
    ¬ (A * q * (T - 1) ≤ (A * T - 1) + (q - 1) * (A - 1)) := by
  intro h
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 3 := ⟨q - 3, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, A = a + 1 := ⟨A - 1, by omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, T = s + (k + 3) := ⟨T - (k + 3), by omega⟩
  rw [show k + 3 - 1 = k + 2 from by omega, show a + 1 - 1 = a from by omega,
    show s + (k + 3) - 1 = s + k + 2 from by omega] at h
  have h1 : (a + 1) * (k + 3) * (s + k + 2) + (a + 1) =
      (a + 1) * (s + (k + 3)) + (k + 2) * a +
        ((a + 1) * ((k + 2) * (s + k + 1)) + (k + 2)) := by ring
  have h4 : a + 1 ≤ (a + 1) * ((k + 2) * (s + k + 1)) := by
    calc a + 1 = (a + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (a + 1) * ((k + 2) * (s + k + 1)) :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (by positivity))
  omega

theorem core_ineq [CharP E 2] (L : Submodule E K) (t : ℕ)
    (ht : ∀ x : K, t ≤ finrank E K - finrank E (sqS (L ⊔ Submodule.span E {x}))) :
    Fintype.card E ^ (finrank E L + 1) * (Fintype.card E ^ t - 1) ≤
      (Fintype.card E ^ (finrank E K - finrank E (sqS L)) - 1) +
        (Fintype.card E - 1) * (Fintype.card E ^ finrank E L - 1) := by
  have hqpos : 0 < Fintype.card E := Fintype.card_pos
  have key : ∀ x : K, Fintype.card E ^ t - 1 ≤
      Fintype.card E ^ (finrank E K - finrank E (sqS (L ⊔ Submodule.span E {x}))) - 1 :=
    fun x => Nat.sub_le_sub_right (Nat.pow_le_pow_right hqpos (ht x)) 1
  have hsum : Fintype.card K * (Fintype.card E ^ t - 1) ≤
      ∑ x : K, (Fintype.card E ^
        (finrank E K - finrank E (sqS (L ⊔ Submodule.span E {x}))) - 1) := by
    calc Fintype.card K * (Fintype.card E ^ t - 1)
        = ∑ _x : K, (Fintype.card E ^ t - 1) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x _ => key x)
  have hK : Fintype.card K = Fintype.card E ^ finrank E K := Module.card_eq_pow_finrank
  rw [hK] at hsum
  have hcount : (Finset.univ.filter (fun a : K => a ≠ 0 ∧ a ∈ L ∧
      ∀ w ∈ sqS L, Algebra.trace E K ((a⁻¹)^2 * w) = 0)).card + 1 ≤
      Fintype.card E ^ finrank E L :=
    count_le L _ (fun a ha => ⟨ha.1, ha.2.1⟩)
  have hA := identA L
  have h5 := le_trans (Nat.mul_le_mul_left (Fintype.card E ^ (finrank E L + 1)) hsum)
    (le_of_eq hA)
  have h6 : Fintype.card E ^ (finrank E K) *
      ((Fintype.card E ^ (finrank E K - finrank E (sqS L)) - 1) +
        (Fintype.card E - 1) * (Finset.univ.filter (fun a : K => a ≠ 0 ∧ a ∈ L ∧
          ∀ w ∈ sqS L, Algebra.trace E K ((a⁻¹)^2 * w) = 0)).card) ≤
      Fintype.card E ^ (finrank E K) *
      ((Fintype.card E ^ (finrank E K - finrank E (sqS L)) - 1) +
        (Fintype.card E - 1) * (Fintype.card E ^ finrank E L - 1)) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)
  have h7 : Fintype.card E ^ (finrank E K) *
      (Fintype.card E ^ (finrank E L + 1) * (Fintype.card E ^ t - 1)) ≤
      Fintype.card E ^ (finrank E K) *
      ((Fintype.card E ^ (finrank E K - finrank E (sqS L)) - 1) +
        (Fintype.card E - 1) * (Fintype.card E ^ finrank E L - 1)) := by
    have e : Fintype.card E ^ (finrank E K) *
        (Fintype.card E ^ (finrank E L + 1) * (Fintype.card E ^ t - 1)) =
        Fintype.card E ^ (finrank E L + 1) *
        (Fintype.card E ^ (finrank E K) * (Fintype.card E ^ t - 1)) :=
      Nat.mul_left_comm _ _ _
    rw [e]
    exact le_trans h5 h6
  exact Nat.le_of_mul_le_mul_left h7 (pow_pos hqpos _)

theorem growth_step [CharP E 2] (hq : 2 < Fintype.card E) (L : Submodule E K)
    (hL : finrank E L < finrank E K) :
    ∃ x : K, x ∉ L ∧ finrank E (sqS (L ⊔ Submodule.span E {x})) =
      min (finrank E K) (finrank E (sqS L) + finrank E L + 1) := by
  have hqpos : 0 < Fintype.card E := Fintype.card_pos
  have hex : ∃ x : K, x ∉ L := by
    by_contra hne
    push_neg at hne
    have hT : L = ⊤ := Submodule.eq_top_iff'.2 hne
    rw [hT, finrank_top] at hL
    exact lt_irrefl _ hL
  have hup := sqS_ext_le L
  have hm : ∀ x : K, finrank E (sqS (L ⊔ Submodule.span E {x})) ≤ finrank E K :=
    fun x => Submodule.finrank_le _
  have hlow : ∀ x : K,
      finrank E (sqS L) ≤ finrank E (sqS (L ⊔ Submodule.span E {x})) :=
    fun x => Submodule.finrank_mono (sqS_mono le_sup_left)
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ x : K, x ∉ L →
      finrank E (sqS (L ⊔ Submodule.span E {x})) < finrank E K ∧
      finrank E (sqS (L ⊔ Submodule.span E {x})) <
        finrank E (sqS L) + finrank E L + 1 := by
    intro x hx
    exact lt_min_iff.1 (lt_of_le_of_ne (le_min (hm x) (hup x)) (hcon x hx))
  have hW : finrank E (sqS L) < finrank E K := by
    obtain ⟨x, hx⟩ := hex
    have h1 := (hlt x hx).1
    have h2 := hlow x
    omega
  have main : ∀ t : ℕ, t ≤ finrank E K - finrank E (sqS L) →
      (t = 1 ∨ t + finrank E L ≤ finrank E K - finrank E (sqS L)) →
      Fintype.card E ^ (finrank E L + 1) * (Fintype.card E ^ t - 1) ≤
      (Fintype.card E ^ (finrank E K - finrank E (sqS L)) - 1) +
        (Fintype.card E - 1) * (Fintype.card E ^ finrank E L - 1) := by
    intro t ht1 ht2
    refine core_ineq L t ?_
    intro x
    by_cases hx : x ∈ L
    · have e : L ⊔ Submodule.span E {x} = L :=
        sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 hx)
      rw [e]
      exact ht1
    · have h1 := hlt x hx
      have h2 := hlow x
      omega
  rcases Nat.lt_or_ge (finrank E L) (finrank E K - finrank E (sqS L)) with hc | hc
  · have h := main (finrank E K - finrank E (sqS L) - finrank E L) (Nat.sub_le _ _)
      (Or.inr (by omega))
    have e : Fintype.card E ^ (finrank E K - finrank E (sqS L)) =
        Fintype.card E ^ finrank E L *
          Fintype.card E ^ (finrank E K - finrank E (sqS L) - finrank E L) := by
      rw [← pow_add]
      congr 1
      omega
    rw [e, pow_succ] at h
    refine num2 (Fintype.card E) (Fintype.card E ^ finrank E L)
      (Fintype.card E ^ (finrank E K - finrank E (sqS L) - finrank E L)) hq
      (pow_pos hqpos _) ?_ h
    calc Fintype.card E = Fintype.card E ^ 1 := (pow_one _).symm
      _ ≤ Fintype.card E ^ (finrank E K - finrank E (sqS L) - finrank E L) :=
        Nat.pow_le_pow_right hqpos (by omega)
  · have h := main 1 (by omega) (Or.inl rfl)
    rw [pow_one, pow_succ] at h
    exact num1 (Fintype.card E) (Fintype.card E ^ finrank E L)
      (Fintype.card E ^ (finrank E K - finrank E (sqS L))) hq
      (pow_pos hqpos _) (pow_pos hqpos _) (Nat.pow_le_pow_right hqpos hc) h

noncomputable def nextV [CharP E 2] (hq : 2 < Fintype.card E) (V : Submodule E K) :
    Submodule E K :=
  if h : finrank E V < finrank E K then
    V ⊔ Submodule.span E {Classical.choose (growth_step hq V h)}
  else V

theorem nextV_le [CharP E 2] (hq : 2 < Fintype.card E) (V : Submodule E K) :
    V ≤ nextV hq V := by
  unfold nextV
  split_ifs with h
  · exact le_sup_left
  · exact le_rfl

theorem nextV_lt [CharP E 2] (hq : 2 < Fintype.card E) (V : Submodule E K)
    (h : finrank E V < finrank E K) :
    finrank E (nextV hq V) = finrank E V + 1 ∧
    finrank E (sqS (nextV hq V)) =
      min (finrank E K) (finrank E (sqS V) + finrank E V + 1) := by
  have hs := Classical.choose_spec (growth_step hq V h)
  have e : nextV hq V = V ⊔ Submodule.span E {Classical.choose (growth_step hq V h)} := by
    unfold nextV
    exact dif_pos h
  rw [e]
  exact ⟨Submodule.finrank_sup_span_singleton hs.1, hs.2⟩

theorem nextV_ge [CharP E 2] (hq : 2 < Fintype.card E) (V : Submodule E K)
    (h : ¬ finrank E V < finrank E K) : nextV hq V = V := by
  unfold nextV
  exact dif_neg h

noncomputable def chainV [CharP E 2] (hq : 2 < Fintype.card E) (L : Submodule E K) :
    ℕ → Submodule E K
  | 0 => L
  | n + 1 => nextV hq (chainV hq L n)

theorem chainV_zero [CharP E 2] (hq : 2 < Fintype.card E) (L : Submodule E K) :
    chainV hq L 0 = L := rfl

theorem chainV_succ [CharP E 2] (hq : 2 < Fintype.card E) (L : Submodule E K) (n : ℕ) :
    chainV hq L (n + 1) = nextV hq (chainV hq L n) := rfl

theorem growth_chain [CharP E 2] (hq : 2 < Fintype.card E) (L : Submodule E K) :
    ∃ V : ℕ → Submodule E K, V 0 = L ∧ Monotone V ∧
      ∀ j : ℕ, finrank E (V j) = min (finrank E K) (finrank E L + j) ∧
        finrank E (sqS (V j)) =
          min (finrank E K) (finrank E (sqS L) + j * finrank E L + j * (j + 1) / 2) := by
  refine ⟨chainV hq L, rfl, monotone_nat_of_le_succ (fun n => ?_), ?_⟩
  · rw [chainV_succ]
    exact nextV_le hq _
  intro j
  induction j with
  | zero =>
    rw [chainV_zero]
    have a := Submodule.finrank_le L
    have b := Submodule.finrank_le (sqS L)
    constructor
    · first
        | omega
        | (simp only [Nat.add_zero]; exact (min_eq_right a).symm)
    · first
        | omega
        | (simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_div]; exact (min_eq_right b).symm)
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [chainV_succ]
    have hm1 := Submodule.finrank_le (chainV hq L j)
    have e1 : (j + 1) * finrank E L = j * finrank E L + finrank E L := by ring
    have e2 : (j + 1) * (j + 1 + 1) / 2 = j * (j + 1) / 2 + (j + 1) := by
      have e3 : (j + 1) * (j + 1 + 1) = j * (j + 1) + 2 * (j + 1) := by ring
      rw [e3]
      omega
    by_cases h : finrank E (chainV hq L j) < finrank E K
    · obtain ⟨n1, n2⟩ := nextV_lt hq _ h
      constructor
      · omega
      · omega
    · have hn := nextV_ge hq _ h
      rw [hn]
      have hd : finrank E (chainV hq L j) = finrank E K := by omega
      have htop : chainV hq L j = ⊤ := Submodule.eq_top_of_finrank_eq hd
      have hw : finrank E (sqS (chainV hq L j)) = finrank E K := by
        rw [htop]
        exact sqS_top
      constructor
      · omega
      · omega
end PEqualNP.Outside.L_lib_830_aux

theorem PEqualNP.Outside.L_lib_830 : ∀ (E K : Type) [Field E] [CharP E 2] [Fintype E] [Field K] [Algebra E K]
    [FiniteDimensional E K] [Fintype K],
  let q := Fintype.card E
  let m := Module.finrank E K
  let dim := fun (L : Submodule E K) => Module.finrank E L
  let sq := fun (L : Submodule E K) =>
    Submodule.span E (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K)))
  let extend := fun (L : Submodule E K) (x : K) => L ⊔ Submodule.span E {x}
  2 < q → ∀ L : Submodule E K,
    let W := sq L
    let c := m - dim W
    let e := dim L + 1
    let exc := fun a : K => a ≠ 0 ∧ a ∈ L ∧
      ∀ w ∈ W, Algebra.trace E K ((a⁻¹)^2 * w) = 0
    let count := (@Finset.filter K exc (fun a => Classical.propDecidable (exc a)) Finset.univ).card
    q^e * (∑ x : K, (q^(m - dim (sq (extend L x))) - 1 : ℕ)) =
      q^m * ((q^c - 1) + (q-1)*count) ∧
    ∃ V : ℕ → Submodule E K, V 0 = L ∧ Monotone V ∧
      ∀ j : ℕ, dim (V j) = min m (dim L+j) ∧
        dim (sq (V j)) = min m (dim W+j*dim L+j*(j+1)/2) := by
  intro E K _ _ _ _ _ _ _ q m dim sq extend hq L W c e exc count
  refine ⟨?_, ?_⟩
  · have h := PEqualNP.Outside.L_lib_830_aux.identA (E := E) L
    convert h using 4
    all_goals first | rfl | (show Finset.card _ = Finset.card _; congr)
  · exact PEqualNP.Outside.L_lib_830_aux.growth_chain hq L
