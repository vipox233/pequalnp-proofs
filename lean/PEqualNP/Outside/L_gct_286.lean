import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_286_aux

open scoped BigOperators

abbrev Vec := Fin 5 → ℂ
abbrev Mat := Fin 4 → Fin 5 → ℂ

def dot (u v : Vec) : ℂ := ∑ j : Fin 5, u j * v j

def had (u v : Vec) : Vec := fun j => u j * v j

def sumLin : Vec →ₗ[ℂ] ℂ where
  toFun v := ∑ j : Fin 5, v j
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum]

def H0 : Submodule ℂ Vec := LinearMap.ker sumLin

noncomputable def e0 : ℂ := ∑ _f : Fin 4 ↪ Fin 5, (1 : ℂ)

noncomputable def e1 (X : Mat) : ℂ :=
  ∑ f : Fin 4 ↪ Fin 5, (X 0 (f 0) + X 1 (f 1) + X 2 (f 2) + X 3 (f 3))

noncomputable def e2 (X : Mat) : ℂ :=
  ∑ f : Fin 4 ↪ Fin 5,
    (X 0 (f 0) * X 1 (f 1) + X 0 (f 0) * X 2 (f 2) + X 0 (f 0) * X 3 (f 3) +
     X 1 (f 1) * X 2 (f 2) + X 1 (f 1) * X 3 (f 3) + X 2 (f 2) * X 3 (f 3))

noncomputable def e3 (X : Mat) : ℂ :=
  ∑ f : Fin 4 ↪ Fin 5,
    (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) + X 0 (f 0) * X 1 (f 1) * X 3 (f 3) +
     X 0 (f 0) * X 2 (f 2) * X 3 (f 3) + X 1 (f 1) * X 2 (f 2) * X 3 (f 3))

noncomputable def e4 (X : Mat) : ℂ :=
  ∑ f : Fin 4 ↪ Fin 5, X 0 (f 0) * X 1 (f 1) * X 2 (f 2) * X 3 (f 3)

lemma poly_expand (X : Mat) (t : ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + (t • X) i (f i))) =
      e0 + t * e1 X + t ^ 2 * e2 X + t ^ 3 * e3 X + t ^ 4 * e4 X := by
  have hterm : ∀ f : Fin 4 ↪ Fin 5,
      (∏ i : Fin 4, (1 + (t • X) i (f i))) =
        (1 : ℂ) +
        t * (X 0 (f 0) + X 1 (f 1) + X 2 (f 2) + X 3 (f 3)) +
        t ^ 2 * (X 0 (f 0) * X 1 (f 1) + X 0 (f 0) * X 2 (f 2) + X 0 (f 0) * X 3 (f 3) +
          X 1 (f 1) * X 2 (f 2) + X 1 (f 1) * X 3 (f 3) + X 2 (f 2) * X 3 (f 3)) +
        t ^ 3 * (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) + X 0 (f 0) * X 1 (f 1) * X 3 (f 3) +
          X 0 (f 0) * X 2 (f 2) * X 3 (f 3) + X 1 (f 1) * X 2 (f 2) * X 3 (f 3)) +
        t ^ 4 * (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) * X 3 (f 3)) := by
    intro f
    rw [Fin.prod_univ_four]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

lemma coeffs_zero_of_const (X : Mat)
    (h : ∀ t : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + (t • X) i (f i))) = 120) :
    e2 X = 0 ∧ e3 X = 0 ∧ e4 X = 0 := by
  have h0 := h 0; rw [poly_expand] at h0
  have h1 := h 1; rw [poly_expand] at h1
  have hm1 := h (-1); rw [poly_expand] at hm1
  have h2 := h 2; rw [poly_expand] at h2
  have hm2 := h (-2); rw [poly_expand] at hm2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (16 * h1 + 16 * hm1 - h2 - hm2 - 30 * h0) / 24
  · linear_combination (h2 - hm2 - 2 * h1 + 2 * hm1) / 12
  · linear_combination (h2 + hm2 - 4 * h1 - 4 * hm1 + 6 * h0) / 24

def validTuple (t : Fin 5 × Fin 5 × Fin 5 × Fin 5) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧
  t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2

instance : DecidablePred validTuple := fun t => by
  unfold validTuple; infer_instance

lemma sum_emb_eq_nested (g : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, g (f 0) (f 1) (f 2) (f 3)) =
      ∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
          ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, g j0 j1 j2 j3 := by
  have h1 : (∑ f : Fin 4 ↪ Fin 5, g (f 0) (f 1) (f 2) (f 3)) =
      ∑ t ∈ Finset.univ.filter validTuple, g t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    refine Finset.sum_nbij (fun f => (f 0, f 1, f 2, f 3)) ?_ ?_ ?_ ?_
    · intro f _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, validTuple]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := f.injective h <;> omega
    · intro f1 _ f2 _ h
      have h0 : f1 0 = f2 0 := congrArg Prod.fst h
      have h1' : f1 1 = f2 1 := congrArg (fun p => p.2.1) h
      have h2' : f1 2 = f2 2 := congrArg (fun p => p.2.2.1) h
      have h3' : f1 3 = f2 3 := congrArg (fun p => p.2.2.2) h
      exact DFunLike.ext f1 f2 fun i => by fin_cases i <;> assumption
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, validTuple] at ht
      rcases t with ⟨j0, j1, j2, j3⟩
      rcases ht with ⟨h01, h02, h03, h12, h13, h23⟩
      refine ⟨⟨![j0, j1, j2, j3], ?_⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [Ne.symm]
    · intro f _
      rfl
  rw [h1]
  rw [Finset.sum_filter]
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j0 _ => ?_
  have hf1 : ∀ x : Fin 5, (∑ j2 : Fin 5, ∑ j3 : Fin 5,
      if validTuple (j0, x, j2, j3) then g j0 x j2 j3 else 0) =
      if x ∈ Finset.univ.erase j0 then
        ∑ j2 ∈ (Finset.univ.erase j0).erase x,
          ∑ j3 ∈ ((Finset.univ.erase j0).erase x).erase j2, g j0 x j2 j3
      else 0 := by
    intro j1
    by_cases h01 : j0 = j1
    · subst h01
      simp [validTuple]
    · have hm1 : j1 ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨Ne.symm h01, Finset.mem_univ _⟩
      rw [if_pos hm1]
      trans ∑ j2 : Fin 5, if j2 ∈ (Finset.univ.erase j0).erase j1 then
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, g j0 j1 j2 j3 else 0
      · refine Finset.sum_congr rfl fun j2 _ => ?_
        by_cases h2 : j2 ∈ (Finset.univ.erase j0).erase j1
        · rw [if_pos h2]
          have h02 : j0 ≠ j2 := Ne.symm (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h2))
          have h12 : j1 ≠ j2 := Ne.symm (Finset.ne_of_mem_erase h2)
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext j3
          simp [validTuple, h01, h02, h12]; exact ⟨fun ⟨a, b, c⟩ => ⟨Ne.symm c, Ne.symm b, Ne.symm a⟩, fun ⟨c, b, a⟩ => ⟨Ne.symm a, Ne.symm b, Ne.symm c⟩⟩
        · rw [if_neg h2]
          have h2' : j0 = j2 ∨ j1 = j2 := by
            simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_and, not_not] at h2
            by_cases h12 : j2 = j1
            · exact Or.inr h12.symm
            · exact Or.inl (h2 h12).symm
          apply Finset.sum_eq_zero
          intro j3 _
          rcases h2' with rfl | rfl <;> simp [validTuple]
      · rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext j2; simp
  simp_rw [hf1]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j1; simp

lemma sum_emb_01 (a b : Vec) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) :
    (∑ f : Fin 4 ↪ Fin 5, a (f 0) * b (f 1)) = -6 * dot a b := by
  rw [sum_emb_eq_nested (fun j0 j1 _ _ => a j0 * b j1)]
  have hinner : ∀ (j0 : Fin 5) (j1 : Fin 5), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1) = 6 * (a j0 * b j1) := by
    intro j0 j1 hj1
    have hcard1 : ((Finset.univ : Finset (Fin 5)).erase j0).card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hcard2 : (((Finset.univ : Finset (Fin 5)).erase j0).erase j1).card = 3 := by
      rw [Finset.card_erase_of_mem hj1, hcard1]
    have hstep : ∀ j2 ∈ ((Finset.univ : Finset (Fin 5)).erase j0).erase j1,
        (∑ j3 ∈ (((Finset.univ : Finset (Fin 5)).erase j0).erase j1).erase j2, a j0 * b j1) =
          2 * (a j0 * b j1) := by
      intro j2 hj2
      rw [Finset.sum_const, Finset.card_erase_of_mem hj2, hcard2]
      norm_num
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, hcard2]
    push_cast; ring
  have h1 : (∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1) =
      ∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0, 6 * (a j0 * b j1) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => hinner j0 j1 hj1
  rw [h1]
  have h2 : ∀ j0 : Fin 5, (∑ j1 ∈ Finset.univ.erase j0, 6 * (a j0 * b j1)) = -6 * (a j0 * b j0) := by
    intro j0
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb]
    ring
  simp_rw [h2, ← Finset.mul_sum]
  rfl

lemma sum_emb_pair_eq (i1 i2 : Fin 4) (hi : i1 ≠ i2) (a b : Vec)
    (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) :
    (∑ f : Fin 4 ↪ Fin 5, a (f i1) * b (f i2)) = -6 * dot a b := by
  have hswap : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 ∧ σ 1 = i2 := by
    have he : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 := ⟨Equiv.swap 0 i1, by simp⟩
    rcases he with ⟨σ1, hσ1⟩
    have hne : σ1.symm i2 ≠ 0 := by
      intro h
      have := congrArg σ1 h
      rw [Equiv.apply_symm_apply, hσ1] at this
      exact hi this.symm
    refine ⟨σ1 * Equiv.swap 1 (σ1.symm i2), ?_, ?_⟩
    · simp only [Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) hne.symm, hσ1]
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]
  rcases hswap with ⟨σ, hσ0, hσ1⟩
  have hbij : (∑ f : Fin 4 ↪ Fin 5, a (f i1) * b (f i2)) =
      ∑ f : Fin 4 ↪ Fin 5, a (f 0) * b (f 1) := by
    refine Finset.sum_nbij (fun f => σ.toEmbedding.trans f) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro f1 _ f2 _ h
      exact DFunLike.ext f1 f2 fun x => by
        have := DFunLike.congr_fun h (σ.symm x)
        simpa using this
    · intro f _
      refine ⟨σ.symm.toEmbedding.trans f, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      exact DFunLike.ext _ _ fun x => by simp
    · intro f _
      simp [hσ0, hσ1]
  rw [hbij]
  exact sum_emb_01 a b ha hb

lemma e2_eq (X : Mat) (hr : ∀ i, ∑ j, X i j = 0) (hc : ∀ j, ∑ i, X i j = 0) :
    e2 X = 3 * (dot (X 0) (X 0) + dot (X 1) (X 1) + dot (X 2) (X 2) + dot (X 3) (X 3)) := by
  unfold e2
  simp_rw [Finset.sum_add_distrib]
  rw [sum_emb_pair_eq 0 1 (by decide) (X 0) (X 1) (hr 0) (hr 1),
      sum_emb_pair_eq 0 2 (by decide) (X 0) (X 2) (hr 0) (hr 2),
      sum_emb_pair_eq 0 3 (by decide) (X 0) (X 3) (hr 0) (hr 3),
      sum_emb_pair_eq 1 2 (by decide) (X 1) (X 2) (hr 1) (hr 2),
      sum_emb_pair_eq 1 3 (by decide) (X 1) (X 3) (hr 1) (hr 3),
      sum_emb_pair_eq 2 3 (by decide) (X 2) (X 3) (hr 2) (hr 3)]
  have hsq : ∑ j : Fin 5, (X 0 j + X 1 j + X 2 j + X 3 j) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj := hc j
    rw [Fin.sum_univ_four] at hj
    rw [hj]; ring
  unfold dot
  have hcomb : ∑ j : Fin 5,
      ((X 0 j + X 1 j + X 2 j + X 3 j) ^ 2 -
       (X 0 j * X 0 j + X 1 j * X 1 j + X 2 j * X 2 j + X 3 j * X 3 j) -
       2 * (X 0 j * X 1 j + X 0 j * X 2 j + X 0 j * X 3 j +
            X 1 j * X 2 j + X 1 j * X 3 j + X 2 j * X 3 j)) = 0 := by
    apply Finset.sum_eq_zero; intro j _; ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hcomb
  linear_combination 3 * hcomb - 3 * hsq

lemma sum_emb_012 (a b c : Vec) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) :
    (∑ f : Fin 4 ↪ Fin 5, a (f 0) * b (f 1) * c (f 2)) = 4 * ∑ j, a j * b j * c j := by
  rw [sum_emb_eq_nested (fun j0 j1 j2 _ => a j0 * b j1 * c j2)]
  have hstep3 : ∀ (j0 : Fin 5) (j1 : Fin 5) (j2 : Fin 5),
      j1 ∈ Finset.univ.erase j0 → j2 ∈ (Finset.univ.erase j0).erase j1 →
      (∑ _j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2) =
        2 * (a j0 * b j1 * c j2) := by
    intro j0 j1 j2 hj1 hj2
    have hcard1 : ((Finset.univ : Finset (Fin 5)).erase j0).card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hcard2 : (((Finset.univ : Finset (Fin 5)).erase j0).erase j1).card = 3 := by
      rw [Finset.card_erase_of_mem hj1, hcard1]
    rw [Finset.sum_const, Finset.card_erase_of_mem hj2, hcard2]
    norm_num
  have h1 : (∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ _j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2) =
      ∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1, 2 * (a j0 * b j1 * c j2) :=
    Finset.sum_congr rfl fun j0 _ =>
      Finset.sum_congr rfl fun j1 hj1 =>
        Finset.sum_congr rfl fun j2 hj2 => hstep3 j0 j1 j2 hj1 hj2
  rw [h1]
  have h2 : ∀ (j0 : Fin 5) (j1 : Fin 5), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1, 2 * (a j0 * b j1 * c j2)) =
        2 * (a j0 * b j1 * (- c j0 - c j1)) := by
    intro j0 j1 hj1
    have : ∀ j2, 2 * (a j0 * b j1 * c j2) = (2 * a j0 * b j1) * c j2 := fun _ => by ring
    simp_rw [this, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hc]
    ring
  have h3 : (∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1, 2 * (a j0 * b j1 * c j2)) =
      ∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0, 2 * (a j0 * b j1 * (- c j0 - c j1)) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => h2 j0 j1 hj1
  rw [h3]
  have h4 : ∀ j0 : Fin 5,
      (∑ j1 ∈ Finset.univ.erase j0, 2 * (a j0 * b j1 * (- c j0 - c j1))) =
        4 * (a j0 * b j0 * c j0) - 2 * a j0 * (∑ j1, b j1 * c j1) := by
    intro j0
    have hsplit : ∀ j1, 2 * (a j0 * b j1 * (- c j0 - c j1)) =
        (-2 * a j0 * c j0) * b j1 - (2 * a j0) * (b j1 * c j1) := fun _ => by ring
    simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j0), Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb]
    ring
  simp_rw [h4, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [ha]; ring

lemma sum_emb_triple_eq (i1 i2 i3 : Fin 4) (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3)
    (a b c : Vec) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) :
    (∑ f : Fin 4 ↪ Fin 5, a (f i1) * b (f i2) * c (f i3)) = 4 * ∑ j, a j * b j * c j := by
  have hperm : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 ∧ σ 1 = i2 ∧ σ 2 = i3 := by
    have hi4 : ∃ i4 : Fin 4, i4 ≠ i1 ∧ i4 ≠ i2 ∧ i4 ≠ i3 := by
      fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;> simp_all <;> decide
    rcases hi4 with ⟨i4, h41, h42, h43⟩
    have hinj : Function.Injective ![i1, i2, i3, i4] := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [Ne.symm]
    refine ⟨Equiv.ofBijective ![i1, i2, i3, i4] (Finite.injective_iff_bijective.mp hinj), rfl, rfl, rfl⟩
  rcases hperm with ⟨σ, hσ0, hσ1, hσ2⟩
  have hbij : (∑ f : Fin 4 ↪ Fin 5, a (f i1) * b (f i2) * c (f i3)) =
      ∑ f : Fin 4 ↪ Fin 5, a (f 0) * b (f 1) * c (f 2) := by
    refine Finset.sum_nbij (fun f => σ.toEmbedding.trans f) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro f1 _ f2 _ h
      exact DFunLike.ext f1 f2 fun x => by
        have := DFunLike.congr_fun h (σ.symm x)
        simpa using this
    · intro f _
      refine ⟨σ.symm.toEmbedding.trans f, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      exact DFunLike.ext _ _ fun x => by simp
    · intro f _
      simp [hσ0, hσ1, hσ2]
  rw [hbij]
  exact sum_emb_012 a b c ha hb hc

lemma e3_eq (X : Mat) (hr : ∀ i, ∑ j, X i j = 0) :
    e3 X = 4 * ∑ j, (X 0 j * X 1 j * X 2 j + X 0 j * X 1 j * X 3 j +
      X 0 j * X 2 j * X 3 j + X 1 j * X 2 j * X 3 j) := by
  unfold e3
  simp_rw [Finset.sum_add_distrib]
  rw [sum_emb_triple_eq 0 1 2 (by decide) (by decide) (by decide) (X 0) (X 1) (X 2) (hr 0) (hr 1) (hr 2),
      sum_emb_triple_eq 0 1 3 (by decide) (by decide) (by decide) (X 0) (X 1) (X 3) (hr 0) (hr 1) (hr 3),
      sum_emb_triple_eq 0 2 3 (by decide) (by decide) (by decide) (X 0) (X 2) (X 3) (hr 0) (hr 2) (hr 3),
      sum_emb_triple_eq 1 2 3 (by decide) (by decide) (by decide) (X 1) (X 2) (X 3) (hr 1) (hr 2) (hr 3)]
  ring

lemma e4_eq (a b c d : Vec)
    (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) (hd : ∑ j, d j = 0) :
    (∑ f : Fin 4 ↪ Fin 5, a (f 0) * b (f 1) * c (f 2) * d (f 3)) =
      dot a b * dot c d + dot a c * dot b d + dot a d * dot b c -
        6 * ∑ j, a j * b j * c j * d j := by
  rw [sum_emb_eq_nested (fun j0 j1 j2 j3 => a j0 * b j1 * c j2 * d j3)]
  have h3 : ∀ (j0 j1 j2 : Fin 5), j1 ∈ Finset.univ.erase j0 →
      j2 ∈ (Finset.univ.erase j0).erase j1 →
      (∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2 * d j3) =
        a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) := by
    intro j0 j1 j2 hj1 hj2
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hj2, Finset.sum_erase_eq_sub hj1,
        Finset.sum_erase_eq_sub (Finset.mem_univ j0), hd]
    ring
  have hs3 : (∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2 * d j3) =
      ∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) :=
    Finset.sum_congr rfl fun j0 _ =>
      Finset.sum_congr rfl fun j1 hj1 =>
        Finset.sum_congr rfl fun j2 hj2 => h3 j0 j1 j2 hj1 hj2
  rw [hs3]
  have h2 : ∀ (j0 j1 : Fin 5), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2)) =
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) := by
    intro j0 j1 hj1
    have hsp : ∀ j2, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) =
        (a j0 * b j1 * (- d j0 - d j1)) * c j2 - (a j0 * b j1) * (c j2 * d j2) := fun _ => by ring
    simp_rw [hsp, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hc,
        Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0)]
    unfold dot; ring
  have hs2 : (∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2)) =
      ∑ j0 : Fin 5, ∑ j1 ∈ Finset.univ.erase j0,
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => h2 j0 j1 hj1
  rw [hs2]
  have h1 : ∀ j0 : Fin 5,
      (∑ j1 ∈ Finset.univ.erase j0,
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1)) =
        a j0 * (dot b c * d j0 + dot b d * c j0 + b j0 * dot c d +
          2 * (∑ j1, b j1 * c j1 * d j1) - 6 * b j0 * c j0 * d j0) := by
    intro j0
    have hsp : ∀ j1, a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) =
        (a j0 * (2 * c j0 * d j0 - dot c d)) * b j1 +
        (a j0 * d j0) * (b j1 * c j1) +
        (a j0 * c j0) * (b j1 * d j1) +
        (2 * a j0) * (b j1 * c j1 * d j1) := fun _ => by ring
    simp_rw [hsp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb,
        Finset.sum_erase_eq_sub (Finset.mem_univ j0),
        Finset.sum_erase_eq_sub (Finset.mem_univ j0),
        Finset.sum_erase_eq_sub (Finset.mem_univ j0)]
    unfold dot; ring
  simp_rw [h1]
  have h0sp : ∀ j0, a j0 * (dot b c * d j0 + dot b d * c j0 + b j0 * dot c d +
      2 * (∑ j1, b j1 * c j1 * d j1) - 6 * b j0 * c j0 * d j0) =
      dot b c * (a j0 * d j0) + dot b d * (a j0 * c j0) + dot c d * (a j0 * b j0) +
      (2 * ∑ j1, b j1 * c j1 * d j1) * a j0 - 6 * (a j0 * b j0 * c j0 * d j0) := fun _ => by ring
  simp_rw [h0sp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [ha]
  unfold dot; ring

lemma finrank_H0 : Module.finrank ℂ H0 = 4 := by
  have hsurj : Function.Surjective sumLin := by
    intro c
    refine ⟨fun _ => c / 5, ?_⟩
    simp [sumLin]
    ring
  have hr : LinearMap.range sumLin = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h := LinearMap.finrank_range_add_finrank_ker sumLin
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_pi] at h
  change 1 + Module.finrank ℂ H0 = 5 at h
  omega

def dotLin (v : Vec) : Vec →ₗ[ℂ] ℂ where
  toFun w := dot v w
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

def dotH0 : H0 →ₗ[ℂ] Module.Dual ℂ H0 where
  toFun v := (dotLin v.1).comp H0.subtype
  map_add' x y := by
    ext w
    simp [dotLin, dot, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    ext w
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, dotLin, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, dot, SetLike.val_smul,
      Pi.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

lemma dotH0_injective : Function.Injective dotH0 := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  apply Subtype.ext
  have hsingle : ∀ (i : Fin 5) (f : Fin 5 → ℂ), (∑ k : Fin 5, f k * (Pi.single i (1 : ℂ) : Vec) k) = f i := by
    intro i f
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki; simp [Pi.single_eq_of_ne hki]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hpair : ∀ i j : Fin 5, v.1 i = v.1 j := by
    intro i j
    let w : Vec := Pi.single i 1 - Pi.single j 1
    have hw : w ∈ H0 := by
      change ∑ k : Fin 5, ((Pi.single i (1 : ℂ) : Vec) k - (Pi.single j (1 : ℂ) : Vec) k) = 0
      rw [Finset.sum_sub_distrib]
      have hi1 := hsingle i (fun _ => 1)
      have hj1 := hsingle j (fun _ => 1)
      simp only [one_mul] at hi1 hj1
      rw [hi1, hj1, sub_self]
    have h0 := LinearMap.congr_fun hv ⟨w, hw⟩
    change ∑ k : Fin 5, v.1 k * ((Pi.single i (1 : ℂ) : Vec) k - (Pi.single j (1 : ℂ) : Vec) k) = 0 at h0
    simp_rw [mul_sub] at h0
    rw [Finset.sum_sub_distrib, hsingle i v.1, hsingle j v.1] at h0
    exact sub_eq_zero.mp h0
  have hsum : ∑ j : Fin 5, v.1 j = 0 := v.2
  have hconst : ∑ j : Fin 5, v.1 j = 5 * v.1 0 := by
    have h1 : ∀ j : Fin 5, v.1 j = v.1 0 := fun j => hpair j 0
    calc ∑ j : Fin 5, v.1 j = ∑ _j : Fin 5, v.1 0 := Finset.sum_congr rfl fun j _ => h1 j
      _ = 5 * v.1 0 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  rw [hconst] at hsum
  have hv0 : v.1 0 = 0 := by
    have h5 : (5 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hsum).resolve_left h5
  ext j
  rw [hpair j 0, hv0]
  rfl

lemma dotH0_surjective : Function.Surjective dotH0 := by
  have hrank : Module.finrank ℂ H0 = Module.finrank ℂ (Module.Dual ℂ H0) := by
    rw [Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp dotH0_injective

def perpH0 (W : Submodule ℂ Vec) : Submodule ℂ Vec where
  carrier := {v | v ∈ H0 ∧ ∀ w ∈ W, dot v w = 0}; add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    refine ⟨H0.add_mem hx0 hy0, fun w hw => ?_⟩
    have h1 := hx w hw
    have h2 := hy w hw
    unfold dot at h1 h2 ⊢
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [h1, h2, add_zero]
  zero_mem' := ⟨H0.zero_mem, fun w _ => by simp [dot]⟩
  smul_mem' := by
    rintro c x ⟨hx0, hx⟩
    refine ⟨H0.smul_mem c hx0, fun w hw => ?_⟩
    have h1 := hx w hw
    unfold dot at h1 ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    have : (∑ j : Fin 5, c * x j * w j) = c * ∑ j : Fin 5, x j * w j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [this, h1, mul_zero]

lemma finrank_perpH0_add (W : Submodule ℂ Vec) (hW : W ≤ H0) :
    Module.finrank ℂ (perpH0 W) + Module.finrank ℂ W = 4 := by
  let inc : W →ₗ[ℂ] H0 := Submodule.inclusion hW
  let res : Module.Dual ℂ H0 →ₗ[ℂ] Module.Dual ℂ W := inc.dualMap
  let φ : H0 →ₗ[ℂ] Module.Dual ℂ W := res.comp dotH0
  have hres_surj : Function.Surjective res := by
    intro f
    obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (W.comap H0.subtype)
    have hproj : ∃ p : H0 →ₗ[ℂ] W, ∀ w : W, p (inc w) = w := by
      let W' : Submodule ℂ H0 := W.comap H0.subtype
      let e : W ≃ₗ[ℂ] W' :=
        { toFun := fun w => ⟨inc w, w.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          invFun := fun w' => ⟨w'.1.1, w'.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      let p' : H0 →ₗ[ℂ] W' := Submodule.projectionOnto W' Q hQ
      refine ⟨e.symm.toLinearMap.comp p', fun w => ?_⟩
      change e.symm (p' (e w).1) = w
      dsimp only [p']
      rw [Submodule.projectionOnto_apply_left hQ (e w)]
      exact e.symm_apply_apply w
    rcases hproj with ⟨p, hp⟩
    refine ⟨f.comp p, ?_⟩
    ext w
    exact congrArg f (hp w)
  have hφ_surj : Function.Surjective φ := hres_surj.comp dotH0_surjective
  have hr : Module.finrank ℂ (LinearMap.range φ) = Module.finrank ℂ W := by
    rw [LinearMap.range_eq_top.mpr hφ_surj, finrank_top, Subspace.dual_finrank_eq]
  have hker : LinearMap.ker φ = (perpH0 W).comap H0.subtype := by
    ext ⟨v, hv⟩
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype, perpH0,
      Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq, hv, true_and]
    constructor
    · intro h w hw
      have := LinearMap.congr_fun h ⟨w, hw⟩
      exact this
    · intro h
      ext ⟨w, hw⟩
      exact h w hw
  have hkeq : Module.finrank ℂ (LinearMap.ker φ) = Module.finrank ℂ (perpH0 W) := by
    rw [hker]
    have hle : perpH0 W ≤ H0 := fun v hv => hv.1
    let e : (perpH0 W).comap H0.subtype ≃ₗ[ℂ] perpH0 W :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y => ⟨⟨y.1, hle y.2⟩, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  have hfn := LinearMap.finrank_range_add_finrank_ker φ
  rw [hr, hkeq, finrank_H0] at hfn
  omega

lemma iso_finrank_le_two (W : Submodule ℂ Vec) (hW : W ≤ H0)
    (hiso : ∀ u ∈ W, ∀ v ∈ W, dot u v = 0) :
    Module.finrank ℂ W ≤ 2 := by
  have hle : W ≤ perpH0 W := fun u hu => ⟨hW hu, fun v hv => hiso u hu v hv⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_perpH0_add W hW
  omega

lemma iso_eq_perpH0 (W : Submodule ℂ Vec) (hW : W ≤ H0)
    (hiso : ∀ u ∈ W, ∀ v ∈ W, dot u v = 0) (h2 : 2 ≤ Module.finrank ℂ W) :
    W = perpH0 W ∧ Module.finrank ℂ W = 2 := by
  have hle : W ≤ perpH0 W := fun u hu => ⟨hW hu, fun v hv => hiso u hu v hv⟩
  have hsum := finrank_perpH0_add W hW
  have hle2 := iso_finrank_le_two W hW hiso
  have heq2 : Module.finrank ℂ W = 2 := by omega
  have hpeq : Module.finrank ℂ (perpH0 W) = 2 := by omega
  exact ⟨Submodule.eq_of_le_of_finrank_eq hle (by omega), heq2⟩

lemma card_supp_ge_three (v : Vec) (hv0 : v ∈ H0) (hiso : dot v v = 0) (hne : v ≠ 0) :
    3 ≤ (Finset.univ.filter (fun j : Fin 5 => v j ≠ 0)).card := by
  set S := Finset.univ.filter (fun j : Fin 5 => v j ≠ 0)
  have hsum : ∑ j ∈ S, v j = 0 := by
    have h1 : ∑ j ∈ S, v j = ∑ j : Fin 5, v j := by
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
      exact hj
    rw [h1]; exact hv0
  have hsq : ∑ j ∈ S, v j * v j = 0 := by
    have h1 : ∑ j ∈ S, v j * v j = ∑ j : Fin 5, v j * v j := by
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
      simp [hj]
    rw [h1]; exact hiso
  by_contra hlt
  push_neg at hlt
  interval_cases hc : S.card
  · have hSe : S = ∅ := Finset.card_eq_zero.mp hc
    apply hne
    ext j
    have : j ∉ S := by rw [hSe]; simp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at this
    exact this
  · obtain ⟨j0, hj0⟩ := Finset.card_eq_one.mp hc
    rw [hj0, Finset.sum_singleton] at hsum
    have hmem : j0 ∈ S := by rw [hj0]; simp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem hsum
  · obtain ⟨j1, j2, hne12, hS⟩ := Finset.card_eq_two.mp hc
    rw [hS, Finset.sum_pair hne12] at hsum hsq
    have h2 : 2 * (v j1 * v j1) = 0 := by
      have hj2 : v j2 = - v j1 := eq_neg_of_add_eq_zero_right hsum
      rw [hj2] at hsq
      linear_combination hsq
    have hv1 : v j1 = 0 := by
      have h2ne : (2 : ℂ) ≠ 0 := by norm_num
      have := (mul_eq_zero.mp h2).resolve_left h2ne
      exact mul_self_eq_zero.mp this
    have hmem : j1 ∈ S := by rw [hS]; simp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem hv1

lemma no_disjoint_iso (u v : Vec) (hu0 : u ∈ H0) (hv0 : v ∈ H0)
    (hui : dot u u = 0) (hvi : dot v v = 0) (hune : u ≠ 0) (hvne : v ≠ 0)
    (hdisj : had u v = 0) : False := by
  set Su := Finset.univ.filter (fun j : Fin 5 => u j ≠ 0)
  set Sv := Finset.univ.filter (fun j : Fin 5 => v j ≠ 0)
  have hd : Disjoint Su Sv := by
    rw [Finset.disjoint_left]
    intro j hju hjv
    simp only [Su, Sv, Finset.mem_filter, Finset.mem_univ, true_and] at hju hjv
    have h0 : u j * v j = 0 := congrFun hdisj j
    exact (mul_eq_zero.mp h0).elim hju hjv
  have h1 : 3 ≤ Su.card := card_supp_ge_three u hu0 hui hune
  have h2 : 3 ≤ Sv.card := card_supp_ge_three v hv0 hvi hvne
  have h3 : (Su ∪ Sv).card ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_le_card (Finset.subset_univ _)
  rw [Finset.card_union_of_disjoint hd, Finset.card_univ, Fintype.card_fin] at h3
  omega

lemma exists_complex_sq (z : ℂ) : ∃ d : ℂ, d * d = z := by
  let r : ℝ := Real.sqrt (z.re ^ 2 + z.im ^ 2)
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = z.re ^ 2 + z.im ^ 2 := Real.sq_sqrt (by positivity)
  have hrx_le : |z.re| ≤ r := by
    have h1 : z.re ^ 2 ≤ r ^ 2 := by rw [hr_sq]; linarith [sq_nonneg z.im]
    exact abs_le_of_sq_le_sq h1 hr_nonneg
  have hplus : 0 ≤ (r + z.re) / 2 := by linarith [neg_abs_le z.re]
  have hminus : 0 ≤ (r - z.re) / 2 := by linarith [le_abs_self z.re]
  let a : ℝ := Real.sqrt ((r + z.re) / 2)
  let s : ℝ := if 0 ≤ z.im then 1 else -1
  let b : ℝ := s * Real.sqrt ((r - z.re) / 2)
  have hs_sq : s ^ 2 = 1 := by dsimp only [s]; split_ifs <;> norm_num
  have ha_sq : a ^ 2 = (r + z.re) / 2 := Real.sq_sqrt hplus
  have hb_sq : b ^ 2 = (r - z.re) / 2 := by
    dsimp only [b]; rw [mul_pow, hs_sq, one_mul, Real.sq_sqrt hminus]
  have hab_sq : (2 * a * b) ^ 2 = z.im ^ 2 := by
    have : (2 * a * b) ^ 2 = 4 * a ^ 2 * b ^ 2 := by ring
    rw [this, ha_sq, hb_sq]
    linear_combination hr_sq
  have h2ab : 2 * a * b = z.im := by
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hsq0 : 0 ≤ Real.sqrt ((r - z.re) / 2) := Real.sqrt_nonneg _
    have hab_eq : 2 * a * b = z.im ∨ 2 * a * b = -z.im := sq_eq_sq_iff_eq_or_eq_neg.mp hab_sq
    by_cases hy : 0 ≤ z.im
    · have hb0 : 0 ≤ b := by dsimp only [b, s]; rw [if_pos hy, one_mul]; exact hsq0
      have hprod0 : 0 ≤ 2 * a * b := by positivity
      rcases hab_eq with h | h
      · exact h
      · linarith
    · push_neg at hy
      have hb0 : b ≤ 0 := by dsimp only [b, s]; rw [if_neg (not_le.mpr hy)]; linarith
      have hprod0 : 2 * a * b ≤ 0 := by nlinarith
      rcases hab_eq with h | h
      · exact h
      · linarith
  refine ⟨⟨a, b⟩, ?_⟩
  apply Complex.ext
  · simp only [Complex.mul_re]
    linarith [ha_sq, hb_sq]
  · simp only [Complex.mul_im]
    linarith [h2ab]

lemma had_triple_linindep (W : Submodule ℂ Vec) (hW : W ≤ H0)
    (hiso : ∀ u ∈ W, ∀ v ∈ W, dot u v = 0) (u1 u2 : Vec) (hu1 : u1 ∈ W) (hu2 : u2 ∈ W)
    (hind : LinearIndependent ℂ ![u1, u2]) :
    LinearIndependent ℂ ![had u1 u1, had u1 u2, had u2 u2] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  have hcomb : ∀ j : Fin 5, c 0 * (u1 j * u1 j) + c 1 * (u1 j * u2 j) + c 2 * (u2 j * u2 j) = 0 := by
    intro j
    have hj := congrFun hc j
    simp only [Fin.sum_univ_three, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, had, Pi.zero_apply] at hj
    exact hj
  have hne_any : c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 := by
    rcases hne with ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  have hu2_ne : u2 ≠ 0 := by
    intro h0
    have := (Fintype.linearIndependent_iff.mp hind) ![0, 1] (by simp [Fin.sum_univ_two, h0]) 1
    simp at this
  by_cases hc0 : c 0 = 0
  · let w : Vec := c 1 • u1 + c 2 • u2
    have hwW : w ∈ W := W.add_mem (W.smul_mem _ hu1) (W.smul_mem _ hu2)
    have hw_ne : w ≠ 0 := by
      intro hw0
      have hlin := Fintype.linearIndependent_iff.mp hind ![c 1, c 2] (by simpa [Fin.sum_univ_two, w] using hw0)
      rcases hne_any with h | h | h
      · exact h hc0
      · exact h (hlin 0)
      · exact h (hlin 1)
    have hdisj : had u2 w = 0 := by
      ext j
      have hj := hcomb j
      rw [hc0, zero_mul, zero_add] at hj
      simp only [had, w, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      linear_combination hj
    exact no_disjoint_iso u2 w (hW hu2) (hW hwW) (hiso u2 hu2 u2 hu2) (hiso w hwW w hwW) hu2_ne hw_ne hdisj
  · obtain ⟨d, hd⟩ := exists_complex_sq (c 1 ^ 2 - 4 * c 0 * c 2)
    let r1 : ℂ := (-c 1 + d) / (2 * c 0)
    let r2 : ℂ := (-c 1 - d) / (2 * c 0)
    let v : Vec := u1 - r1 • u2
    let w : Vec := u1 - r2 • u2
    have hvW : v ∈ W := W.sub_mem hu1 (W.smul_mem _ hu2)
    have hwW : w ∈ W := W.sub_mem hu1 (W.smul_mem _ hu2)
    have hv_ne : v ≠ 0 := by
      intro hv0
      have hlin := Fintype.linearIndependent_iff.mp hind ![1, -r1]
        (by simp [Fin.sum_univ_two, sub_eq_add_neg] at hv0 ⊢; simpa [v, sub_eq_add_neg] using hv0)
      have := hlin 0; simp at this
    have hw_ne : w ≠ 0 := by
      intro hw0
      have hlin := Fintype.linearIndependent_iff.mp hind ![1, -r2]
        (by simp [Fin.sum_univ_two, sub_eq_add_neg] at hw0 ⊢; simpa [w, sub_eq_add_neg] using hw0)
      have := hlin 0; simp at this
    have hdisj : had v w = 0 := by
      ext j
      have hj := hcomb j
      simp only [had, v, w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hfac : c 0 * ((u1 j - r1 * u2 j) * (u1 j - r2 * u2 j)) = 0 := by
        have h2c : (2 * c 0 : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hc0
        dsimp only [r1, r2]
        field_simp [h2c]
        linear_combination 4 * c 0 * hj - (u2 j) ^ 2 * hd
      exact (mul_eq_zero.mp hfac).resolve_left hc0
    exact no_disjoint_iso v w (hW hvW) (hW hwW) (hiso v hvW v hvW) (hiso w hwW w hwW) hv_ne hw_ne hdisj

def sqSpan (W : Submodule ℂ Vec) : Submodule ℂ Vec :=
  Submodule.span ℂ {z | ∃ u ∈ W, ∃ v ∈ W, z = had u v}

lemma sqSpan_le_H0 (W : Submodule ℂ Vec) (hiso : ∀ u ∈ W, ∀ v ∈ W, dot u v = 0) :
    sqSpan W ≤ H0 := by
  rw [sqSpan, Submodule.span_le]
  rintro z ⟨u, hu, v, hv, rfl⟩
  exact hiso u hu v hv

lemma finrank_sqSpan_ge_three (W : Submodule ℂ Vec) (hW : W ≤ H0)
    (hiso : ∀ u ∈ W, ∀ v ∈ W, dot u v = 0) (hdim : Module.finrank ℂ W = 2) :
    3 ≤ Module.finrank ℂ (sqSpan W) := by
  let b := Module.finBasisOfFinrankEq ℂ W hdim
  let u1 : Vec := (b 0).1
  let u2 : Vec := (b 1).1
  have hind : LinearIndependent ℂ ![u1, u2] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hcW : ∑ i : Fin 2, c i • b i = 0 := by
      apply Subtype.ext
      simpa [Fin.sum_univ_two, u1, u2] using hc
    exact Fintype.linearIndependent_iff.mp b.linearIndependent c hcW
  have ht := had_triple_linindep W hW hiso u1 u2 (b 0).2 (b 1).2 hind
  let f : Fin 3 → sqSpan W := fun i =>
    ⟨![had u1 u1, had u1 u2, had u2 u2] i, by
      fin_cases i
      · exact Submodule.subset_span ⟨u1, (b 0).2, u1, (b 0).2, rfl⟩
      · exact Submodule.subset_span ⟨u1, (b 0).2, u2, (b 1).2, rfl⟩
      · exact Submodule.subset_span ⟨u2, (b 1).2, u2, (b 1).2, rfl⟩⟩
  have hfi : LinearIndependent ℂ f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ i : Fin 3, c i • ![had u1 u1, had u1 u2, had u2 u2] i = 0 := by
      have := congrArg Subtype.val hc
      simpa [f] using this
    exact Fintype.linearIndependent_iff.mp ht c hc'
  have hle := hfi.fintype_card_le_finrank
  simpa using hle

lemma mat_dot_polar (L : Submodule ℂ Mat)
    (hL : ∀ X ∈ L, (∀ i, ∑ j, X i j = 0) ∧ (∀ j, ∑ i, X i j = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120) :
    (∀ X ∈ L, dot (X 0) (X 0) + dot (X 1) (X 1) + dot (X 2) (X 2) + dot (X 3) (X 3) = 0) ∧
    (∀ X ∈ L, ∀ Y ∈ L, dot (X 0) (Y 0) + dot (X 1) (Y 1) + dot (X 2) (Y 2) + dot (X 3) (Y 3) = 0) := by
  have hsq : ∀ X ∈ L, dot (X 0) (X 0) + dot (X 1) (X 1) + dot (X 2) (X 2) + dot (X 3) (X 3) = 0 := by
    intro X hX
    have hconst : ∀ t : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + (t • X) i (f i))) = 120 :=
      fun t => (hL (t • X) (L.smul_mem t hX)).2.2
    have he2 := (coeffs_zero_of_const X hconst).1
    rw [e2_eq X (hL X hX).1 (hL X hX).2.1] at he2
    exact (mul_eq_zero.mp he2).resolve_left (by norm_num)
  refine ⟨hsq, fun X hX Y hY => ?_⟩
  have hXY := hsq (X + Y) (L.add_mem hX hY)
  have hX0 := hsq X hX
  have hY0 := hsq Y hY
  have hexp : ∀ i : Fin 4, dot ((X + Y) i) ((X + Y) i) =
      dot (X i) (X i) + 2 * dot (X i) (Y i) + dot (Y i) (Y i) := by
    intro i
    simp only [dot, Pi.add_apply]
    have : ∀ j, (X i j + Y i j) * (X i j + Y i j) =
        X i j * X i j + 2 * (X i j * Y i j) + Y i j * Y i j := fun _ => by ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexp 0, hexp 1, hexp 2, hexp 3] at hXY
  linear_combination (hXY - hX0 - hY0) / 2

lemma e3_polar_top (L : Submodule ℂ Mat)
    (hL : ∀ X ∈ L, (∀ i, ∑ j, X i j = 0) ∧ (∀ j, ∑ i, X i j = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120)
    (X : Mat) (hX : X ∈ L) (h01 : X 0 = X 1)
    (u : Vec) (hu : (![u, -u, 0, 0] : Mat) ∈ L) :
    dot (had u u) (X 0) = 0 := by
  have he3t : ∀ t : ℂ, e3 (X + t • (![u, -u, 0, 0] : Mat)) = 0 := by
    intro t
    let Z : Mat := X + t • (![u, -u, 0, 0] : Mat)
    have hZ : Z ∈ L := L.add_mem hX (L.smul_mem t hu)
    exact (coeffs_zero_of_const Z (fun s => (hL (s • Z) (L.smul_mem s hZ)).2.2)).2.1
  have hcol : ∀ j : Fin 5, X 2 j + X 3 j = -2 * X 0 j := by
    intro j
    have hc := (hL X hX).2.1 j
    rw [Fin.sum_univ_four, ← h01] at hc
    linear_combination hc
  have hform : ∀ t : ℂ,
      e3 (X + t • (![u, -u, 0, 0] : Mat)) =
        e3 X + 8 * t ^ 2 * dot (had u u) (X 0) := by
    intro t
    let Z : Mat := X + t • (![u, -u, 0, 0] : Mat)
    have hZ : Z ∈ L := L.add_mem hX (L.smul_mem t hu)
    rw [e3_eq Z (hL Z hZ).1, e3_eq X (hL X hX).1]
    have hdiff : ∀ j : Fin 5,
        (Z 0 j * Z 1 j * Z 2 j + Z 0 j * Z 1 j * Z 3 j +
         Z 0 j * Z 2 j * Z 3 j + Z 1 j * Z 2 j * Z 3 j) -
        (X 0 j * X 1 j * X 2 j + X 0 j * X 1 j * X 3 j +
         X 0 j * X 2 j * X 3 j + X 1 j * X 2 j * X 3 j) =
        2 * t ^ 2 * (u j * u j * X 0 j) := by
      intro j
      have hz0 : Z 0 j = X 0 j + t * u j := by change X 0 j + t * u j = _; rfl
      have hz1 : Z 1 j = X 0 j - t * u j := by
        have h1' : Z 1 j = X 1 j + t * (-u j) := rfl
        rw [h1', ← h01]; ring
      have hz2 : Z 2 j = X 2 j := by change X 2 j + t * 0 = X 2 j; ring
      have hz3 : Z 3 j = X 3 j := by change X 3 j + t * 0 = X 3 j; ring
      have hx1 : X 1 j = X 0 j := congrFun h01.symm j
      rw [hz0, hz1, hz2, hz3, hx1]
      linear_combination -(t ^ 2 * u j ^ 2) * hcol j
    have hsum := Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hdiff j
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    unfold dot had
    linear_combination 4 * hsum
  have h0 := he3t 0; rw [hform 0] at h0
  have h1 := he3t 1; rw [hform 1] at h1
  linear_combination (h1 - h0) / 8

lemma e3_polar_bot (L : Submodule ℂ Mat)
    (hL : ∀ X ∈ L, (∀ i, ∑ j, X i j = 0) ∧ (∀ j, ∑ i, X i j = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120)
    (a : Vec) (ha : (![a, a, -a, -a] : Mat) ∈ L)
    (v : Vec) (hv : (![0, 0, v, -v] : Mat) ∈ L) :
    dot (had v v) a = 0 := by
  have he3t : ∀ t : ℂ, e3 ((![a, a, -a, -a] : Mat) + t • (![0, 0, v, -v] : Mat)) = 0 := by
    intro t
    let Z : Mat := (![a, a, -a, -a] : Mat) + t • (![0, 0, v, -v] : Mat)
    have hZ : Z ∈ L := L.add_mem ha (L.smul_mem t hv)
    exact (coeffs_zero_of_const Z (fun s => (hL (s • Z) (L.smul_mem s hZ)).2.2)).2.1
  have h1 := he3t 1
  let Z : Mat := (![a, a, -a, -a] : Mat) + (1 : ℂ) • (![0, 0, v, -v] : Mat)
  have hZ : Z ∈ L := L.add_mem ha (L.smul_mem 1 hv)
  rw [e3_eq Z (hL Z hZ).1] at h1
  have hterm : ∀ j : Fin 5,
      Z 0 j * Z 1 j * Z 2 j + Z 0 j * Z 1 j * Z 3 j +
      Z 0 j * Z 2 j * Z 3 j + Z 1 j * Z 2 j * Z 3 j =
      -2 * (v j * v j * a j) := by
    intro j
    have hz0 : Z 0 j = a j := by simp [Z]
    have hz1 : Z 1 j = a j := by simp [Z]
    have hz2 : Z 2 j = -a j + v j := by simp [Z]
    have hz3 : Z 3 j = -a j - v j := by simp [Z, sub_eq_add_neg]
    rw [hz0, hz1, hz2, hz3]
    ring
  simp_rw [hterm, ← Finset.mul_sum] at h1
  unfold dot had
  linear_combination -h1 / 8

lemma e4_cross (L : Submodule ℂ Mat)
    (hL : ∀ X ∈ L, (∀ i, ∑ j, X i j = 0) ∧ (∀ j, ∑ i, X i j = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120)
    (u v : Vec) (hu : (![u, -u, 0, 0] : Mat) ∈ L) (hv : (![0, 0, v, -v] : Mat) ∈ L)
    (hui : dot u u = 0) (hvi : dot v v = 0) :
    3 * dot (had u u) (had v v) = (dot u v) ^ 2 := by
  let Z : Mat := (![u, -u, 0, 0] : Mat) + (![0, 0, v, -v] : Mat)
  have hZ : Z ∈ L := L.add_mem hu hv
  have he4 := (coeffs_zero_of_const Z (fun s => (hL (s • Z) (L.smul_mem s hZ)).2.2)).2.2
  have hZ0 : Z 0 = u := by ext j; simp [Z]
  have hZ1 : Z 1 = -u := by ext j; simp [Z]
  have hZ2 : Z 2 = v := by ext j; simp [Z]
  have hZ3 : Z 3 = -v := by ext j; simp [Z]
  have hhr := (hL Z hZ).1
  have hr0 : ∑ j, u j = 0 := by simpa [hZ0] using hhr 0
  have hr1 : ∑ j, (-u) j = 0 := by simpa [hZ1] using hhr 1
  have hr2 : ∑ j, v j = 0 := by simpa [hZ2] using hhr 2
  have hr3 : ∑ j, (-v) j = 0 := by simpa [hZ3] using hhr 3
  unfold e4 at he4
  rw [hZ0, hZ1, hZ2, hZ3] at he4
  rw [e4_eq u (-u) v (-v) hr0 hr1 hr2 hr3] at he4
  have hd1 : dot u (-u) = 0 := by
    have : dot u (-u) = - dot u u := by simp [dot, Finset.sum_neg_distrib]
    rw [this, hui, neg_zero]
  have hd2 : dot (-u) (-v) = dot u v := by simp [dot]
  have hd3 : dot u (-v) = - dot u v := by simp [dot, Finset.sum_neg_distrib]
  have hd4 : dot (-u) v = - dot u v := by simp [dot, Finset.sum_neg_distrib]
  have h4 : (∑ j : Fin 5, u j * (-u) j * v j * (-v) j) = dot (had u u) (had v v) := by
    unfold dot had
    refine Finset.sum_congr rfl fun j _ => by simp; ring
  rw [hd1, hd2, hd3, hd4, h4] at he4
  linear_combination -he4 / 2

lemma e4_cross_polar (L : Submodule ℂ Mat)
    (hL : ∀ X ∈ L, (∀ i, ∑ j, X i j = 0) ∧ (∀ j, ∑ i, X i j = 0) ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120)
    (U V : Submodule ℂ Vec)
    (hU : ∀ u ∈ U, (![u, -u, 0, 0] : Mat) ∈ L)
    (hV : ∀ v ∈ V, (![0, 0, v, -v] : Mat) ∈ L)
    (hUiso : ∀ u ∈ U, dot u u = 0) (hViso : ∀ v ∈ V, dot v v = 0)
    (u1 u2 : Vec) (hu1 : u1 ∈ U) (hu2 : u2 ∈ U)
    (v1 v2 : Vec) (hv1 : v1 ∈ V) (hv2 : v2 ∈ V) :
    6 * dot (had u1 u2) (had v1 v2) = dot u1 v1 * dot u2 v2 + dot u1 v2 * dot u2 v1 := by
  have hbase : ∀ u ∈ U, ∀ v ∈ V, 3 * dot (had u u) (had v v) = (dot u v) ^ 2 :=
    fun u hu v hv => e4_cross L hL u v (hU u hu) (hV v hv) (hUiso u hu) (hViso v hv)
  have hpol_v : ∀ u ∈ U, 3 * dot (had u u) (had v1 v2) = dot u v1 * dot u v2 := by
    intro u hu
    have h12 := hbase u hu (v1 + v2) (V.add_mem hv1 hv2)
    have h1 := hbase u hu v1 hv1
    have h2 := hbase u hu v2 hv2
    have hdadd : dot u (v1 + v2) = dot u v1 + dot u v2 := by
      simp [dot, mul_add, Finset.sum_add_distrib]
    have hhad : dot (had u u) (had (v1 + v2) (v1 + v2)) =
        dot (had u u) (had v1 v1) + 2 * dot (had u u) (had v1 v2) + dot (had u u) (had v2 v2) := by
      unfold dot had
      have : ∀ j, u j * u j * ((v1 j + v2 j) * (v1 j + v2 j)) =
          u j * u j * (v1 j * v1 j) + 2 * (u j * u j * (v1 j * v2 j)) + u j * u j * (v2 j * v2 j) :=
        fun _ => by ring
      simp_rw [Pi.add_apply, this, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hdadd, hhad] at h12
    linear_combination (h12 - h1 - h2) / 2
  have h12 := hpol_v (u1 + u2) (U.add_mem hu1 hu2)
  have h1 := hpol_v u1 hu1
  have h2 := hpol_v u2 hu2
  have hd1 : dot (u1 + u2) v1 = dot u1 v1 + dot u2 v1 := by
    simp [dot, add_mul, Finset.sum_add_distrib]
  have hd2 : dot (u1 + u2) v2 = dot u1 v2 + dot u2 v2 := by
    simp [dot, add_mul, Finset.sum_add_distrib]
  have hhad : dot (had (u1 + u2) (u1 + u2)) (had v1 v2) =
      dot (had u1 u1) (had v1 v2) + 2 * dot (had u1 u2) (had v1 v2) + dot (had u2 u2) (had v1 v2) := by
    unfold dot had
    have : ∀ j, (u1 j + u2 j) * (u1 j + u2 j) * (v1 j * v2 j) =
        u1 j * u1 j * (v1 j * v2 j) + 2 * (u1 j * u2 j * (v1 j * v2 j)) + u2 j * u2 j * (v1 j * v2 j) :=
      fun _ => by ring
    simp_rw [Pi.add_apply, this, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hd1, hd2, hhad] at h12
  linear_combination h12 - h1 - h2

end PEqualNP.Outside.L_gct_286_aux

theorem PEqualNP.Outside.L_gct_286 :
  ∀ (L : Submodule ℂ (Fin 4 → Fin 5 → ℂ)) (U : Submodule ℂ (Fin 5 → ℂ)),
  (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120) →
  (∀ u ∈ U, (![u, -u, 0, 0] : Fin 4 → Fin 5 → ℂ) ∈ L) →
  2 ≤ Module.finrank ℂ U → Module.finrank ℂ L ≤ 4 := by
  intro L U hL hU hU2
  open PEqualNP.Outside.L_gct_286_aux in
  have hpolar := mat_dot_polar L hL
  have hU_H0 : U ≤ H0 := by
    intro u hu
    exact (hL _ (hU u hu)).1 0
  have hU_iso : ∀ u ∈ U, ∀ v ∈ U, dot u v = 0 := by
    intro u hu v hv
    have hp := hpolar.2 _ (hU u hu) _ (hU v hv)
    have h0 : dot u v + dot (-u) (-v) + dot 0 0 + dot 0 0 = 0 := by simpa using hp
    have hneg : dot (-u) (-v) = dot u v := by simp [dot]
    have hzero : dot 0 0 = 0 := by simp [dot]
    rw [hneg, hzero] at h0
    linear_combination h0 / 2
  have ⟨hU_perp, hU_dim⟩ := iso_eq_perpH0 U hU_H0 hU_iso hU2
  have hdiff_U : ∀ X ∈ L, X 0 - X 1 ∈ U := by
    intro X hX
    rw [hU_perp]
    refine ⟨H0.sub_mem ((hL X hX).1 0) ((hL X hX).1 1), fun u hu => ?_⟩
    have hp := hpolar.2 X hX _ (hU u hu)
    have h1 : dot (X 0) u + dot (X 1) (-u) + dot (X 2) 0 + dot (X 3) 0 = 0 := by simpa using hp
    have hneg : dot (X 1) (-u) = - dot (X 1) u := by simp [dot, Finset.sum_neg_distrib]
    have hz2 : dot (X 2) 0 = 0 := by simp [dot]
    have hz3 : dot (X 3) 0 = 0 := by simp [dot]
    have hsub : dot (X 0 - X 1) u = dot (X 0) u - dot (X 1) u := by
      simp [dot, sub_mul, Finset.sum_sub_distrib]
    rw [hneg, hz2, hz3] at h1
    rw [hsub]
    linear_combination h1
  let L' : Submodule ℂ Mat :=
    { carrier := {X | X ∈ L ∧ X 0 = X 1}, add_mem' := fun hx hy => ⟨L.add_mem hx.1 hy.1, by simp [hx.2, hy.2]⟩
      zero_mem' := ⟨L.zero_mem, rfl⟩
      smul_mem' := fun c _ hx => ⟨L.smul_mem c hx.1, by simp [hx.2]⟩ }
  let projU : L →ₗ[ℂ] U :=
    { toFun := fun X => ⟨(1 / 2 : ℂ) • (X.1 0 - X.1 1), U.smul_mem _ (hdiff_U X.1 X.2)⟩
      map_add' := fun X Y => by
        apply Subtype.ext; ext j; simp; ring
      map_smul' := fun c X => by
        apply Subtype.ext; ext j; simp; ring }
  have hker_proj : Module.finrank ℂ (LinearMap.ker projU) = Module.finrank ℂ L' := by
    let e : LinearMap.ker projU ≃ₗ[ℂ] L' :=
      { toFun := fun x => ⟨x.1.1, x.1.2, by
          have hx := congrArg Subtype.val x.2
          have hx' : (1 / 2 : ℂ) • (x.1.1 0 - x.1.1 1) = 0 := hx
          have hsub : x.1.1 0 - x.1.1 1 = 0 := (smul_eq_zero.mp hx').resolve_left (by norm_num)
          exact sub_eq_zero.mp hsub⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, by
          apply Subtype.ext; simp [projU, y.2.2]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  have hL_le : Module.finrank ℂ L ≤ 2 + Module.finrank ℂ L' := by
    have hfn := LinearMap.finrank_range_add_finrank_ker projU
    have hrle : Module.finrank ℂ (LinearMap.range projU) ≤ Module.finrank ℂ U :=
      Submodule.finrank_le _
    rw [hker_proj] at hfn
    rw [hU_dim] at hrle
    omega
  by_contra hgt
  push_neg at hgt
  have hL'_ge : 3 ≤ Module.finrank ℂ L' := by omega
  let V : Submodule ℂ Vec :=
    { carrier := {v | (![0, 0, v, -v] : Mat) ∈ L}, add_mem' := by
        intro x y hx hy
        have hsum : (![0, 0, x + y, -(x + y)] : Mat) = (![0, 0, x, -x] : Mat) + (![0, 0, y, -y] : Mat) := by
          ext i j; fin_cases i <;> simp [neg_add, add_comm]
        change (![0, 0, x + y, -(x + y)] : Mat) ∈ L
        rw [hsum]; exact L.add_mem hx hy
      zero_mem' := by
        have hz : (![0, 0, (0 : Vec), -(0 : Vec)] : Mat) = 0 := by ext i j; fin_cases i <;> simp
        change (![0, 0, (0 : Vec), -(0 : Vec)] : Mat) ∈ L
        rw [hz]; exact L.zero_mem
      smul_mem' := by
        intro c x hx
        have hsm : (![0, 0, c • x, -(c • x)] : Mat) = c • (![0, 0, x, -x] : Mat) := by
          ext i j; fin_cases i <;> simp [smul_neg]
        change (![0, 0, c • x, -(c • x)] : Mat) ∈ L
        rw [hsm]; exact L.smul_mem c hx }
  have hV_H0 : V ≤ H0 := fun v hv => (hL _ hv).1 2
  have hV_iso : ∀ u ∈ V, ∀ v ∈ V, dot u v = 0 := by
    intro u hu v hv
    have hp := hpolar.2 _ hu _ hv
    have h0 : dot 0 0 + dot 0 0 + dot u v + dot (-u) (-v) = 0 := by simpa using hp
    have hneg : dot (-u) (-v) = dot u v := by simp [dot]
    have hzero : dot 0 0 = 0 := by simp [dot]
    rw [hneg, hzero] at h0
    linear_combination h0 / 2
  have hV_le2 : Module.finrank ℂ V ≤ 2 := iso_finrank_le_two V hV_H0 hV_iso
  let pi1 : L' →ₗ[ℂ] perpH0 (sqSpan U) :=
    { toFun := fun X => ⟨X.1 0, (hL X.1 X.2.1).1 0, by
        intro w hw
        refine Submodule.span_induction (p := fun w _ => dot (X.1 0) w = 0) ?_ ?_ ?_ ?_ hw
        · rintro z ⟨u, hu, v, hv, rfl⟩
          have h12 := e3_polar_top L hL X.1 X.2.1 X.2.2 (u + v) (hU _ (U.add_mem hu hv))
          have h1 := e3_polar_top L hL X.1 X.2.1 X.2.2 u (hU u hu)
          have h2 := e3_polar_top L hL X.1 X.2.1 X.2.2 v (hU v hv)
          have hcomm : dot (X.1 0) (had u v) = dot (had u v) (X.1 0) := by
            unfold dot; refine Finset.sum_congr rfl fun j _ => by ring
          have hexp : dot (had (u + v) (u + v)) (X.1 0) =
              dot (had u u) (X.1 0) + 2 * dot (had u v) (X.1 0) + dot (had v v) (X.1 0) := by
            unfold dot had
            have : ∀ j, (u j + v j) * (u j + v j) * X.1 0 j =
                u j * u j * X.1 0 j + 2 * (u j * v j * X.1 0 j) + v j * v j * X.1 0 j := fun _ => by ring
            simp_rw [Pi.add_apply, this, Finset.sum_add_distrib, ← Finset.mul_sum]
          rw [hexp] at h12
          rw [hcomm]
          linear_combination (h12 - h1 - h2) / 2
        · simp [dot]
        · intro x y _ _ hx hy
          unfold dot at hx hy ⊢
          simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
          rw [hx, hy, add_zero]
        · intro c x _ hx
          have : dot (X.1 0) (c • x) = c * dot (X.1 0) x := by
            simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
          rw [this, hx, mul_zero]⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker_pi1 : Module.finrank ℂ (LinearMap.ker pi1) = Module.finrank ℂ V := by
    let e : LinearMap.ker pi1 ≃ₗ[ℂ] V :=
      { toFun := fun x => ⟨x.1.1 2, by
          have hx0 : x.1.1 0 = 0 := congrArg Subtype.val x.2
          have hx1 : x.1.1 1 = 0 := by rw [← x.1.2.2, hx0]
          have hx3 : x.1.1 3 = - x.1.1 2 := by
            ext j
            have hc := (hL x.1.1 x.1.2.1).2.1 j
            rw [Fin.sum_univ_four, hx0, hx1] at hc
            simp only [Pi.zero_apply, zero_add] at hc
            exact eq_neg_of_add_eq_zero_right hc
          have heq : (![0, 0, x.1.1 2, - x.1.1 2] : Mat) = x.1.1 := by
            ext i j; fin_cases i <;> simp [hx0, hx1, hx3]
          change (![0, 0, x.1.1 2, - x.1.1 2] : Mat) ∈ L; rw [heq]; exact x.1.2.1⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun v => ⟨⟨![0, 0, v.1, -v.1], v.2, rfl⟩, rfl⟩
        left_inv := fun x => by
          apply Subtype.ext; apply Subtype.ext; ext i j
          have hx0 : x.1.1 0 = 0 := congrArg Subtype.val x.2
          have hx1 : x.1.1 1 = 0 := by rw [← x.1.2.2, hx0]
          have hx3 : x.1.1 3 = - x.1.1 2 := by
            ext k
            have hc := (hL x.1.1 x.1.2.1).2.1 k
            rw [Fin.sum_univ_four, hx0, hx1] at hc
            simp only [Pi.zero_apply, zero_add] at hc
            exact eq_neg_of_add_eq_zero_right hc
          fin_cases i <;> simp [hx0, hx1, hx3]
        right_inv := fun _ => rfl }
    exact e.finrank_eq
  have hsqU_dim : 3 ≤ Module.finrank ℂ (sqSpan U) := finrank_sqSpan_ge_three U hU_H0 hU_iso hU_dim
  have hperpU_le : Module.finrank ℂ (perpH0 (sqSpan U)) ≤ 1 := by
    have := finrank_perpH0_add (sqSpan U) (sqSpan_le_H0 U hU_iso)
    omega
  have hpi1_fn := LinearMap.finrank_range_add_finrank_ker pi1
  have hrange_le : Module.finrank ℂ (LinearMap.range pi1) ≤ 1 :=
    (Submodule.finrank_le _).trans hperpU_le
  rw [hker_pi1] at hpi1_fn
  have hV_dim2 : 2 ≤ Module.finrank ℂ V := by omega
  have hrange_eq1 : Module.finrank ℂ (LinearMap.range pi1) = 1 := by omega
  have ⟨hV_perp, hV_dim⟩ := iso_eq_perpH0 V hV_H0 hV_iso hV_dim2
  have hex_a : ∃ X : L', X.1 0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hzero : LinearMap.range pi1 = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro y ⟨X, rfl⟩
      apply Subtype.ext
      exact hall X
    rw [hzero, finrank_bot] at hrange_eq1
    omega
  rcases hex_a with ⟨X, ha_ne⟩
  set a : Vec := X.1 0
  have ha_H0 : a ∈ H0 := (hL X.1 X.2.1).1 0
  have hab_V : a + X.1 2 ∈ V := by
    rw [hV_perp]
    refine ⟨H0.add_mem ha_H0 ((hL X.1 X.2.1).1 2), fun v hv => ?_⟩
    have hp := hpolar.2 X.1 X.2.1 _ hv
    have h1 : dot (X.1 0) 0 + dot (X.1 1) 0 + dot (X.1 2) v + dot (X.1 3) (-v) = 0 := by simpa using hp
    have hcol : X.1 3 = (-2 : ℂ) • a - X.1 2 := by
      ext j
      have hc := (hL X.1 X.2.1).2.1 j
      rw [Fin.sum_univ_four, ← X.2.2] at hc
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, a]
      linear_combination hc
    have hneg : dot (X.1 3) (-v) = 2 * dot a v + dot (X.1 2) v := by
      rw [hcol]
      simp only [dot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
      have : ∀ j, (-2 * a j - X.1 2 j) * -v j = 2 * (a j * v j) + X.1 2 j * v j := fun _ => by ring
      have hsum : (∑ j : Fin 5, (-2 * a j - X.1 2 j) * -v j) =
          2 * (∑ j : Fin 5, a j * v j) + ∑ j : Fin 5, X.1 2 j * v j := by
        simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
      exact hsum
    have hz0 : dot (X.1 0) 0 = 0 := by simp [dot]
    have hz1 : dot (X.1 1) 0 = 0 := by simp [dot]
    have hadd : dot (a + X.1 2) v = dot a v + dot (X.1 2) v := by
      simp [dot, add_mul, Finset.sum_add_distrib]
    rw [hz0, hz1, hneg] at h1
    rw [hadd]
    linear_combination h1 / 2
  have hY_mem : (![a, a, -a, -a] : Mat) ∈ L := by
    have heq : (![a, a, -a, -a] : Mat) = X.1 - (![0, 0, a + X.1 2, -(a + X.1 2)] : Mat) := by
      ext i j
      have hc := (hL X.1 X.2.1).2.1 j
      rw [Fin.sum_univ_four, ← X.2.2] at hc
      fin_cases i
      · simp [a]
      · simp [a, X.2.2]
      · simp [a]
      · change -a j = X.1 3 j - -(a j + X.1 2 j)
        linear_combination -hc
    rw [heq]
    exact L.sub_mem X.2.1 hab_V
  have ha_iso : dot a a = 0 := by
    have hsq := hpolar.1 _ hY_mem
    have h0 : dot a a + dot a a + dot (-a) (-a) + dot (-a) (-a) = 0 := by simpa using hsq
    have hneg : dot (-a) (-a) = dot a a := by simp [dot]
    rw [hneg] at h0
    linear_combination h0 / 4
  have ha_perp_U : a ∈ perpH0 (sqSpan U) := (pi1 X).2
  have ha_perp_V : a ∈ perpH0 (sqSpan V) := by
    refine ⟨ha_H0, fun w hw => ?_⟩
    refine Submodule.span_induction (p := fun w _ => dot a w = 0) ?_ ?_ ?_ ?_ hw
    · rintro z ⟨u, hu, v, hv, rfl⟩
      have h12 := e3_polar_bot L hL a hY_mem (u + v) (V.add_mem hu hv)
      have h1 := e3_polar_bot L hL a hY_mem u hu
      have h2 := e3_polar_bot L hL a hY_mem v hv
      have hcomm : dot a (had u v) = dot (had u v) a := by
        unfold dot; refine Finset.sum_congr rfl fun j _ => by ring
      have hexp : dot (had (u + v) (u + v)) a =
          dot (had u u) a + 2 * dot (had u v) a + dot (had v v) a := by
        unfold dot had
        have : ∀ j, (u j + v j) * (u j + v j) * a j =
            u j * u j * a j + 2 * (u j * v j * a j) + v j * v j * a j := fun _ => by ring
        simp_rw [Pi.add_apply, this, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hexp] at h12
      rw [hcomm]
      linear_combination (h12 - h1 - h2) / 2
    · simp [dot]
    · intro x y _ _ hx hy
      unfold dot at hx hy ⊢
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [hx, hy, add_zero]
    · intro c x _ hx
      have : dot a (c • x) = c * dot a x := by
        simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [this, hx, mul_zero]
  have hsqU_eq : sqSpan U = perpH0 (Submodule.span ℂ {a}) := by
    have hle : sqSpan U ≤ perpH0 (Submodule.span ℂ {a}) := by
      intro w hw
      refine ⟨sqSpan_le_H0 U hU_iso hw, fun z hz => ?_⟩
      rw [Submodule.mem_span_singleton] at hz
      rcases hz with ⟨c, rfl⟩
      have hwa : dot w a = 0 := by
        have hcomm : dot w a = dot a w := by unfold dot; refine Finset.sum_congr rfl fun j _ => by ring
        rw [hcomm]
        exact ha_perp_U.2 w hw
      have : dot w (c • a) = c * dot w a := by
        simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [this, hwa, mul_zero]
    have hspan_H0 : Submodule.span ℂ {a} ≤ H0 := by
      rw [Submodule.span_le]; rintro _ rfl; exact ha_H0
    have hspan_dim : Module.finrank ℂ (Submodule.span ℂ {a}) = 1 :=
      finrank_span_singleton ha_ne
    have hp_dim : Module.finrank ℂ (perpH0 (Submodule.span ℂ {a})) = 3 := by
      have := finrank_perpH0_add (Submodule.span ℂ {a}) hspan_H0
      omega
    have hsq_le : Module.finrank ℂ (sqSpan U) ≤ 3 := by
      have := Submodule.finrank_mono hle; omega
    exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have ha_in_sqU : a ∈ sqSpan U := by
    rw [hsqU_eq]
    refine ⟨ha_H0, fun z hz => ?_⟩
    rw [Submodule.mem_span_singleton] at hz
    rcases hz with ⟨c, rfl⟩
    have : dot a (c • a) = c * dot a a := by
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [this, ha_iso, mul_zero]
  let pairUV : U →ₗ[ℂ] Module.Dual ℂ V :=
    { toFun := fun u =>
        { toFun := fun v => dot u.1 v.1
          map_add' := fun x y => by simp [dot, mul_add, Finset.sum_add_distrib]
          map_smul' := fun c x => by
            simp only [dot, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring }
      map_add' := fun x y => by
        ext v; simp [dot, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        ext v
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
          SetLike.val_smul, Pi.smul_apply, dot, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring }
  by_cases hinj : Function.Injective pairUV
  · have hsurj : Function.Surjective pairUV := by
      have hrank : Module.finrank ℂ U = Module.finrank ℂ (Module.Dual ℂ V) := by
        rw [Subspace.dual_finrank_eq, hU_dim, hV_dim]
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
    let bV := Module.finBasisOfFinrankEq ℂ V hV_dim
    let f0 : Module.Dual ℂ V := bV.coord 0
    let f1 : Module.Dual ℂ V := bV.coord 1
    obtain ⟨u1, hu1⟩ := hsurj f0
    obtain ⟨u2, hu2⟩ := hsurj f1
    have hdu10 : dot u1.1 (bV 0).1 = 1 := by
      have := LinearMap.congr_fun hu1 (bV 0)
      change dot u1.1 (bV 0).1 = bV.coord 0 (bV 0) at this
      simpa using this
    have hdu11 : dot u1.1 (bV 1).1 = 0 := by
      have := LinearMap.congr_fun hu1 (bV 1)
      change dot u1.1 (bV 1).1 = bV.coord 0 (bV 1) at this
      simpa using this
    have hdu20 : dot u2.1 (bV 0).1 = 0 := by
      have := LinearMap.congr_fun hu2 (bV 0)
      change dot u2.1 (bV 0).1 = bV.coord 1 (bV 0) at this
      simpa using this
    have hdu21 : dot u2.1 (bV 1).1 = 1 := by
      have := LinearMap.congr_fun hu2 (bV 1)
      change dot u2.1 (bV 1).1 = bV.coord 1 (bV 1) at this
      simpa using this
    have hindU : LinearIndependent ℂ ![u1.1, u2.1] := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have h0 : dot (c 0 • u1.1 + c 1 • u2.1) (bV 0).1 = 0 := by
        have : c 0 • u1.1 + c 1 • u2.1 = 0 := by simpa [Fin.sum_univ_two] using hc
        rw [this]; simp [dot]
      have h1 : dot (c 0 • u1.1 + c 1 • u2.1) (bV 1).1 = 0 := by
        have : c 0 • u1.1 + c 1 • u2.1 = 0 := by simpa [Fin.sum_univ_two] using hc
        rw [this]; simp [dot]
      have hexp : ∀ v : Vec, dot (c 0 • u1.1 + c 1 • u2.1) v = c 0 * dot u1.1 v + c 1 * dot u2.1 v := by
        intro v
        simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
        have s1 : (∑ j : Fin 5, c 0 * u1.1 j * v j) = c 0 * ∑ j : Fin 5, u1.1 j * v j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        have s2 : (∑ j : Fin 5, c 1 * u2.1 j * v j) = c 1 * ∑ j : Fin 5, u2.1 j * v j := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
        rw [s1, s2]
      rw [hexp, hdu10, hdu20] at h0
      rw [hexp, hdu11, hdu21] at h1
      intro i; fin_cases i
      · change c 0 = 0; linear_combination h0
      · change c 1 = 0; linear_combination h1
    have hU_span : U = Submodule.span ℂ {u1.1, u2.1} := by
      have hle : Submodule.span ℂ {u1.1, u2.1} ≤ U := by
        rw [Submodule.span_le]
        rintro x (rfl | rfl)
        · exact u1.2
        · exact u2.2
      have hdim_sp : Module.finrank ℂ (Submodule.span ℂ {u1.1, u2.1}) = 2 := by
        have hrange : Set.range ![u1.1, u2.1] = {u1.1, u2.1} := by
          ext x; simp [Fin.exists_fin_two, or_comm]
        rw [← hrange, finrank_span_eq_card hindU, Fintype.card_fin]
      exact (Submodule.eq_of_le_of_finrank_eq hle (hdim_sp.trans hU_dim.symm)).symm
    have hsq_span : sqSpan U ≤ Submodule.span ℂ {had u1.1 u1.1, had u1.1 u2.1, had u2.1 u2.1} := by
      rw [sqSpan, Submodule.span_le]
      rintro z ⟨x, hx, y, hy, rfl⟩
      rw [hU_span, Submodule.mem_span_pair] at hx hy
      rcases hx with ⟨p1, p2, rfl⟩
      rcases hy with ⟨q1, q2, rfl⟩
      have hexp : had (p1 • u1.1 + p2 • u2.1) (q1 • u1.1 + q2 • u2.1) =
          (p1 * q1) • had u1.1 u1.1 + (p1 * q2 + p2 * q1) • had u1.1 u2.1 + (p2 * q2) • had u2.1 u2.1 := by
        ext j; simp [had]; ring
      rw [hexp]
      refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have ha_mem_sp := hsq_span ha_in_sqU
    rw [Submodule.mem_span_insert] at ha_mem_sp
    rcases ha_mem_sp with ⟨c0, r, hr, ha_eq⟩
    rw [Submodule.mem_span_pair] at hr
    rcases hr with ⟨c1, c2, rfl⟩
    have hpol := e4_cross_polar L hL U V hU (fun v hv => hv) (fun u hu => hU_iso u hu u hu)
      (fun v hv => hV_iso v hv v hv)
    have hdot_a : ∀ w ∈ sqSpan V, dot a w = 0 := ha_perp_V.2
    have h11 : dot a (had (bV 0).1 (bV 0).1) = 0 :=
      hdot_a _ (Submodule.subset_span ⟨(bV 0).1, (bV 0).2, (bV 0).1, (bV 0).2, rfl⟩)
    have h12 : dot a (had (bV 0).1 (bV 1).1) = 0 :=
      hdot_a _ (Submodule.subset_span ⟨(bV 0).1, (bV 0).2, (bV 1).1, (bV 1).2, rfl⟩)
    have h22 : dot a (had (bV 1).1 (bV 1).1) = 0 :=
      hdot_a _ (Submodule.subset_span ⟨(bV 1).1, (bV 1).2, (bV 1).1, (bV 1).2, rfl⟩)
    have hlin_dot : ∀ w : Vec, dot a w =
        c0 * dot (had u1.1 u1.1) w + c1 * dot (had u1.1 u2.1) w + c2 * dot (had u2.1 u2.1) w := by
      intro w
      rw [ha_eq]
      simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib]
      have s0 : (∑ j : Fin 5, c0 * had u1.1 u1.1 j * w j) = c0 * ∑ j : Fin 5, had u1.1 u1.1 j * w j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      have s1 : (∑ j : Fin 5, c1 * had u1.1 u2.1 j * w j) = c1 * ∑ j : Fin 5, had u1.1 u2.1 j * w j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      have s2 : (∑ j : Fin 5, c2 * had u2.1 u2.1 j * w j) = c2 * ∑ j : Fin 5, had u2.1 u2.1 j * w j := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      rw [s0, s1, s2]
      ring
    have hp00_00 := hpol u1.1 u1.1 u1.2 u1.2 (bV 0).1 (bV 0).1 (bV 0).2 (bV 0).2
    have hp01_00 := hpol u1.1 u2.1 u1.2 u2.2 (bV 0).1 (bV 0).1 (bV 0).2 (bV 0).2
    have hp11_00 := hpol u2.1 u2.1 u2.2 u2.2 (bV 0).1 (bV 0).1 (bV 0).2 (bV 0).2
    have hp00_01 := hpol u1.1 u1.1 u1.2 u1.2 (bV 0).1 (bV 1).1 (bV 0).2 (bV 1).2
    have hp01_01 := hpol u1.1 u2.1 u1.2 u2.2 (bV 0).1 (bV 1).1 (bV 0).2 (bV 1).2
    have hp11_01 := hpol u2.1 u2.1 u2.2 u2.2 (bV 0).1 (bV 1).1 (bV 0).2 (bV 1).2
    have hp00_11 := hpol u1.1 u1.1 u1.2 u1.2 (bV 1).1 (bV 1).1 (bV 1).2 (bV 1).2
    have hp01_11 := hpol u1.1 u2.1 u1.2 u2.2 (bV 1).1 (bV 1).1 (bV 1).2 (bV 1).2
    have hp11_11 := hpol u2.1 u2.1 u2.2 u2.2 (bV 1).1 (bV 1).1 (bV 1).2 (bV 1).2
    simp only [hdu10, hdu11, hdu20, hdu21] at hp00_00 hp01_00 hp11_00 hp00_01 hp01_01 hp11_01 hp00_11 hp01_11 hp11_11
    rw [hlin_dot] at h11 h12 h22
    have hc0 : c0 = 0 := by linear_combination 3 * h11 - (c0 * hp00_00 + c1 * hp01_00 + c2 * hp11_00) / 2
    have hc1 : c1 = 0 := by linear_combination 6 * h12 - (c0 * hp00_01 + c1 * hp01_01 + c2 * hp11_01)
    have hc2 : c2 = 0 := by linear_combination 3 * h22 - (c0 * hp00_11 + c1 * hp01_11 + c2 * hp11_11) / 2
    rw [hc0, hc1, hc2, zero_smul, zero_smul, zero_smul, add_zero, add_zero] at ha_eq
    exact ha_ne ha_eq
  · rw [injective_iff_map_eq_zero] at hinj
    push_neg at hinj
    rcases hinj with ⟨u2, hu2_ker, hu2_ne⟩
    have hu2_dot : ∀ v ∈ V, dot u2.1 v = 0 := fun v hv => by
      have := LinearMap.congr_fun hu2_ker ⟨v, hv⟩
      exact this
    have hex_u1 : ∃ u1 : U, LinearIndependent ℂ ![u1.1, u2.1] := by
      have hne_span : Submodule.span ℂ {u2} ≠ ⊤ := by
        intro htop
        have h1 : Module.finrank ℂ (Submodule.span ℂ {u2}) = 1 := finrank_span_singleton hu2_ne
        rw [htop, finrank_top, hU_dim] at h1
        omega
      obtain ⟨u1, hu1_not⟩ : ∃ u1 : U, u1 ∉ Submodule.span ℂ {u2} := by
        by_contra h
        push_neg at h
        apply hne_span
        rw [eq_top_iff]; intro x _; exact h x
      refine ⟨u1, ?_⟩
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hcU : c 0 • u1 + c 1 • u2 = 0 := by
        apply Subtype.ext; simpa [Fin.sum_univ_two] using hc
      have hc0 : c 0 = 0 := by
        by_contra h0
        have hu1_eq : u1 = (-(c 1 / c 0)) • u2 := by
          have hneg : c 0 • u1 = -(c 1 • u2) := eq_neg_of_add_eq_zero_left hcU
          calc u1 = (c 0)⁻¹ • (c 0 • u1) := by rw [inv_smul_smul₀ h0]
            _ = (c 0)⁻¹ • (-(c 1 • u2)) := by rw [hneg]
            _ = (-(c 1 / c 0)) • u2 := by rw [smul_neg, smul_smul, ← neg_smul]; congr 1; ring
        apply hu1_not
        rw [Submodule.mem_span_singleton]
        exact ⟨-(c 1 / c 0), hu1_eq.symm⟩
      rw [hc0, zero_smul, zero_add] at hcU
      have hc1 : c 1 = 0 := (smul_eq_zero.mp hcU).resolve_right hu2_ne
      intro i; fin_cases i <;> assumption
    rcases hex_u1 with ⟨u1, hindU⟩
    have hht := had_triple_linindep U hU_H0 hU_iso u1.1 u2.1 u1.2 u2.2 hindU
    have hpol := e4_cross_polar L hL U V hU (fun v hv => hv) (fun u hu => hU_iso u hu u hu)
      (fun v hv => hV_iso v hv v hv)
    have hmem12 : had u1.1 u2.1 ∈ perpH0 (sqSpan V) := by
      refine ⟨sqSpan_le_H0 U hU_iso (Submodule.subset_span ⟨u1.1, u1.2, u2.1, u2.2, rfl⟩), fun w hw => ?_⟩
      refine Submodule.span_induction (p := fun w _ => dot (had u1.1 u2.1) w = 0) ?_ ?_ ?_ ?_ hw
      · rintro z ⟨v1, hv1, v2, hv2, rfl⟩
        have hp := hpol u1.1 u2.1 u1.2 u2.2 v1 v2 hv1 hv2
        rw [hu2_dot v1 hv1, hu2_dot v2 hv2] at hp
        linear_combination hp / 6
      · simp [dot]
      · intro x y _ _ hx hy
        unfold dot at hx hy ⊢
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        rw [hx, hy, add_zero]
      · intro c x _ hx
        have : dot (had u1.1 u2.1) (c • x) = c * dot (had u1.1 u2.1) x := by
          simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [this, hx, mul_zero]
    have hmem22 : had u2.1 u2.1 ∈ perpH0 (sqSpan V) := by
      refine ⟨sqSpan_le_H0 U hU_iso (Submodule.subset_span ⟨u2.1, u2.2, u2.1, u2.2, rfl⟩), fun w hw => ?_⟩
      refine Submodule.span_induction (p := fun w _ => dot (had u2.1 u2.1) w = 0) ?_ ?_ ?_ ?_ hw
      · rintro z ⟨v1, hv1, v2, hv2, rfl⟩
        have hp := hpol u2.1 u2.1 u2.2 u2.2 v1 v2 hv1 hv2
        rw [hu2_dot v1 hv1, hu2_dot v2 hv2] at hp
        linear_combination hp / 6
      · simp [dot]
      · intro x y _ _ hx hy
        unfold dot at hx hy ⊢
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        rw [hx, hy, add_zero]
      · intro c x _ hx
        have : dot (had u2.1 u2.1) (c • x) = c * dot (had u2.1 u2.1) x := by
          simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [this, hx, mul_zero]
    let g : Fin 2 → perpH0 (sqSpan V) := ![⟨had u1.1 u2.1, hmem12⟩, ⟨had u2.1 u2.1, hmem22⟩]
    have hgi : LinearIndependent ℂ g := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hc' : ∑ i : Fin 3, ![0, c 0, c 1] i • ![had u1.1 u1.1, had u1.1 u2.1, had u2.1 u2.1] i = 0 := by
        have := congrArg Subtype.val hc
        simpa [Fin.sum_univ_three, Fin.sum_univ_two, g] using this
      have h0 := Fintype.linearIndependent_iff.mp hht ![0, c 0, c 1] hc'
      intro i
      fin_cases i
      · exact h0 1
      · exact h0 2
    have hle2 : 2 ≤ Module.finrank ℂ (perpH0 (sqSpan V)) := by
      simpa using hgi.fintype_card_le_finrank
    have hsqV_dim : 3 ≤ Module.finrank ℂ (sqSpan V) := finrank_sqSpan_ge_three V hV_H0 hV_iso hV_dim
    have hperpV_le : Module.finrank ℂ (perpH0 (sqSpan V)) ≤ 1 := by
      have := finrank_perpH0_add (sqSpan V) (sqSpan_le_H0 V hV_iso)
      omega
    omega
