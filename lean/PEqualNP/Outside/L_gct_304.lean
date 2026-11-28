import PEqualNP.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.NormNum.Prime

namespace PEqualNP.Outside.L_gct_304_aux

namespace Sub142
theorem coord_zero (n : ℕ) (W : Submodule ℂ (Fin n → ℂ))
    (hW : ∀ w ∈ W, ∏ i, (1 + w i) + ∏ i, (1 - w i) = 2)
    (u : Fin n → ℂ) (hu : u ∈ W) (k : Fin n) (huk : u k ≠ 0)
    (z : Fin n → ℂ) (hz : z ∈ W) (hzk : z k = 0) : z = 0 := by
  by_contra hne
  obtain ⟨i0, hi0⟩ : ∃ i0, z i0 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext hall)
  set w0 : Fin n → ℂ := (-1 / u k) • u with hw0
  set s : ℂ := (1 - w0 i0) / z i0 with hs
  have hw : w0 + s • z ∈ W := W.add_mem (W.smul_mem _ hu) (W.smul_mem _ hz)
  have e := hW _ hw
  have hA : ∏ i, (1 + (w0 + s • z) i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp only [hw0, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hzk, mul_zero, add_zero]
    field_simp
    ring
  have hB : ∏ i, (1 - (w0 + s • z) i) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i0)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs]
    field_simp
    ring
  rw [hA, hB] at e
  norm_num at e

end Sub142
namespace Sub286

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


set_option maxHeartbeats 800000 in
theorem main :
  ∀ (L : Submodule ℂ (Fin 4 → Fin 5 → ℂ)) (U : Submodule ℂ (Fin 5 → ℂ)),
  (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120) →
  (∀ u ∈ U, (![u, -u, 0, 0] : Fin 4 → Fin 5 → ℂ) ∈ L) →
  2 ≤ Module.finrank ℂ U → Module.finrank ℂ L ≤ 4 := by
  intro L U hL hU hU2
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
end Sub286
namespace Sub303
open Finset Module
noncomputable section
abbrev V := Fin 5 → ℂ
def HH (U : Submodule ℂ V) : Prop := ∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^3) = 0
def Concl (U : Submodule ℂ V) : Prop :=
  ∃ π : Equiv.Perm (Fin 5),
      (∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
        u (π j) = (![s, -s, t, -t, 0] : Fin 5 → ℂ) j) ∨
      (∃ z : ℂ, IsPrimitiveRoot z 5 ∧
        ∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
          u (π j) = s * z^j.val + t * z^(4*j.val))
variable {U : Submodule ℂ V}
lemma fS (H : HH U) (π : Equiv.Perm (Fin 5)) {u : V} (hu : u ∈ U) :
    u (π 0) + u (π 1) + u (π 2) + u (π 3) + u (π 4) = 0 := by
  have h := (H u hu).1
  rw [← Equiv.sum_comp π u] at h
  simpa [Fin.sum_univ_five] using h
lemma fC (H : HH U) (π : Equiv.Perm (Fin 5)) {u : V} (hu : u ∈ U) :
    u (π 0)^3 + u (π 1)^3 + u (π 2)^3 + u (π 3)^3 + u (π 4)^3 = 0 := by
  have h := (H u hu).2
  rw [← Equiv.sum_comp π (fun j => u j ^ 3)] at h
  simpa [Fin.sum_univ_five] using h
lemma pol (H : HH U) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    (∑ j, x j ^ 2 * y j) = 0 := by
  have h1 := (H (x + y) (U.add_mem hx hy)).2
  have h2 := (H (x - y) (U.sub_mem hx hy)).2
  have h3 := (H y hy).2
  simp only [Pi.add_apply, Pi.sub_apply, Fin.sum_univ_five] at h1 h2 h3 ⊢
  linear_combination (h1 - h2 - 2 * h3) / 6
lemma fP (H : HH U) (π : Equiv.Perm (Fin 5)) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x (π 0)^2 * y (π 0) + x (π 1)^2 * y (π 1) + x (π 2)^2 * y (π 2) +
      x (π 3)^2 * y (π 3) + x (π 4)^2 * y (π 4) = 0 := by
  have h := pol H hx hy
  rw [← Equiv.sum_comp π (fun j => x j ^ 2 * y j)] at h
  simpa [Fin.sum_univ_five] using h
lemma GP (H : HH U) (π : Equiv.Perm (Fin 5)) {x y : V} (hx : x ∈ U) (hy : y ∈ U)
    (x0 : x (π 0) = 1) (x1 : x (π 1) = -1) (x2 : x (π 2) = 0) (x3 : x (π 3) = 0)
    (x4 : x (π 4) = 0) (y0 : y (π 0) = 0) (y1 : y (π 1) = 0) (y2 : y (π 2) = 1)
    (y3 : y (π 3) = -1) (y4 : y (π 4) = 0) : Concl U := by
  refine ⟨π, Or.inl fun u => ⟨fun hu => ?_, fun ⟨s, t, h⟩ => ?_⟩⟩
  · have p1 := fP H π hx hu
    have p2 := fP H π hy hu
    have p3 := fS H π hu
    rw [x0, x1, x2, x3, x4] at p1
    rw [y0, y1, y2, y3, y4] at p2
    refine ⟨u (π 0), u (π 2), fun j => ?_⟩
    fin_cases j <;> simp <;> first | linear_combination p1 | linear_combination p2 | linear_combination p3 - p1 - p2
  · have e : u = s • x + t • y := by
      funext k
      obtain ⟨j, rfl⟩ := π.surjective k
      rw [h j]
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4]
    rw [e]
    exact U.add_mem (U.smul_mem _ hx) (U.smul_mem _ hy)
lemma GF (H : HH U) (π : Equiv.Perm (Fin 5)) (z : ℂ) (hz : IsPrimitiveRoot z 5)
    (hd : finrank ℂ U ≤ 2) {x y : V} (hx : x ∈ U) (hy : y ∈ U)
    (x0 : x (π 0) = 2) (x1 : x (π 1) = z + z^4) (x2 : x (π 2) = z^2 + z^3)
    (x3 : x (π 3) = z^3 + z^2) (x4 : x (π 4) = z^4 + z)
    (y0 : y (π 0) = 0) (y1 : y (π 1) = z - z^4) (y2 : y (π 2) = z^2 - z^3)
    (y3 : y (π 3) = z^3 - z^2) (y4 : y (π 4) = z^4 - z) : Concl U := by
  have h5 : z ^ 5 = 1 := hz.pow_eq_one
  have e8 : z ^ 8 = z ^ 3 := by linear_combination z^3 * h5
  have e12 : z ^ 12 = z ^ 2 := by linear_combination (z^7 + z^2) * h5
  have e16 : z ^ 16 = z := by linear_combination (z^11 + z^6 + z) * h5
  refine ⟨π, Or.inr ⟨z, hz, fun u => ⟨fun hu => ?_, fun ⟨s, t, h⟩ => ?_⟩⟩⟩
  · have hne : z - z ^ 4 ≠ 0 := by
      intro e
      have hz0 : z ≠ 0 := hz.ne_zero (by norm_num)
      have e3 : z ^ 3 = 1 := by
        have : z * (z ^ 3 - 1) = 0 := by linear_combination -e
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hz0
        · linear_combination h
      exact hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) e3
    have hind : LinearIndependent ℂ ![x, y] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have a0 := congrFun hst (π 0)
      have a1 := congrFun hst (π 1)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, x0, y0, x1, y1] at a0 a1
      have hs : s = 0 := by linear_combination a0 / 2
      subst hs
      refine ⟨rfl, ?_⟩
      have : t * (z - z ^ 4) = 0 := by linear_combination a1
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h hne
    have hsp : Submodule.span ℂ (Set.range ![x, y]) = U := by
      apply Submodule.eq_of_le_of_finrank_le
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        fin_cases i
        · exact hx
        · exact hy
      · rw [finrank_span_eq_card hind]; simpa using hd
    rw [← hsp, Submodule.mem_span_range_iff_exists_fun] at hu
    obtain ⟨c, hc⟩ := hu
    refine ⟨c 0 + c 1, c 0 - c 1, fun j => ?_⟩
    rw [← hc]
    fin_cases j <;> simp [Fin.sum_univ_two, x0, x1, x2, x3, x4, y0, y1, y2, y3, y4,
      e8, e12, e16] <;> ring
  · have e : u = ((s + t) / 2) • x + ((s - t) / 2) • y := by
      funext k
      obtain ⟨j, rfl⟩ := π.surjective k
      rw [h j]
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4, e8, e12, e16] <;> ring
    rw [e]
    exact U.add_mem (U.smul_mem _ hx) (U.smul_mem _ hy)
lemma rev (U : Submodule ℂ V) (h : Concl U) : HH U := by
  obtain ⟨π, h⟩ := h
  intro u hu
  rw [← Equiv.sum_comp π u, ← Equiv.sum_comp π (fun j => u j ^ 3)]
  rcases h with h | ⟨z, hz, h⟩
  · obtain ⟨s, t, h⟩ := (h u).1 hu
    simp only [Fin.sum_univ_five, h]
    constructor <;> simp <;> ring
  · obtain ⟨s, t, h⟩ := (h u).1 hu
    have h5 : z ^ 5 = 1 := hz.pow_eq_one
    have e8 : z ^ 8 = z ^ 3 := by linear_combination z^3 * h5
    have e12 : z ^ 12 = z ^ 2 := by linear_combination (z^7 + z^2) * h5
    have e16 : z ^ 16 = z := by linear_combination (z^11 + z^6 + z) * h5
    have geo : 1 + z + z^2 + z^3 + z^4 = 0 := by
      have := hz.geom_sum_eq_zero (by norm_num : 1 < 5)
      simpa [Finset.sum_range_succ, add_assoc] using this
    simp only [Fin.sum_univ_five, h]
    simp [e8, e12, e16]
    constructor
    · linear_combination (s + t) * geo
    · linear_combination (s + t)^3 * geo + (3*z^1*s^2*t^1 + 3*z^4*s^1*t^2 + 1*z^7*s^0*t^3 +
        1*z^1*s^3*t^0 + 3*z^2*s^2*t^1 + 3*z^3*s^1*t^2 + 1*z^4*s^0*t^3 + 1*z^4*s^3*t^0 +
        3*z^3*s^2*t^1 + 3*z^2*s^1*t^2 + 1*z^1*s^0*t^3 + 1*z^7*s^3*t^0 + 3*z^4*s^2*t^1 +
        3*z^1*s^1*t^2 + 1*z^2*s^0*t^3 + 1*z^2*s^3*t^0) * h5
def mk5 (f g : Fin 5 → Fin 5) (h1 : ∀ i, g (f i) = i) (h2 : ∀ i, f (g i) = i) :
    Equiv.Perm (Fin 5) := ⟨f, g, h1, h2⟩
lemma mk5_apply (f g : Fin 5 → Fin 5) (h1 h2) (i : Fin 5) : mk5 f g h1 h2 i = f i := rfl
lemma tA0p (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (b : ℂ) (w0 : w (π 0) = 0) (w1 : w (π 1) = -0) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hb : b ≠ 0) (v : V) (hv : v ∈ U) (r : ℂ)
    (v0 : v (π 0) = 0) (v1 : v (π 1) = -1) (v2 : v (π 2) = r) (v3 : v (π 3) = -r)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![4,1,2,3,0] ![4,1,2,3,0] (by decide) (by decide))
    (x := v - r • (b⁻¹ • w)) (y := b⁻¹ • w)
    (U.sub_mem hv (U.smul_mem _ (U.smul_mem _ hw))) (U.smul_mem _ hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, hb]
lemma tA0q (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (b : ℂ) (w0 : w (π 0) = 0) (w1 : w (π 1) = -0) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hb : b ≠ 0) (v : V) (hv : v ∈ U) (r : ℂ)
    (v0 : v (π 0) = -1) (v1 : v (π 1) = 0) (v2 : v (π 2) = r) (v3 : v (π 3) = -r)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![0,4,2,3,1] ![0,4,2,3,1] (by decide) (by decide))
    (x := r • (b⁻¹ • w) - v) (y := b⁻¹ • w)
    (U.sub_mem (U.smul_mem _ (U.smul_mem _ hw)) hv) (U.smul_mem _ hw) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, hb]
lemma tB0r (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (a : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = 0) (w3 : w (π 3) = -0)
    (w4 : w (π 4) = 0) (ha : a ≠ 0) (v : V) (hv : v ∈ U) (p : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = -p) (v2 : v (π 2) = 0) (v3 : v (π 3) = -1)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![0,1,4,3,2] ![0,1,4,3,2] (by decide) (by decide))
    (x := a⁻¹ • w) (y := v - p • (a⁻¹ • w))
    (U.smul_mem _ hw) (U.sub_mem hv (U.smul_mem _ (U.smul_mem _ hw))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, ha]
lemma tB0s (π : Equiv.Perm (Fin 5)) (H : HH U) (w : V) (hw : w ∈ U)
    (a : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = 0) (w3 : w (π 3) = -0)
    (w4 : w (π 4) = 0) (ha : a ≠ 0) (v : V) (hv : v ∈ U) (p : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = -p) (v2 : v (π 2) = -1) (v3 : v (π 3) = 0)
    (v4 : v (π 4) = 1) : Concl U := by
  refine GP H (π * mk5 ![0,1,2,4,3] ![0,1,2,4,3] (by decide) (by decide))
    (x := a⁻¹ • w) (y := p • (a⁻¹ • w) - v)
    (U.smul_mem _ hw) (U.sub_mem (U.smul_mem _ (U.smul_mem _ hw)) hv) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp [mk5_apply, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4, ha]
lemma alg1 (p q r s : ℂ) (hS : p + q + r + s + 1 = 0) (hT : r + s = 0)
    (hC : p^3 + q^3 + r^3 + s^3 + 1 = 0) : p = 0 ∨ q = 0 := by
  have hs : s = -r := by linear_combination hT
  subst hs
  have hq : q = -1 - p := by linear_combination hS
  subst hq
  have h : p * (-1 - p) = 0 := by linear_combination hC / 3
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl h
  · exact Or.inr h
lemma alg2 (a b p r s : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (E1 : a^2*p + a^2*p + b^2*r + b^2*s = 0) (E2 : b*r^2 - b*s^2 = 0)
    (S : p + p + r + s + 1 = 0) (C : p^3 + p^3 + r^3 + s^3 + 1 = 0) :
    r = s ∧ s = -1/2 - p ∧ 4*p^2 + 2*p - 1 = 0 ∧ (b = 2*p*a ∨ b = -(2*p*a)) := by
  have h1 : (r - s) * (r + s) = 0 := by
    have : b * ((r - s) * (r + s)) = 0 := by linear_combination E2
    exact (mul_eq_zero.1 this).resolve_left hb
  rcases mul_eq_zero.1 h1 with h | h
  · have hrs : r = s := by linear_combination h
    subst hrs
    have hs : r = -1/2 - p := by linear_combination S / 2
    subst hs
    have hQ : 4*p^2 + 2*p - 1 = 0 := by linear_combination (-4/3) * C
    refine ⟨rfl, rfl, hQ, ?_⟩
    have e : (b - 2*p*a) * (b + 2*p*a) * (1/2 + p) = 0 := by
      linear_combination (-1/2) * E1 - a^2 * p * hQ
    have hp : (1/2 + p) ≠ 0 := by
      intro e2
      have : p = -1/2 := by linear_combination e2
      subst this; norm_num at hQ
    rcases mul_eq_zero.1 ((mul_eq_zero.1 e).resolve_right hp) with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · exfalso
    have : a^2 = 0 := by linear_combination -E1 + a^2 * S + (b^2 - a^2) * h
    exact ha (pow_eq_zero_iff (by norm_num) |>.1 this)
lemma CaseBgen (π : Equiv.Perm (Fin 5)) (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U)
    (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (ha : a ≠ 0) (hb : b ≠ 0) (v : V) (hv : v ∈ U) (p r s : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = p) (v2 : v (π 2) = r) (v3 : v (π 3) = s)
    (v4 : v (π 4) = 1) : Concl U := by
  have E1 := fP H π hw hv
  have E2 := fP H π hv hw
  have S := fS H π hv
  have C := fC H π hv
  rw [w0, w1, w2, w3, w4, v0, v1, v2, v3, v4] at E1 E2
  rw [v0, v1, v2, v3, v4] at S C
  obtain ⟨hrs, hs, hQ, hb'⟩ := alg2 a b p r s ha hb (by linear_combination E1)
    (by linear_combination E2) (by linear_combination S) (by linear_combination C)
  obtain ⟨d, hd2⟩ := IsAlgClosed.exists_pow_nat_eq (p^2 - 1) (by norm_num : 0 < 2)
  have hzq : (p + d)^2 - 2*p*(p + d) + 1 = 0 := by linear_combination hd2
  generalize p + d = z at hzq
  have geo : 1 + z + z^2 + z^3 + z^4 = 0 := by
    linear_combination (z^2 + (1 + 2*p)*z + 2*p*(1 + 2*p)) * hzq + (2*p*z - 1) * hQ
  have h5 : z ^ 5 = 1 := by linear_combination (z - 1) * geo
  have hz1 : z ≠ 1 := by
    intro e; subst e; norm_num at geo
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hz : IsPrimitiveRoot z 5 := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime h5 hz1)
  have hm2 : 2*p = z + z^4 := by linear_combination (-z^4) * hzq + (z - 2*p) * h5
  have hca : ((z - z^4) * a⁻¹) * a = z - z^4 := by field_simp
  rcases hb' with hb' | hb'
  · refine GF H (π * mk5 ![4,0,2,3,1] ![1,4,2,3,0] (by decide) (by decide)) z hz hd
      (x := (2:ℂ) • v) (y := ((z - z^4) * a⁻¹) • w) (U.smul_mem _ hv) (U.smul_mem _ hw)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [mk5_apply, Equiv.Perm.mul_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4]
    · norm_num
    · linear_combination hm2
    · linear_combination 2 * hrs + 2 * hs - hm2 - geo
    · linear_combination 2 * hs - hm2 - geo
    · linear_combination hm2
    · ring
    · linear_combination hca
    · linear_combination ((z - z^4) * a⁻¹) * hb' + 2*p*hca + (z - z^4)*hm2 - z^3*h5
    · linear_combination -(((z - z^4) * a⁻¹) * hb' + 2*p*hca + (z - z^4)*hm2 - z^3*h5)
    · linear_combination -hca
  · refine GF H (π * mk5 ![4,0,3,2,1] ![1,4,3,2,0] (by decide) (by decide)) z hz hd
      (x := (2:ℂ) • v) (y := ((z - z^4) * a⁻¹) • w) (U.smul_mem _ hv) (U.smul_mem _ hw)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp only [mk5_apply, Equiv.Perm.mul_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, w0, w1, w2, w3, w4, v0, v1, v2, v3, v4]
    · norm_num
    · linear_combination hm2
    · linear_combination 2 * hs - hm2 - geo
    · linear_combination 2 * hrs + 2 * hs - hm2 - geo
    · linear_combination hm2
    · ring
    · linear_combination hca
    · linear_combination -((z - z^4) * a⁻¹) * hb' + 2*p*hca + (z - z^4)*hm2 - z^3*h5
    · linear_combination ((z - z^4) * a⁻¹) * hb' - (2*p*hca + (z - z^4)*hm2 - z^3*h5)
    · linear_combination -hca
lemma CaseB1 (π : Equiv.Perm (Fin 5)) (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U)
    (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hne : a ≠ 0 ∨ b ≠ 0) (v : V) (hv : v ∈ U) (p q r s : ℂ)
    (v0 : v (π 0) = p) (v1 : v (π 1) = q) (v2 : v (π 2) = r) (v3 : v (π 3) = s)
    (v4 : v (π 4) = 1) : Concl U := by
  have E1 := fP H π hw hv
  have S := fS H π hv
  have C := fC H π hv
  rw [w0, w1, w2, w3, w4, v0, v1, v2, v3, v4] at E1
  rw [v0, v1, v2, v3, v4] at S C
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    have hb : b ≠ 0 := hne.resolve_left (by simp)
    have hrs : r + s = 0 := by
      have : b^2 * (r + s) = 0 := by linear_combination E1
      exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hb)
    rcases alg1 p q r s (by linear_combination S) hrs (by linear_combination C) with hp | hq
    · exact tA0p π H w hw b w0 w1 w2 w3 w4 hb v hv r (v0.trans hp)
        (by rw [v1]; linear_combination S - hp - hrs) v2 (by rw [v3]; linear_combination hrs) v4
    · exact tA0q π H w hw b w0 w1 w2 w3 w4 hb v hv r
        (by rw [v0]; linear_combination S - hq - hrs) (v1.trans hq) v2
        (by rw [v3]; linear_combination hrs) v4
  · by_cases hb : b = 0
    · subst hb
      have hpq : p + q = 0 := by
        have : a^2 * (p + q) = 0 := by linear_combination E1
        exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ ha)
      rcases alg1 r s p q (by linear_combination S) hpq (by linear_combination C) with hr | hs
      · exact tB0r π H w hw a w0 w1 w2 w3 w4 ha v hv p v0
          (by rw [v1]; linear_combination hpq) (v2.trans hr)
          (by rw [v3]; linear_combination S - hr - hpq) v4
      · exact tB0s π H w hw a w0 w1 w2 w3 w4 ha v hv p v0
          (by rw [v1]; linear_combination hpq)
          (by rw [v2]; linear_combination S - hs - hpq) (v3.trans hs) v4
    · have hvU : v + ((q - p) / (2 * a)) • w ∈ U := U.add_mem hv (U.smul_mem _ hw)
      refine CaseBgen π H hd w hw a b w0 w1 w2 w3 w4 ha hb _ hvU
        (p + (q - p) / (2 * a) * a) (r + (q - p) / (2 * a) * b) (s + (q - p) / (2 * a) * (-b))
        ?_ ?_ ?_ ?_ ?_
      all_goals simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w0, w1, w2, w3, w4,
        v0, v1, v2, v3, v4]
      · field_simp; ring
      · simp
lemma CaseB (π : Equiv.Perm (Fin 5)) (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U)
    (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a) (w2 : w (π 2) = b) (w3 : w (π 3) = -b)
    (w4 : w (π 4) = 0) (hne : a ≠ 0 ∨ b ≠ 0) (v : V) (hv : v ∈ U) (hv4 : v (π 4) ≠ 0) :
    Concl U := by
  have hvU : (v (π 4))⁻¹ • v ∈ U := U.smul_mem _ hv
  exact CaseB1 π H hd w hw a b w0 w1 w2 w3 w4 hne _ hvU _ _ _ _ rfl rfl rfl rfl
    (by simp [hv4])
lemma CaseA (π : Equiv.Perm (Fin 5)) (H : HH U) (x : V) (hx : x ∈ U)
    (a b : ℂ) (x0 : x (π 0) = a) (x1 : x (π 1) = -a) (x2 : x (π 2) = b) (x3 : x (π 3) = -b)
    (x4 : x (π 4) = 0) (y : V) (hy : y ∈ U)
    (a' b' : ℂ) (y0 : y (π 0) = a') (y1 : y (π 1) = -a') (y2 : y (π 2) = b') (y3 : y (π 3) = -b')
    (y4 : y (π 4) = 0) (hind : ∀ s t : ℂ, s • x + t • y = 0 → s = 0 ∧ t = 0) : Concl U := by
  have hdet : a * b' - a' * b ≠ 0 := by
    intro hd0
    have k1 := hind b' (-b) (by
      funext k; obtain ⟨j, rfl⟩ := π.surjective k
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4] <;>
        first | linear_combination hd0 | linear_combination -hd0 | ring)
    have k2 := hind a' (-a) (by
      funext k; obtain ⟨j, rfl⟩ := π.surjective k
      fin_cases j <;> simp [x0, x1, x2, x3, x4, y0, y1, y2, y3, y4] <;>
        first | linear_combination hd0 | linear_combination -hd0 | ring)
    have hb : b = 0 := by linear_combination -k1.2
    have ha : a = 0 := by linear_combination -k2.2
    have k3 := hind 1 0 (by
      funext k; obtain ⟨j, rfl⟩ := π.surjective k
      fin_cases j <;> simp [x0, x1, x2, x3, x4, ha, hb])
    exact one_ne_zero k3.1
  refine GP H π (x := (a * b' - a' * b)⁻¹ • (b' • x - b • y))
    (y := (a * b' - a' * b)⁻¹ • (a • y - a' • x))
    (U.smul_mem _ (U.sub_mem (U.smul_mem _ hx) (U.smul_mem _ hy)))
    (U.smul_mem _ (U.sub_mem (U.smul_mem _ hy) (U.smul_mem _ hx))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, x0, x1, x2, x3, x4,
    y0, y1, y2, y3, y4]
  all_goals field_simp
  all_goals ring
lemma fac (H : HH U) {x : V} (hx : x ∈ U) (x4 : x 4 = 0) :
    (x 0 + x 1) * (x 0 + x 2) * (x 0 + x 3) = 0 := by
  have S := (H x hx).1
  have C := (H x hx).2
  simp only [Fin.sum_univ_five, x4] at S C
  have h3 : x 3 = -(x 0 + x 1 + x 2) := by linear_combination S
  rw [h3] at C ⊢
  linear_combination C / 3
lemma two {α β : ℂ} (l m : ℂ) (hlm : l ≠ m) (h1 : α + l * β = 0) (h2 : α + m * β = 0) :
    α = 0 ∧ β = 0 := by
  have hb : β = 0 := by
    have : (l - m) * β = 0 := by linear_combination h1 - h2
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hlm)
  subst hb
  exact ⟨by linear_combination h1, rfl⟩
lemma pig (α1 β1 α2 β2 α3 β3 : ℂ)
    (F : ∀ l : ℂ, (α1 + l * β1) * (α2 + l * β2) * (α3 + l * β3) = 0) :
    (α1 = 0 ∧ β1 = 0) ∨ (α2 = 0 ∧ β2 = 0) ∨ (α3 = 0 ∧ β3 = 0) := by
  have e0 := F 0
  have e1 := F 1
  have e2 := F 2
  have e3 := F 3
  simp only [mul_eq_zero] at e0 e1 e2 e3
  rcases e0 with (a0 | b0) | c0 <;> rcases e1 with (a1 | b1) | c1 <;>
    rcases e2 with (a2 | b2) | c2 <;> rcases e3 with (a3 | b3) | c3 <;>
    first
    | exact Or.inl (two 0 1 (by norm_num) a0 a1)
    | exact Or.inl (two 0 2 (by norm_num) a0 a2)
    | exact Or.inl (two 0 3 (by norm_num) a0 a3)
    | exact Or.inl (two 1 2 (by norm_num) a1 a2)
    | exact Or.inl (two 1 3 (by norm_num) a1 a3)
    | exact Or.inl (two 2 3 (by norm_num) a2 a3)
    | exact Or.inr (Or.inl (two 0 1 (by norm_num) b0 b1))
    | exact Or.inr (Or.inl (two 0 2 (by norm_num) b0 b2))
    | exact Or.inr (Or.inl (two 0 3 (by norm_num) b0 b3))
    | exact Or.inr (Or.inl (two 1 2 (by norm_num) b1 b2))
    | exact Or.inr (Or.inl (two 1 3 (by norm_num) b1 b3))
    | exact Or.inr (Or.inl (two 2 3 (by norm_num) b2 b3))
    | exact Or.inr (Or.inr (two 0 1 (by norm_num) c0 c1))
    | exact Or.inr (Or.inr (two 0 2 (by norm_num) c0 c2))
    | exact Or.inr (Or.inr (two 0 3 (by norm_num) c0 c3))
    | exact Or.inr (Or.inr (two 1 2 (by norm_num) c1 c2))
    | exact Or.inr (Or.inr (two 1 3 (by norm_num) c1 c3))
    | exact Or.inr (Or.inr (two 2 3 (by norm_num) c2 c3))
lemma killG {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (X : Submodule ℂ M) {n : ℕ} (φ : M →ₗ[ℂ] (Fin n → ℂ)) (h : n < finrank ℂ X) :
    ∃ v ∈ X, v ≠ 0 ∧ φ v = 0 := by
  let ψ := φ.domRestrict X
  have h1 := LinearMap.finrank_range_add_finrank_ker ψ
  have h2 : finrank ℂ (LinearMap.range ψ) ≤ n := by
    have := Submodule.finrank_le (LinearMap.range ψ); simpa using this
  have h3 : LinearMap.ker ψ ≠ ⊥ := by
    intro e; rw [e, finrank_bot] at h1; omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  refine ⟨w.1, w.2, fun e => hw0 (Subtype.ext e), ?_⟩
  have : ψ w = 0 := hw
  simpa [ψ] using this
def Q12 : Equiv.Perm (Fin 5) := mk5 ![0,2,1,3,4] ![0,2,1,3,4] (by decide) (by decide)
def Q13 : Equiv.Perm (Fin 5) := mk5 ![0,3,2,1,4] ![0,3,2,1,4] (by decide) (by decide)
lemma nzf (π : Equiv.Perm (Fin 5)) (w : V) (a b : ℂ) (w0 : w (π 0) = a) (w1 : w (π 1) = -a)
    (w2 : w (π 2) = b) (w3 : w (π 3) = -b) (w4 : w (π 4) = 0) (hw : w ≠ 0) :
    a ≠ 0 ∨ b ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  funext k
  obtain ⟨j, rfl⟩ := π.surjective k
  fin_cases j <;> simp [w0, w1, w2, w3, w4, h.1, h.2]
lemma topB (H : HH U) (hd : finrank ℂ U ≤ 2) (w : V) (hw : w ∈ U) (hw0 : w ≠ 0)
    (w4 : w 4 = 0) (v : V) (hv : v ∈ U) (hv4 : v 4 ≠ 0) : Concl U := by
  have S := (H w hw).1
  simp only [Fin.sum_univ_five, w4] at S
  rcases mul_eq_zero.1 (fac H hw w4) with h | h
  · rcases mul_eq_zero.1 h with h | h
    · have w0 : w ((1 : Equiv.Perm (Fin 5)) 0) = w 0 := rfl
      have w1 : w ((1 : Equiv.Perm (Fin 5)) 1) = -(w 0) := by
        show w 1 = _; linear_combination h
      have w2 : w ((1 : Equiv.Perm (Fin 5)) 2) = w 2 := rfl
      have w3 : w ((1 : Equiv.Perm (Fin 5)) 3) = -(w 2) := by
        show w 3 = _; linear_combination S - h
      have w4' : w ((1 : Equiv.Perm (Fin 5)) 4) = 0 := w4
      exact CaseB 1 H hd w hw _ _ w0 w1 w2 w3 w4' (nzf 1 w _ _ w0 w1 w2 w3 w4' hw0) v hv hv4
    · have w0 : w (Q12 0) = w 0 := rfl
      have w1 : w (Q12 1) = -(w 0) := by
        show w 2 = _; linear_combination h
      have w2 : w (Q12 2) = w 1 := rfl
      have w3 : w (Q12 3) = -(w 1) := by
        show w 3 = _; linear_combination S - h
      have w4' : w (Q12 4) = 0 := w4
      exact CaseB Q12 H hd w hw _ _ w0 w1 w2 w3 w4' (nzf Q12 w _ _ w0 w1 w2 w3 w4' hw0) v hv hv4
  · have w0 : w (Q13 0) = w 0 := rfl
    have w1 : w (Q13 1) = -(w 0) := by
      show w 3 = _; linear_combination h
    have w2 : w (Q13 2) = w 2 := rfl
    have w3 : w (Q13 3) = -(w 2) := by
      show w 1 = _; linear_combination S - h
    have w4' : w (Q13 4) = 0 := w4
    exact CaseB Q13 H hd w hw _ _ w0 w1 w2 w3 w4' (nzf Q13 w _ _ w0 w1 w2 w3 w4' hw0) v hv hv4
lemma topA (H : HH U) (x : V) (hx : x ∈ U) (x4 : x 4 = 0) (y : V) (hy : y ∈ U) (y4 : y 4 = 0)
    (hind : ∀ s t : ℂ, s • x + t • y = 0 → s = 0 ∧ t = 0) : Concl U := by
  have Sx := (H x hx).1
  have Sy := (H y hy).1
  simp only [Fin.sum_univ_five, x4, y4] at Sx Sy
  have F : ∀ l : ℂ, ((x 0 + x 1) + l * (y 0 + y 1)) * ((x 0 + x 2) + l * (y 0 + y 2)) *
      ((x 0 + x 3) + l * (y 0 + y 3)) = 0 := by
    intro l
    have := fac H (U.add_mem hx (U.smul_mem l hy)) (by simp [x4, y4])
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    linear_combination this
  rcases pig _ _ _ _ _ _ F with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
  · exact CaseA 1 H x hx (x 0) (x 2) rfl (by show x 1 = _; linear_combination h) rfl
      (by show x 3 = _; linear_combination Sx - h) x4 y hy (y 0) (y 2) rfl
      (by show y 1 = _; linear_combination h') rfl
      (by show y 3 = _; linear_combination Sy - h') y4 hind
  · exact CaseA Q12 H x hx (x 0) (x 1) rfl (by show x 2 = _; linear_combination h) rfl
      (by show x 3 = _; linear_combination Sx - h) x4 y hy (y 0) (y 1) rfl
      (by show y 2 = _; linear_combination h') rfl
      (by show y 3 = _; linear_combination Sy - h') y4 hind
  · exact CaseA Q13 H x hx (x 0) (x 2) rfl (by show x 3 = _; linear_combination h) rfl
      (by show x 1 = _; linear_combination Sx - h) x4 y hy (y 0) (y 2) rfl
      (by show y 3 = _; linear_combination h') rfl
      (by show y 1 = _; linear_combination Sy - h') y4 hind
lemma fwd (U : Submodule ℂ V) (hd : 2 ≤ finrank ℂ U) (H : HH U) : Concl U := by
  obtain ⟨b0, hb0, hb00, e0⟩ :=
    killG U (LinearMap.pi ![(LinearMap.proj 4 : V →ₗ[ℂ] ℂ)]) (by omega)
  have hb04 : b0 4 = 0 := by simpa using congrFun e0 0
  obtain ⟨k, hk⟩ : ∃ k, b0 k ≠ 0 := by
    by_contra h; push_neg at h; exact hb00 (funext h)
  by_cases hA : ∃ b1 ∈ U, b1 ≠ 0 ∧ b1 4 = 0 ∧ b1 k = 0
  · obtain ⟨b1, hb1, hb10, hb14, hb1k⟩ := hA
    refine topA H b0 hb0 hb04 b1 hb1 hb14 fun s t hst => ?_
    have e := congrFun hst k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb1k, mul_zero, add_zero,
      Pi.zero_apply] at e
    have hs : s = 0 := (mul_eq_zero.1 e).resolve_right hk
    subst hs
    refine ⟨rfl, ?_⟩
    simp only [zero_smul, zero_add, smul_eq_zero] at hst
    exact hst.resolve_right hb10
  · push_neg at hA
    have hd2 : finrank ℂ U ≤ 2 := by
      by_contra h3; push_neg at h3
      obtain ⟨b1, hb1, hb10, e⟩ := killG U (LinearMap.pi ![(LinearMap.proj 4 : V →ₗ[ℂ] ℂ),
        (LinearMap.proj k : V →ₗ[ℂ] ℂ)]) (by omega)
      exact hA b1 hb1 hb10 (by simpa using congrFun e 0) (by simpa using congrFun e 1)
    have hv : ∃ v ∈ U, v 4 ≠ 0 := by
      by_contra hv; push_neg at hv
      obtain ⟨b1, hb1, hb10, e⟩ :=
        killG U (LinearMap.pi ![(LinearMap.proj k : V →ₗ[ℂ] ℂ)]) (by omega)
      exact hA b1 hb1 hb10 (hv b1 hb1) (by simpa using congrFun e 0)
    obtain ⟨v, hv, hv4⟩ := hv
    exact topB H hd2 b0 hb0 hb00 hb04 v hv hv4
end
theorem main : ∀ U : Submodule ℂ (Fin 5 → ℂ), 2 ≤ Module.finrank ℂ U →
  ((∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^3) = 0) ↔
    ∃ π : Equiv.Perm (Fin 5),
      (∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
        u (π j) = (![s, -s, t, -t, 0] : Fin 5 → ℂ) j) ∨
      (∃ z : ℂ, IsPrimitiveRoot z 5 ∧
        ∀ u : Fin 5 → ℂ, u ∈ U ↔ ∃ s t : ℂ, ∀ j : Fin 5,
          u (π j) = s * z^j.val + t * z^(4*j.val))) := by
  intro U hd
  exact ⟨fwd U hd, rev U⟩
end Sub303
namespace Core

open Sub286
open scoped BigOperators

def ValidL (L : Submodule ℂ Mat) : Prop :=
  ∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120

def outer (a : Fin 4 → ℂ) (u : Vec) : Mat := fun i j => a i * u j

def dotMat (X Y : Mat) : ℂ := ∑ i : Fin 4, ∑ j : Fin 5, X i j * Y i j

def e4Form (X : Mat) : ℂ :=
  dot (X 0) (X 1) * dot (X 2) (X 3) +
  dot (X 0) (X 2) * dot (X 1) (X 3) +
  dot (X 0) (X 3) * dot (X 1) (X 2) -
  6 * ∑ j : Fin 5, X 0 j * X 1 j * X 2 j * X 3 j

lemma dotMat_zero (L : Submodule ℂ Mat) (hL : ValidL L) (X : Mat) (hX : X ∈ L) :
    dotMat X X = 0 := by
  have h := (mat_dot_polar L hL).1 X hX
  unfold dot at h
  unfold dotMat
  rw [Fin.sum_univ_four]
  exact h

lemma lin_dot_zero (L : Submodule ℂ Mat) (hL : ValidL L)
    (X : Mat) (hX : X ∈ L) (Y : Mat) (hY : Y ∈ L) :
    ∑ i : Fin 4, ∑ j : Fin 5, X i j * Y i j = 0 := by
  have h := (mat_dot_polar L hL).2 X hX Y hY
  unfold dot at h
  rw [Fin.sum_univ_four]
  exact h

lemma cube_sum_zero (L : Submodule ℂ Mat) (hL : ValidL L) (X : Mat) (hX : X ∈ L) :
    ∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 3 = 0 := by
  have hconst : ∀ t : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + (t • X) i (f i))) = 120 :=
    fun t => (hL (t • X) (L.smul_mem t hX)).2.2
  have he3 := (coeffs_zero_of_const X hconst).2.1
  rw [e3_eq X (hL X hX).1] at he3
  have hcol' : ∀ j : Fin 5,
      (X 0 j) ^ 3 + (X 1 j) ^ 3 + (X 2 j) ^ 3 + (X 3 j) ^ 3 =
        3 * (X 0 j * X 1 j * X 2 j + X 0 j * X 1 j * X 3 j +
          X 0 j * X 2 j * X 3 j + X 1 j * X 2 j * X 3 j) := by
    intro j
    have hc := (hL X hX).2.1 j
    rw [Fin.sum_univ_four] at hc
    have : (X 0 j + X 1 j + X 2 j + X 3 j) ^ 3 = 0 := by rw [hc]; ring
    linear_combination this -
      3 * (X 0 j * X 1 j + X 0 j * X 2 j + X 0 j * X 3 j +
           X 1 j * X 2 j + X 1 j * X 3 j + X 2 j * X 3 j) * hc
  rw [Fin.sum_univ_four]
  have hrew : (∑ j : Fin 5, (X 0 j) ^ 3) + (∑ j : Fin 5, (X 1 j) ^ 3) +
      (∑ j : Fin 5, (X 2 j) ^ 3) + (∑ j : Fin 5, (X 3 j) ^ 3) =
      ∑ j : Fin 5, ((X 0 j) ^ 3 + (X 1 j) ^ 3 + (X 2 j) ^ 3 + (X 3 j) ^ 3) := by
    simp only [Finset.sum_add_distrib]
  rw [hrew]
  simp_rw [hcol', ← Finset.mul_sum]
  linear_combination (3 / 4 : ℂ) * he3

lemma lin_d3_zero (L : Submodule ℂ Mat) (hL : ValidL L)
    (X : Mat) (hX : X ∈ L) (Y : Mat) (hY : Y ∈ L) :
    ∑ i : Fin 4, ∑ j : Fin 5, X i j * (Y i j) ^ 2 = 0 := by
  have hp := cube_sum_zero L hL (X + Y) (L.add_mem hX hY)
  have hm := cube_sum_zero L hL (X - Y) (L.sub_mem hX hY)
  have hx := cube_sum_zero L hL X hX
  have hexp : (∑ i : Fin 4, ∑ j : Fin 5, ((X + Y) i j) ^ 3) +
      (∑ i : Fin 4, ∑ j : Fin 5, ((X - Y) i j) ^ 3) -
      2 * (∑ i : Fin 4, ∑ j : Fin 5, (X i j) ^ 3) =
      6 * ∑ i : Fin 4, ∑ j : Fin 5, X i j * (Y i j) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Pi.add_apply, Pi.sub_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  linear_combination (hp + hm - 2 * hx - hexp) / 6

lemma e4Form_zero (L : Submodule ℂ Mat) (hL : ValidL L) (X : Mat) (hX : X ∈ L) :
    e4Form X = 0 := by
  have hconst : ∀ t : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + (t • X) i (f i))) = 120 :=
    fun t => (hL (t • X) (L.smul_mem t hX)).2.2
  have he4 := (coeffs_zero_of_const X hconst).2.2
  unfold e4 at he4
  rw [e4_eq (X 0) (X 1) (X 2) (X 3) ((hL X hX).1 0) ((hL X hX).1 1) ((hL X hX).1 2) ((hL X hX).1 3)] at he4
  exact he4

lemma e4Form_expand (X Y : Mat) (t : ℂ) :
    e4Form (X + t • Y) =
      e4Form X +
      t * (dot (X 0) (X 1) * (dot (X 2) (Y 3) + dot (Y 2) (X 3)) +
           (dot (X 0) (Y 1) + dot (Y 0) (X 1)) * dot (X 2) (X 3) +
           dot (X 0) (X 2) * (dot (X 1) (Y 3) + dot (Y 1) (X 3)) +
           (dot (X 0) (Y 2) + dot (Y 0) (X 2)) * dot (X 1) (X 3) +
           dot (X 0) (X 3) * (dot (X 1) (Y 2) + dot (Y 1) (X 2)) +
           (dot (X 0) (Y 3) + dot (Y 0) (X 3)) * dot (X 1) (X 2) -
           6 * ∑ j : Fin 5, (X 0 j * X 1 j * X 2 j * Y 3 j + X 0 j * X 1 j * Y 2 j * X 3 j +
             X 0 j * Y 1 j * X 2 j * X 3 j + Y 0 j * X 1 j * X 2 j * X 3 j)) +
      t ^ 2 * (dot (X 0) (X 1) * dot (Y 2) (Y 3) + dot (Y 0) (Y 1) * dot (X 2) (X 3) +
               (dot (X 0) (Y 1) + dot (Y 0) (X 1)) * (dot (X 2) (Y 3) + dot (Y 2) (X 3)) +
               dot (X 0) (X 2) * dot (Y 1) (Y 3) + dot (Y 0) (Y 2) * dot (X 1) (X 3) +
               (dot (X 0) (Y 2) + dot (Y 0) (X 2)) * (dot (X 1) (Y 3) + dot (Y 1) (X 3)) +
               dot (X 0) (X 3) * dot (Y 1) (Y 2) + dot (Y 0) (Y 3) * dot (X 1) (X 2) +
               (dot (X 0) (Y 3) + dot (Y 0) (X 3)) * (dot (X 1) (Y 2) + dot (Y 1) (X 2)) -
               6 * ∑ j : Fin 5, (X 0 j * X 1 j * Y 2 j * Y 3 j + X 0 j * Y 1 j * X 2 j * Y 3 j +
                 X 0 j * Y 1 j * Y 2 j * X 3 j + Y 0 j * X 1 j * X 2 j * Y 3 j +
                 Y 0 j * X 1 j * Y 2 j * X 3 j + Y 0 j * Y 1 j * X 2 j * X 3 j)) +
      t ^ 3 * ((dot (X 0) (Y 1) + dot (Y 0) (X 1)) * dot (Y 2) (Y 3) +
               dot (Y 0) (Y 1) * (dot (X 2) (Y 3) + dot (Y 2) (X 3)) +
               (dot (X 0) (Y 2) + dot (Y 0) (X 2)) * dot (Y 1) (Y 3) +
               dot (Y 0) (Y 2) * (dot (X 1) (Y 3) + dot (Y 1) (X 3)) +
               (dot (X 0) (Y 3) + dot (Y 0) (X 3)) * dot (Y 1) (Y 2) +
               dot (Y 0) (Y 3) * (dot (X 1) (Y 2) + dot (Y 1) (X 2)) -
               6 * ∑ j : Fin 5, (X 0 j * Y 1 j * Y 2 j * Y 3 j + Y 0 j * X 1 j * Y 2 j * Y 3 j +
                 Y 0 j * Y 1 j * X 2 j * Y 3 j + Y 0 j * Y 1 j * Y 2 j * X 3 j)) +
      t ^ 4 * e4Form Y := by
  have hd : ∀ a b : Fin 4, dot ((X + t • Y) a) ((X + t • Y) b) =
      dot (X a) (X b) + t * (dot (X a) (Y b) + dot (Y a) (X b)) + t ^ 2 * dot (Y a) (Y b) := by
    intro a b
    simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hpt : ∀ j : Fin 5, (X a j + t * Y a j) * (X b j + t * Y b j) =
        X a j * X b j + t * (X a j * Y b j + Y a j * X b j) + t ^ 2 * (Y a j * Y b j) :=
      fun _ => by ring
    simp_rw [hpt]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h4 : ∑ j : Fin 5, (X + t • Y) 0 j * (X + t • Y) 1 j * (X + t • Y) 2 j * (X + t • Y) 3 j =
      (∑ j : Fin 5, X 0 j * X 1 j * X 2 j * X 3 j) +
      t * (∑ j : Fin 5, (X 0 j * X 1 j * X 2 j * Y 3 j + X 0 j * X 1 j * Y 2 j * X 3 j +
        X 0 j * Y 1 j * X 2 j * X 3 j + Y 0 j * X 1 j * X 2 j * X 3 j)) +
      t ^ 2 * (∑ j : Fin 5, (X 0 j * X 1 j * Y 2 j * Y 3 j + X 0 j * Y 1 j * X 2 j * Y 3 j +
        X 0 j * Y 1 j * Y 2 j * X 3 j + Y 0 j * X 1 j * X 2 j * Y 3 j +
        Y 0 j * X 1 j * Y 2 j * X 3 j + Y 0 j * Y 1 j * X 2 j * X 3 j)) +
      t ^ 3 * (∑ j : Fin 5, (X 0 j * Y 1 j * Y 2 j * Y 3 j + Y 0 j * X 1 j * Y 2 j * Y 3 j +
        Y 0 j * Y 1 j * X 2 j * Y 3 j + Y 0 j * Y 1 j * Y 2 j * X 3 j)) +
      t ^ 4 * (∑ j : Fin 5, Y 0 j * Y 1 j * Y 2 j * Y 3 j) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hpt : ∀ j : Fin 5,
        (X 0 j + t * Y 0 j) * (X 1 j + t * Y 1 j) * (X 2 j + t * Y 2 j) * (X 3 j + t * Y 3 j) =
        X 0 j * X 1 j * X 2 j * X 3 j +
        t * (X 0 j * X 1 j * X 2 j * Y 3 j + X 0 j * X 1 j * Y 2 j * X 3 j +
          X 0 j * Y 1 j * X 2 j * X 3 j + Y 0 j * X 1 j * X 2 j * X 3 j) +
        t ^ 2 * (X 0 j * X 1 j * Y 2 j * Y 3 j + X 0 j * Y 1 j * X 2 j * Y 3 j +
          X 0 j * Y 1 j * Y 2 j * X 3 j + Y 0 j * X 1 j * X 2 j * Y 3 j +
          Y 0 j * X 1 j * Y 2 j * X 3 j + Y 0 j * Y 1 j * X 2 j * X 3 j) +
        t ^ 3 * (X 0 j * Y 1 j * Y 2 j * Y 3 j + Y 0 j * X 1 j * Y 2 j * Y 3 j +
          Y 0 j * Y 1 j * X 2 j * Y 3 j + Y 0 j * Y 1 j * Y 2 j * X 3 j) +
        t ^ 4 * (Y 0 j * Y 1 j * Y 2 j * Y 3 j) := fun _ => by ring
    simp_rw [hpt]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold e4Form
  rw [hd 0 1, hd 2 3, hd 0 2, hd 1 3, hd 0 3, hd 1 2, h4]
  ring

lemma lin_q4_zero (L : Submodule ℂ Mat) (hL : ValidL L)
    (X : Mat) (hX : X ∈ L) (Y : Mat) (hY : Y ∈ L) :
    (dot (X 0) (Y 1) + dot (Y 0) (X 1)) * dot (Y 2) (Y 3) +
    dot (Y 0) (Y 1) * (dot (X 2) (Y 3) + dot (Y 2) (X 3)) +
    (dot (X 0) (Y 2) + dot (Y 0) (X 2)) * dot (Y 1) (Y 3) +
    dot (Y 0) (Y 2) * (dot (X 1) (Y 3) + dot (Y 1) (X 3)) +
    (dot (X 0) (Y 3) + dot (Y 0) (X 3)) * dot (Y 1) (Y 2) +
    dot (Y 0) (Y 3) * (dot (X 1) (Y 2) + dot (Y 1) (X 2)) -
    6 * ∑ j : Fin 5, (X 0 j * Y 1 j * Y 2 j * Y 3 j + Y 0 j * X 1 j * Y 2 j * Y 3 j +
      Y 0 j * Y 1 j * X 2 j * Y 3 j + Y 0 j * Y 1 j * Y 2 j * X 3 j) = 0 := by
  have ht : ∀ t : ℂ, e4Form (X + t • Y) = 0 :=
    fun t => e4Form_zero L hL _ (L.add_mem hX (L.smul_mem t hY))
  have h1 := ht 1; rw [e4Form_expand] at h1
  have hm1 := ht (-1); rw [e4Form_expand] at hm1
  have h2 := ht 2; rw [e4Form_expand] at h2
  have hm2 := ht (-2); rw [e4Form_expand] at hm2
  linear_combination (h2 - hm2 - 2 * h1 + 2 * hm1) / 12

lemma quad_b4_zero (L : Submodule ℂ Mat) (hL : ValidL L)
    (X : Mat) (hX : X ∈ L) (Y : Mat) (hY : Y ∈ L) :
    dot (X 0) (X 1) * dot (Y 2) (Y 3) + dot (Y 0) (Y 1) * dot (X 2) (X 3) +
    (dot (X 0) (Y 1) + dot (Y 0) (X 1)) * (dot (X 2) (Y 3) + dot (Y 2) (X 3)) +
    dot (X 0) (X 2) * dot (Y 1) (Y 3) + dot (Y 0) (Y 2) * dot (X 1) (X 3) +
    (dot (X 0) (Y 2) + dot (Y 0) (X 2)) * (dot (X 1) (Y 3) + dot (Y 1) (X 3)) +
    dot (X 0) (X 3) * dot (Y 1) (Y 2) + dot (Y 0) (Y 3) * dot (X 1) (X 2) +
    (dot (X 0) (Y 3) + dot (Y 0) (X 3)) * (dot (X 1) (Y 2) + dot (Y 1) (X 2)) -
    6 * ∑ j : Fin 5, (X 0 j * X 1 j * Y 2 j * Y 3 j + X 0 j * Y 1 j * X 2 j * Y 3 j +
      X 0 j * Y 1 j * Y 2 j * X 3 j + Y 0 j * X 1 j * X 2 j * Y 3 j +
      Y 0 j * X 1 j * Y 2 j * X 3 j + Y 0 j * Y 1 j * X 2 j * X 3 j) = 0 := by
  have ht : ∀ t : ℂ, e4Form (X + t • Y) = 0 :=
    fun t => e4Form_zero L hL _ (L.add_mem hX (L.smul_mem t hY))
  have h0 := ht 0; rw [e4Form_expand] at h0
  have h1 := ht 1; rw [e4Form_expand] at h1
  have hm1 := ht (-1); rw [e4Form_expand] at hm1
  have h2 := ht 2; rw [e4Form_expand] at h2
  have hm2 := ht (-2); rw [e4Form_expand] at hm2
  linear_combination (16 * h1 + 16 * hm1 - h2 - hm2 - 30 * h0) / 24


lemma case_3a_eqs (w : ℂ) (hw : w^2 + w + 1 = 0)
    (L : Submodule ℂ Mat) (hL : ValidL L)
    (h0 : outer (![((1 : ℂ)), (w), (w^2), (0 : ℂ)]) (![((1 : ℂ)), (-(1 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ)]) ∈ L)
    (h1 : outer (![((1 : ℂ)), (w), (w^2), (0 : ℂ)]) (![(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (-(1 : ℂ)), (0 : ℂ)]) ∈ L)
    (X : Mat) (hX : X ∈ L) :
    (X 0 0 = (-w) * X 2 1 + (((1 : ℂ) / 2)) * X 2 2 + (((1 : ℂ) / 2)) * X 2 3 + (((1 : ℂ) / 2)) * X 2 4 + (((2 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 3 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * X 3 4) ∧
    (X 0 1 = (w) * X 2 1 + (((1 : ℂ) / 2) + w) * X 2 2 + (((1 : ℂ) / 2) + w) * X 2 3 + (((1 : ℂ) / 2) + w) * X 2 4 + (((2 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 3 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * X 3 4) ∧
    (X 0 2 = (-((1 : ℂ) / 2)) * X 2 2 + (-((1 : ℂ) / 2) - w) * X 2 3 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 3 3) ∧
    (X 0 3 = (-((1 : ℂ) / 2) - w) * X 2 2 + (-((1 : ℂ) / 2)) * X 2 3 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 3 3) ∧
    (X 0 4 = (-(1 : ℂ) - w) * X 2 4 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 3 4) ∧
    (X 1 0 = ((1 : ℂ) + w) * X 2 1 + (((1 : ℂ) / 2)) * X 2 2 + (((1 : ℂ) / 2)) * X 2 3 + (((1 : ℂ) / 2)) * X 2 4 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 3 3 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * X 3 4) ∧
    (X 1 1 = (-(1 : ℂ) - w) * X 2 1 + (-((1 : ℂ) / 2) - w) * X 2 2 + (-((1 : ℂ) / 2) - w) * X 2 3 + (-((1 : ℂ) / 2) - w) * X 2 4 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 3 3 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * X 3 4) ∧
    (X 1 2 = (-((1 : ℂ) / 2)) * X 2 2 + (((1 : ℂ) / 2) + w) * X 2 3 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 3) ∧
    (X 1 3 = (((1 : ℂ) / 2) + w) * X 2 2 + (-((1 : ℂ) / 2)) * X 2 3 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 3) ∧
    (X 1 4 = (w) * X 2 4 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 4) ∧
    (X 2 0 = (-(1 : ℂ)) * X 2 1 + (-(1 : ℂ)) * X 2 2 + (-(1 : ℂ)) * X 2 3 + (-(1 : ℂ)) * X 2 4) ∧
    (X 3 0 = (-(1 : ℂ)) * X 3 3 + (-((1 : ℂ) / 2)) * X 3 4) ∧
    (X 3 1 = (-(1 : ℂ)) * X 3 3 + (-((1 : ℂ) / 2)) * X 3 4) ∧
    (X 3 2 = ((1 : ℂ)) * X 3 3) := by
  let a : Fin 4 → ℂ := ![((1 : ℂ)), (w), (w^2), (0 : ℂ)]
  let u0 : Vec := ![((1 : ℂ)), (-(1 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ)]
  let u1 : Vec := ![(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (-(1 : ℂ)), (0 : ℂ)]
  have h0' : outer a u0 ∈ L := h0
  have h1' : outer a u1 ∈ L := h1
  have h01' : outer a (u0 + u1) ∈ L := by
    have := L.add_mem h0' h1'; convert this using 1; ext i j; simp [outer, mul_add]
  have h0m1' : outer a (u0 - u1) ∈ L := by
    have := L.sub_mem h0' h1'; convert this using 1; ext i j; simp [outer, mul_sub]
  have heq_0 : ((1 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 0 1 + ((1 : ℂ)) * X 0 2 + ((1 : ℂ)) * X 0 3 + ((1 : ℂ)) * X 0 4 = 0 := by
    have h := (hL X hX).1 0; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_1 : ((1 : ℂ)) * X 1 0 + ((1 : ℂ)) * X 1 1 + ((1 : ℂ)) * X 1 2 + ((1 : ℂ)) * X 1 3 + ((1 : ℂ)) * X 1 4 = 0 := by
    have h := (hL X hX).1 1; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_2 : ((1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 1 + ((1 : ℂ)) * X 2 2 + ((1 : ℂ)) * X 2 3 + ((1 : ℂ)) * X 2 4 = 0 := by
    have h := (hL X hX).1 2; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_3 : ((1 : ℂ)) * X 3 0 + ((1 : ℂ)) * X 3 1 + ((1 : ℂ)) * X 3 2 + ((1 : ℂ)) * X 3 3 + ((1 : ℂ)) * X 3 4 = 0 := by
    have h := (hL X hX).1 3; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_4 : ((1 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 1 0 + ((1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 3 0 = 0 := by
    have h := (hL X hX).2.1 0; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_5 : ((1 : ℂ)) * X 0 1 + ((1 : ℂ)) * X 1 1 + ((1 : ℂ)) * X 2 1 + ((1 : ℂ)) * X 3 1 = 0 := by
    have h := (hL X hX).2.1 1; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_6 : ((1 : ℂ)) * X 0 2 + ((1 : ℂ)) * X 1 2 + ((1 : ℂ)) * X 2 2 + ((1 : ℂ)) * X 3 2 = 0 := by
    have h := (hL X hX).2.1 2; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_7 : ((1 : ℂ)) * X 0 3 + ((1 : ℂ)) * X 1 3 + ((1 : ℂ)) * X 2 3 + ((1 : ℂ)) * X 3 3 = 0 := by
    have h := (hL X hX).2.1 3; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_8 : ((1 : ℂ)) * X 0 0 + (-(1 : ℂ)) * X 0 1 + (w) * X 1 0 + (-w) * X 1 1 + (-(1 : ℂ) - w) * X 2 0 + ((1 : ℂ) + w) * X 2 1 = 0 := by
    have h := lin_dot_zero L hL X hX _ h0'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 1) * hw
  have heq_9 : ((1 : ℂ)) * X 0 2 + (-(1 : ℂ)) * X 0 3 + (w) * X 1 2 + (-w) * X 1 3 + (-(1 : ℂ) - w) * X 2 2 + ((1 : ℂ) + w) * X 2 3 = 0 := by
    have h := lin_dot_zero L hL X hX _ h1'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(1 : ℂ)) * X 2 2 + ((1 : ℂ)) * X 2 3) * hw
  have heq_10 : ((1 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 0 1 + (-(1 : ℂ) - w) * X 1 0 + (-(1 : ℂ) - w) * X 1 1 + (w) * X 2 0 + (w) * X 2 1 = 0 := by
    have h := lin_d3_zero L hL X hX _ h0'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(1 : ℂ)) * X 1 0 + (-(1 : ℂ)) * X 1 1 + (w - w^2) * X 2 0 + (w - w^2) * X 2 1) * hw
  have heq_11 : ((1 : ℂ)) * X 0 2 + ((1 : ℂ)) * X 0 3 + (-(1 : ℂ) - w) * X 1 2 + (-(1 : ℂ) - w) * X 1 3 + (w) * X 2 2 + (w) * X 2 3 = 0 := by
    have h := lin_d3_zero L hL X hX _ h1'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(1 : ℂ)) * X 1 2 + (-(1 : ℂ)) * X 1 3 + (w - w^2) * X 2 2 + (w - w^2) * X 2 3) * hw
  have heq_12 : ((6 : ℂ)) * X 3 0 + (-(6 : ℂ)) * X 3 1 + ((6 : ℂ)) * X 3 2 + (-(6 : ℂ)) * X 3 3 = 0 := by
    have h := lin_q4_zero L hL X hX _ h01'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + (((6 : ℂ) - 6 * w) * X 3 0 + (-(6 : ℂ) + 6 * w) * X 3 1 + ((6 : ℂ) - 6 * w) * X 3 2 + (-(6 : ℂ) + 6 * w) * X 3 3) * hw
  have heq_13 : ((6 : ℂ)) * X 3 0 + (-(6 : ℂ)) * X 3 1 + (-(6 : ℂ)) * X 3 2 + ((6 : ℂ)) * X 3 3 = 0 := by
    have h := lin_q4_zero L hL X hX _ h0m1'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + (((6 : ℂ) - 6 * w) * X 3 0 + (-(6 : ℂ) + 6 * w) * X 3 1 + (-(6 : ℂ) + 6 * w) * X 3 2 + ((6 : ℂ) - 6 * w) * X 3 3) * hw
  have hpiv_0 : X 0 0 = (-w) * X 2 1 + (((1 : ℂ) / 2)) * X 2 2 + (((1 : ℂ) / 2)) * X 2 3 + (((1 : ℂ) / 2)) * X 2 4 + (((2 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 3 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * X 3 4 := by
    linear_combination (-((1 : ℂ) / 2)) * heq_2 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w) * heq_3 + (((1 : ℂ) / 2)) * heq_4 + (((1 : ℂ) / 6) + ((1 : ℂ) / 3) * w) * heq_5 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * heq_8 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_10 + (((1 : ℂ) / 72) + ((1 : ℂ) / 36) * w) * heq_12 + (-((1 : ℂ) / 24)) * heq_13 + ((-((1 : ℂ) / 3)) * X 1 0 + (((1 : ℂ) / 3)) * X 2 0) * hw
  have hpiv_1 : X 0 1 = (w) * X 2 1 + (((1 : ℂ) / 2) + w) * X 2 2 + (((1 : ℂ) / 2) + w) * X 2 3 + (((1 : ℂ) / 2) + w) * X 2 4 + (((2 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 3 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * X 3 4 := by
    linear_combination (-((1 : ℂ) / 2) - w) * heq_2 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w) * heq_3 + (((1 : ℂ) / 6) + ((1 : ℂ) / 3) * w) * heq_4 + (((1 : ℂ) / 2)) * heq_5 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w) * heq_8 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_10 + (((1 : ℂ) / 24)) * heq_12 + (-((1 : ℂ) / 72) - ((1 : ℂ) / 36) * w) * heq_13 + ((-((1 : ℂ) / 3)) * X 1 1 + (((1 : ℂ) / 3)) * X 2 1) * hw
  have hpiv_2 : X 0 2 = (-((1 : ℂ) / 2)) * X 2 2 + (-((1 : ℂ) / 2) - w) * X 2 3 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 3 3 := by
    linear_combination (((1 : ℂ) / 2)) * heq_6 + (((1 : ℂ) / 6) + ((1 : ℂ) / 3) * w) * heq_7 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * heq_9 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_11 + (-((1 : ℂ) / 24)) * heq_12 + (((1 : ℂ) / 24)) * heq_13 + ((-((1 : ℂ) / 3)) * X 1 2 + (((1 : ℂ) / 3)) * X 2 2) * hw
  have hpiv_3 : X 0 3 = (-((1 : ℂ) / 2) - w) * X 2 2 + (-((1 : ℂ) / 2)) * X 2 3 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 3 3 := by
    linear_combination (((1 : ℂ) / 6) + ((1 : ℂ) / 3) * w) * heq_6 + (((1 : ℂ) / 2)) * heq_7 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w) * heq_9 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_11 + (-((1 : ℂ) / 72) - ((1 : ℂ) / 36) * w) * heq_12 + (((1 : ℂ) / 72) + ((1 : ℂ) / 36) * w) * heq_13 + ((-((1 : ℂ) / 3)) * X 1 3 + (((1 : ℂ) / 3)) * X 2 3) * hw
  have hpiv_4 : X 0 4 = (-(1 : ℂ) - w) * X 2 4 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 3 4 := by
    linear_combination ((1 : ℂ)) * heq_0 + ((1 : ℂ) + w) * heq_2 + (((2 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * heq_3 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * heq_4 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * heq_5 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * heq_6 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * heq_7 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * heq_10 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * heq_11 + ((((1 : ℂ) / 3)) * X 1 0 + (((1 : ℂ) / 3)) * X 1 1 + (((1 : ℂ) / 3)) * X 1 2 + (((1 : ℂ) / 3)) * X 1 3 + (-((1 : ℂ) / 3)) * X 2 0 + (-((1 : ℂ) / 3)) * X 2 1 + (-((1 : ℂ) / 3)) * X 2 2 + (-((1 : ℂ) / 3)) * X 2 3) * hw
  have hpiv_5 : X 1 0 = ((1 : ℂ) + w) * X 2 1 + (((1 : ℂ) / 2)) * X 2 2 + (((1 : ℂ) / 2)) * X 2 3 + (((1 : ℂ) / 2)) * X 2 4 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 3 3 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * X 3 4 := by
    linear_combination (-((1 : ℂ) / 2)) * heq_2 + (-((1 : ℂ) / 6) + ((1 : ℂ) / 6) * w) * heq_3 + (((1 : ℂ) / 2)) * heq_4 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 3) * w) * heq_5 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w) * heq_8 + (-((1 : ℂ) / 6) + ((1 : ℂ) / 6) * w) * heq_10 + (-((1 : ℂ) / 72) - ((1 : ℂ) / 36) * w) * heq_12 + (-((1 : ℂ) / 24)) * heq_13 + ((((1 : ℂ) / 3)) * X 1 0 + (-((1 : ℂ) / 3)) * X 2 0) * hw
  have hpiv_6 : X 1 1 = (-(1 : ℂ) - w) * X 2 1 + (-((1 : ℂ) / 2) - w) * X 2 2 + (-((1 : ℂ) / 2) - w) * X 2 3 + (-((1 : ℂ) / 2) - w) * X 2 4 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 3 3 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * X 3 4 := by
    linear_combination (((1 : ℂ) / 2) + w) * heq_2 + (-((1 : ℂ) / 6) + ((1 : ℂ) / 6) * w) * heq_3 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 3) * w) * heq_4 + (((1 : ℂ) / 2)) * heq_5 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * heq_8 + (-((1 : ℂ) / 6) + ((1 : ℂ) / 6) * w) * heq_10 + (((1 : ℂ) / 24)) * heq_12 + (((1 : ℂ) / 72) + ((1 : ℂ) / 36) * w) * heq_13 + ((((1 : ℂ) / 3)) * X 1 1 + (-((1 : ℂ) / 3)) * X 2 1) * hw
  have hpiv_7 : X 1 2 = (-((1 : ℂ) / 2)) * X 2 2 + (((1 : ℂ) / 2) + w) * X 2 3 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 3 := by
    linear_combination (((1 : ℂ) / 2)) * heq_6 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 3) * w) * heq_7 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w) * heq_9 + (-((1 : ℂ) / 6) + ((1 : ℂ) / 6) * w) * heq_11 + (-((1 : ℂ) / 24)) * heq_12 + (((1 : ℂ) / 24)) * heq_13 + ((((1 : ℂ) / 3)) * X 1 2 + (-((1 : ℂ) / 3)) * X 2 2) * hw
  have hpiv_8 : X 1 3 = (((1 : ℂ) / 2) + w) * X 2 2 + (-((1 : ℂ) / 2)) * X 2 3 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 3 := by
    linear_combination (-((1 : ℂ) / 6) - ((1 : ℂ) / 3) * w) * heq_6 + (((1 : ℂ) / 2)) * heq_7 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * heq_9 + (-((1 : ℂ) / 6) + ((1 : ℂ) / 6) * w) * heq_11 + (((1 : ℂ) / 72) + ((1 : ℂ) / 36) * w) * heq_12 + (-((1 : ℂ) / 72) - ((1 : ℂ) / 36) * w) * heq_13 + ((((1 : ℂ) / 3)) * X 1 3 + (-((1 : ℂ) / 3)) * X 2 3) * hw
  have hpiv_9 : X 1 4 = (w) * X 2 4 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 4 := by
    linear_combination ((1 : ℂ)) * heq_1 + (-w) * heq_2 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * heq_3 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * heq_4 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * heq_5 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * heq_6 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * heq_7 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * heq_10 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * heq_11 + ((-((1 : ℂ) / 3)) * X 1 0 + (-((1 : ℂ) / 3)) * X 1 1 + (-((1 : ℂ) / 3)) * X 1 2 + (-((1 : ℂ) / 3)) * X 1 3 + (((1 : ℂ) / 3)) * X 2 0 + (((1 : ℂ) / 3)) * X 2 1 + (((1 : ℂ) / 3)) * X 2 2 + (((1 : ℂ) / 3)) * X 2 3) * hw
  have hpiv_10 : X 2 0 = (-(1 : ℂ)) * X 2 1 + (-(1 : ℂ)) * X 2 2 + (-(1 : ℂ)) * X 2 3 + (-(1 : ℂ)) * X 2 4 := by
    linear_combination ((1 : ℂ)) * heq_2
  have hpiv_11 : X 3 0 = (-(1 : ℂ)) * X 3 3 + (-((1 : ℂ) / 2)) * X 3 4 := by
    linear_combination (((1 : ℂ) / 2)) * heq_3 + (((1 : ℂ) / 12)) * heq_13
  have hpiv_12 : X 3 1 = (-(1 : ℂ)) * X 3 3 + (-((1 : ℂ) / 2)) * X 3 4 := by
    linear_combination (((1 : ℂ) / 2)) * heq_3 + (-((1 : ℂ) / 12)) * heq_12
  have hpiv_13 : X 3 2 = ((1 : ℂ)) * X 3 3 := by
    linear_combination (((1 : ℂ) / 12)) * heq_12 + (-((1 : ℂ) / 12)) * heq_13
  exact ⟨hpiv_0, hpiv_1, hpiv_2, hpiv_3, hpiv_4, hpiv_5, hpiv_6, hpiv_7, hpiv_8, hpiv_9, hpiv_10, hpiv_11, hpiv_12, hpiv_13⟩


lemma case_2a_eqs (hI : Complex.I^2 + 1 = 0)
    (L : Submodule ℂ Mat) (hL : ValidL L)
    (h0 : outer (![((1 : ℂ)), (Complex.I), (-(1 : ℂ)), (-Complex.I)]) (![((1 : ℂ)), (-(1 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ)]) ∈ L)
    (h1 : outer (![((1 : ℂ)), (Complex.I), (-(1 : ℂ)), (-Complex.I)]) (![((1 : ℂ)), (0 : ℂ), (-(1 : ℂ)), (0 : ℂ), (0 : ℂ)]) ∈ L)
    (X : Mat) (hX : X ∈ L) :
    (X 0 0 = (-Complex.I) * X 3 1 + (-Complex.I) * X 3 2 + (-((1 : ℂ) / 3) * Complex.I) * X 3 3 + (-((1 : ℂ) / 3) * Complex.I) * X 3 4) ∧
    (X 0 1 = (Complex.I) * X 3 1 + (((2 : ℂ) / 3) * Complex.I) * X 3 3 + (((2 : ℂ) / 3) * Complex.I) * X 3 4) ∧
    (X 0 2 = (Complex.I) * X 3 2 + (((2 : ℂ) / 3) * Complex.I) * X 3 3 + (((2 : ℂ) / 3) * Complex.I) * X 3 4) ∧
    (X 0 3 = ((1 : ℂ)) * X 1 4 + ((1 : ℂ)) * X 2 4 + (-Complex.I) * X 3 3 + ((1 : ℂ) - Complex.I) * X 3 4) ∧
    (X 0 4 = (-(1 : ℂ)) * X 1 4 + (-(1 : ℂ)) * X 2 4 + (-(1 : ℂ)) * X 3 4) ∧
    (X 1 0 = ((1 : ℂ)) * X 3 1 + ((1 : ℂ)) * X 3 2 + ((1 : ℂ)) * X 3 3 + ((1 : ℂ)) * X 3 4) ∧
    (X 1 1 = (-(1 : ℂ)) * X 3 1) ∧
    (X 1 2 = (-(1 : ℂ)) * X 3 2) ∧
    (X 1 3 = (-(1 : ℂ)) * X 1 4 + (-(1 : ℂ)) * X 3 3 + (-(1 : ℂ)) * X 3 4) ∧
    (X 2 0 = (Complex.I) * X 3 1 + (Complex.I) * X 3 2 + (((1 : ℂ) / 3) * Complex.I) * X 3 3 + (((1 : ℂ) / 3) * Complex.I) * X 3 4) ∧
    (X 2 1 = (-Complex.I) * X 3 1 + (-((2 : ℂ) / 3) * Complex.I) * X 3 3 + (-((2 : ℂ) / 3) * Complex.I) * X 3 4) ∧
    (X 2 2 = (-Complex.I) * X 3 2 + (-((2 : ℂ) / 3) * Complex.I) * X 3 3 + (-((2 : ℂ) / 3) * Complex.I) * X 3 4) ∧
    (X 2 3 = (-(1 : ℂ)) * X 2 4 + (Complex.I) * X 3 3 + (Complex.I) * X 3 4) ∧
    (X 3 0 = (-(1 : ℂ)) * X 3 1 + (-(1 : ℂ)) * X 3 2 + (-(1 : ℂ)) * X 3 3 + (-(1 : ℂ)) * X 3 4) := by
  let a : Fin 4 → ℂ := ![((1 : ℂ)), (Complex.I), (-(1 : ℂ)), (-Complex.I)]
  let u0 : Vec := ![((1 : ℂ)), (-(1 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ)]
  let u1 : Vec := ![((1 : ℂ)), (0 : ℂ), (-(1 : ℂ)), (0 : ℂ), (0 : ℂ)]
  have h0' : outer a u0 ∈ L := h0
  have h1' : outer a u1 ∈ L := h1
  have h01' : outer a (u0 + u1) ∈ L := by
    have := L.add_mem h0' h1'; convert this using 1; ext i j; simp [outer, mul_add]
  have h0m1' : outer a (u0 - u1) ∈ L := by
    have := L.sub_mem h0' h1'; convert this using 1; ext i j; simp [outer, mul_sub]
  have heq_0 : ((1 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 0 1 + ((1 : ℂ)) * X 0 2 + ((1 : ℂ)) * X 0 3 + ((1 : ℂ)) * X 0 4 = 0 := by
    have h := (hL X hX).1 0; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_1 : ((1 : ℂ)) * X 1 0 + ((1 : ℂ)) * X 1 1 + ((1 : ℂ)) * X 1 2 + ((1 : ℂ)) * X 1 3 + ((1 : ℂ)) * X 1 4 = 0 := by
    have h := (hL X hX).1 1; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_2 : ((1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 1 + ((1 : ℂ)) * X 2 2 + ((1 : ℂ)) * X 2 3 + ((1 : ℂ)) * X 2 4 = 0 := by
    have h := (hL X hX).1 2; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_3 : ((1 : ℂ)) * X 3 0 + ((1 : ℂ)) * X 3 1 + ((1 : ℂ)) * X 3 2 + ((1 : ℂ)) * X 3 3 + ((1 : ℂ)) * X 3 4 = 0 := by
    have h := (hL X hX).1 3; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_4 : ((1 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 1 0 + ((1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 3 0 = 0 := by
    have h := (hL X hX).2.1 0; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_5 : ((1 : ℂ)) * X 0 1 + ((1 : ℂ)) * X 1 1 + ((1 : ℂ)) * X 2 1 + ((1 : ℂ)) * X 3 1 = 0 := by
    have h := (hL X hX).2.1 1; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_6 : ((1 : ℂ)) * X 0 2 + ((1 : ℂ)) * X 1 2 + ((1 : ℂ)) * X 2 2 + ((1 : ℂ)) * X 3 2 = 0 := by
    have h := (hL X hX).2.1 2; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_7 : ((1 : ℂ)) * X 0 3 + ((1 : ℂ)) * X 1 3 + ((1 : ℂ)) * X 2 3 + ((1 : ℂ)) * X 3 3 = 0 := by
    have h := (hL X hX).2.1 3; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_8 : ((1 : ℂ)) * X 0 0 + (-(1 : ℂ)) * X 0 1 + (Complex.I) * X 1 0 + (-Complex.I) * X 1 1 + (-(1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 1 + (-Complex.I) * X 3 0 + (Complex.I) * X 3 1 = 0 := by
    have h := lin_dot_zero L hL X hX _ h0'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h
  have heq_9 : ((1 : ℂ)) * X 0 0 + (-(1 : ℂ)) * X 0 2 + (Complex.I) * X 1 0 + (-Complex.I) * X 1 2 + (-(1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 2 + (-Complex.I) * X 3 0 + (Complex.I) * X 3 2 = 0 := by
    have h := lin_dot_zero L hL X hX _ h1'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h
  have heq_10 : ((1 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 0 1 + (-(1 : ℂ)) * X 1 0 + (-(1 : ℂ)) * X 1 1 + ((1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 1 + (-(1 : ℂ)) * X 3 0 + (-(1 : ℂ)) * X 3 1 = 0 := by
    have h := lin_d3_zero L hL X hX _ h0'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(1 : ℂ)) * X 1 0 + (-(1 : ℂ)) * X 1 1 + (-(1 : ℂ)) * X 3 0 + (-(1 : ℂ)) * X 3 1) * hI
  have heq_11 : ((1 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 0 2 + (-(1 : ℂ)) * X 1 0 + (-(1 : ℂ)) * X 1 2 + ((1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 2 + (-(1 : ℂ)) * X 3 0 + (-(1 : ℂ)) * X 3 2 = 0 := by
    have h := lin_d3_zero L hL X hX _ h1'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(1 : ℂ)) * X 1 0 + (-(1 : ℂ)) * X 1 2 + (-(1 : ℂ)) * X 3 0 + (-(1 : ℂ)) * X 3 2) * hI
  have heq_12 : ((4 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 0 1 + ((1 : ℂ)) * X 0 2 + (-(4 : ℂ)) * X 1 0 + (-(1 : ℂ)) * X 1 1 + (-(1 : ℂ)) * X 1 2 + ((4 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 1 + ((1 : ℂ)) * X 2 2 + (-(4 : ℂ)) * X 3 0 + (-(1 : ℂ)) * X 3 1 + (-(1 : ℂ)) * X 3 2 = 0 := by
    have h := lin_d3_zero L hL X hX _ h01'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(4 : ℂ)) * X 1 0 + (-(1 : ℂ)) * X 1 1 + (-(1 : ℂ)) * X 1 2 + (-(4 : ℂ)) * X 3 0 + (-(1 : ℂ)) * X 3 1 + (-(1 : ℂ)) * X 3 2) * hI
  have heq_13 : ((12 : ℂ)) * X 0 0 + ((12 : ℂ)) * X 0 1 + ((12 : ℂ)) * X 0 2 + (-12 * Complex.I) * X 1 0 + (-12 * Complex.I) * X 1 1 + (-12 * Complex.I) * X 1 2 + (-(12 : ℂ)) * X 2 0 + (-(12 : ℂ)) * X 2 1 + (-(12 : ℂ)) * X 2 2 + (12 * Complex.I) * X 3 0 + (12 * Complex.I) * X 3 1 + (12 * Complex.I) * X 3 2 = 0 := by
    have h := lin_q4_zero L hL X hX _ h01'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + (((12 : ℂ)) * X 0 0 + ((12 : ℂ)) * X 0 1 + ((12 : ℂ)) * X 0 2 + (-(12 : ℂ)) * X 2 0 + (-(12 : ℂ)) * X 2 1 + (-(12 : ℂ)) * X 2 2) * hI
  have hpiv_0 : X 0 0 = (-Complex.I) * X 3 1 + (-Complex.I) * X 3 2 + (-((1 : ℂ) / 3) * Complex.I) * X 3 3 + (-((1 : ℂ) / 3) * Complex.I) * X 3 4 := by
    linear_combination (((1 : ℂ) / 3) * Complex.I) * heq_3 + (((1 : ℂ) / 4) - ((1 : ℂ) / 12) * Complex.I) * heq_4 + (((1 : ℂ) / 6) * Complex.I) * heq_5 + (((1 : ℂ) / 6) * Complex.I) * heq_6 + (((1 : ℂ) / 6)) * heq_8 + (((1 : ℂ) / 6)) * heq_9 + (-((1 : ℂ) / 8) - ((3 : ℂ) / 8) * Complex.I) * heq_10 + (-((1 : ℂ) / 8) - ((3 : ℂ) / 8) * Complex.I) * heq_11 + (((1 : ℂ) / 8) + ((5 : ℂ) / 24) * Complex.I) * heq_12 + (((1 : ℂ) / 72)) * heq_13
  have hpiv_1 : X 0 1 = (Complex.I) * X 3 1 + (((2 : ℂ) / 3) * Complex.I) * X 3 3 + (((2 : ℂ) / 3) * Complex.I) * X 3 4 := by
    linear_combination (-((2 : ℂ) / 3) * Complex.I) * heq_3 + (((1 : ℂ) / 6) * Complex.I) * heq_4 + (((1 : ℂ) / 4) - ((1 : ℂ) / 12) * Complex.I) * heq_5 + (((1 : ℂ) / 6) * Complex.I) * heq_6 + (-((1 : ℂ) / 3)) * heq_8 + (((1 : ℂ) / 6)) * heq_9 + (((3 : ℂ) / 8) + ((1 : ℂ) / 8) * Complex.I) * heq_10 + (((1 : ℂ) / 8) - ((1 : ℂ) / 8) * Complex.I) * heq_11 + (-((1 : ℂ) / 8) - ((1 : ℂ) / 24) * Complex.I) * heq_12 + (((1 : ℂ) / 72)) * heq_13
  have hpiv_2 : X 0 2 = (Complex.I) * X 3 2 + (((2 : ℂ) / 3) * Complex.I) * X 3 3 + (((2 : ℂ) / 3) * Complex.I) * X 3 4 := by
    linear_combination (-((2 : ℂ) / 3) * Complex.I) * heq_3 + (((1 : ℂ) / 6) * Complex.I) * heq_4 + (((1 : ℂ) / 6) * Complex.I) * heq_5 + (((1 : ℂ) / 4) - ((1 : ℂ) / 12) * Complex.I) * heq_6 + (((1 : ℂ) / 6)) * heq_8 + (-((1 : ℂ) / 3)) * heq_9 + (((1 : ℂ) / 8) - ((1 : ℂ) / 8) * Complex.I) * heq_10 + (((3 : ℂ) / 8) + ((1 : ℂ) / 8) * Complex.I) * heq_11 + (-((1 : ℂ) / 8) - ((1 : ℂ) / 24) * Complex.I) * heq_12 + (((1 : ℂ) / 72)) * heq_13
  have hpiv_3 : X 0 3 = ((1 : ℂ)) * X 1 4 + ((1 : ℂ)) * X 2 4 + (-Complex.I) * X 3 3 + ((1 : ℂ) - Complex.I) * X 3 4 := by
    linear_combination (-(1 : ℂ)) * heq_1 + (-(1 : ℂ)) * heq_2 + (-(1 : ℂ) + Complex.I) * heq_3 + (((3 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_4 + (((3 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_5 + (((3 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_6 + ((1 : ℂ)) * heq_7 + (-((3 : ℂ) / 8) + ((3 : ℂ) / 8) * Complex.I) * heq_10 + (-((3 : ℂ) / 8) + ((3 : ℂ) / 8) * Complex.I) * heq_11 + (((1 : ℂ) / 8) - ((1 : ℂ) / 8) * Complex.I) * heq_12 + (-((1 : ℂ) / 24)) * heq_13
  have hpiv_4 : X 0 4 = (-(1 : ℂ)) * X 1 4 + (-(1 : ℂ)) * X 2 4 + (-(1 : ℂ)) * X 3 4 := by
    linear_combination ((1 : ℂ)) * heq_0 + ((1 : ℂ)) * heq_1 + ((1 : ℂ)) * heq_2 + ((1 : ℂ)) * heq_3 + (-(1 : ℂ)) * heq_4 + (-(1 : ℂ)) * heq_5 + (-(1 : ℂ)) * heq_6 + (-(1 : ℂ)) * heq_7
  have hpiv_5 : X 1 0 = ((1 : ℂ)) * X 3 1 + ((1 : ℂ)) * X 3 2 + ((1 : ℂ)) * X 3 3 + ((1 : ℂ)) * X 3 4 := by
    linear_combination (-(1 : ℂ)) * heq_3 + (((1 : ℂ) / 2)) * heq_4 + (((1 : ℂ) / 4)) * heq_10 + (((1 : ℂ) / 4)) * heq_11 + (-((1 : ℂ) / 4)) * heq_12
  have hpiv_6 : X 1 1 = (-(1 : ℂ)) * X 3 1 := by
    linear_combination (((1 : ℂ) / 2)) * heq_5 + (-((3 : ℂ) / 4)) * heq_10 + (-((1 : ℂ) / 4)) * heq_11 + (((1 : ℂ) / 4)) * heq_12
  have hpiv_7 : X 1 2 = (-(1 : ℂ)) * X 3 2 := by
    linear_combination (((1 : ℂ) / 2)) * heq_6 + (-((1 : ℂ) / 4)) * heq_10 + (-((3 : ℂ) / 4)) * heq_11 + (((1 : ℂ) / 4)) * heq_12
  have hpiv_8 : X 1 3 = (-(1 : ℂ)) * X 1 4 + (-(1 : ℂ)) * X 3 3 + (-(1 : ℂ)) * X 3 4 := by
    linear_combination ((1 : ℂ)) * heq_1 + ((1 : ℂ)) * heq_3 + (-((1 : ℂ) / 2)) * heq_4 + (-((1 : ℂ) / 2)) * heq_5 + (-((1 : ℂ) / 2)) * heq_6 + (((3 : ℂ) / 4)) * heq_10 + (((3 : ℂ) / 4)) * heq_11 + (-((1 : ℂ) / 4)) * heq_12
  have hpiv_9 : X 2 0 = (Complex.I) * X 3 1 + (Complex.I) * X 3 2 + (((1 : ℂ) / 3) * Complex.I) * X 3 3 + (((1 : ℂ) / 3) * Complex.I) * X 3 4 := by
    linear_combination (-((1 : ℂ) / 3) * Complex.I) * heq_3 + (((1 : ℂ) / 4) + ((1 : ℂ) / 12) * Complex.I) * heq_4 + (-((1 : ℂ) / 6) * Complex.I) * heq_5 + (-((1 : ℂ) / 6) * Complex.I) * heq_6 + (-((1 : ℂ) / 6)) * heq_8 + (-((1 : ℂ) / 6)) * heq_9 + (-((1 : ℂ) / 8) + ((3 : ℂ) / 8) * Complex.I) * heq_10 + (-((1 : ℂ) / 8) + ((3 : ℂ) / 8) * Complex.I) * heq_11 + (((1 : ℂ) / 8) - ((5 : ℂ) / 24) * Complex.I) * heq_12 + (-((1 : ℂ) / 72)) * heq_13
  have hpiv_10 : X 2 1 = (-Complex.I) * X 3 1 + (-((2 : ℂ) / 3) * Complex.I) * X 3 3 + (-((2 : ℂ) / 3) * Complex.I) * X 3 4 := by
    linear_combination (((2 : ℂ) / 3) * Complex.I) * heq_3 + (-((1 : ℂ) / 6) * Complex.I) * heq_4 + (((1 : ℂ) / 4) + ((1 : ℂ) / 12) * Complex.I) * heq_5 + (-((1 : ℂ) / 6) * Complex.I) * heq_6 + (((1 : ℂ) / 3)) * heq_8 + (-((1 : ℂ) / 6)) * heq_9 + (((3 : ℂ) / 8) - ((1 : ℂ) / 8) * Complex.I) * heq_10 + (((1 : ℂ) / 8) + ((1 : ℂ) / 8) * Complex.I) * heq_11 + (-((1 : ℂ) / 8) + ((1 : ℂ) / 24) * Complex.I) * heq_12 + (-((1 : ℂ) / 72)) * heq_13
  have hpiv_11 : X 2 2 = (-Complex.I) * X 3 2 + (-((2 : ℂ) / 3) * Complex.I) * X 3 3 + (-((2 : ℂ) / 3) * Complex.I) * X 3 4 := by
    linear_combination (((2 : ℂ) / 3) * Complex.I) * heq_3 + (-((1 : ℂ) / 6) * Complex.I) * heq_4 + (-((1 : ℂ) / 6) * Complex.I) * heq_5 + (((1 : ℂ) / 4) + ((1 : ℂ) / 12) * Complex.I) * heq_6 + (-((1 : ℂ) / 6)) * heq_8 + (((1 : ℂ) / 3)) * heq_9 + (((1 : ℂ) / 8) + ((1 : ℂ) / 8) * Complex.I) * heq_10 + (((3 : ℂ) / 8) - ((1 : ℂ) / 8) * Complex.I) * heq_11 + (-((1 : ℂ) / 8) + ((1 : ℂ) / 24) * Complex.I) * heq_12 + (-((1 : ℂ) / 72)) * heq_13
  have hpiv_12 : X 2 3 = (-(1 : ℂ)) * X 2 4 + (Complex.I) * X 3 3 + (Complex.I) * X 3 4 := by
    linear_combination ((1 : ℂ)) * heq_2 + (-Complex.I) * heq_3 + (-((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_4 + (-((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_5 + (-((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_6 + (-((3 : ℂ) / 8) - ((3 : ℂ) / 8) * Complex.I) * heq_10 + (-((3 : ℂ) / 8) - ((3 : ℂ) / 8) * Complex.I) * heq_11 + (((1 : ℂ) / 8) + ((1 : ℂ) / 8) * Complex.I) * heq_12 + (((1 : ℂ) / 24)) * heq_13
  have hpiv_13 : X 3 0 = (-(1 : ℂ)) * X 3 1 + (-(1 : ℂ)) * X 3 2 + (-(1 : ℂ)) * X 3 3 + (-(1 : ℂ)) * X 3 4 := by
    linear_combination ((1 : ℂ)) * heq_3
  exact ⟨hpiv_0, hpiv_1, hpiv_2, hpiv_3, hpiv_4, hpiv_5, hpiv_6, hpiv_7, hpiv_8, hpiv_9, hpiv_10, hpiv_11, hpiv_12, hpiv_13⟩


lemma case_2b_eqs (w : ℂ) (hw : w^2 + w + 1 = 0) (hI : Complex.I^2 + 1 = 0)
    (L : Submodule ℂ Mat) (hL : ValidL L)
    (h0 : outer (![((1 : ℂ)), (Complex.I), (-(1 : ℂ)), (-Complex.I)]) (![((1 : ℂ)), (-(1 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ)]) ∈ L)
    (h1 : outer (![((1 : ℂ)), (Complex.I), (-(1 : ℂ)), (-Complex.I)]) (![(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (w), (w^2)]) ∈ L)
    (X : Mat) (hX : X ∈ L) :
    (X 0 0 = (-Complex.I) * X 2 1 + ((1 : ℂ) - Complex.I) * X 3 1 + ((1 : ℂ)) * X 3 2 + ((1 : ℂ)) * X 3 3 + ((1 : ℂ)) * X 3 4) ∧
    (X 0 1 = (Complex.I) * X 2 1 + (-(1 : ℂ) + Complex.I) * X 3 1 + (-(1 : ℂ) + Complex.I) * X 3 2 + (-(1 : ℂ) + Complex.I) * X 3 3 + (-(1 : ℂ) + Complex.I) * X 3 4) ∧
    (X 0 2 = (-w) * X 2 4 + (((1 : ℂ) / 3) * w - ((1 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 2 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w - ((1 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 3 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 4) ∧
    (X 0 3 = ((1 : ℂ) + w) * X 2 4 + (((1 : ℂ) / 3) * w - ((2 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 2 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w - ((2 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 3 + (((1 : ℂ) / 3) - ((2 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 4) ∧
    (X 0 4 = (-(1 : ℂ)) * X 2 4 + (-((2 : ℂ) / 3) * w) * X 3 2 + (((2 : ℂ) / 3) + ((2 : ℂ) / 3) * w) * X 3 3 + (-((2 : ℂ) / 3)) * X 3 4) ∧
    (X 1 0 = ((1 : ℂ) + Complex.I) * X 2 1 + (Complex.I) * X 3 1 + (Complex.I) * X 3 2 + (Complex.I) * X 3 3 + (Complex.I) * X 3 4) ∧
    (X 1 1 = (-(1 : ℂ) - Complex.I) * X 2 1 + (-Complex.I) * X 3 1 + ((1 : ℂ) - Complex.I) * X 3 2 + ((1 : ℂ) - Complex.I) * X 3 3 + ((1 : ℂ) - Complex.I) * X 3 4) ∧
    (X 1 2 = (-((1 : ℂ) / 3)) * X 3 2 + (((2 : ℂ) / 3) * w) * X 3 3 + (-((2 : ℂ) / 3) - ((2 : ℂ) / 3) * w) * X 3 4) ∧
    (X 1 3 = (-((2 : ℂ) / 3) - ((2 : ℂ) / 3) * w) * X 3 2 + (-((1 : ℂ) / 3)) * X 3 3 + (((2 : ℂ) / 3) * w) * X 3 4) ∧
    (X 1 4 = (((2 : ℂ) / 3) * w) * X 3 2 + (-((2 : ℂ) / 3) - ((2 : ℂ) / 3) * w) * X 3 3 + (-((1 : ℂ) / 3)) * X 3 4) ∧
    (X 2 0 = (-(1 : ℂ)) * X 2 1 + (-Complex.I) * X 3 2 + (-Complex.I) * X 3 3 + (-Complex.I) * X 3 4) ∧
    (X 2 2 = (w) * X 2 4 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w + ((1 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 2 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w + ((1 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 3 + (((1 : ℂ) / 3) + ((2 : ℂ) / 3) * w + ((1 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 4) ∧
    (X 2 3 = (-(1 : ℂ) - w) * X 2 4 + (((2 : ℂ) / 3) + ((1 : ℂ) / 3) * w + ((2 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 2 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w + ((2 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 3 + (-((1 : ℂ) / 3) - ((2 : ℂ) / 3) * w + ((2 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 4) ∧
    (X 3 0 = (-(1 : ℂ)) * X 3 1 + (-(1 : ℂ)) * X 3 2 + (-(1 : ℂ)) * X 3 3 + (-(1 : ℂ)) * X 3 4) := by
  let a : Fin 4 → ℂ := ![((1 : ℂ)), (Complex.I), (-(1 : ℂ)), (-Complex.I)]
  let u0 : Vec := ![((1 : ℂ)), (-(1 : ℂ)), (0 : ℂ), (0 : ℂ), (0 : ℂ)]
  let u1 : Vec := ![(0 : ℂ), (0 : ℂ), ((1 : ℂ)), (w), (w^2)]
  have h0' : outer a u0 ∈ L := h0
  have h1' : outer a u1 ∈ L := h1
  have h01' : outer a (u0 + u1) ∈ L := by
    have := L.add_mem h0' h1'; convert this using 1; ext i j; simp [outer, mul_add]
  have h0m1' : outer a (u0 - u1) ∈ L := by
    have := L.sub_mem h0' h1'; convert this using 1; ext i j; simp [outer, mul_sub]
  have heq_0 : ((1 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 0 1 + ((1 : ℂ)) * X 0 2 + ((1 : ℂ)) * X 0 3 + ((1 : ℂ)) * X 0 4 = 0 := by
    have h := (hL X hX).1 0; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_1 : ((1 : ℂ)) * X 1 0 + ((1 : ℂ)) * X 1 1 + ((1 : ℂ)) * X 1 2 + ((1 : ℂ)) * X 1 3 + ((1 : ℂ)) * X 1 4 = 0 := by
    have h := (hL X hX).1 1; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_2 : ((1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 1 + ((1 : ℂ)) * X 2 2 + ((1 : ℂ)) * X 2 3 + ((1 : ℂ)) * X 2 4 = 0 := by
    have h := (hL X hX).1 2; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_3 : ((1 : ℂ)) * X 3 0 + ((1 : ℂ)) * X 3 1 + ((1 : ℂ)) * X 3 2 + ((1 : ℂ)) * X 3 3 + ((1 : ℂ)) * X 3 4 = 0 := by
    have h := (hL X hX).1 3; simp only [Fin.sum_univ_five] at h; linear_combination h
  have heq_4 : ((1 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 1 0 + ((1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 3 0 = 0 := by
    have h := (hL X hX).2.1 0; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_5 : ((1 : ℂ)) * X 0 1 + ((1 : ℂ)) * X 1 1 + ((1 : ℂ)) * X 2 1 + ((1 : ℂ)) * X 3 1 = 0 := by
    have h := (hL X hX).2.1 1; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_6 : ((1 : ℂ)) * X 0 2 + ((1 : ℂ)) * X 1 2 + ((1 : ℂ)) * X 2 2 + ((1 : ℂ)) * X 3 2 = 0 := by
    have h := (hL X hX).2.1 2; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_7 : ((1 : ℂ)) * X 0 3 + ((1 : ℂ)) * X 1 3 + ((1 : ℂ)) * X 2 3 + ((1 : ℂ)) * X 3 3 = 0 := by
    have h := (hL X hX).2.1 3; simp only [Fin.sum_univ_four] at h; linear_combination h
  have heq_8 : ((1 : ℂ)) * X 0 0 + (-(1 : ℂ)) * X 0 1 + (Complex.I) * X 1 0 + (-Complex.I) * X 1 1 + (-(1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 1 + (-Complex.I) * X 3 0 + (Complex.I) * X 3 1 = 0 := by
    have h := lin_dot_zero L hL X hX _ h0'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h
  have heq_9 : ((1 : ℂ)) * X 0 2 + (w) * X 0 3 + (-(1 : ℂ) - w) * X 0 4 + (Complex.I) * X 1 2 + (Complex.I * w) * X 1 3 + (-Complex.I - Complex.I * w) * X 1 4 + (-(1 : ℂ)) * X 2 2 + (-w) * X 2 3 + ((1 : ℂ) + w) * X 2 4 + (-Complex.I) * X 3 2 + (-Complex.I * w) * X 3 3 + (Complex.I + Complex.I * w) * X 3 4 = 0 := by
    have h := lin_dot_zero L hL X hX _ h1'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(1 : ℂ)) * X 0 4 + (-Complex.I) * X 1 4 + ((1 : ℂ)) * X 2 4 + (Complex.I) * X 3 4) * hw
  have heq_10 : ((1 : ℂ)) * X 0 0 + ((1 : ℂ)) * X 0 1 + (-(1 : ℂ)) * X 1 0 + (-(1 : ℂ)) * X 1 1 + ((1 : ℂ)) * X 2 0 + ((1 : ℂ)) * X 2 1 + (-(1 : ℂ)) * X 3 0 + (-(1 : ℂ)) * X 3 1 = 0 := by
    have h := lin_d3_zero L hL X hX _ h0'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(1 : ℂ)) * X 1 0 + (-(1 : ℂ)) * X 1 1 + (-(1 : ℂ)) * X 3 0 + (-(1 : ℂ)) * X 3 1) * hI
  have heq_11 : ((1 : ℂ)) * X 0 2 + (-(1 : ℂ) - w) * X 0 3 + (w) * X 0 4 + (-(1 : ℂ)) * X 1 2 + ((1 : ℂ) + w) * X 1 3 + (-w) * X 1 4 + ((1 : ℂ)) * X 2 2 + (-(1 : ℂ) - w) * X 2 3 + (w) * X 2 4 + (-(1 : ℂ)) * X 3 2 + ((1 : ℂ) + w) * X 3 3 + (-w) * X 3 4 = 0 := by
    have h := lin_d3_zero L hL X hX _ h1'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(1 : ℂ)) * X 1 2 + (-w^2) * X 1 3 + (-w^4) * X 1 4 + (-(1 : ℂ)) * X 3 2 + (-w^2) * X 3 3 + (-w^4) * X 3 4) * hI + ((-(1 : ℂ)) * X 0 3 + (w - w^2) * X 0 4 + ((1 : ℂ)) * X 1 3 + (-w + w^2) * X 1 4 + (-(1 : ℂ)) * X 2 3 + (w - w^2) * X 2 4 + ((1 : ℂ)) * X 3 3 + (-w + w^2) * X 3 4) * hw
  have heq_12 : ((6 : ℂ)) * X 0 2 + ((6 : ℂ)) * X 0 3 + ((6 : ℂ)) * X 0 4 + (-6 * Complex.I) * X 1 2 + (-6 * Complex.I) * X 1 3 + (-6 * Complex.I) * X 1 4 + (-(6 : ℂ)) * X 2 2 + (-(6 : ℂ)) * X 2 3 + (-(6 : ℂ)) * X 2 4 + (6 * Complex.I) * X 3 2 + (6 * Complex.I) * X 3 3 + (6 * Complex.I) * X 3 4 = 0 := by
    have h := lin_q4_zero L hL X hX _ h1'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + (((3 : ℂ) - 3 * w^2 - 3 * w^4) * X 0 2 + (-3 * w + 3 * w^3 - 3 * w^5) * X 0 3 + (-3 * w^2 - 3 * w^4 + 3 * w^6) * X 0 4 + (-(3 : ℂ) + 3 * w^2 + 3 * w^4) * X 2 2 + (3 * w - 3 * w^3 + 3 * w^5) * X 2 3 + (3 * w^2 + 3 * w^4 - 3 * w^6) * X 2 4) * hI + (((3 : ℂ) - 3 * w + 3 * w^2) * X 0 2 + ((6 : ℂ) - 3 * w - 3 * w^2 + 3 * w^3) * X 0 3 + ((6 : ℂ) - 6 * w + 3 * w^2 + 3 * w^3 - 3 * w^4) * X 0 4 + (-3 * Complex.I + 3 * Complex.I * w - 3 * Complex.I * w^2) * X 1 2 + (-6 * Complex.I + 3 * Complex.I * w + 3 * Complex.I * w^2 - 3 * Complex.I * w^3) * X 1 3 + (-6 * Complex.I + 6 * Complex.I * w - 3 * Complex.I * w^2 - 3 * Complex.I * w^3 + 3 * Complex.I * w^4) * X 1 4 + (-(3 : ℂ) + 3 * w - 3 * w^2) * X 2 2 + (-(6 : ℂ) + 3 * w + 3 * w^2 - 3 * w^3) * X 2 3 + (-(6 : ℂ) + 6 * w - 3 * w^2 - 3 * w^3 + 3 * w^4) * X 2 4 + (3 * Complex.I - 3 * Complex.I * w + 3 * Complex.I * w^2) * X 3 2 + (6 * Complex.I - 3 * Complex.I * w - 3 * Complex.I * w^2 + 3 * Complex.I * w^3) * X 3 3 + (6 * Complex.I - 6 * Complex.I * w + 3 * Complex.I * w^2 + 3 * Complex.I * w^3 - 3 * Complex.I * w^4) * X 3 4) * hw
  have heq_13 : ((6 : ℂ) - 6 * w) * X 0 3 + ((12 : ℂ) + 6 * w) * X 0 4 + (-6 * Complex.I + 6 * Complex.I * w) * X 1 3 + (-12 * Complex.I - 6 * Complex.I * w) * X 1 4 + (-(6 : ℂ) + 6 * w) * X 2 3 + (-(12 : ℂ) - 6 * w) * X 2 4 + (6 * Complex.I - 6 * Complex.I * w) * X 3 3 + (12 * Complex.I + 6 * Complex.I * w) * X 3 4 = 0 := by
    have h := lin_q4_zero L hL X hX _ h01'
    simp only [outer, a, u0, u1, dot, Fin.sum_univ_four, Fin.sum_univ_five, Pi.add_apply, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] at h
    linear_combination h + ((-(3 : ℂ) - 3 * w^2 - 3 * w^4) * X 0 0 + ((3 : ℂ) + 3 * w^2 + 3 * w^4) * X 0 1 + (-(3 : ℂ) - 3 * w^2 - 3 * w^4) * X 0 2 + (-9 * w + 3 * w^3 - 3 * w^5) * X 0 3 + (-9 * w^2 - 3 * w^4 + 3 * w^6) * X 0 4 + ((3 : ℂ) + 3 * w^2 + 3 * w^4) * X 2 0 + (-(3 : ℂ) - 3 * w^2 - 3 * w^4) * X 2 1 + ((3 : ℂ) + 3 * w^2 + 3 * w^4) * X 2 2 + (9 * w - 3 * w^3 + 3 * w^5) * X 2 3 + (9 * w^2 + 3 * w^4 - 3 * w^6) * X 2 4) * hI + (((3 : ℂ) - 3 * w + 3 * w^2) * X 0 0 + (-(3 : ℂ) + 3 * w - 3 * w^2) * X 0 1 + ((3 : ℂ) - 3 * w + 3 * w^2) * X 0 2 + ((6 : ℂ) - 3 * w - 3 * w^2 + 3 * w^3) * X 0 3 + ((12 : ℂ) - 6 * w + 3 * w^2 + 3 * w^3 - 3 * w^4) * X 0 4 + (-3 * Complex.I + 3 * Complex.I * w - 3 * Complex.I * w^2) * X 1 0 + (3 * Complex.I - 3 * Complex.I * w + 3 * Complex.I * w^2) * X 1 1 + (-3 * Complex.I + 3 * Complex.I * w - 3 * Complex.I * w^2) * X 1 2 + (-6 * Complex.I + 3 * Complex.I * w + 3 * Complex.I * w^2 - 3 * Complex.I * w^3) * X 1 3 + (-12 * Complex.I + 6 * Complex.I * w - 3 * Complex.I * w^2 - 3 * Complex.I * w^3 + 3 * Complex.I * w^4) * X 1 4 + (-(3 : ℂ) + 3 * w - 3 * w^2) * X 2 0 + ((3 : ℂ) - 3 * w + 3 * w^2) * X 2 1 + (-(3 : ℂ) + 3 * w - 3 * w^2) * X 2 2 + (-(6 : ℂ) + 3 * w + 3 * w^2 - 3 * w^3) * X 2 3 + (-(12 : ℂ) + 6 * w - 3 * w^2 - 3 * w^3 + 3 * w^4) * X 2 4 + (3 * Complex.I - 3 * Complex.I * w + 3 * Complex.I * w^2) * X 3 0 + (-3 * Complex.I + 3 * Complex.I * w - 3 * Complex.I * w^2) * X 3 1 + (3 * Complex.I - 3 * Complex.I * w + 3 * Complex.I * w^2) * X 3 2 + (6 * Complex.I - 3 * Complex.I * w - 3 * Complex.I * w^2 + 3 * Complex.I * w^3) * X 3 3 + (12 * Complex.I - 6 * Complex.I * w + 3 * Complex.I * w^2 + 3 * Complex.I * w^3 - 3 * Complex.I * w^4) * X 3 4) * hw
  have hpiv_0 : X 0 0 = (-Complex.I) * X 2 1 + ((1 : ℂ) - Complex.I) * X 3 1 + ((1 : ℂ)) * X 3 2 + ((1 : ℂ)) * X 3 3 + ((1 : ℂ)) * X 3 4 := by
    linear_combination (((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_0 + (-((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_1 + (-((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_2 + (-((3 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_3 + (((1 : ℂ) / 2)) * heq_4 + (((1 : ℂ) / 2) * Complex.I) * heq_5 + (((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_8 + (-((1 : ℂ) / 24) + ((1 : ℂ) / 24) * Complex.I) * heq_12 + ((-((1 : ℂ) / 4)) * X 1 0 + (((1 : ℂ) / 4)) * X 1 1 + (((1 : ℂ) / 4)) * X 1 2 + (((1 : ℂ) / 4)) * X 1 3 + (((1 : ℂ) / 4)) * X 1 4 + (((1 : ℂ) / 4)) * X 3 0 + (-((1 : ℂ) / 4)) * X 3 1 + (-((1 : ℂ) / 4)) * X 3 2 + (-((1 : ℂ) / 4)) * X 3 3 + (-((1 : ℂ) / 4)) * X 3 4) * hI
  have hpiv_1 : X 0 1 = (Complex.I) * X 2 1 + (-(1 : ℂ) + Complex.I) * X 3 1 + (-(1 : ℂ) + Complex.I) * X 3 2 + (-(1 : ℂ) + Complex.I) * X 3 3 + (-(1 : ℂ) + Complex.I) * X 3 4 := by
    linear_combination (((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_0 + (((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_1 + (-((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_2 + (((3 : ℂ) / 4) - ((3 : ℂ) / 4) * Complex.I) * heq_3 + (-((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_4 + (((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_5 + (-((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_8 + (((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_10 + (-((1 : ℂ) / 24) - ((1 : ℂ) / 24) * Complex.I) * heq_12 + ((((1 : ℂ) / 4)) * X 1 0 + (-((1 : ℂ) / 4)) * X 1 1 + (-((1 : ℂ) / 4)) * X 1 2 + (-((1 : ℂ) / 4)) * X 1 3 + (-((1 : ℂ) / 4)) * X 1 4 + (-((1 : ℂ) / 4)) * X 3 0 + (((1 : ℂ) / 4)) * X 3 1 + (((1 : ℂ) / 4)) * X 3 2 + (((1 : ℂ) / 4)) * X 3 3 + (((1 : ℂ) / 4)) * X 3 4) * hI
  have hpiv_2 : X 0 2 = (-w) * X 2 4 + (((1 : ℂ) / 3) * w - ((1 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 2 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w - ((1 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 3 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 4 := by
    linear_combination (((1 : ℂ) / 3) * w) * heq_0 + (-((1 : ℂ) / 6) + ((1 : ℂ) / 6) * w + ((1 : ℂ) / 6) * Complex.I - ((1 : ℂ) / 6) * Complex.I * w) * heq_1 + (((1 : ℂ) / 3) * w) * heq_2 + (-((1 : ℂ) / 6) + ((1 : ℂ) / 6) * w + ((1 : ℂ) / 6) * Complex.I - ((1 : ℂ) / 6) * Complex.I * w) * heq_3 + (((1 : ℂ) / 12) - ((1 : ℂ) / 4) * w - ((1 : ℂ) / 12) * Complex.I + ((1 : ℂ) / 12) * Complex.I * w) * heq_4 + (((1 : ℂ) / 12) - ((1 : ℂ) / 4) * w - ((1 : ℂ) / 12) * Complex.I + ((1 : ℂ) / 12) * Complex.I * w) * heq_5 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * heq_6 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_7 + (((1 : ℂ) / 6) + ((1 : ℂ) / 12) * w - ((1 : ℂ) / 12) * Complex.I * w) * heq_9 + (-((1 : ℂ) / 12) - ((1 : ℂ) / 12) * w + ((1 : ℂ) / 12) * Complex.I - ((1 : ℂ) / 12) * Complex.I * w) * heq_10 + (((1 : ℂ) / 6)) * heq_11 + (((1 : ℂ) / 18) - ((1 : ℂ) / 72) * w + ((1 : ℂ) / 72) * Complex.I * w) * heq_12 + (-((1 : ℂ) / 36) - ((1 : ℂ) / 72) * w - ((1 : ℂ) / 72) * Complex.I * w) * heq_13 + ((((1 : ℂ) / 6) * w) * X 1 2 + (((1 : ℂ) / 6) * w^2) * X 1 3 + (-((1 : ℂ) / 6) * w - ((1 : ℂ) / 6) * w^2) * X 1 4 + (-((1 : ℂ) / 6) * w) * X 3 2 + (-((1 : ℂ) / 6) * w^2) * X 3 3 + (((1 : ℂ) / 6) * w + ((1 : ℂ) / 6) * w^2) * X 3 4) * hI + ((-((1 : ℂ) / 6)) * X 0 3 + (((1 : ℂ) / 6)) * X 0 4 + (-((1 : ℂ) / 6)) * X 1 3 + (((1 : ℂ) / 6)) * X 1 4 + (((1 : ℂ) / 6)) * X 2 3 + (-((1 : ℂ) / 6)) * X 2 4 + (((1 : ℂ) / 6)) * X 3 3 + (-((1 : ℂ) / 6)) * X 3 4) * hw
  have hpiv_3 : X 0 3 = ((1 : ℂ) + w) * X 2 4 + (((1 : ℂ) / 3) * w - ((2 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 2 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w - ((2 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 3 + (((1 : ℂ) / 3) - ((2 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 4 := by
    linear_combination (-((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * heq_0 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w + ((1 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 6) * Complex.I * w) * heq_1 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * heq_2 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w + ((1 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 6) * Complex.I * w) * heq_3 + (((1 : ℂ) / 3) + ((1 : ℂ) / 4) * w - ((1 : ℂ) / 6) * Complex.I - ((1 : ℂ) / 12) * Complex.I * w) * heq_4 + (((1 : ℂ) / 3) + ((1 : ℂ) / 4) * w - ((1 : ℂ) / 6) * Complex.I - ((1 : ℂ) / 12) * Complex.I * w) * heq_5 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * heq_6 + (((2 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * heq_7 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 12) * w - ((1 : ℂ) / 12) * Complex.I * w) * heq_9 + (((1 : ℂ) / 12) * w + ((1 : ℂ) / 6) * Complex.I + ((1 : ℂ) / 12) * Complex.I * w) * heq_10 + (((1 : ℂ) / 6) * w) * heq_11 + (((1 : ℂ) / 36) + ((1 : ℂ) / 72) * w + ((1 : ℂ) / 72) * Complex.I * w) * heq_12 + (((1 : ℂ) / 36) + ((1 : ℂ) / 72) * w - ((1 : ℂ) / 72) * Complex.I * w) * heq_13 + ((((1 : ℂ) / 6) * w) * X 1 2 + (((1 : ℂ) / 6) * w^2) * X 1 3 + (-((1 : ℂ) / 6) * w - ((1 : ℂ) / 6) * w^2) * X 1 4 + (-((1 : ℂ) / 6) * w) * X 3 2 + (-((1 : ℂ) / 6) * w^2) * X 3 3 + (((1 : ℂ) / 6) * w + ((1 : ℂ) / 6) * w^2) * X 3 4) * hI + ((((1 : ℂ) / 3)) * X 0 3 + (-((1 : ℂ) / 3)) * X 0 4 + (-((1 : ℂ) / 3)) * X 1 3 + (((1 : ℂ) / 3)) * X 1 4) * hw
  have hpiv_4 : X 0 4 = (-(1 : ℂ)) * X 2 4 + (-((2 : ℂ) / 3) * w) * X 3 2 + (((2 : ℂ) / 3) + ((2 : ℂ) / 3) * w) * X 3 3 + (-((2 : ℂ) / 3)) * X 3 4 := by
    linear_combination (((5 : ℂ) / 6)) * heq_0 + (((1 : ℂ) / 2)) * heq_1 + (((5 : ℂ) / 6)) * heq_2 + (((1 : ℂ) / 2)) * heq_3 + (-((2 : ℂ) / 3)) * heq_4 + (-((2 : ℂ) / 3)) * heq_5 + (-((2 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * heq_6 + (-((5 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_7 + (((1 : ℂ) / 6) * Complex.I * w) * heq_9 + (-((1 : ℂ) / 6)) * heq_10 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_11 + (-((1 : ℂ) / 36) * Complex.I * w) * heq_12 + (((1 : ℂ) / 36) * Complex.I * w) * heq_13 + ((-((1 : ℂ) / 3) * w) * X 1 2 + (-((1 : ℂ) / 3) * w^2) * X 1 3 + (((1 : ℂ) / 3) * w + ((1 : ℂ) / 3) * w^2) * X 1 4 + (((1 : ℂ) / 3) * w) * X 3 2 + (((1 : ℂ) / 3) * w^2) * X 3 3 + (-((1 : ℂ) / 3) * w - ((1 : ℂ) / 3) * w^2) * X 3 4) * hI + ((-((1 : ℂ) / 6)) * X 0 3 + (((1 : ℂ) / 6)) * X 0 4 + (((1 : ℂ) / 2)) * X 1 3 + (-((1 : ℂ) / 2)) * X 1 4 + (-((1 : ℂ) / 6)) * X 2 3 + (((1 : ℂ) / 6)) * X 2 4 + (-((1 : ℂ) / 6)) * X 3 3 + (((1 : ℂ) / 6)) * X 3 4) * hw
  have hpiv_5 : X 1 0 = ((1 : ℂ) + Complex.I) * X 2 1 + (Complex.I) * X 3 1 + (Complex.I) * X 3 2 + (Complex.I) * X 3 3 + (Complex.I) * X 3 4 := by
    linear_combination (((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_0 + (((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_1 + (-((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_2 + (-((1 : ℂ) / 4) - ((3 : ℂ) / 4) * Complex.I) * heq_3 + (((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_4 + (-((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_5 + (-((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_8 + (-((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_10 + (-((1 : ℂ) / 24) - ((1 : ℂ) / 24) * Complex.I) * heq_12 + ((((1 : ℂ) / 4)) * X 1 0 + (-((1 : ℂ) / 4)) * X 1 1 + (-((1 : ℂ) / 4)) * X 1 2 + (-((1 : ℂ) / 4)) * X 1 3 + (-((1 : ℂ) / 4)) * X 1 4 + (-((1 : ℂ) / 4)) * X 3 0 + (((1 : ℂ) / 4)) * X 3 1 + (((1 : ℂ) / 4)) * X 3 2 + (((1 : ℂ) / 4)) * X 3 3 + (((1 : ℂ) / 4)) * X 3 4) * hI
  have hpiv_6 : X 1 1 = (-(1 : ℂ) - Complex.I) * X 2 1 + (-Complex.I) * X 3 1 + ((1 : ℂ) - Complex.I) * X 3 2 + ((1 : ℂ) - Complex.I) * X 3 3 + ((1 : ℂ) - Complex.I) * X 3 4 := by
    linear_combination (-((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_0 + (-((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_1 + (((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_2 + (-((3 : ℂ) / 4) + ((3 : ℂ) / 4) * Complex.I) * heq_3 + (((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_4 + (((3 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_5 + (((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_8 + (-((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_10 + (((1 : ℂ) / 24) + ((1 : ℂ) / 24) * Complex.I) * heq_12 + ((-((1 : ℂ) / 4)) * X 1 0 + (((1 : ℂ) / 4)) * X 1 1 + (((1 : ℂ) / 4)) * X 1 2 + (((1 : ℂ) / 4)) * X 1 3 + (((1 : ℂ) / 4)) * X 1 4 + (((1 : ℂ) / 4)) * X 3 0 + (-((1 : ℂ) / 4)) * X 3 1 + (-((1 : ℂ) / 4)) * X 3 2 + (-((1 : ℂ) / 4)) * X 3 3 + (-((1 : ℂ) / 4)) * X 3 4) * hI
  have hpiv_7 : X 1 2 = (-((1 : ℂ) / 3)) * X 3 2 + (((2 : ℂ) / 3) * w) * X 3 3 + (-((2 : ℂ) / 3) - ((2 : ℂ) / 3) * w) * X 3 4 := by
    linear_combination (((1 : ℂ) / 6) * w) * heq_0 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * heq_1 + (((1 : ℂ) / 6) * w) * heq_2 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * heq_3 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_4 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_5 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_6 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 3) * w) * heq_7 + (-((1 : ℂ) / 6) * Complex.I) * heq_9 + (((1 : ℂ) / 6)) * heq_10 + (-((1 : ℂ) / 6)) * heq_11 + (((1 : ℂ) / 36) * Complex.I) * heq_12 + (-((1 : ℂ) / 36) * Complex.I) * heq_13 + ((((1 : ℂ) / 3)) * X 1 2 + (((1 : ℂ) / 3) * w) * X 1 3 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 1 4 + (-((1 : ℂ) / 3)) * X 3 2 + (-((1 : ℂ) / 3) * w) * X 3 3 + (((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 4) * hI
  have hpiv_8 : X 1 3 = (-((2 : ℂ) / 3) - ((2 : ℂ) / 3) * w) * X 3 2 + (-((1 : ℂ) / 3)) * X 3 3 + (((2 : ℂ) / 3) * w) * X 3 4 := by
    linear_combination (-((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_0 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_1 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_2 + (((1 : ℂ) / 6) - ((1 : ℂ) / 6) * w) * heq_3 + (((1 : ℂ) / 6) * w) * heq_4 + (((1 : ℂ) / 6) * w) * heq_5 + (((1 : ℂ) / 6) + ((1 : ℂ) / 3) * w) * heq_6 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * heq_7 + (((1 : ℂ) / 6) * Complex.I + ((1 : ℂ) / 6) * Complex.I * w) * heq_9 + (((1 : ℂ) / 6)) * heq_10 + (-((1 : ℂ) / 6) * w) * heq_11 + (-((1 : ℂ) / 36) * Complex.I - ((1 : ℂ) / 36) * Complex.I * w) * heq_12 + (((1 : ℂ) / 36) * Complex.I + ((1 : ℂ) / 36) * Complex.I * w) * heq_13 + ((-((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w) * X 1 2 + (-((1 : ℂ) / 3) * w - ((1 : ℂ) / 3) * w^2) * X 1 3 + (((1 : ℂ) / 3) + ((2 : ℂ) / 3) * w + ((1 : ℂ) / 3) * w^2) * X 1 4 + (((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w) * X 3 2 + (((1 : ℂ) / 3) * w + ((1 : ℂ) / 3) * w^2) * X 3 3 + (-((1 : ℂ) / 3) - ((2 : ℂ) / 3) * w - ((1 : ℂ) / 3) * w^2) * X 3 4) * hI + ((-((1 : ℂ) / 6)) * X 0 3 + (((1 : ℂ) / 6)) * X 0 4 + (((1 : ℂ) / 2)) * X 1 3 + (-((1 : ℂ) / 2)) * X 1 4 + (-((1 : ℂ) / 6)) * X 2 3 + (((1 : ℂ) / 6)) * X 2 4 + (-((1 : ℂ) / 6)) * X 3 3 + (((1 : ℂ) / 6)) * X 3 4) * hw
  have hpiv_9 : X 1 4 = (((2 : ℂ) / 3) * w) * X 3 2 + (-((2 : ℂ) / 3) - ((2 : ℂ) / 3) * w) * X 3 3 + (-((1 : ℂ) / 3)) * X 3 4 := by
    linear_combination (((1 : ℂ) / 6)) * heq_0 + (((1 : ℂ) / 2)) * heq_1 + (((1 : ℂ) / 6)) * heq_2 + (((1 : ℂ) / 2)) * heq_3 + (-((1 : ℂ) / 3)) * heq_4 + (-((1 : ℂ) / 3)) * heq_5 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w) * heq_6 + (-((1 : ℂ) / 6) + ((1 : ℂ) / 6) * w) * heq_7 + (-((1 : ℂ) / 6) * Complex.I * w) * heq_9 + (((1 : ℂ) / 6)) * heq_10 + (((1 : ℂ) / 6) + ((1 : ℂ) / 6) * w) * heq_11 + (((1 : ℂ) / 36) * Complex.I * w) * heq_12 + (-((1 : ℂ) / 36) * Complex.I * w) * heq_13 + ((((1 : ℂ) / 3) * w) * X 1 2 + (((1 : ℂ) / 3) * w^2) * X 1 3 + (-((1 : ℂ) / 3) * w - ((1 : ℂ) / 3) * w^2) * X 1 4 + (-((1 : ℂ) / 3) * w) * X 3 2 + (-((1 : ℂ) / 3) * w^2) * X 3 3 + (((1 : ℂ) / 3) * w + ((1 : ℂ) / 3) * w^2) * X 3 4) * hI + ((((1 : ℂ) / 6)) * X 0 3 + (-((1 : ℂ) / 6)) * X 0 4 + (-((1 : ℂ) / 2)) * X 1 3 + (((1 : ℂ) / 2)) * X 1 4 + (((1 : ℂ) / 6)) * X 2 3 + (-((1 : ℂ) / 6)) * X 2 4 + (((1 : ℂ) / 6)) * X 3 3 + (-((1 : ℂ) / 6)) * X 3 4) * hw
  have hpiv_10 : X 2 0 = (-(1 : ℂ)) * X 2 1 + (-Complex.I) * X 3 2 + (-Complex.I) * X 3 3 + (-Complex.I) * X 3 4 := by
    linear_combination (-((1 : ℂ) / 2)) * heq_0 + (((1 : ℂ) / 2) * Complex.I) * heq_1 + (((1 : ℂ) / 2)) * heq_2 + (((1 : ℂ) / 2) * Complex.I) * heq_3 + (((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_4 + (((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * heq_5 + (((1 : ℂ) / 4) + ((1 : ℂ) / 4) * Complex.I) * heq_10 + (((1 : ℂ) / 12)) * heq_12
  have hpiv_11 : X 2 2 = (w) * X 2 4 + (-((2 : ℂ) / 3) - ((1 : ℂ) / 3) * w + ((1 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 2 + (((1 : ℂ) / 3) - ((1 : ℂ) / 3) * w + ((1 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 3 + (((1 : ℂ) / 3) + ((2 : ℂ) / 3) * w + ((1 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 3) * Complex.I * w) * X 3 4 := by
    linear_combination (-((1 : ℂ) / 2) * w) * heq_0 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 3) * w - ((1 : ℂ) / 6) * Complex.I + ((1 : ℂ) / 6) * Complex.I * w) * heq_1 + (-((1 : ℂ) / 2) * w) * heq_2 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 3) * w - ((1 : ℂ) / 6) * Complex.I + ((1 : ℂ) / 6) * Complex.I * w) * heq_3 + (((1 : ℂ) / 12) + ((5 : ℂ) / 12) * w + ((1 : ℂ) / 12) * Complex.I - ((1 : ℂ) / 12) * Complex.I * w) * heq_4 + (((1 : ℂ) / 12) + ((5 : ℂ) / 12) * w + ((1 : ℂ) / 12) * Complex.I - ((1 : ℂ) / 12) * Complex.I * w) * heq_5 + (((1 : ℂ) / 2) + ((1 : ℂ) / 2) * w) * heq_6 + (((1 : ℂ) / 2) * w) * heq_7 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 12) * w + ((1 : ℂ) / 6) * Complex.I + ((1 : ℂ) / 12) * Complex.I * w) * heq_9 + (-((1 : ℂ) / 12) + ((1 : ℂ) / 12) * w - ((1 : ℂ) / 12) * Complex.I + ((1 : ℂ) / 12) * Complex.I * w) * heq_10 + (-((1 : ℂ) / 18) + ((1 : ℂ) / 72) * w - ((1 : ℂ) / 36) * Complex.I - ((1 : ℂ) / 72) * Complex.I * w) * heq_12 + (((1 : ℂ) / 36) + ((1 : ℂ) / 72) * w + ((1 : ℂ) / 36) * Complex.I + ((1 : ℂ) / 72) * Complex.I * w) * heq_13 + ((-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w) * X 1 2 + (-((1 : ℂ) / 3) * w - ((1 : ℂ) / 6) * w^2) * X 1 3 + (((1 : ℂ) / 3) + ((1 : ℂ) / 2) * w + ((1 : ℂ) / 6) * w^2) * X 1 4 + (((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * X 3 2 + (((1 : ℂ) / 3) * w + ((1 : ℂ) / 6) * w^2) * X 3 3 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 2) * w - ((1 : ℂ) / 6) * w^2) * X 3 4) * hI + ((((1 : ℂ) / 6)) * X 0 3 + (-((1 : ℂ) / 6)) * X 0 4 + (((1 : ℂ) / 6)) * X 1 3 + (-((1 : ℂ) / 6)) * X 1 4 + (-((1 : ℂ) / 6)) * X 2 3 + (((1 : ℂ) / 6)) * X 2 4 + (-((1 : ℂ) / 6)) * X 3 3 + (((1 : ℂ) / 6)) * X 3 4) * hw
  have hpiv_12 : X 2 3 = (-(1 : ℂ) - w) * X 2 4 + (((2 : ℂ) / 3) + ((1 : ℂ) / 3) * w + ((2 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 2 + (-((1 : ℂ) / 3) + ((1 : ℂ) / 3) * w + ((2 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 3 + (-((1 : ℂ) / 3) - ((2 : ℂ) / 3) * w + ((2 : ℂ) / 3) * Complex.I + ((1 : ℂ) / 3) * Complex.I * w) * X 3 4 := by
    linear_combination (((1 : ℂ) / 2) + ((1 : ℂ) / 2) * w) * heq_0 + (((1 : ℂ) / 6) + ((1 : ℂ) / 3) * w - ((1 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 6) * Complex.I * w) * heq_1 + (((1 : ℂ) / 2) + ((1 : ℂ) / 2) * w) * heq_2 + (((1 : ℂ) / 6) + ((1 : ℂ) / 3) * w - ((1 : ℂ) / 3) * Complex.I - ((1 : ℂ) / 6) * Complex.I * w) * heq_3 + (-((1 : ℂ) / 3) - ((5 : ℂ) / 12) * w + ((1 : ℂ) / 6) * Complex.I + ((1 : ℂ) / 12) * Complex.I * w) * heq_4 + (-((1 : ℂ) / 3) - ((5 : ℂ) / 12) * w + ((1 : ℂ) / 6) * Complex.I + ((1 : ℂ) / 12) * Complex.I * w) * heq_5 + (-((1 : ℂ) / 2) - ((1 : ℂ) / 2) * w) * heq_6 + (-((1 : ℂ) / 2) * w) * heq_7 + (((1 : ℂ) / 6) + ((1 : ℂ) / 12) * w - ((1 : ℂ) / 6) * Complex.I - ((1 : ℂ) / 12) * Complex.I * w) * heq_9 + (-((1 : ℂ) / 6) - ((1 : ℂ) / 12) * w - ((1 : ℂ) / 6) * Complex.I - ((1 : ℂ) / 12) * Complex.I * w) * heq_10 + (-((1 : ℂ) / 36) - ((1 : ℂ) / 72) * w + ((1 : ℂ) / 36) * Complex.I + ((1 : ℂ) / 72) * Complex.I * w) * heq_12 + (-((1 : ℂ) / 36) - ((1 : ℂ) / 72) * w - ((1 : ℂ) / 36) * Complex.I - ((1 : ℂ) / 72) * Complex.I * w) * heq_13 + ((((1 : ℂ) / 3) + ((1 : ℂ) / 6) * w) * X 1 2 + (((1 : ℂ) / 3) * w + ((1 : ℂ) / 6) * w^2) * X 1 3 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 2) * w - ((1 : ℂ) / 6) * w^2) * X 1 4 + (-((1 : ℂ) / 3) - ((1 : ℂ) / 6) * w) * X 3 2 + (-((1 : ℂ) / 3) * w - ((1 : ℂ) / 6) * w^2) * X 3 3 + (((1 : ℂ) / 3) + ((1 : ℂ) / 2) * w + ((1 : ℂ) / 6) * w^2) * X 3 4) * hI + ((-((1 : ℂ) / 6)) * X 0 3 + (((1 : ℂ) / 6)) * X 0 4 + (-((1 : ℂ) / 6)) * X 1 3 + (((1 : ℂ) / 6)) * X 1 4 + (((1 : ℂ) / 6)) * X 2 3 + (-((1 : ℂ) / 6)) * X 2 4 + (((1 : ℂ) / 6)) * X 3 3 + (-((1 : ℂ) / 6)) * X 3 4) * hw
  have hpiv_13 : X 3 0 = (-(1 : ℂ)) * X 3 1 + (-(1 : ℂ)) * X 3 2 + (-(1 : ℂ)) * X 3 3 + (-(1 : ℂ)) * X 3 4 := by
    linear_combination ((1 : ℂ)) * heq_3
  exact ⟨hpiv_0, hpiv_1, hpiv_2, hpiv_3, hpiv_4, hpiv_5, hpiv_6, hpiv_7, hpiv_8, hpiv_9, hpiv_10, hpiv_11, hpiv_12, hpiv_13⟩


def dot6 (u v : Fin 6 → ℂ) : ℂ := ∑ i : Fin 6, u i * v i

def dot6Map : (Fin 6 → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin 6 → ℂ) where
  toFun u :=
    { toFun := fun v => dot6 u v
      map_add' := fun x y => by simp [dot6, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [dot6, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring }
  map_add' x y := by
    apply LinearMap.ext; intro v; simp [dot6, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    apply LinearMap.ext; intro v
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, dot6, Pi.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

lemma dot6Map_inj : Function.Injective dot6Map := by
  intro x y h
  funext i
  have hi := LinearMap.congr_fun h (Pi.single i 1)
  change dot6 x (Pi.single i 1) = dot6 y (Pi.single i 1) at hi
  simpa [dot6, Pi.single_apply] using hi

lemma dot6Map_surj : Function.Surjective dot6Map := by
  have h := LinearMap.finrank_range_add_finrank_ker dot6Map
  have hk : Module.finrank ℂ (LinearMap.ker dot6Map) = 0 := by
    rw [LinearMap.ker_eq_bot.mpr dot6Map_inj, finrank_bot]
  have hd : Module.finrank ℂ (Module.Dual ℂ (Fin 6 → ℂ)) = 6 := by
    rw [Subspace.dual_finrank_eq, Module.finrank_fin_fun]
  have htop : LinearMap.range dot6Map = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [hd]; rw [Module.finrank_fin_fun, hk] at h; omega)
  exact LinearMap.range_eq_top.mp htop

lemma isotropic_finrank_le_four (W : Submodule ℂ (Fin 6 → ℂ))
    (M : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ))
    (hker : Module.finrank ℂ (LinearMap.ker M) ≤ 3)
    (hiso : ∀ x ∈ W, ∀ y ∈ W, dot6 (M x) y = 0) :
    Module.finrank ℂ W ≤ 4 := by
  let φ : (Fin 6 → ℂ) →ₗ[ℂ] Module.Dual ℂ W := W.subtype.dualMap.comp dot6Map
  have hres_surj : Function.Surjective W.subtype.dualMap := by
    intro f
    obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
    refine ⟨f.comp (Submodule.projectionOnto W Q hQ), ?_⟩
    ext w
    change f (Submodule.projectionOnto W Q hQ w.1) = f w
    rw [Submodule.projectionOnto_apply_left hQ w]
  have hφ_surj : Function.Surjective φ := hres_surj.comp dot6Map_surj
  have hrφ : Module.finrank ℂ (LinearMap.range φ) = Module.finrank ℂ W := by
    rw [LinearMap.range_eq_top.mpr hφ_surj, finrank_top, Subspace.dual_finrank_eq]
  have hkφ : Module.finrank ℂ (LinearMap.ker φ) + Module.finrank ℂ W = 6 := by
    have h := LinearMap.finrank_range_add_finrank_ker φ
    rw [hrφ, Module.finrank_fin_fun] at h
    omega
  have hle : W.map M ≤ LinearMap.ker φ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [LinearMap.mem_ker]
    ext ⟨y, hy⟩
    exact hiso x hx y hy
  have hmap_le : Module.finrank ℂ (W.map M) ≤ Module.finrank ℂ (LinearMap.ker φ) :=
    Submodule.finrank_mono hle
  let Mres : W →ₗ[ℂ] (Fin 6 → ℂ) := M.domRestrict W
  have hrn := LinearMap.finrank_range_add_finrank_ker Mres
  have hr_eq : LinearMap.range Mres = W.map M := by
    ext z; simp [Mres, LinearMap.mem_range, Submodule.mem_map]
  have hker_sub : Module.finrank ℂ (LinearMap.ker Mres) ≤ Module.finrank ℂ (LinearMap.ker M) := by
    let f : LinearMap.ker Mres →ₗ[ℂ] LinearMap.ker M :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b hab => by
      apply Subtype.ext; apply Subtype.ext; simpa [f] using congrArg Subtype.val hab
    exact LinearMap.finrank_le_finrank_of_injective hf
  rw [hr_eq] at hrn
  omega

lemma dft5_zero (z : ℂ) (hz : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0) (v : Vec)
    (h0 : v 0 + v 1 + v 2 + v 3 + v 4 = 0)
    (h1 : v 0 + z * v 1 + z ^ 2 * v 2 + z ^ 3 * v 3 + z ^ 4 * v 4 = 0)
    (h2 : v 0 + z ^ 2 * v 1 + z ^ 4 * v 2 + z * v 3 + z ^ 3 * v 4 = 0)
    (h3 : v 0 + z ^ 3 * v 1 + z * v 2 + z ^ 4 * v 3 + z ^ 2 * v 4 = 0)
    (h4 : v 0 + z ^ 4 * v 1 + z ^ 3 * v 2 + z ^ 2 * v 3 + z * v 4 = 0) :
    ∀ j : Fin 5, v j = 0 := by
  have hv0 : v 0 = 0 := by
    linear_combination (h0 + h1 + h2 + h3 + h4 - (v 1 + v 2 + v 3 + v 4) * hz) / 5
  have hv1 : v 1 = 0 := by
    linear_combination (h0 + z ^ 4 * h1 + z ^ 3 * h2 + z ^ 2 * h3 + z * h4 -
      (v 0 + (-4 + 4 * z) * v 1 + (1 - z + z ^ 3) * v 2 +
       (1 - z + z ^ 3) * v 3 + (1 - z + z ^ 2 - z ^ 3 + z ^ 4) * v 4) * hz) / 5
  have hv2 : v 2 = 0 := by
    linear_combination (h0 + z ^ 3 * h1 + z * h2 + z ^ 4 * h3 + z ^ 2 * h4 -
      (v 0 + (1 - z + z ^ 3) * v 1 + (-4 + 4 * z) * v 2 +
       (1 - z + z ^ 2 - z ^ 3 + z ^ 4) * v 3 + (1 - z + z ^ 3) * v 4) * hz) / 5
  have hv3 : v 3 = 0 := by
    linear_combination (h0 + z ^ 2 * h1 + z ^ 4 * h2 + z * h3 + z ^ 3 * h4 -
      (v 0 + (1 - z + z ^ 3) * v 1 + (1 - z + z ^ 2 - z ^ 3 + z ^ 4) * v 2 +
       (-4 + 4 * z) * v 3 + (1 - z + z ^ 3) * v 4) * hz) / 5
  have hv4 : v 4 = 0 := by
    linear_combination (h0 + z * h1 + z ^ 2 * h2 + z ^ 3 * h3 + z ^ 4 * h4 -
      (v 0 + (1 - z + z ^ 2 - z ^ 3 + z ^ 4) * v 1 + (1 - z + z ^ 3) * v 2 +
       (1 - z + z ^ 3) * v 3 + (-4 + 4 * z) * v 4) * hz) / 5
  intro j
  fin_cases j
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3
  · exact hv4

lemma case_3b_ker (w z : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (hz : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0)
    (L : Submodule ℂ Mat) (hL : ValidL L)
    (h0 : outer ![1, w, w ^ 2, 0] ![1, z, z ^ 2, z ^ 3, z ^ 4] ∈ L)
    (h1 : outer ![1, w, w ^ 2, 0] ![1, z ^ 4, z ^ 3, z ^ 2, z] ∈ L)
    (X : Mat) (hX : X ∈ L)
    (hf0 : X 2 1 = 0) (hf1 : X 2 2 = 0) (hf2 : X 2 3 = 0) (hf3 : X 2 4 = 0) :
    X = 0 := by
  let a : Fin 4 → ℂ := ![1, w, w ^ 2, 0]
  let u0 : Vec := ![1, z, z ^ 2, z ^ 3, z ^ 4]
  let u1 : Vec := ![1, z ^ 4, z ^ 3, z ^ 2, z]
  have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  have hz5 : z ^ 5 = 1 := by linear_combination (z - 1) * hz
  have hq4_r3 : ∀ u : Vec, outer a u ∈ L →
      dot u u * dot u (X 3) - 2 * ∑ j : Fin 5, (u j) ^ 3 * X 3 j = 0 := by
    intro u hu
    have hq := lin_q4_zero L hL X hX (outer a u) hu
    have hy0 : outer a u 0 = u := by ext j; simp [outer, a]
    have hy1 : outer a u 1 = w • u := by ext j; simp [outer, a]
    have hy2 : outer a u 2 = (w ^ 2) • u := by ext j; simp [outer, a]
    have hy3 : outer a u 3 = 0 := by ext j; simp [outer, a]
    have hd_smul_l : ∀ (c : ℂ) (p q : Vec), dot (c • p) q = c * dot p q := by
      intro c p q; simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hd_smul_r : ∀ (c : ℂ) (p q : Vec), dot p (c • q) = c * dot p q := by
      intro c p q; simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    have hd_z_l : ∀ p : Vec, dot 0 p = 0 := fun p => by simp [dot]
    have hd_z_r : ∀ p : Vec, dot p 0 = 0 := fun p => by simp [dot]
    rw [hy0, hy1, hy2, hy3] at hq
    simp only [hd_z_l, hd_z_r, hd_smul_l, hd_smul_r, Pi.zero_apply, Pi.smul_apply, smul_eq_mul,
      mul_zero, zero_mul, add_zero, zero_add] at hq
    have hsum3 : (∑ j : Fin 5, u j * (w * u j) * (w ^ 2 * u j) * X 3 j) =
        w ^ 3 * ∑ j : Fin 5, (u j) ^ 3 * X 3 j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
    rw [hsum3] at hq
    linear_combination (hq - 3 * (dot u u * dot u (X 3) - 2 * ∑ j : Fin 5, (u j) ^ 3 * X 3 j) * hw3) / 3
  have hu01_prod : ∀ j : Fin 5, u0 j * u1 j = 1 := by
    intro j; fin_cases j <;> simp [u0, u1]
    · linear_combination hz5
    · linear_combination hz5
    · linear_combination hz5
    · linear_combination hz5
  have hu0_sq : dot u0 u0 = 0 := by
    simp only [dot, u0, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (z ^ 3 + z) * hz5 + hz
  have hu1_sq : dot u1 u1 = 0 := by
    simp only [dot, u1, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (z ^ 3 + z) * hz5 + hz
  have hu01_dot : dot u0 u1 = 5 := by
    unfold dot; simp_rw [hu01_prod]; simp
  have hsum_u0c : ∑ j : Fin 5, (u0 j) ^ 3 * X 3 j = 0 := by
    have h := hq4_r3 u0 h0
    rw [hu0_sq, zero_mul, zero_sub] at h
    linear_combination -h / 2
  have hsum_u1c : ∑ j : Fin 5, (u1 j) ^ 3 * X 3 j = 0 := by
    have h := hq4_r3 u1 h1
    rw [hu1_sq, zero_mul, zero_sub] at h
    linear_combination -h / 2
  have h01_mem : outer a (u0 + u1) ∈ L := by
    have := L.add_mem h0 h1; convert this using 1; ext i j; simp [outer, a, u0, u1, mul_add]
  have h0m1_mem : outer a (u0 - u1) ∈ L := by
    have := L.sub_mem h0 h1; convert this using 1; ext i j; simp [outer, a, u0, u1, mul_sub]
  have hdot_p : dot (u0 + u1) (X 3) = 0 := by
    have h := hq4_r3 (u0 + u1) h01_mem
    have hsq : dot (u0 + u1) (u0 + u1) = 10 := by
      have : dot (u0 + u1) (u0 + u1) = dot u0 u0 + 2 * dot u0 u1 + dot u1 u1 := by
        unfold dot; simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [this, hu0_sq, hu1_sq, hu01_dot]; norm_num
    have hcb : (∑ j : Fin 5, ((u0 + u1) j) ^ 3 * X 3 j) =
        (∑ j : Fin 5, (u0 j) ^ 3 * X 3 j) + (∑ j : Fin 5, (u1 j) ^ 3 * X 3 j) +
        3 * dot (u0 + u1) (X 3) := by
      unfold dot; simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination 3 * (u0 j + u1 j) * X 3 j * hu01_prod j
    rw [hsq, hcb, hsum_u0c, hsum_u1c] at h
    linear_combination h / 4
  have hdot_m : dot (u0 - u1) (X 3) = 0 := by
    have h := hq4_r3 (u0 - u1) h0m1_mem
    have hsq : dot (u0 - u1) (u0 - u1) = -10 := by
      have : dot (u0 - u1) (u0 - u1) = dot u0 u0 - 2 * dot u0 u1 + dot u1 u1 := by
        unfold dot; simp only [Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [this, hu0_sq, hu1_sq, hu01_dot]; norm_num
    have hcb : (∑ j : Fin 5, ((u0 - u1) j) ^ 3 * X 3 j) =
        (∑ j : Fin 5, (u0 j) ^ 3 * X 3 j) - (∑ j : Fin 5, (u1 j) ^ 3 * X 3 j) -
        3 * dot (u0 - u1) (X 3) := by
      unfold dot; simp only [Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination -3 * (u0 j - u1 j) * X 3 j * hu01_prod j
    rw [hsq, hcb, hsum_u0c, hsum_u1c] at h
    linear_combination -h / 4
  have h3_1 : X 3 0 + z * X 3 1 + z ^ 2 * X 3 2 + z ^ 3 * X 3 3 + z ^ 4 * X 3 4 = 0 := by
    have hsum_d : dot u0 (X 3) = 0 := by
      have : dot (u0 + u1) (X 3) + dot (u0 - u1) (X 3) = 2 * dot u0 (X 3) := by
        unfold dot; simp only [Pi.add_apply, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      linear_combination (hdot_p + hdot_m - this) / 2
    simpa [dot, u0, Fin.sum_univ_five] using hsum_d
  have h3_4 : X 3 0 + z ^ 4 * X 3 1 + z ^ 3 * X 3 2 + z ^ 2 * X 3 3 + z * X 3 4 = 0 := by
    have hsum_d : dot u1 (X 3) = 0 := by
      have : dot (u0 + u1) (X 3) - dot (u0 - u1) (X 3) = 2 * dot u1 (X 3) := by
        unfold dot; simp only [Pi.add_apply, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      linear_combination (hdot_p - hdot_m - this) / 2
    simpa [dot, u1, Fin.sum_univ_five] using hsum_d
  have h3_3 : X 3 0 + z ^ 3 * X 3 1 + z * X 3 2 + z ^ 4 * X 3 3 + z ^ 2 * X 3 4 = 0 := by
    simp only [u0, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hsum_u0c
    linear_combination hsum_u0c - (z * X 3 2 + (z ^ 4) * X 3 3 + (z ^ 7 + z ^ 2) * X 3 4) * hz5
  have h3_2 : X 3 0 + z ^ 2 * X 3 1 + z ^ 4 * X 3 2 + z * X 3 3 + z ^ 3 * X 3 4 = 0 := by
    simp only [u1, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hsum_u1c
    linear_combination hsum_u1c - ((z ^ 7 + z ^ 2) * X 3 1 + (z ^ 4) * X 3 2 + z * X 3 3) * hz5
  have h3_0 : X 3 0 + X 3 1 + X 3 2 + X 3 3 + X 3 4 = 0 := by
    have h := (hL X hX).1 3; simpa [Fin.sum_univ_five] using h
  have hX3 : ∀ j : Fin 5, X 3 j = 0 := dft5_zero z hz (X 3) h3_0 h3_1 h3_2 h3_3 h3_4
  have hX2_0 : X 2 0 = 0 := by
    have h := (hL X hX).1 2; simp only [Fin.sum_univ_five, hf0, hf1, hf2, hf3] at h
    linear_combination h
  have hX2 : ∀ j : Fin 5, X 2 j = 0 := by
    intro j; fin_cases j <;> first | exact hX2_0 | exact hf0 | exact hf1 | exact hf2 | exact hf3
  have hX1 : ∀ j : Fin 5, X 1 j = -X 0 j := by
    intro j
    have h := (hL X hX).2.1 j
    simp only [Fin.sum_univ_four, hX2 j, hX3 j] at h
    linear_combination h
  have hw_ne1 : 1 - w ≠ 0 := by
    intro h; have : (3 : ℂ) = 0 := by linear_combination hw + (w + 2) * h
    norm_num at this
  have hw2_ne1 : 1 - w ^ 2 ≠ 0 := by
    intro h; have : (3 : ℂ) = 0 := by linear_combination (2 - w) * hw + (1 - w) * h
    norm_num at this
  have hdot_r0 : ∀ u : Vec, outer a u ∈ L → dot u (X 0) = 0 := by
    intro u hu
    have hd := lin_dot_zero L hL X hX (outer a u) hu
    simp only [Fin.sum_univ_four, outer, a, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      hX2, hX3, zero_mul, mul_zero, Finset.sum_const_zero, add_zero] at hd
    have hfac : (∑ j : Fin 5, X 0 j * (1 * u j)) + (∑ j : Fin 5, X 1 j * (w * u j)) =
        (1 - w) * dot u (X 0) := by
      unfold dot; simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by rw [hX1 j]; ring
    rw [hfac] at hd
    exact (mul_eq_zero.mp hd).resolve_left hw_ne1
  have hd3_r0 : ∀ u : Vec, outer a u ∈ L → ∑ j : Fin 5, (u j) ^ 2 * X 0 j = 0 := by
    intro u hu
    have hd := lin_d3_zero L hL X hX (outer a u) hu
    simp only [Fin.sum_univ_four, outer, a, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      hX2, hX3, zero_mul, mul_zero, Finset.sum_const_zero, add_zero] at hd
    have hfac : (∑ j : Fin 5, X 0 j * (1 * u j) ^ 2) + (∑ j : Fin 5, X 1 j * (w * u j) ^ 2) =
        (1 - w ^ 2) * ∑ j : Fin 5, (u j) ^ 2 * X 0 j := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by rw [hX1 j]; ring
    rw [hfac] at hd
    exact (mul_eq_zero.mp hd).resolve_left hw2_ne1
  have h0_0 : X 0 0 + X 0 1 + X 0 2 + X 0 3 + X 0 4 = 0 := by
    have h := (hL X hX).1 0; simpa [Fin.sum_univ_five] using h
  have h0_1 : X 0 0 + z * X 0 1 + z ^ 2 * X 0 2 + z ^ 3 * X 0 3 + z ^ 4 * X 0 4 = 0 := by
    simpa [dot, u0, Fin.sum_univ_five] using hdot_r0 u0 h0
  have h0_4 : X 0 0 + z ^ 4 * X 0 1 + z ^ 3 * X 0 2 + z ^ 2 * X 0 3 + z * X 0 4 = 0 := by
    simpa [dot, u1, Fin.sum_univ_five] using hdot_r0 u1 h1
  have h0_2 : X 0 0 + z ^ 2 * X 0 1 + z ^ 4 * X 0 2 + z * X 0 3 + z ^ 3 * X 0 4 = 0 := by
    have h := hd3_r0 u0 h0
    simp only [u0, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
    linear_combination h - (z * X 0 3 + z ^ 3 * X 0 4) * hz5
  have h0_3 : X 0 0 + z ^ 3 * X 0 1 + z * X 0 2 + z ^ 4 * X 0 3 + z ^ 2 * X 0 4 = 0 := by
    have h := hd3_r0 u1 h1
    simp only [u1, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
    linear_combination h - (z ^ 3 * X 0 1 + z * X 0 2) * hz5
  have hX0 : ∀ j : Fin 5, X 0 j = 0 := dft5_zero z hz (X 0) h0_0 h0_1 h0_2 h0_3 h0_4
  ext i j
  fin_cases i
  · exact hX0 j
  · change X 1 j = 0; rw [hX1 j, hX0 j, neg_zero]
  · exact hX2 j
  · exact hX3 j

lemma case_3b_bound (w z : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (hz : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0)
    (L : Submodule ℂ Mat) (hL : ValidL L)
    (h0 : outer ![1, w, w ^ 2, 0] ![1, z, z ^ 2, z ^ 3, z ^ 4] ∈ L)
    (h1 : outer ![1, w, w ^ 2, 0] ![1, z ^ 4, z ^ 3, z ^ 2, z] ∈ L) :
    Module.finrank ℂ L ≤ 4 := by
  let Φ : L →ₗ[ℂ] (Fin 4 → ℂ) :=
    { toFun := fun X => ![X.1 2 1, X.1 2 2, X.1 2 3, X.1 2 4]
      map_add' := fun X Y => by ext k; fin_cases k <;> simp
      map_smul' := fun c X => by ext k; fin_cases k <;> simp }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    apply Subtype.ext
    refine case_3b_ker w z hw hz L hL (by simpa using h0) (by simpa using h1) X.1 X.2 ?_ ?_ ?_ ?_
    · exact congrFun hX 0
    · exact congrFun hX 1
    · exact congrFun hX 2
    · exact congrFun hX 3
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fin_fun] using h

set_option maxHeartbeats 800000 in
lemma case_2b_bound (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (L : Submodule ℂ Mat) (hL : ValidL L)
    (h0 : outer ![1, Complex.I, -1, -Complex.I] ![1, -1, 0, 0, 0] ∈ L)
    (h1 : outer ![1, Complex.I, -1, -Complex.I] ![0, 0, 1, w, w ^ 2] ∈ L) :
    Module.finrank ℂ L ≤ 4 := by
  have hI : Complex.I ^ 2 + 1 = 0 := by rw [Complex.I_sq]; ring
  have hlin : ∀ X ∈ L, X 2 1 + Complex.I * (X 3 1 + X 3 2 + X 3 3 + X 3 4) = 0 ∧
      X 3 2 + X 3 3 + X 3 4 = 0 := by
    intro X hX
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
      case_2b_eqs w hw hI L hL (by simpa using h0) (by simpa using h1) X hX
    have hdm := dotMat_zero L hL X hX
    unfold dotMat at hdm
    simp only [Fin.sum_univ_four, Fin.sum_univ_five] at hdm
    rw [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13] at hdm
    set c0 := X 2 1; set c1 := X 2 4; set c2 := X 3 1; set c3 := X 3 2; set c4 := X 3 3; set c5 := X 3 4
    have hsq1 : 4 * Complex.I * (c0 + Complex.I * (c2 + c3 + c4 + c5)) ^ 2 = 0 := by
      linear_combination hdm -
        ((((46 : ℂ) / 9) + ((4 : ℂ) / 9) * w + ((4 : ℂ) / 9) * w^2 - 4 * Complex.I) * c5^2 +
         (((92 : ℂ) / 9) + ((8 : ℂ) / 9) * w + ((8 : ℂ) / 9) * w^2 - 8 * Complex.I) * c4 * c5 +
         (((46 : ℂ) / 9) + ((4 : ℂ) / 9) * w + ((4 : ℂ) / 9) * w^2 - 4 * Complex.I) * c4^2 +
         (((92 : ℂ) / 9) + ((8 : ℂ) / 9) * w + ((8 : ℂ) / 9) * w^2 - 8 * Complex.I) * c3 * c5 +
         (((92 : ℂ) / 9) + ((8 : ℂ) / 9) * w + ((8 : ℂ) / 9) * w^2 - 8 * Complex.I) * c3 * c4 +
         (((46 : ℂ) / 9) + ((4 : ℂ) / 9) * w + ((4 : ℂ) / 9) * w^2 - 4 * Complex.I) * c3^2 +
         ((6 : ℂ) - 8 * Complex.I) * c2 * c5 + ((6 : ℂ) - 8 * Complex.I) * c2 * c4 +
         ((6 : ℂ) - 8 * Complex.I) * c2 * c3 + ((4 : ℂ) - 4 * Complex.I) * c2^2 +
         (-(2 : ℂ)) * c0 * c5 + (-(2 : ℂ)) * c0 * c4 + (-(2 : ℂ)) * c0 * c3 + ((4 : ℂ)) * c0^2) * hI -
        ((((4 : ℂ) / 3) - ((8 : ℂ) / 9) * Complex.I) * c5^2 +
         (-((8 : ℂ) / 3) - ((4 : ℂ) / 9) * Complex.I) * c4 * c5 +
         (((4 : ℂ) / 3) + ((4 : ℂ) / 9) * Complex.I) * c4^2 +
         (-((8 : ℂ) / 3) - ((4 : ℂ) / 9) * Complex.I) * c3 * c5 +
         (-((8 : ℂ) / 3) + ((8 : ℂ) / 9) * Complex.I) * c3 * c4 +
         (((4 : ℂ) / 3) + ((4 : ℂ) / 9) * Complex.I) * c3^2 +
         (((8 : ℂ) / 3) - ((8 : ℂ) / 3) * Complex.I) * c1 * c5 +
         (-((4 : ℂ) / 3) - ((8 : ℂ) / 3) * Complex.I) * c1 * c4 +
         (-((4 : ℂ) / 3) - ((8 : ℂ) / 3) * Complex.I) * c1 * c3 + ((4 : ℂ)) * c1^2) * hw
    have hl1 : c0 + Complex.I * (c2 + c3 + c4 + c5) = 0 := by
      have h4I : (4 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hsq1).resolve_left h4I)
    have hb4 := quad_b4_zero L hL X hX _ h0
    simp only [outer, dot, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Matrix.head_cons] at hb4
    rw [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13] at hb4
    have hsq2 : ((8 : ℂ) / 3) * (c3 + c4 + c5) ^ 2 = 0 := by
      linear_combination hb4 -
        ((-((56 : ℂ) / 9) - ((20 : ℂ) / 9) * w - ((20 : ℂ) / 9) * w^2 - ((8 : ℂ) / 9) * Complex.I -
          ((8 : ℂ) / 9) * Complex.I * w - ((8 : ℂ) / 9) * Complex.I * w^2 - ((8 : ℂ) / 9) * Complex.I^2 +
          ((4 : ℂ) / 9) * Complex.I^2 * w + ((4 : ℂ) / 9) * Complex.I^2 * w^2) * c5^2 +
         (-((88 : ℂ) / 9) - ((16 : ℂ) / 9) * w - ((16 : ℂ) / 9) * w^2 - ((4 : ℂ) / 9) * Complex.I -
          ((4 : ℂ) / 9) * Complex.I * w - ((4 : ℂ) / 9) * Complex.I * w^2 - ((16 : ℂ) / 9) * Complex.I^2 +
          ((8 : ℂ) / 9) * Complex.I^2 * w + ((8 : ℂ) / 9) * Complex.I^2 * w^2) * c4 * c5 +
         (-((32 : ℂ) / 9) + ((4 : ℂ) / 9) * w + ((4 : ℂ) / 9) * w^2 + ((4 : ℂ) / 9) * Complex.I +
          ((4 : ℂ) / 9) * Complex.I * w + ((4 : ℂ) / 9) * Complex.I * w^2 - ((8 : ℂ) / 9) * Complex.I^2 +
          ((4 : ℂ) / 9) * Complex.I^2 * w + ((4 : ℂ) / 9) * Complex.I^2 * w^2) * c4^2 +
         (-((88 : ℂ) / 9) - ((16 : ℂ) / 9) * w - ((16 : ℂ) / 9) * w^2 - ((4 : ℂ) / 9) * Complex.I -
          ((4 : ℂ) / 9) * Complex.I * w - ((4 : ℂ) / 9) * Complex.I * w^2 - ((16 : ℂ) / 9) * Complex.I^2 +
          ((8 : ℂ) / 9) * Complex.I^2 * w + ((8 : ℂ) / 9) * Complex.I^2 * w^2) * c3 * c5 +
         (-((64 : ℂ) / 9) + ((8 : ℂ) / 9) * w + ((8 : ℂ) / 9) * w^2 + ((8 : ℂ) / 9) * Complex.I +
          ((8 : ℂ) / 9) * Complex.I * w + ((8 : ℂ) / 9) * Complex.I * w^2 - ((16 : ℂ) / 9) * Complex.I^2 +
          ((8 : ℂ) / 9) * Complex.I^2 * w + ((8 : ℂ) / 9) * Complex.I^2 * w^2) * c3 * c4 +
         (-((32 : ℂ) / 9) + ((4 : ℂ) / 9) * w + ((4 : ℂ) / 9) * w^2 + ((4 : ℂ) / 9) * Complex.I +
          ((4 : ℂ) / 9) * Complex.I * w + ((4 : ℂ) / 9) * Complex.I * w^2 - ((8 : ℂ) / 9) * Complex.I^2 +
          ((4 : ℂ) / 9) * Complex.I^2 * w + ((4 : ℂ) / 9) * Complex.I^2 * w^2) * c3^2 +
         (((8 : ℂ) / 3) + ((8 : ℂ) / 3) * w + ((8 : ℂ) / 3) * w^2 - ((8 : ℂ) / 3) * Complex.I -
          ((8 : ℂ) / 3) * Complex.I * w - ((8 : ℂ) / 3) * Complex.I * w^2) * c1 * c5 +
         (-((4 : ℂ) / 3) - ((4 : ℂ) / 3) * w - ((4 : ℂ) / 3) * w^2 - ((8 : ℂ) / 3) * Complex.I -
          ((8 : ℂ) / 3) * Complex.I * w - ((8 : ℂ) / 3) * Complex.I * w^2) * c1 * c4 +
         (-((4 : ℂ) / 3) - ((4 : ℂ) / 3) * w - ((4 : ℂ) / 3) * w^2 - ((8 : ℂ) / 3) * Complex.I -
          ((8 : ℂ) / 3) * Complex.I * w - ((8 : ℂ) / 3) * Complex.I * w^2) * c1 * c3 +
         ((4 : ℂ) + 4 * w + 4 * w^2) * c1^2) * hI -
        ((((20 : ℂ) / 9) + ((8 : ℂ) / 3) * Complex.I) * c5^2 +
         (((16 : ℂ) / 9) - ((4 : ℂ) / 3) * Complex.I) * c4 * c5 +
         (-((4 : ℂ) / 9) - ((4 : ℂ) / 3) * Complex.I) * c4^2 +
         (((16 : ℂ) / 9) - ((4 : ℂ) / 3) * Complex.I) * c3 * c5 +
         (-((8 : ℂ) / 9) + ((8 : ℂ) / 3) * Complex.I) * c3 * c4 +
         (-((4 : ℂ) / 9) - ((4 : ℂ) / 3) * Complex.I) * c3^2 +
         (-((8 : ℂ) / 3) + 8 * Complex.I) * c1 * c5 +
         (((4 : ℂ) / 3)) * c1 * c4 + (((4 : ℂ) / 3)) * c1 * c3 + (-(4 : ℂ)) * c1^2) * hw
    have hl2 : c3 + c4 + c5 = 0 :=
      sq_eq_zero_iff.mp ((mul_eq_zero.mp hsq2).resolve_left (by norm_num))
    exact ⟨hl1, hl2⟩
  let Φ : L →ₗ[ℂ] (Fin 4 → ℂ) :=
    { toFun := fun X => ![X.1 2 4, X.1 3 1, X.1 3 3, X.1 3 4]
      map_add' := fun X Y => by ext k; fin_cases k <;> simp
      map_smul' := fun c X => by ext k; fin_cases k <;> simp }
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    have hc1 : X.1 2 4 = 0 := congrFun hX 0
    have hc2 : X.1 3 1 = 0 := congrFun hX 1
    have hc4 : X.1 3 3 = 0 := congrFun hX 2
    have hc5 : X.1 3 4 = 0 := congrFun hX 3
    obtain ⟨hl1, hl2⟩ := hlin X.1 X.2
    have hc3 : X.1 3 2 = 0 := by linear_combination hl2 - hc4 - hc5
    have hc0 : X.1 2 1 = 0 := by linear_combination hl1 - Complex.I * (hc2 + hc3 + hc4 + hc5)
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
      case_2b_eqs w hw hI L hL (by simpa using h0) (by simpa using h1) X.1 X.2
    simp only [hc0, hc1, hc2, hc3, hc4, hc5, mul_zero, add_zero, zero_add] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;> simp only [Pi.zero_apply]
    · exact p0
    · exact p1
    · exact p2
    · exact p3
    · exact p4
    · exact p5
    · exact p6
    · exact p7
    · exact p8
    · exact p9
    · exact p10
    · exact hc0
    · exact p11
    · exact p12
    · exact hc1
    · exact p13
    · exact hc2
    · exact hc3
    · exact hc4
    · exact hc5
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fin_fun] using h

set_option maxHeartbeats 800000 in
lemma case_2a_bound (L : Submodule ℂ Mat) (hL : ValidL L)
    (h0 : outer ![1, Complex.I, -1, -Complex.I] ![1, -1, 0, 0, 0] ∈ L)
    (h1 : outer ![1, Complex.I, -1, -Complex.I] ![1, 0, -1, 0, 0] ∈ L) :
    Module.finrank ℂ L ≤ 4 := by
  have hI : Complex.I ^ 2 + 1 = 0 := by rw [Complex.I_sq]; ring
  let Φ : L →ₗ[ℂ] (Fin 6 → ℂ) :=
    { toFun := fun X => ![X.1 1 4, X.1 2 4, X.1 3 1, X.1 3 2, X.1 3 3, X.1 3 4]
      map_add' := fun X Y => by ext k; fin_cases k <;> simp
      map_smul' := fun c X => by ext k; fin_cases k <;> simp }
  have hΦ_inj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    have hc0 : X.1 1 4 = 0 := congrFun hX 0
    have hc1 : X.1 2 4 = 0 := congrFun hX 1
    have hc2 : X.1 3 1 = 0 := congrFun hX 2
    have hc3 : X.1 3 2 = 0 := congrFun hX 3
    have hc4 : X.1 3 3 = 0 := congrFun hX 4
    have hc5 : X.1 3 4 = 0 := congrFun hX 5
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
      case_2a_eqs hI L hL (by simpa using h0) (by simpa using h1) X.1 X.2
    simp only [hc0, hc1, hc2, hc3, hc4, hc5, mul_zero, add_zero, zero_add] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;> simp only [Pi.zero_apply]
    · exact p0
    · exact p1
    · exact p2
    · exact p3
    · exact p4
    · exact p5
    · exact p6
    · exact p7
    · exact p8
    · exact hc0
    · exact p9
    · exact p10
    · exact p11
    · exact p12
    · exact hc1
    · exact p13
    · exact hc2
    · exact hc3
    · exact hc4
    · exact hc5
  let M : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) :=
    { toFun := fun c =>
        ![4 * c 0 + 2 * c 1 + (1 - Complex.I) * c 4 + (3 - Complex.I) * c 5,
          2 * c 0 + 4 * c 1 - 2 * Complex.I * c 4 + (2 - 2 * Complex.I) * c 5,
          0,
          0,
          (1 - Complex.I) * c 0 - 2 * Complex.I * c 1 + (-1 - Complex.I) * c 5,
          (3 - Complex.I) * c 0 + (2 - 2 * Complex.I) * c 1 + (-1 - Complex.I) * c 4 + (2 - 2 * Complex.I) * c 5]
      map_add' := fun u v => by ext k; fin_cases k <;> simp <;> ring
      map_smul' := fun s u => by ext k; fin_cases k <;> simp <;> ring }
  have hkerM : Module.finrank ℂ (LinearMap.ker M) ≤ 3 := by
    let ψ : LinearMap.ker M →ₗ[ℂ] (Fin 3 → ℂ) :=
      { toFun := fun v => ![v.1 2, v.1 3, v.1 5]
        map_add' := fun u v => by ext k; fin_cases k <;> simp
        map_smul' := fun s u => by ext k; fin_cases k <;> simp }
    have hψ_inj : Function.Injective ψ := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have h2 : v.1 2 = 0 := congrFun hv 0
      have h3 : v.1 3 = 0 := congrFun hv 1
      have h5 : v.1 5 = 0 := congrFun hv 2
      have hm0 : 4 * v.1 0 + 2 * v.1 1 + (1 - Complex.I) * v.1 4 + (3 - Complex.I) * v.1 5 = 0 :=
        congrFun v.2 0
      have hm1 : 2 * v.1 0 + 4 * v.1 1 - 2 * Complex.I * v.1 4 + (2 - 2 * Complex.I) * v.1 5 = 0 :=
        congrFun v.2 1
      have hm4 : (1 - Complex.I) * v.1 0 - 2 * Complex.I * v.1 1 + (-1 - Complex.I) * v.1 5 = 0 :=
        congrFun v.2 4
      have hv0 : v.1 0 = 0 := by
        linear_combination ((1 : ℂ) / 2) * hm0 + (-((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * hm1 +
          (-((1 : ℂ) / 2)) * hm4 + (-(1 : ℂ)) * h5 +
          ((-((1 : ℂ) / 2)) * v.1 4 + (-((1 : ℂ) / 2)) * v.1 5) * hI
      have hv1 : v.1 1 = 0 := by
        linear_combination (-((1 : ℂ) / 4) - ((1 : ℂ) / 4) * Complex.I) * hm0 +
          (((1 : ℂ) / 4) * Complex.I) * hm1 + (((1 : ℂ) / 4) + ((3 : ℂ) / 4) * Complex.I) * hm4 +
          Complex.I * h5 + ((((3 : ℂ) / 4)) * v.1 0 + (((3 : ℂ) / 2)) * v.1 1 +
          (((1 : ℂ) / 4)) * v.1 4 + (1 : ℂ) * v.1 5) * hI
      have hv4 : v.1 4 = 0 := by
        linear_combination (-((1 : ℂ) / 2)) * hm0 + (((1 : ℂ) / 4) + ((3 : ℂ) / 4) * Complex.I) * hm1 +
          (((3 : ℂ) / 2)) * hm4 + (1 : ℂ) * h5 +
          ((((3 : ℂ) / 2)) * v.1 4 + (((3 : ℂ) / 2)) * v.1 5) * hI
      apply Subtype.ext; ext k
      fin_cases k <;> simp only [Pi.zero_apply]
      · exact hv0
      · exact hv1
      · exact h2
      · exact h3
      · exact hv4
      · exact h5
    have h := LinearMap.finrank_le_finrank_of_injective hψ_inj
    simpa [Module.finrank_fin_fun] using h
  have hiso : ∀ x ∈ LinearMap.range Φ, ∀ y ∈ LinearMap.range Φ, dot6 (M x) y = 0 := by
    rintro _ ⟨X, rfl⟩ _ ⟨Z, rfl⟩
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
      case_2a_eqs hI L hL (by simpa using h0) (by simpa using h1) X.1 X.2
    obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13⟩ :=
      case_2a_eqs hI L hL (by simpa using h0) (by simpa using h1) Z.1 Z.2
    have hd := lin_dot_zero L hL X.1 X.2 Z.1 Z.2
    simp only [Fin.sum_univ_four, Fin.sum_univ_five] at hd
    rw [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13,
        q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13] at hd
    set c0 := X.1 1 4; set c1 := X.1 2 4; set c2 := X.1 3 1; set c3 := X.1 3 2; set c4 := X.1 3 3; set c5 := X.1 3 4
    set d0 := Z.1 1 4; set d1 := Z.1 2 4; set d2 := Z.1 3 1; set d3 := Z.1 3 2; set d4 := Z.1 3 3; set d5 := Z.1 3 4
    unfold dot6
    simp only [M, Φ, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    linear_combination hd -
      (4 * c5 * d5 + 4 * c5 * d4 + 2 * c5 * d3 + 2 * c5 * d2 +
       4 * c4 * d5 + 4 * c4 * d4 + 2 * c4 * d3 + 2 * c4 * d2 +
       2 * c3 * d5 + 2 * c3 * d4 + 4 * c3 * d3 + 2 * c3 * d2 +
       2 * c2 * d5 + 2 * c2 * d4 + 2 * c2 * d3 + 4 * c2 * d2) * hI
  have hW := isotropic_finrank_le_four (LinearMap.range Φ) M hkerM hiso
  have heq : Module.finrank ℂ (LinearMap.range Φ) = Module.finrank ℂ L :=
    LinearMap.finrank_range_of_inj hΦ_inj
  omega

set_option maxHeartbeats 800000 in
lemma case_3a_bound (w : ℂ) (hw : w ^ 2 + w + 1 = 0)
    (L : Submodule ℂ Mat) (hL : ValidL L)
    (h0 : outer ![1, w, w ^ 2, 0] ![1, -1, 0, 0, 0] ∈ L)
    (h1 : outer ![1, w, w ^ 2, 0] ![0, 0, 1, -1, 0] ∈ L) :
    Module.finrank ℂ L ≤ 4 := by
  by_contra h5
  push_neg at h5
  let proj : L →ₗ[ℂ] (Fin 2 → ℂ) :=
    { toFun := fun X => ![X.1 3 3, X.1 3 4]
      map_add' := fun X Y => by ext k; fin_cases k <;> simp
      map_smul' := fun c X => by ext k; fin_cases k <;> simp }
  have hnot_surj : LinearMap.range proj ≠ ⊤ := by
    intro htop
    have hmem : (![1, 0] : Fin 2 → ℂ) ∈ LinearMap.range proj := by rw [htop]; trivial
    rcases hmem with ⟨X, hX⟩
    have hc4 : X.1 3 3 = 1 := congrFun hX 0
    have hc5 : X.1 3 4 = 0 := congrFun hX 1
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
      case_3a_eqs w hw L hL (by simpa using h0) (by simpa using h1) X.1 X.2
    have hdm := dotMat_zero L hL X.1 X.2
    unfold dotMat at hdm
    simp only [Fin.sum_univ_four, Fin.sum_univ_five] at hdm
    rw [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13] at hdm
    set c0 := X.1 2 1; set c1 := X.1 2 2; set c2 := X.1 2 3; set c3 := X.1 2 4
    have hq : ((16 : ℂ) / 3) * (X.1 3 3) ^ 2 + ((8 : ℂ) / 3) * (X.1 3 3) * (X.1 3 4) +
        2 * (X.1 3 4) ^ 2 = 0 := by
      linear_combination hdm -
        ((((1 : ℂ) / 3)) * (X.1 3 4)^2 + (((4 : ℂ) / 9)) * (X.1 3 3) * (X.1 3 4) +
         (((8 : ℂ) / 9)) * (X.1 3 3)^2 + 2 * c3 * (X.1 3 4) + (((4 : ℂ) / 3)) * c3 * (X.1 3 3) +
         4 * c3^2 + (((2 : ℂ) / 3)) * c2 * (X.1 3 4) + (((8 : ℂ) / 3)) * c2 * (X.1 3 3) +
         4 * c2 * c3 + 4 * c2^2 + (((2 : ℂ) / 3)) * c1 * (X.1 3 4) +
         (((8 : ℂ) / 3)) * c1 * (X.1 3 3) + 4 * c1 * c3 + 4 * c1 * c2 + 4 * c1^2 +
         4 * c0 * c3 + 4 * c0 * c2 + 4 * c0 * c1 + 4 * c0^2) * hw
    rw [hc4, hc5] at hq
    norm_num at hq
  have hr_le : Module.finrank ℂ (LinearMap.range proj) ≤ 1 := by
    have hle2 : Module.finrank ℂ (LinearMap.range proj) ≤ 2 := by
      have := Submodule.finrank_le (LinearMap.range proj)
      simpa [Module.finrank_fin_fun] using this
    by_contra hgt
    push_neg at hgt
    have heq2 : Module.finrank ℂ (LinearMap.range proj) = 2 := by omega
    exact hnot_surj (Submodule.eq_top_of_finrank_eq (by simpa [Module.finrank_fin_fun] using heq2))
  have hker_ge : 4 ≤ Module.finrank ℂ (LinearMap.ker proj) := by
    have h := LinearMap.finrank_range_add_finrank_ker proj
    omega
  let ψ : LinearMap.ker proj →ₗ[ℂ] (Fin 4 → ℂ) :=
    { toFun := fun X => ![X.1.1 2 1, X.1.1 2 2, X.1.1 2 3, X.1.1 2 4]
      map_add' := fun X Y => by ext k; fin_cases k <;> simp
      map_smul' := fun c X => by ext k; fin_cases k <;> simp }
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro X hX
    have hc0 : X.1.1 2 1 = 0 := congrFun hX 0
    have hc1 : X.1.1 2 2 = 0 := congrFun hX 1
    have hc2 : X.1.1 2 3 = 0 := congrFun hX 2
    have hc3 : X.1.1 2 4 = 0 := congrFun hX 3
    have hc4 : X.1.1 3 3 = 0 := congrFun X.2 0
    have hc5 : X.1.1 3 4 = 0 := congrFun X.2 1
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
      case_3a_eqs w hw L hL (by simpa using h0) (by simpa using h1) X.1.1 X.1.2
    simp only [hc0, hc1, hc2, hc3, hc4, hc5, mul_zero, add_zero, zero_add] at p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13
    apply Subtype.ext; apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;> simp only [Pi.zero_apply]
    · exact p0
    · exact p1
    · exact p2
    · exact p3
    · exact p4
    · exact p5
    · exact p6
    · exact p7
    · exact p8
    · exact p9
    · exact p10
    · exact hc0
    · exact hc1
    · exact hc2
    · exact hc3
    · exact p11
    · exact p12
    · exact p13
    · exact hc4
    · exact hc5
  have hψ_top : LinearMap.range ψ = ⊤ := by
    have hle4 : Module.finrank ℂ (LinearMap.range ψ) ≤ 4 := by
      have := Submodule.finrank_le (LinearMap.range ψ)
      simpa [Module.finrank_fin_fun] using this
    have hge4 : 4 ≤ Module.finrank ℂ (LinearMap.range ψ) := by
      rw [LinearMap.finrank_range_of_inj hψ_inj]; exact hker_ge
    exact Submodule.eq_top_of_finrank_eq (by simpa [Module.finrank_fin_fun] using le_antisymm hle4 hge4)
  have hB3 : (![0, 0, 0, 1] : Fin 4 → ℂ) ∈ LinearMap.range ψ := by rw [hψ_top]; trivial
  rcases hB3 with ⟨X, hX⟩
  have hc0 : X.1.1 2 1 = 0 := congrFun hX 0
  have hc1 : X.1.1 2 2 = 0 := congrFun hX 1
  have hc2 : X.1.1 2 3 = 0 := congrFun hX 2
  have hc3 : X.1.1 2 4 = 1 := congrFun hX 3
  have hc4 : X.1.1 3 3 = 0 := congrFun X.2 0
  have hc5 : X.1.1 3 4 = 0 := congrFun X.2 1
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13⟩ :=
    case_3a_eqs w hw L hL (by simpa using h0) (by simpa using h1) X.1.1 X.1.2
  have hcube := cube_sum_zero L hL X.1.1 X.1.2
  simp only [Fin.sum_univ_four, Fin.sum_univ_five] at hcube
  rw [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13,
      hc0, hc1, hc2, hc3, hc4, hc5] at hcube
  have hne : (9 : ℂ) / 4 = 0 := by
    linear_combination hcube + 3 * hw
  norm_num at hne

def rowPermEquiv (π : Equiv.Perm (Fin 4)) : Mat ≃ₗ[ℂ] Mat where
  toFun X i j := X (π i) j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun X i j := X (π.symm i) j
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp

def colPermEquiv (σ : Equiv.Perm (Fin 5)) : Mat ≃ₗ[ℂ] Mat where
  toFun X i j := X i (σ j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun X i j := X i (σ.symm j)
  left_inv X := by ext i j; simp
  right_inv X := by ext i j; simp

lemma rowPerm_valid (π : Equiv.Perm (Fin 4)) (L : Submodule ℂ Mat) (hL : ValidL L) :
    ValidL (L.map (rowPermEquiv π).toLinearMap) := by
  rintro _ ⟨X, hX, rfl⟩
  refine ⟨fun i => (hL X hX).1 (π i), fun j => ?_, ?_⟩
  · change ∑ i : Fin 4, X (π i) j = 0
    rw [Equiv.sum_comp π (fun i => X i j)]
    exact (hL X hX).2.1 j
  · change (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X (π i) (f i))) = 120
    have hbij : (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X (π i) (f i))) =
        ∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i)) := by
      refine Finset.sum_nbij (fun f => π.symm.toEmbedding.trans f) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro f1 _ f2 _ h
        exact DFunLike.ext f1 f2 fun i => by
          have := DFunLike.congr_fun h (π i); simpa using this
      · intro f _
        refine ⟨π.toEmbedding.trans f, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
        exact DFunLike.ext _ _ fun i => by simp
      · intro f _
        simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
        rw [← Equiv.prod_comp π (fun i => 1 + X i (f (π.symm i)))]
        refine Finset.prod_congr rfl fun i _ => by simp
    rw [hbij]
    exact (hL X hX).2.2

lemma colPerm_valid (σ : Equiv.Perm (Fin 5)) (L : Submodule ℂ Mat) (hL : ValidL L) :
    ValidL (L.map (colPermEquiv σ).toLinearMap) := by
  rintro _ ⟨X, hX, rfl⟩
  refine ⟨fun i => ?_, fun j => (hL X hX).2.1 (σ j), ?_⟩
  · change ∑ j : Fin 5, X i (σ j) = 0
    rw [Equiv.sum_comp σ (fun j => X i j)]
    exact (hL X hX).1 i
  · change (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (σ (f i)))) = 120
    have hbij : (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (σ (f i)))) =
        ∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i)) := by
      refine Finset.sum_nbij (fun f => f.trans σ.toEmbedding) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro f1 _ f2 _ h
        exact DFunLike.ext f1 f2 fun i => σ.injective (DFunLike.congr_fun h i)
      · intro f _
        refine ⟨f.trans σ.symm.toEmbedding, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
        exact DFunLike.ext _ _ fun i => by simp
      · intro f _; rfl
    rw [hbij]
    exact (hL X hX).2.2

def esym4 (u : Vec) : ℂ :=
  u 0 * u 1 * u 2 * u 3 + u 0 * u 1 * u 2 * u 4 + u 0 * u 1 * u 3 * u 4 +
  u 0 * u 2 * u 3 * u 4 + u 1 * u 2 * u 3 * u 4

lemma esym4_powsum (u : Vec) (hu : ∑ j : Fin 5, u j = 0) :
    24 * esym4 u = 3 * (∑ j : Fin 5, (u j) ^ 2) ^ 2 - 6 * (∑ j : Fin 5, (u j) ^ 4) := by
  unfold esym4
  simp only [Fin.sum_univ_five] at hu ⊢
  linear_combination ((u 0 + u 1 + u 2 + u 3 + u 4) ^ 3 -
    6 * (u 0 + u 1 + u 2 + u 3 + u 4) * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + u 4 ^ 2) +
    8 * (u 0 ^ 3 + u 1 ^ 3 + u 2 ^ 3 + u 3 ^ 3 + u 4 ^ 3)) * hu

lemma esym4_perm (σ : Equiv.Perm (Fin 5)) (u : Vec) (hu : ∑ j : Fin 5, u j = 0) :
    esym4 (fun j => u (σ j)) = esym4 u := by
  have hu' : ∑ j : Fin 5, u (σ j) = 0 := by rw [Equiv.sum_comp σ u]; exact hu
  have h1 := esym4_powsum (fun j => u (σ j)) hu'
  have h2 := esym4_powsum u hu
  have hp2 : ∑ j : Fin 5, (u (σ j)) ^ 2 = ∑ j : Fin 5, (u j) ^ 2 :=
    Equiv.sum_comp σ (fun j => (u j) ^ 2)
  have hp4 : ∑ j : Fin 5, (u (σ j)) ^ 4 = ∑ j : Fin 5, (u j) ^ 4 :=
    Equiv.sum_comp σ (fun j => (u j) ^ 4)
  rw [hp2, hp4] at h1
  linear_combination (h1 - h2) / 24

lemma outer_relations (L : Submodule ℂ Mat) (hL : ValidL L)
    (a : Fin 4 → ℂ) (u : Vec) (hu : ∑ j, u j = 0)
    (hmem : outer a u ∈ L) :
    (∑ i : Fin 4, (a i) ^ 2) * (∑ j : Fin 5, (u j) ^ 2) = 0 ∧
    (∑ i : Fin 4, (a i) ^ 3) * (∑ j : Fin 5, (u j) ^ 3) = 0 ∧
    (a 0 * a 1 * a 2 * a 3) * esym4 u = 0 := by
  have h1 := dotMat_zero L hL _ hmem
  have h2 := cube_sum_zero L hL _ hmem
  have h3 := e4Form_zero L hL _ hmem
  refine ⟨?_, ?_, ?_⟩
  · unfold dotMat outer at h1
    simp only [Fin.sum_univ_four, Fin.sum_univ_five] at h1 ⊢
    linear_combination h1
  · unfold outer at h2
    simp only [Fin.sum_univ_four, Fin.sum_univ_five] at h2 ⊢
    linear_combination h2
  · have he := esym4_powsum u hu
    unfold e4Form dot outer at h3
    simp only [Fin.sum_univ_five] at h3 he ⊢
    linear_combination (h3 + (a 0 * a 1 * a 2 * a 3) * he) / 24

lemma not_p2_and_e4 (U : Submodule ℂ Vec) (hU2 : 2 ≤ Module.finrank ℂ U)
    (hsum : ∀ u ∈ U, ∑ j, u j = 0)
    (hp2 : ∀ u ∈ U, ∑ j : Fin 5, (u j) ^ 2 = 0)
    (he4 : ∀ u ∈ U, esym4 u = 0) : False := by
  have hW' : ∀ w ∈ U, ∏ i : Fin 5, (1 + w i) + ∏ i : Fin 5, (1 - w i) = 2 := by
    intro w hw
    have h1 := hsum w hw
    have h2 := hp2 w hw
    have h4 := he4 w hw
    unfold esym4 at h4
    simp only [Fin.prod_univ_five, Fin.sum_univ_five] at h1 h2 ⊢
    linear_combination (w 0 + w 1 + w 2 + w 3 + w 4) * h1 - h2 + 2 * h4
  have hle1 : Module.finrank ℂ U ≤ 1 := by
    by_cases hex : ∃ u ∈ U, u ≠ 0
    · obtain ⟨u, hu, hu0⟩ := hex
      obtain ⟨k, hk⟩ : ∃ k, u k ≠ 0 := by
        by_contra hall; push_neg at hall; exact hu0 (funext hall)
      refine finrank_le_one (⟨u, hu⟩ : U) fun w => ⟨w.1 k / u k, ?_⟩
      have hz := Sub142.coord_zero 5 U hW' u hu k hk (u k • w.1 - w.1 k • u)
        (U.sub_mem (U.smul_mem _ w.2) (U.smul_mem _ hu)) (by simp; ring)
      apply Subtype.ext
      simp only [SetLike.val_smul]
      have hz' : u k • w.1 = w.1 k • u := sub_eq_zero.mp hz
      funext i
      have := congrFun hz' i
      simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
      field_simp
      linear_combination this.symm
    · push_neg at hex
      refine finrank_le_one (0 : U) fun w => ⟨0, ?_⟩
      apply Subtype.ext
      simp [hex w.1 w.2]
  omega

lemma p3_excludes_p2_and_e4 (U : Submodule ℂ Vec) (hU2 : 2 ≤ Module.finrank ℂ U)
    (hsum : ∀ u ∈ U, ∑ j, u j = 0)
    (hp3 : ∀ u ∈ U, ∑ j : Fin 5, (u j) ^ 3 = 0) :
    (∃ u ∈ U, ∑ j : Fin 5, (u j) ^ 2 ≠ 0) ∧ (∃ u ∈ U, esym4 u ≠ 0) := by
  have hcls := (Sub303.main U hU2).mp (fun u hu => ⟨hsum u hu, hp3 u hu⟩)
  rcases hcls with ⟨π, hpair | ⟨z, hz, hroot⟩⟩
  · have hm1 : (fun j => (![1, -1, 0, 0, 0] : Vec) (π.symm j)) ∈ U :=
      (hpair _).mpr ⟨1, 0, fun j => by simp⟩
    have hm2 : (fun j => (![1, -1, 1, -1, 0] : Vec) (π.symm j)) ∈ U :=
      (hpair _).mpr ⟨1, 1, fun j => by simp⟩
    refine ⟨⟨_, hm1, ?_⟩, ⟨_, hm2, ?_⟩⟩
    · rw [Equiv.sum_comp π.symm (fun j => ((![1, -1, 0, 0, 0] : Vec) j) ^ 2)]
      simp [Fin.sum_univ_five]
    · rw [esym4_perm π.symm ![1, -1, 1, -1, 0] (by simp [Fin.sum_univ_five])]
      simp [esym4]
  · have hz5 : z ^ 5 = 1 := hz.pow_eq_one
    have hz1 : z ≠ 1 := hz.ne_one (by decide)
    have hzp : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 := by
      have hmul : (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = 0 := by
        linear_combination hz5
      exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hz1)
    let v : Vec := fun j => z ^ j.val + z ^ (4 * j.val)
    have hm : (fun j => v (π.symm j)) ∈ U :=
      (hroot _).mpr ⟨1, 1, fun j => by simp [v]⟩
    have hv0 : v 0 = 2 := by simp [v]; norm_num
    have hv1 : v 1 = z + z ^ 4 := by simp [v]
    have hv2 : v 2 = z ^ 2 + z ^ 3 := by
      change z ^ 2 + z ^ (4 * 2) = z ^ 2 + z ^ 3
      calc z ^ 2 + z ^ (4 * 2) = z ^ 2 + z ^ 5 * z ^ 3 := by ring
        _ = z ^ 2 + z ^ 3 := by rw [hz5, one_mul]
    have hv3 : v 3 = z ^ 3 + z ^ 2 := by
      change z ^ 3 + z ^ (4 * 3) = z ^ 3 + z ^ 2
      calc z ^ 3 + z ^ (4 * 3) = z ^ 3 + (z ^ 5) ^ 2 * z ^ 2 := by ring
        _ = z ^ 3 + z ^ 2 := by rw [hz5]; ring
    have hv4 : v 4 = z ^ 4 + z := by
      change z ^ 4 + z ^ (4 * 4) = z ^ 4 + z
      calc z ^ 4 + z ^ (4 * 4) = z ^ 4 + (z ^ 5) ^ 3 * z := by ring
        _ = z ^ 4 + z := by rw [hz5]; ring
    have hvsum : ∑ j : Fin 5, v j = 0 := by
      rw [Fin.sum_univ_five, hv0, hv1, hv2, hv3, hv4]
      linear_combination 2 * hzp
    have hvp2 : ∑ j : Fin 5, (v j) ^ 2 = 10 := by
      rw [Fin.sum_univ_five, hv0, hv1, hv2, hv3, hv4]
      have h8 : z ^ 8 = z ^ 3 := by calc z ^ 8 = z ^ 5 * z ^ 3 := by ring
        _ = z ^ 3 := by rw [hz5, one_mul]
      have h6 : z ^ 6 = z := by calc z ^ 6 = z ^ 5 * z := by ring
        _ = z := by rw [hz5, one_mul]
      linear_combination 2 * h8 + 2 * h6 + 8 * hz5 + 2 * hzp
    have hvp4 : ∑ j : Fin 5, (v j) ^ 4 = 30 := by
      rw [Fin.sum_univ_five, hv0, hv1, hv2, hv3, hv4]
      have h16 : z ^ 16 = z := by calc z ^ 16 = (z ^ 5) ^ 3 * z := by ring
        _ = z := by rw [hz5]; ring
      have h13 : z ^ 13 = z ^ 3 := by calc z ^ 13 = (z ^ 5) ^ 2 * z ^ 3 := by ring
        _ = z ^ 3 := by rw [hz5]; ring
      have h12 : z ^ 12 = z ^ 2 := by calc z ^ 12 = (z ^ 5) ^ 2 * z ^ 2 := by ring
        _ = z ^ 2 := by rw [hz5]; ring
      have h11 : z ^ 11 = z := by calc z ^ 11 = (z ^ 5) ^ 2 * z := by ring
        _ = z := by rw [hz5]; ring
      have h10 : z ^ 10 = 1 := by calc z ^ 10 = (z ^ 5) ^ 2 := by ring
        _ = 1 := by rw [hz5]; ring
      have h9 : z ^ 9 = z ^ 4 := by calc z ^ 9 = z ^ 5 * z ^ 4 := by ring
        _ = z ^ 4 := by rw [hz5]; ring
      have h8 : z ^ 8 = z ^ 3 := by calc z ^ 8 = z ^ 5 * z ^ 3 := by ring
        _ = z ^ 3 := by rw [hz5]; ring
      have h7 : z ^ 7 = z ^ 2 := by calc z ^ 7 = z ^ 5 * z ^ 2 := by ring
        _ = z ^ 2 := by rw [hz5]; ring
      linear_combination 2 * h16 + 8 * h13 + 2 * h12 + 8 * h11 + 24 * h10 +
        8 * h9 + 2 * h8 + 8 * h7 + 10 * hzp
    refine ⟨⟨_, hm, ?_⟩, ⟨_, hm, ?_⟩⟩
    · rw [Equiv.sum_comp π.symm (fun j => (v j) ^ 2), hvp2]; norm_num
    · rw [esym4_perm π.symm v hvsum]
      have he := esym4_powsum v hvsum
      rw [hvp2, hvp4] at he
      intro h0; rw [h0] at he; norm_num at he

lemma classify_a (a : Fin 4 → ℂ) (ha_ne : a ≠ 0) (ha1 : ∑ i : Fin 4, a i = 0)
    (h234 : (∑ i : Fin 4, (a i) ^ 2 = 0 ∧ ∑ i : Fin 4, (a i) ^ 3 = 0) ∨
            (∑ i : Fin 4, (a i) ^ 2 = 0 ∧ a 0 * a 1 * a 2 * a 3 = 0) ∨
            (∑ i : Fin 4, (a i) ^ 3 = 0 ∧ a 0 * a 1 * a 2 * a 3 = 0)) :
    (∃ (π : Equiv.Perm (Fin 4)) (c : ℂ), c ≠ 0 ∧ ∀ i, a (π i) = c * (![1, -1, 0, 0] : Fin 4 → ℂ) i) ∨
    (∃ (π : Equiv.Perm (Fin 4)) (c : ℂ), c ≠ 0 ∧
      ∀ i, a (π i) = c * (![1, Complex.I, -1, -Complex.I] : Fin 4 → ℂ) i) ∨
    (∃ (π : Equiv.Perm (Fin 4)) (c w : ℂ), c ≠ 0 ∧ w ^ 2 + w + 1 = 0 ∧
      ∀ i, a (π i) = c * (![1, w, w ^ 2, 0] : Fin 4 → ℂ) i) := by
  have exists_zero_to_three : ∀ (b : Fin 4 → ℂ), b 0 * b 1 * b 2 * b 3 = 0 →
      ∃ π : Equiv.Perm (Fin 4), b (π 3) = 0 := by
    intro b hb
    have hdisj : b 0 = 0 ∨ b 1 = 0 ∨ b 2 = 0 ∨ b 3 = 0 := by
      rcases mul_eq_zero.mp hb with h012 | h3
      · rcases mul_eq_zero.mp h012 with h01 | h2
        · rcases mul_eq_zero.mp h01 with h0 | h1
          · exact Or.inl h0
          · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr h3))
    rcases hdisj with h | h | h | h
    · exact ⟨Equiv.swap 0 3, by simp [h]⟩
    · exact ⟨Equiv.swap 1 3, by simp [h]⟩
    · exact ⟨Equiv.swap 2 3, by simp [h]⟩
    · exact ⟨1, h⟩
  rcases h234 with ⟨ha2, ha3⟩ | ⟨ha2, ha4⟩ | ⟨ha3, ha4⟩
  · obtain ⟨k, hk⟩ : ∃ k : Fin 4, a k ≠ 0 := by
      by_contra h; push_neg at h; exact ha_ne (funext h)
    let π0 : Equiv.Perm (Fin 4) := Equiv.swap 0 k
    let b : Fin 4 → ℂ := fun i => (a k)⁻¹ * a (π0 i)
    have hb0 : b 0 = 1 := by simp [b, π0, hk]
    have hb1 : b 0 + b 1 + b 2 + b 3 = 0 := by
      have hs : ∑ i : Fin 4, a (π0 i) = 0 := by rw [Equiv.sum_comp π0 a]; exact ha1
      rw [Fin.sum_univ_four] at hs
      simp only [b]; linear_combination (a k)⁻¹ * hs
    have hb2 : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 = 0 := by
      have hs : ∑ i : Fin 4, (a (π0 i)) ^ 2 = 0 := by
        rw [Equiv.sum_comp π0 (fun i => (a i) ^ 2)]; exact ha2
      rw [Fin.sum_univ_four] at hs
      simp only [b]; linear_combination ((a k)⁻¹) ^ 2 * hs
    have hb3 : b 0 ^ 3 + b 1 ^ 3 + b 2 ^ 3 + b 3 ^ 3 = 0 := by
      have hs : ∑ i : Fin 4, (a (π0 i)) ^ 3 = 0 := by
        rw [Equiv.sum_comp π0 (fun i => (a i) ^ 3)]; exact ha3
      rw [Fin.sum_univ_four] at hs
      simp only [b]; linear_combination ((a k)⁻¹) ^ 3 * hs
    rw [hb0] at hb1 hb2 hb3
    have hprod : (Complex.I - b 1) * (Complex.I - b 2) * (Complex.I - b 3) = 0 := by
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      have he2 : b 1 * b 2 + b 1 * b 3 + b 2 * b 3 = 1 := by
        linear_combination ((b 1 + b 2 + b 3 - 1) * hb1 - hb2) / 2
      have he3 : b 1 * b 2 * b 3 = -1 := by
        linear_combination (hb3 - ((b 1 + b 2 + b 3) ^ 2 - (b 1 + b 2 + b 3) + 1) * hb1 +
          3 * (b 1 + b 2 + b 3) * he2 + 3 * hb1) / 3
      linear_combination (Complex.I + 1) * hI - Complex.I ^ 2 * hb1 + Complex.I * he2 - he3
    have hI_mem : b 1 = Complex.I ∨ b 2 = Complex.I ∨ b 3 = Complex.I := by
      rcases mul_eq_zero.mp hprod with h12 | h3
      · rcases mul_eq_zero.mp h12 with h1 | h2
        · exact Or.inl (sub_eq_zero.mp h1).symm
        · exact Or.inr (Or.inl (sub_eq_zero.mp h2).symm)
      · exact Or.inr (Or.inr (sub_eq_zero.mp h3).symm)
    have hπ1 : ∃ σ : Equiv.Perm (Fin 4), σ 0 = 0 ∧ b (σ 1) = Complex.I := by
      rcases hI_mem with h | h | h
      · exact ⟨1, rfl, h⟩
      · exact ⟨Equiv.swap 1 2, by decide, by simp [h]⟩
      · exact ⟨Equiv.swap 1 3, by decide, by simp [h]⟩
    rcases hπ1 with ⟨σ, hσ0, hσ1⟩
    let d : Fin 4 → ℂ := fun i => b (σ i)
    have hd0 : d 0 = 1 := by simp [d, hσ0, hb0]
    have hd1 : d 1 = Complex.I := hσ1
    have hdsum : d 0 + d 1 + d 2 + d 3 = 0 := by
      have : ∑ i : Fin 4, b (σ i) = ∑ i : Fin 4, b i := Equiv.sum_comp σ b
      rw [Fin.sum_univ_four, Fin.sum_univ_four, hb0] at this
      change d 0 + d 1 + d 2 + d 3 = _ at this
      rw [this]; exact hb1
    have hdsq : d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 + d 3 ^ 2 = 0 := by
      have : ∑ i : Fin 4, (b (σ i)) ^ 2 = ∑ i : Fin 4, (b i) ^ 2 :=
        Equiv.sum_comp σ (fun i => (b i) ^ 2)
      rw [Fin.sum_univ_four, Fin.sum_univ_four, hb0] at this
      change d 0 ^ 2 + d 1 ^ 2 + d 2 ^ 2 + d 3 ^ 2 = _ at this
      rw [this]; exact hb2
    rw [hd0, hd1] at hdsum hdsq
    have hquad' : (d 2 + 1) * (d 2 + Complex.I) = 0 := by
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      have hd3 : d 3 = -(1 + Complex.I + d 2) := by linear_combination hdsum
      rw [hd3] at hdsq
      linear_combination hdsq / 2 - hI
    rcases mul_eq_zero.mp hquad' with h2m1 | h2mI
    · have hd2 : d 2 = -1 := by linear_combination h2m1
      have hd3 : d 3 = -Complex.I := by linear_combination hdsum - hd2
      refine Or.inr (Or.inl ⟨σ.trans π0, a k, hk, fun i => ?_⟩)
      have hdi : a (π0 (σ i)) = a k * d i := by simp [d, b, mul_inv_cancel_left₀ hk]
      change a (π0 (σ i)) = _
      rw [hdi]; fin_cases i <;> simp [hd0, hd1, hd2, hd3]
    · have hd2 : d 2 = -Complex.I := by linear_combination h2mI
      have hd3 : d 3 = -1 := by linear_combination hdsum - hd2
      refine Or.inr (Or.inl ⟨(Equiv.swap 2 3).trans (σ.trans π0), a k, hk, fun i => ?_⟩)
      change a (π0 (σ (Equiv.swap 2 3 i))) = _
      have hdi : ∀ j, a (π0 (σ j)) = a k * d j := fun j => by simp [d, b, mul_inv_cancel_left₀ hk]
      rw [hdi]; fin_cases i <;> simp [Equiv.swap_apply_def, hd0, hd1, hd2, hd3]
  · obtain ⟨π0, h3z⟩ := exists_zero_to_three a ha4
    let b : Fin 4 → ℂ := fun i => a (π0 i)
    have hb3 : b 3 = 0 := h3z
    have hbsum : b 0 + b 1 + b 2 = 0 := by
      have : ∑ i : Fin 4, a (π0 i) = 0 := by rw [Equiv.sum_comp π0 a]; exact ha1
      rw [Fin.sum_univ_four] at this; change b 0 + b 1 + b 2 + b 3 = 0 at this
      rw [hb3] at this; linear_combination this
    have hbsq : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 = 0 := by
      have : ∑ i : Fin 4, (a (π0 i)) ^ 2 = 0 := by
        rw [Equiv.sum_comp π0 (fun i => (a i) ^ 2)]; exact ha2
      rw [Fin.sum_univ_four] at this; change b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 = 0 at this
      rw [hb3] at this; linear_combination this
    have hb0_ne : b 0 ≠ 0 := by
      intro h0
      rw [h0] at hbsum hbsq
      have h12 : b 1 = 0 ∧ b 2 = 0 := by
        have hsq : 2 * b 1 ^ 2 = 0 := by linear_combination hbsq - (b 2 - b 1) * hbsum
        have hb1 : b 1 = 0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hsq).resolve_left (by norm_num))
        exact ⟨hb1, by linear_combination hbsum - hb1⟩
      apply ha_ne; funext i
      have := congrFun (show b = 0 by
        funext j; fin_cases j <;> simp [h0, h12.1, h12.2, hb3]) (π0.symm i)
      simpa [b] using this
    let w : ℂ := b 1 / b 0
    have hw : w ^ 2 + w + 1 = 0 := by
      have hb2 : b 2 = -(b 0 + b 1) := by linear_combination hbsum
      rw [hb2] at hbsq
      have hq : b 1 ^ 2 + b 0 * b 1 + b 0 ^ 2 = 0 := by linear_combination hbsq / 2
      dsimp [w]; field_simp [hb0_ne]; linear_combination hq
    have hb1_eq : b 1 = b 0 * w := by dsimp [w]; field_simp [hb0_ne]
    have hb2_eq : b 2 = b 0 * w ^ 2 := by
      linear_combination hbsum - hb1_eq - b 0 * hw
    refine Or.inr (Or.inr ⟨π0, b 0, w, hb0_ne, hw, fun i => ?_⟩)
    change b i = _
    fin_cases i <;> simp [hb1_eq, hb2_eq, hb3]
  · obtain ⟨π0, h3z⟩ := exists_zero_to_three a ha4
    let b : Fin 4 → ℂ := fun i => a (π0 i)
    have hb3 : b 3 = 0 := h3z
    have hbsum : b 0 + b 1 + b 2 = 0 := by
      have : ∑ i : Fin 4, a (π0 i) = 0 := by rw [Equiv.sum_comp π0 a]; exact ha1
      rw [Fin.sum_univ_four] at this; change b 0 + b 1 + b 2 + b 3 = 0 at this
      rw [hb3] at this; linear_combination this
    have hbcube : b 0 ^ 3 + b 1 ^ 3 + b 2 ^ 3 = 0 := by
      have : ∑ i : Fin 4, (a (π0 i)) ^ 3 = 0 := by
        rw [Equiv.sum_comp π0 (fun i => (a i) ^ 3)]; exact ha3
      rw [Fin.sum_univ_four] at this; change b 0 ^ 3 + b 1 ^ 3 + b 2 ^ 3 + b 3 ^ 3 = 0 at this
      rw [hb3] at this; linear_combination this
    have hprod3 : b 0 * b 1 * b 2 = 0 := by
      have hcb : (b 0 + b 1 + b 2) ^ 3 = 0 := by rw [hbsum]; ring
      linear_combination (hbcube - hcb + 3 * (b 0 * b 1 + b 0 * b 2 + b 1 * b 2) * hbsum) / 3
    have hσ : ∃ σ : Equiv.Perm (Fin 4), σ 3 = 3 ∧ b (σ 2) = 0 := by
      rcases mul_eq_zero.mp hprod3 with h01 | h2
      · rcases mul_eq_zero.mp h01 with h0 | h1
        · exact ⟨Equiv.swap 0 2, by decide, by simp [h0]⟩
        · exact ⟨Equiv.swap 1 2, by decide, by simp [h1]⟩
      · exact ⟨1, rfl, h2⟩
    rcases hσ with ⟨σ, hσ3, hσ2⟩
    let d : Fin 4 → ℂ := fun i => b (σ i)
    have hd2 : d 2 = 0 := hσ2
    have hd3 : d 3 = 0 := by simp [d, hσ3, hb3]
    have hdsum : d 0 + d 1 = 0 := by
      have : ∑ i : Fin 4, b (σ i) = ∑ i : Fin 4, b i := Equiv.sum_comp σ b
      rw [Fin.sum_univ_four, Fin.sum_univ_four, hb3] at this
      change d 0 + d 1 + d 2 + d 3 = _ at this
      rw [hd2, hd3] at this; linear_combination this + hbsum
    have hd0_ne : d 0 ≠ 0 := by
      intro h0
      have h1 : d 1 = 0 := by linear_combination hdsum - h0
      apply ha_ne; funext i
      have := congrFun (show d = 0 by funext j; fin_cases j <;> simp [h0, h1, hd2, hd3])
        (σ.symm (π0.symm i))
      simpa [d, b] using this
    have hd1 : d 1 = -d 0 := by linear_combination hdsum
    refine Or.inl ⟨σ.trans π0, d 0, hd0_ne, fun i => ?_⟩
    change d i = _
    fin_cases i <;> simp [hd1, hd2, hd3]

lemma perm5_inj (a0 a1 a2 a3 a4 : Fin 5)
    (h01 : a0 ≠ a1) (h02 : a0 ≠ a2) (h03 : a0 ≠ a3) (h04 : a0 ≠ a4)
    (h12 : a1 ≠ a2) (h13 : a1 ≠ a3) (h14 : a1 ≠ a4)
    (h23 : a2 ≠ a3) (h24 : a2 ≠ a4) (h34 : a3 ≠ a4) :
    Function.Injective ![a0, a1, a2, a3, a4] := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [Ne.symm]

set_option maxHeartbeats 800000 in
lemma classify_U_e4 (U : Submodule ℂ Vec) (hU2 : 2 ≤ Module.finrank ℂ U)
    (hsum : ∀ u ∈ U, ∑ j : Fin 5, u j = 0)
    (he4 : ∀ u ∈ U, esym4 u = 0) :
    ∃ σ : Equiv.Perm (Fin 5),
      ((fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j)) ∈ U ∧
       (fun j => (![1, 0, -1, 0, 0] : Vec) (σ.symm j)) ∈ U) ∨
      (∃ w : ℂ, w ^ 2 + w + 1 = 0 ∧
       (fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j)) ∈ U ∧
       (fun j => (![0, 0, 1, w, w ^ 2] : Vec) (σ.symm j)) ∈ U) := by
  let b := Module.finBasis ℂ U
  let i0 : Fin (Module.finrank ℂ U) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank ℂ U) := ⟨1, by omega⟩
  let v : Vec := (b i0).1
  let u : Vec := (b i1).1
  have hv : v ∈ U := (b i0).2
  have hu : u ∈ U := (b i1).2
  have hli : ∀ s t : ℂ, s • v + t • u = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    have hsub : s • b i0 + t • b i1 = 0 := by
      apply Subtype.ext; simpa [v, u] using hst
    have hli' := b.linearIndependent
    have hcomb : (Finsupp.single i0 s + Finsupp.single i1 t) = 0 := by
      have h0 : Finsupp.linearCombination ℂ b
          (Finsupp.single i0 s + Finsupp.single i1 t) = 0 := by
        simp [Finsupp.linearCombination_single, hsub]
      exact (linearIndependent_iff.mp hli') _ h0
    have hne01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
    have hs := congrArg (fun f => f i0) hcomb
    have ht := congrArg (fun f => f i1) hcomb
    simp [Finsupp.single_apply, hne01, hne01.symm] at hs ht
    exact ⟨hs, ht⟩
  by_cases hzero : ∃ j0 : Fin 5, v j0 = 0 ∧ u j0 = 0
  · obtain ⟨j0, hv0, hu0⟩ := hzero
    let σ0 : Equiv.Perm (Fin 5) := Equiv.swap 4 j0
    let v' : Vec := fun j => v (σ0 j)
    let u' : Vec := fun j => u (σ0 j)
    have hv'4 : v' 4 = 0 := by simp [v', σ0, hv0]
    have hu'4 : u' 4 = 0 := by simp [u', σ0, hu0]
    have hprod : ∀ s : ℂ, ∃ j : Fin 4, s * v' j.castSucc + u' j.castSucc = 0 := by
      intro s
      have hmem : s • v + u ∈ U := U.add_mem (U.smul_mem s hv) hu
      have h4 := he4 _ hmem
      rw [← esym4_perm σ0 _ (hsum _ hmem)] at h4
      have hval : (fun j => (s • v + u) (σ0 j)) 4 = 0 := by
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        change s * v' 4 + u' 4 = 0
        rw [hv'4, hu'4]; ring
      unfold esym4 at h4
      rw [hval] at h4
      have h0123 : (s * v' 0 + u' 0) * (s * v' 1 + u' 1) * (s * v' 2 + u' 2) * (s * v' 3 + u' 3) = 0 := by
        simpa [v', u', Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h4
      rcases mul_eq_zero.mp h0123 with h012 | h3
      · rcases mul_eq_zero.mp h012 with h01 | h2
        · rcases mul_eq_zero.mp h01 with h0 | h1
          · exact ⟨0, h0⟩
          · exact ⟨1, h1⟩
        · exact ⟨2, h2⟩
      · exact ⟨3, h3⟩
    choose f hf using fun k : Fin 5 => hprod (k.val : ℂ)
    have hnotinj : ¬ Function.Injective f := by
      intro hinj
      have hcard := Fintype.card_le_of_injective f hinj
      simp at hcard
    rw [Function.not_injective_iff] at hnotinj
    obtain ⟨k1, k2, hfeq, hkne⟩ := hnotinj
    let j1 : Fin 4 := f k1
    have hk1 : (k1.val : ℂ) * v' j1.castSucc + u' j1.castSucc = 0 := hf k1
    have hk2 : (k2.val : ℂ) * v' j1.castSucc + u' j1.castSucc = 0 := by
      dsimp only [j1]; rw [hfeq]; exact hf k2
    have hdiff : ((k1.val : ℂ) - (k2.val : ℂ)) * v' j1.castSucc = 0 := by
      linear_combination hk1 - hk2
    have hne_c : (k1.val : ℂ) - (k2.val : ℂ) ≠ 0 := by
      intro h; apply hkne; apply Fin.ext; exact_mod_cast sub_eq_zero.mp h
    have hv'j1 : v' j1.castSucc = 0 := (mul_eq_zero.mp hdiff).resolve_left hne_c
    have hu'j1 : u' j1.castSucc = 0 := by linear_combination hk1 - (k1.val : ℂ) * hv'j1
    let σ1 : Equiv.Perm (Fin 5) := Equiv.swap 3 j1.castSucc
    have hσ1_4 : σ1 4 = 4 := by
      apply Equiv.swap_apply_of_ne_of_ne (by decide)
      have hj1lt : j1.val < 4 := j1.isLt
      exact Fin.ne_of_val_ne (by simp; omega)
    let σ : Equiv.Perm (Fin 5) := σ1.trans σ0
    let v2 : Vec := fun j => v (σ j)
    let u2 : Vec := fun j => u (σ j)
    have hv2_3 : v2 3 = 0 := by simp [v2, σ, σ1, v', hv'j1]
    have hu2_3 : u2 3 = 0 := by simp [u2, σ, σ1, u', hu'j1]
    have hv2_4 : v2 4 = 0 := by simp [v2, σ, hσ1_4, v', hv'4]
    have hu2_4 : u2 4 = 0 := by simp [u2, σ, hσ1_4, u', hu'4]
    have hv2_sum : v2 0 + v2 1 + v2 2 = 0 := by
      have hs : ∑ j : Fin 5, v (σ j) = 0 := by rw [Equiv.sum_comp σ v]; exact hsum v hv
      rw [Fin.sum_univ_five] at hs; change v2 0 + v2 1 + v2 2 + v2 3 + v2 4 = 0 at hs
      rw [hv2_3, hv2_4] at hs; linear_combination hs
    have hu2_sum : u2 0 + u2 1 + u2 2 = 0 := by
      have hs : ∑ j : Fin 5, u (σ j) = 0 := by rw [Equiv.sum_comp σ u]; exact hsum u hu
      rw [Fin.sum_univ_five] at hs; change u2 0 + u2 1 + u2 2 + u2 3 + u2 4 = 0 at hs
      rw [hu2_3, hu2_4] at hs; linear_combination hs
    have hdet : v2 1 * u2 2 - v2 2 * u2 1 ≠ 0 := by
      intro hd
      by_cases h1 : v2 1 = 0 ∧ u2 1 = 0
      · have hzero' : u2 2 • v - v2 2 • u = 0 := by
          funext j
          have hσj : ∀ i : Fin 5, u2 2 * v2 i - v2 2 * u2 i = 0 := by
            intro i
            fin_cases i
            · change u2 2 * v2 0 - v2 2 * u2 0 = 0
              linear_combination u2 2 * hv2_sum - v2 2 * hu2_sum + v2 2 * h1.2 - u2 2 * h1.1
            · change u2 2 * v2 1 - v2 2 * u2 1 = 0
              rw [h1.1, h1.2]; ring
            · change u2 2 * v2 2 - v2 2 * u2 2 = 0; ring
            · change u2 2 * v2 3 - v2 2 * u2 3 = 0
              rw [hv2_3, hu2_3]; ring
            · change u2 2 * v2 4 - v2 2 * u2 4 = 0
              rw [hv2_4, hu2_4]; ring
          simpa [v2, u2] using hσj (σ.symm j)
        have hli0 := hli (u2 2) (-v2 2) (by simpa [sub_eq_add_neg] using hzero')
        have hvz : v = 0 := by
          funext j
          have hσj : ∀ i : Fin 5, v2 i = 0 := by
            intro i; fin_cases i
            · change v2 0 = 0; linear_combination hv2_sum - h1.1 + hli0.2
            · exact h1.1
            · change v2 2 = 0; linear_combination -hli0.2
            · exact hv2_3
            · exact hv2_4
          simpa [v2] using hσj (σ.symm j)
        exact one_ne_zero (hli 1 0 (by simp [hvz])).1
      · have hzero' : u2 1 • v - v2 1 • u = 0 := by
          funext j
          have hσj : ∀ i : Fin 5, u2 1 * v2 i - v2 1 * u2 i = 0 := by
            intro i; fin_cases i
            · change u2 1 * v2 0 - v2 1 * u2 0 = 0
              linear_combination u2 1 * hv2_sum - v2 1 * hu2_sum + hd
            · change u2 1 * v2 1 - v2 1 * u2 1 = 0; ring
            · change u2 1 * v2 2 - v2 1 * u2 2 = 0; linear_combination -hd
            · change u2 1 * v2 3 - v2 1 * u2 3 = 0; rw [hv2_3, hu2_3]; ring
            · change u2 1 * v2 4 - v2 1 * u2 4 = 0; rw [hv2_4, hu2_4]; ring
          simpa [v2, u2] using hσj (σ.symm j)
        have hli0 := hli (u2 1) (-v2 1) (by simpa [sub_eq_add_neg] using hzero')
        exact h1 ⟨by linear_combination -hli0.2, hli0.1⟩
    let D := v2 1 * u2 2 - v2 2 * u2 1
    have hD : D ≠ 0 := hdet
    refine ⟨σ, Or.inl ⟨?_, ?_⟩⟩
    · have heq : (fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j)) =
          (-u2 2 / D) • v + (v2 2 / D) • u := by
        funext j
        have hσj : ∀ i : Fin 5, (![1, -1, 0, 0, 0] : Vec) i =
            (-u2 2 / D) * v2 i + (v2 2 / D) * u2 i := by
          intro i; fin_cases i
          · change 1 = (-u2 2 / D) * v2 0 + (v2 2 / D) * u2 0
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
            dsimp [D]; linear_combination u2 2 * hv2_sum - v2 2 * hu2_sum
          · change -1 = (-u2 2 / D) * v2 1 + (v2 2 / D) * u2 1
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
            dsimp [D]; ring
          · change 0 = (-u2 2 / D) * v2 2 + (v2 2 / D) * u2 2
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
            ring
          · change 0 = (-u2 2 / D) * v2 3 + (v2 2 / D) * u2 3; simp [hv2_3, hu2_3]
          · change 0 = (-u2 2 / D) * v2 4 + (v2 2 / D) * u2 4; simp [hv2_4, hu2_4]
        simpa [v2, u2] using hσj (σ.symm j)
      rw [heq]; exact U.add_mem (U.smul_mem _ hv) (U.smul_mem _ hu)
    · have heq : (fun j => (![1, 0, -1, 0, 0] : Vec) (σ.symm j)) =
          (u2 1 / D) • v + (-v2 1 / D) • u := by
        funext j
        have hσj : ∀ i : Fin 5, (![1, 0, -1, 0, 0] : Vec) i =
            (u2 1 / D) * v2 i + (-v2 1 / D) * u2 i := by
          intro i; fin_cases i
          · change 1 = (u2 1 / D) * v2 0 + (-v2 1 / D) * u2 0
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
            dsimp [D]; linear_combination -u2 1 * hv2_sum + v2 1 * hu2_sum
          · change 0 = (u2 1 / D) * v2 1 + (-v2 1 / D) * u2 1
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
            ring
          · change -1 = (u2 1 / D) * v2 2 + (-v2 1 / D) * u2 2
            rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD]
            dsimp [D]; ring
          · change 0 = (u2 1 / D) * v2 3 + (-v2 1 / D) * u2 3; simp [hv2_3, hu2_3]
          · change 0 = (u2 1 / D) * v2 4 + (-v2 1 / D) * u2 4; simp [hv2_4, hu2_4]
        simpa [v2, u2] using hσj (σ.symm j)
      rw [heq]; exact U.add_mem (U.smul_mem _ hv) (U.smul_mem _ hu)
  · push_neg at hzero
    have hnz : ∀ j : Fin 5, v j ≠ 0 ∨ u j ≠ 0 := fun j =>
      if h : v j = 0 then Or.inr (hzero j h) else Or.inl h
    let rel (j k : Fin 5) : Prop := v j * u k = u j * v k
    have hrel_trans : ∀ i j k, rel i j → rel j k → rel i k := by
      intro i j k hij hjk
      rcases hnz j with hvj | huj
      · have : v j * (v i * u k - u i * v k) = 0 := by
          linear_combination v k * hij + v i * hjk
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hvj)
      · have : u j * (v i * u k - u i * v k) = 0 := by
          linear_combination u k * hij + u i * hjk
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left huj)
    have hpair : ∀ j : Fin 5, ∃ k : Fin 5, k ≠ j ∧ rel j k := by
      intro j
      let x : Vec := (-u j) • v + (v j) • u
      have hxU : x ∈ U := U.add_mem (U.smul_mem _ hv) (U.smul_mem _ hu)
      have hxj : x j = 0 := by simp [x]; ring
      let σj : Equiv.Perm (Fin 5) := Equiv.swap 4 j
      have h4 := he4 x hxU
      rw [← esym4_perm σj x (hsum x hxU)] at h4
      have hx4 : x (σj 4) = 0 := by simp [σj, hxj]
      unfold esym4 at h4
      dsimp only at h4
      rw [hx4] at h4
      have h0123 : x (σj 0) * x (σj 1) * x (σj 2) * x (σj 3) = 0 := by
        linear_combination h4
      have hsome : ∃ a : Fin 4, x (σj a.castSucc) = 0 := by
        rcases mul_eq_zero.mp h0123 with h012 | h3
        · rcases mul_eq_zero.mp h012 with h01 | h2
          · rcases mul_eq_zero.mp h01 with h0 | h1
            · exact ⟨0, h0⟩
            · exact ⟨1, h1⟩
          · exact ⟨2, h2⟩
        · exact ⟨3, h3⟩
      rcases hsome with ⟨a, ha⟩
      refine ⟨σj a.castSucc, ?_, ?_⟩
      · intro heq
        have h1 : σj a.castSucc = σj 4 := by rw [heq]; simp [σj]
        have h2 : a.castSucc = 4 := σj.injective h1
        have halt : a.val < 4 := a.isLt
        exact Fin.ne_of_val_ne (by simp; omega) h2
      · simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha
        change v j * u (σj a.castSucc) = u j * v (σj a.castSucc)
        linear_combination ha
    have hnot_all : ¬ ∀ j : Fin 5, rel 0 j := by
      intro hall
      have h0 : (-u 0) • v + (v 0) • u = 0 := by
        funext j; simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
        linear_combination hall j
      have hli0 := hli (-u 0) (v 0) h0
      rcases hnz 0 with hv0 | hu0
      · exact hv0 hli0.2
      · exact hu0 (neg_eq_zero.mp hli0.1)
    letI : DecidablePred (fun j : Fin 5 => rel 0 j) := Classical.decPred _
    let S : Finset (Fin 5) := Finset.univ.filter (fun j => rel 0 j)
    let T : Finset (Fin 5) := Finset.univ.filter (fun j => ¬ rel 0 j)
    have hS0 : (0 : Fin 5) ∈ S := by simp [S, rel, mul_comm]
    have hS_ge2 : 2 ≤ S.card := by
      obtain ⟨k, hk0, hrel⟩ := hpair 0
      have hkS : k ∈ S := by simp [S, hrel]
      have hsub : ({0, k} : Finset (Fin 5)) ⊆ S := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      have hc2 : ({0, k} : Finset (Fin 5)).card = 2 := Finset.card_pair hk0.symm
      exact hc2 ▸ Finset.card_le_card hsub
    have hT_ge2 : 2 ≤ T.card := by
      push_neg at hnot_all
      obtain ⟨j, hj⟩ := hnot_all
      obtain ⟨k, hkj, hrel⟩ := hpair j
      have hjT : j ∈ T := by simp [T, hj]
      have hkT : k ∈ T := by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        intro h0k
        exact hj (hrel_trans 0 k j h0k (by unfold rel at hrel ⊢; linear_combination -hrel))
      have hsub : ({j, k} : Finset (Fin 5)) ⊆ T := by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
      have hc2 : ({j, k} : Finset (Fin 5)).card = 2 := Finset.card_pair hkj.symm
      exact hc2 ▸ Finset.card_le_card hsub
    have hST_disj : Disjoint S T := by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hxS hxT
      exact hxT hxS
    have hST_sum : S.card + T.card = 5 := by
      rw [← Finset.card_union_of_disjoint hST_disj]
      have hun : S ∪ T = Finset.univ := by
        ext x; simp [S, T, em]
      rw [hun]; simp
    have hT_equiv : ∀ j ∈ T, ∀ k ∈ T, rel j k := by
      intro j hj k hk
      by_contra hne
      letI : DecidablePred (fun x : Fin 5 => rel j x) := Classical.decPred _
      letI : DecidablePred (fun x : Fin 5 => rel k x) := Classical.decPred _
      let Cj := T.filter (fun x => rel j x)
      let Ck := T.filter (fun x => rel k x)
      have hdisj : Disjoint Cj Ck := by
        rw [Finset.disjoint_left]
        intro x hxj hxk
        simp only [Cj, Ck, Finset.mem_filter] at hxj hxk
        exact hne (hrel_trans j x k hxj.2 (by unfold rel at hxk ⊢; linear_combination -hxk.2))
      have hCj2 : 2 ≤ Cj.card := by
        obtain ⟨j', hj'ne, hj'r⟩ := hpair j
        have hj'T : j' ∈ T := by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          intro h0; exact hj (hrel_trans 0 j' j h0 (by unfold rel at hj'r ⊢; linear_combination -hj'r))
        have hsub : ({j, j'} : Finset (Fin 5)) ⊆ Cj := by
          intro x hx; simp at hx; rcases hx with rfl | rfl
          · simp [Cj, hj, rel, mul_comm]
          · simp [Cj, hj'T, hj'r]
        exact (Finset.card_pair hj'ne.symm) ▸ Finset.card_le_card hsub
      have hCk2 : 2 ≤ Ck.card := by
        obtain ⟨k', hk'ne, hk'r⟩ := hpair k
        have hk'T : k' ∈ T := by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          intro h0; exact hk (hrel_trans 0 k' k h0 (by unfold rel at hk'r ⊢; linear_combination -hk'r))
        have hsub : ({k, k'} : Finset (Fin 5)) ⊆ Ck := by
          intro x hx; simp at hx; rcases hx with rfl | rfl
          · simp [Ck, hk, rel, mul_comm]
          · simp [Ck, hk'T, hk'r]
        exact (Finset.card_pair hk'ne.symm) ▸ Finset.card_le_card hsub
      have hle : Cj.card + Ck.card ≤ T.card := by
        rw [← Finset.card_union_of_disjoint hdisj]
        exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      omega
    have hPQ : ∃ (P Q : Finset (Fin 5)), P.card = 2 ∧ Q.card = 3 ∧ Disjoint P Q ∧
        (∀ x ∈ P, ∀ y ∈ P, rel x y) ∧ (∀ x ∈ Q, ∀ y ∈ Q, rel x y) ∧
        (∀ x ∈ P, ∀ y ∈ Q, ¬ rel x y) := by
      have hS_equiv : ∀ x ∈ S, ∀ y ∈ S, rel x y := fun x hx y hy => by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        exact hrel_trans x 0 y (by unfold rel at hx ⊢; linear_combination -hx) hy
      have hST_not : ∀ x ∈ S, ∀ y ∈ T, ¬ rel x y := fun x hx y hy hxy => by
        simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        exact hy (hrel_trans 0 x y hx hxy)
      rcases (by omega : S.card = 2 ∧ T.card = 3 ∨ S.card = 3 ∧ T.card = 2) with ⟨hS2, hT3⟩ | ⟨hS3, hT2⟩
      · exact ⟨S, T, hS2, hT3, hST_disj, hS_equiv, hT_equiv, hST_not⟩
      · exact ⟨T, S, hT2, hS3, hST_disj.symm, hT_equiv, hS_equiv, fun x hx y hy hxy =>
          hST_not y hy x hx (by unfold rel at hxy ⊢; linear_combination -hxy)⟩
    obtain ⟨P, Q, hP2, hQ3, hPQ_disj, hP_rel, hQ_rel, hPQ_nrel⟩ := hPQ
    obtain ⟨p0, p1, hpne, rfl⟩ := Finset.card_eq_two.mp hP2
    obtain ⟨q0, q1, q2, hq01, hq02, hq12, rfl⟩ := Finset.card_eq_three.mp hQ3
    have hp0Q : p0 ≠ q0 ∧ p0 ≠ q1 ∧ p0 ≠ q2 := by
      have h := Finset.disjoint_left.mp hPQ_disj (by simp : p0 ∈ ({p0, p1} : Finset (Fin 5)))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    have hp1Q : p1 ≠ q0 ∧ p1 ≠ q1 ∧ p1 ≠ q2 := by
      have h := Finset.disjoint_left.mp hPQ_disj (by simp : p1 ∈ ({p0, p1} : Finset (Fin 5)))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    have hinj : Function.Injective ![p0, p1, q0, q1, q2] :=
      perm5_inj p0 p1 q0 q1 q2 hpne hp0Q.1 hp0Q.2.1 hp0Q.2.2 hp1Q.1 hp1Q.2.1 hp1Q.2.2 hq01 hq02 hq12
    let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective ![p0, p1, q0, q1, q2]
      (Finite.injective_iff_bijective.mp hinj)
    let x0 : Vec := (-u q0) • v + (v q0) • u
    have hx0U : x0 ∈ U := U.add_mem (U.smul_mem _ hv) (U.smul_mem _ hu)
    have hx0_Q : x0 q0 = 0 ∧ x0 q1 = 0 ∧ x0 q2 = 0 := by
      refine ⟨by simp [x0]; ring, ?_, ?_⟩
      · have h := hQ_rel q0 (by simp) q1 (by simp)
        simp only [x0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linear_combination h
      · have h := hQ_rel q0 (by simp) q2 (by simp)
        simp only [x0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linear_combination h
    have hx0_p0 : x0 p0 ≠ 0 := by
      intro h0
      apply hPQ_nrel p0 (by simp) q0 (by simp)
      simp only [x0, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
      unfold rel; linear_combination -h0
    have hx0_p1 : x0 p1 = -x0 p0 := by
      have hs : ∑ j : Fin 5, x0 (σ j) = 0 := by rw [Equiv.sum_comp σ x0]; exact hsum x0 hx0U
      rw [Fin.sum_univ_five] at hs
      have hσ : σ 0 = p0 ∧ σ 1 = p1 ∧ σ 2 = q0 ∧ σ 3 = q1 ∧ σ 4 = q2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
      rw [hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2, hx0_Q.1, hx0_Q.2.1, hx0_Q.2.2] at hs
      linear_combination hs
    let x1 : Vec := (-u p0) • v + (v p0) • u
    have hx1U : x1 ∈ U := U.add_mem (U.smul_mem _ hv) (U.smul_mem _ hu)
    have hx1_P : x1 p0 = 0 ∧ x1 p1 = 0 := by
      refine ⟨by simp [x1]; ring, ?_⟩
      have h := hP_rel p0 (by simp) p1 (by simp)
      simp only [x1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; linear_combination h
    have hx1_q0 : x1 q0 ≠ 0 := by
      intro h0
      apply hPQ_nrel p0 (by simp) q0 (by simp)
      simp only [x1, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0
      unfold rel; linear_combination h0
    let y0 : Vec := (x0 p0)⁻¹ • x0
    let y1 : Vec := (x1 q0)⁻¹ • x1
    have hy0U : y0 ∈ U := U.smul_mem _ hx0U
    have hy1U : y1 ∈ U := U.smul_mem _ hx1U
    let w : ℂ := y1 q1
    have hy1_sum : 1 + w + y1 q2 = 0 := by
      have hs : ∑ j : Fin 5, y1 (σ j) = 0 := by rw [Equiv.sum_comp σ y1]; exact hsum y1 hy1U
      rw [Fin.sum_univ_five] at hs
      have hσ : σ 0 = p0 ∧ σ 1 = p1 ∧ σ 2 = q0 ∧ σ 3 = q1 ∧ σ 4 = q2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
      rw [hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2] at hs
      have h0 : y1 p0 = 0 := by simp [y1, hx1_P.1]
      have h1 : y1 p1 = 0 := by simp [y1, hx1_P.2]
      have h2 : y1 q0 = 1 := by simp [y1, hx1_q0]
      rw [h0, h1, h2] at hs; dsimp [w]; linear_combination hs
    have hw : w ^ 2 + w + 1 = 0 := by
      have h4 := he4 (y0 + y1) (U.add_mem hy0U hy1U)
      rw [← esym4_perm σ (y0 + y1) (hsum _ (U.add_mem hy0U hy1U))] at h4
      have hσ : σ 0 = p0 ∧ σ 1 = p1 ∧ σ 2 = q0 ∧ σ 3 = q1 ∧ σ 4 = q2 := ⟨rfl, rfl, rfl, rfl, rfl⟩
      unfold esym4 at h4
      dsimp only at h4
      simp only [Pi.add_apply, hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2] at h4
      have hy0_vals : y0 p0 = 1 ∧ y0 p1 = -1 ∧ y0 q0 = 0 ∧ y0 q1 = 0 ∧ y0 q2 = 0 := by
        refine ⟨by simp [y0, hx0_p0], ?_, by simp [y0, hx0_Q.1], by simp [y0, hx0_Q.2.1], by simp [y0, hx0_Q.2.2]⟩
        simp only [y0, Pi.smul_apply, smul_eq_mul, hx0_p1, mul_neg, inv_mul_cancel₀ hx0_p0]
      have hy1_vals : y1 p0 = 0 ∧ y1 p1 = 0 ∧ y1 q0 = 1 :=
        ⟨by simp [y1, hx1_P.1], by simp [y1, hx1_P.2], by simp [y1, hx1_q0]⟩
      rw [hy0_vals.1, hy0_vals.2.1, hy0_vals.2.2.1, hy0_vals.2.2.2.1, hy0_vals.2.2.2.2,
          hy1_vals.1, hy1_vals.2.1, hy1_vals.2.2] at h4
      have hq2 : y1 q2 = -1 - w := by linear_combination hy1_sum
      rw [hq2] at h4
      change y1 q1 ^ 2 + y1 q1 + 1 = 0
      dsimp only [w] at h4
      linear_combination h4
    have hy1_q2 : y1 q2 = w ^ 2 := by linear_combination hy1_sum - hw
    refine ⟨σ, Or.inr ⟨w, hw, ?_, ?_⟩⟩
    · have heq : (fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j)) = y0 := by
        funext j
        have hσj : ∀ i : Fin 5, (![1, -1, 0, 0, 0] : Vec) i = y0 (σ i) := by
          intro i; fin_cases i
          · simp [σ, y0, hx0_p0]
          · simp [σ, y0, hx0_p1, inv_mul_cancel₀ hx0_p0]
          · simp [σ, y0, hx0_Q.1]
          · simp [σ, y0, hx0_Q.2.1]
          · simp [σ, y0, hx0_Q.2.2]
        simpa using hσj (σ.symm j)
      rw [heq]; exact hy0U
    · have heq : (fun j => (![0, 0, 1, w, w ^ 2] : Vec) (σ.symm j)) = y1 := by
        funext j
        have hσj : ∀ i : Fin 5, (![0, 0, 1, w, w ^ 2] : Vec) i = y1 (σ i) := by
          intro i; fin_cases i
          · simp [σ, y1, hx1_P.1]
          · simp [σ, y1, hx1_P.2]
          · simp [σ, y1, hx1_q0]
          · simp [σ, w]
          · simp [σ, hy1_q2]
        simpa using hσj (σ.symm j)
      rw [heq]; exact hy1U

lemma main_304 (L : Submodule ℂ Mat) (a : Fin 4 → ℂ) (U : Submodule ℂ Vec)
    (ha_ne : a ≠ 0) (hU2 : 2 ≤ Module.finrank ℂ U)
    (hL : ValidL L) (h_pure : ∀ u ∈ U, outer a u ∈ L) :
    Module.finrank ℂ L ≤ 4 := by
  have hU_ne : ∃ u0 ∈ U, u0 ≠ 0 := by
    by_contra hall; push_neg at hall
    have hbot : U = ⊥ := (Submodule.eq_bot_iff U).mpr hall
    rw [hbot, finrank_bot] at hU2; omega
  have ha1 : ∑ i : Fin 4, a i = 0 := by
    obtain ⟨u0, hu0, hu0_ne⟩ := hU_ne
    obtain ⟨j0, hj0⟩ : ∃ j0, u0 j0 ≠ 0 := by
      by_contra h; push_neg at h; exact hu0_ne (funext h)
    have hc := (hL _ (h_pure u0 hu0)).2.1 j0
    simp only [outer, ← Finset.sum_mul] at hc
    exact (mul_eq_zero.mp hc).resolve_right hj0
  have hU_sum : ∀ u ∈ U, ∑ j : Fin 5, u j = 0 := by
    intro u hu
    obtain ⟨i0, hi0⟩ : ∃ i0, a i0 ≠ 0 := by
      by_contra h; push_neg at h; exact ha_ne (funext h)
    have hr := (hL _ (h_pure u hu)).1 i0
    simp only [outer, ← Finset.mul_sum] at hr
    exact (mul_eq_zero.mp hr).resolve_left hi0
  have hrel : ∀ u ∈ U,
      (∑ i : Fin 4, (a i) ^ 2) * (∑ j : Fin 5, (u j) ^ 2) = 0 ∧
      (∑ i : Fin 4, (a i) ^ 3) * (∑ j : Fin 5, (u j) ^ 3) = 0 ∧
      (a 0 * a 1 * a 2 * a 3) * esym4 u = 0 :=
    fun u hu => outer_relations L hL a u (hU_sum u hu) (h_pure u hu)
  have hp2_or : (∑ i : Fin 4, (a i) ^ 2 = 0) ∨ (∀ u ∈ U, ∑ j : Fin 5, (u j) ^ 2 = 0) := by
    by_cases h : ∑ i : Fin 4, (a i) ^ 2 = 0
    · exact Or.inl h
    · exact Or.inr fun u hu => (mul_eq_zero.mp (hrel u hu).1).resolve_left h
  have hp3_or : (∑ i : Fin 4, (a i) ^ 3 = 0) ∨ (∀ u ∈ U, ∑ j : Fin 5, (u j) ^ 3 = 0) := by
    by_cases h : ∑ i : Fin 4, (a i) ^ 3 = 0
    · exact Or.inl h
    · exact Or.inr fun u hu => (mul_eq_zero.mp (hrel u hu).2.1).resolve_left h
  have he4_or : (a 0 * a 1 * a 2 * a 3 = 0) ∨ (∀ u ∈ U, esym4 u = 0) := by
    by_cases h : a 0 * a 1 * a 2 * a 3 = 0
    · exact Or.inl h
    · exact Or.inr fun u hu => (mul_eq_zero.mp (hrel u hu).2.2).resolve_left h
  have h234 : (∑ i : Fin 4, (a i) ^ 2 = 0 ∧ ∑ i : Fin 4, (a i) ^ 3 = 0) ∨
              (∑ i : Fin 4, (a i) ^ 2 = 0 ∧ a 0 * a 1 * a 2 * a 3 = 0) ∨
              (∑ i : Fin 4, (a i) ^ 3 = 0 ∧ a 0 * a 1 * a 2 * a 3 = 0) := by
    rcases hp2_or with ha2 | hu2
    · rcases hp3_or with ha3 | hu3
      · exact Or.inl ⟨ha2, ha3⟩
      · rcases he4_or with ha4 | hu4
        · exact Or.inr (Or.inl ⟨ha2, ha4⟩)
        · obtain ⟨_, u, hu, hne⟩ := p3_excludes_p2_and_e4 U hU2 hU_sum hu3
          exact False.elim (hne (hu4 u hu))
    · rcases hp3_or with ha3 | hu3
      · rcases he4_or with ha4 | hu4
        · exact Or.inr (Or.inr ⟨ha3, ha4⟩)
        · exact False.elim (not_p2_and_e4 U hU2 hU_sum hu2 hu4)
      · obtain ⟨⟨u, hu, hne⟩, _⟩ := p3_excludes_p2_and_e4 U hU2 hU_sum hu3
        exact False.elim (hne (hu2 u hu))
  have ha_cls := classify_a a ha_ne ha1 h234
  rcases ha_cls with ⟨π, c, hc, ha_eq⟩ | ⟨π, c, hc, ha_eq⟩ | ⟨π, c, w, hc, hw, ha_eq⟩
  · let L1 := L.map (rowPermEquiv π).toLinearMap
    have hL1 : ValidL L1 := rowPerm_valid π L hL
    have hdim : Module.finrank ℂ L1 = Module.finrank ℂ L :=
      LinearEquiv.finrank_map_eq (rowPermEquiv π) L
    rw [← hdim]
    refine Sub286.main L1 U hL1 (fun u hu => ?_) hU2
    have hmem : outer a (c⁻¹ • u) ∈ L := h_pure _ (U.smul_mem c⁻¹ hu)
    refine ⟨outer a (c⁻¹ • u), hmem, ?_⟩
    ext i j
    change a (π i) * (c⁻¹ * u j) = (![u, -u, 0, 0] : Mat) i j
    rw [ha_eq i]
    fin_cases i <;> simp [hc] <;> field_simp [hc]
  · have hprod_ne : a 0 * a 1 * a 2 * a 3 ≠ 0 := by
      have hpe : ∏ i : Fin 4, a i = ∏ i : Fin 4, a (π i) :=
        (Equiv.prod_comp π a).symm
      rw [Fin.prod_univ_four, Fin.prod_univ_four] at hpe
      rw [hpe, ha_eq 0, ha_eq 1, ha_eq 2, ha_eq 3]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      have hval : c * 1 * (c * Complex.I) * (c * -1) * (c * -Complex.I) = -c ^ 4 := by
        linear_combination (c ^ 4) * hI
      rw [hval]
      exact neg_ne_zero.mpr (pow_ne_zero 4 hc)
    have hU_e4 : ∀ u ∈ U, esym4 u = 0 := fun u hu =>
      (mul_eq_zero.mp (hrel u hu).2.2).resolve_left hprod_ne
    obtain ⟨σ, ⟨hu0, hu1⟩ | ⟨w, hw, hu0, hu1⟩⟩ := classify_U_e4 U hU2 hU_sum hU_e4
    · let L1 := (L.map (rowPermEquiv π).toLinearMap).map (colPermEquiv σ).toLinearMap
      have hL1 : ValidL L1 := colPerm_valid σ _ (rowPerm_valid π L hL)
      have hdim : Module.finrank ℂ L1 = Module.finrank ℂ L := by
        rw [LinearEquiv.finrank_map_eq (colPermEquiv σ), LinearEquiv.finrank_map_eq (rowPermEquiv π)]
      rw [← hdim]
      refine case_2a_bound L1 hL1 ?_ ?_
      · refine ⟨rowPermEquiv π (outer a (c⁻¹ • (fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j)))),
          ⟨outer a (c⁻¹ • (fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j))),
            h_pure _ (U.smul_mem c⁻¹ hu0), rfl⟩, ?_⟩
        ext i j; change a (π i) * (c⁻¹ * (![1, -1, 0, 0, 0] : Vec) (σ.symm (σ j))) = _
        rw [ha_eq i, Equiv.symm_apply_apply]; simp only [outer]; field_simp [hc]
      · refine ⟨rowPermEquiv π (outer a (c⁻¹ • (fun j => (![1, 0, -1, 0, 0] : Vec) (σ.symm j)))),
          ⟨outer a (c⁻¹ • (fun j => (![1, 0, -1, 0, 0] : Vec) (σ.symm j))),
            h_pure _ (U.smul_mem c⁻¹ hu1), rfl⟩, ?_⟩
        ext i j; change a (π i) * (c⁻¹ * (![1, 0, -1, 0, 0] : Vec) (σ.symm (σ j))) = _
        rw [ha_eq i, Equiv.symm_apply_apply]; simp only [outer]; field_simp [hc]
    · let L1 := (L.map (rowPermEquiv π).toLinearMap).map (colPermEquiv σ).toLinearMap
      have hL1 : ValidL L1 := colPerm_valid σ _ (rowPerm_valid π L hL)
      have hdim : Module.finrank ℂ L1 = Module.finrank ℂ L := by
        rw [LinearEquiv.finrank_map_eq (colPermEquiv σ), LinearEquiv.finrank_map_eq (rowPermEquiv π)]
      rw [← hdim]
      refine case_2b_bound w hw L1 hL1 ?_ ?_
      · refine ⟨rowPermEquiv π (outer a (c⁻¹ • (fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j)))),
          ⟨outer a (c⁻¹ • (fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j))),
            h_pure _ (U.smul_mem c⁻¹ hu0), rfl⟩, ?_⟩
        ext i j; change a (π i) * (c⁻¹ * (![1, -1, 0, 0, 0] : Vec) (σ.symm (σ j))) = _
        rw [ha_eq i, Equiv.symm_apply_apply]; simp only [outer]; field_simp [hc]
      · refine ⟨rowPermEquiv π (outer a (c⁻¹ • (fun j => (![0, 0, 1, w, w ^ 2] : Vec) (σ.symm j)))),
          ⟨outer a (c⁻¹ • (fun j => (![0, 0, 1, w, w ^ 2] : Vec) (σ.symm j))),
            h_pure _ (U.smul_mem c⁻¹ hu1), rfl⟩, ?_⟩
        ext i j; change a (π i) * (c⁻¹ * (![0, 0, 1, w, w ^ 2] : Vec) (σ.symm (σ j))) = _
        rw [ha_eq i, Equiv.symm_apply_apply]; simp only [outer]; field_simp [hc]
  · have hp3_ne : ∑ i : Fin 4, (a i) ^ 3 ≠ 0 := by
      rw [← Equiv.sum_comp π (fun i => (a i) ^ 3), Fin.sum_univ_four,
          ha_eq 0, ha_eq 1, ha_eq 2, ha_eq 3]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
      have hval : (c * 1) ^ 3 + (c * w) ^ 3 + (c * w ^ 2) ^ 3 + (c * 0) ^ 3 = 3 * c ^ 3 := by
        linear_combination (c ^ 3 + c ^ 3 * (w ^ 3 + 1)) * hw3
      rw [hval]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 3 hc)
    have hU_p3 : ∀ u ∈ U, ∑ j : Fin 5, (u j) ^ 3 = 0 := fun u hu =>
      (mul_eq_zero.mp (hrel u hu).2.1).resolve_left hp3_ne
    have hcls := (Sub303.main U hU2).mp (fun u hu => ⟨hU_sum u hu, hU_p3 u hu⟩)
    rcases hcls with ⟨σ, hpair | ⟨z, hz, hroot⟩⟩
    · have hu0 : (fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j)) ∈ U :=
        (hpair _).mpr ⟨1, 0, fun j => by simp⟩
      have hu1 : (fun j => (![0, 0, 1, -1, 0] : Vec) (σ.symm j)) ∈ U :=
        (hpair _).mpr ⟨0, 1, fun j => by simp⟩
      let L1 := (L.map (rowPermEquiv π).toLinearMap).map (colPermEquiv σ).toLinearMap
      have hL1 : ValidL L1 := colPerm_valid σ _ (rowPerm_valid π L hL)
      have hdim : Module.finrank ℂ L1 = Module.finrank ℂ L := by
        rw [LinearEquiv.finrank_map_eq (colPermEquiv σ), LinearEquiv.finrank_map_eq (rowPermEquiv π)]
      rw [← hdim]
      refine case_3a_bound w hw L1 hL1 ?_ ?_
      · refine ⟨rowPermEquiv π (outer a (c⁻¹ • (fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j)))),
          ⟨outer a (c⁻¹ • (fun j => (![1, -1, 0, 0, 0] : Vec) (σ.symm j))),
            h_pure _ (U.smul_mem c⁻¹ hu0), rfl⟩, ?_⟩
        ext i j; change a (π i) * (c⁻¹ * (![1, -1, 0, 0, 0] : Vec) (σ.symm (σ j))) = _
        rw [ha_eq i, Equiv.symm_apply_apply]; simp only [outer]; field_simp [hc]
      · refine ⟨rowPermEquiv π (outer a (c⁻¹ • (fun j => (![0, 0, 1, -1, 0] : Vec) (σ.symm j)))),
          ⟨outer a (c⁻¹ • (fun j => (![0, 0, 1, -1, 0] : Vec) (σ.symm j))),
            h_pure _ (U.smul_mem c⁻¹ hu1), rfl⟩, ?_⟩
        ext i j; change a (π i) * (c⁻¹ * (![0, 0, 1, -1, 0] : Vec) (σ.symm (σ j))) = _
        rw [ha_eq i, Equiv.symm_apply_apply]; simp only [outer]; field_simp [hc]
    · have hz5 : z ^ 5 = 1 := hz.pow_eq_one
      have hz1 : z ≠ 1 := hz.ne_one (by decide)
      have hzp : z ^ 4 + z ^ 3 + z ^ 2 + z + 1 = 0 := by
        have hmul : (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = 0 := by linear_combination hz5
        exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hz1)
      have hu0 : (fun j => (![1, z, z ^ 2, z ^ 3, z ^ 4] : Vec) (σ.symm j)) ∈ U :=
        (hroot _).mpr ⟨1, 0, fun j => by
          simp only [Equiv.symm_apply_apply, one_mul, zero_mul, add_zero]
          fin_cases j <;> simp⟩
      have hu1 : (fun j => (![1, z ^ 4, z ^ 3, z ^ 2, z] : Vec) (σ.symm j)) ∈ U :=
        (hroot _).mpr ⟨0, 1, fun j => by
          simp only [Equiv.symm_apply_apply, zero_mul, one_mul, zero_add]
          fin_cases j <;> simp
          · calc z ^ 3 = 1 * z ^ 3 := by ring
              _ = z ^ 5 * z ^ 3 := by rw [hz5]
              _ = z ^ 8 := by ring
          · calc z ^ 2 = 1 ^ 2 * z ^ 2 := by ring
              _ = (z ^ 5) ^ 2 * z ^ 2 := by rw [hz5]
              _ = z ^ 12 := by ring
          · calc z = 1 ^ 3 * z := by ring
              _ = (z ^ 5) ^ 3 * z := by rw [hz5]
              _ = z ^ 16 := by ring⟩
      let L1 := (L.map (rowPermEquiv π).toLinearMap).map (colPermEquiv σ).toLinearMap
      have hL1 : ValidL L1 := colPerm_valid σ _ (rowPerm_valid π L hL)
      have hdim : Module.finrank ℂ L1 = Module.finrank ℂ L := by
        rw [LinearEquiv.finrank_map_eq (colPermEquiv σ), LinearEquiv.finrank_map_eq (rowPermEquiv π)]
      rw [← hdim]
      refine case_3b_bound w z hw hzp L1 hL1 ?_ ?_
      · refine ⟨rowPermEquiv π (outer a (c⁻¹ • (fun j => (![1, z, z ^ 2, z ^ 3, z ^ 4] : Vec) (σ.symm j)))),
          ⟨outer a (c⁻¹ • (fun j => (![1, z, z ^ 2, z ^ 3, z ^ 4] : Vec) (σ.symm j))),
            h_pure _ (U.smul_mem c⁻¹ hu0), rfl⟩, ?_⟩
        ext i j; change a (π i) * (c⁻¹ * (![1, z, z ^ 2, z ^ 3, z ^ 4] : Vec) (σ.symm (σ j))) = _
        rw [ha_eq i, Equiv.symm_apply_apply]; simp only [outer]; field_simp [hc]
      · refine ⟨rowPermEquiv π (outer a (c⁻¹ • (fun j => (![1, z ^ 4, z ^ 3, z ^ 2, z] : Vec) (σ.symm j)))),
          ⟨outer a (c⁻¹ • (fun j => (![1, z ^ 4, z ^ 3, z ^ 2, z] : Vec) (σ.symm j))),
            h_pure _ (U.smul_mem c⁻¹ hu1), rfl⟩, ?_⟩
        ext i j; change a (π i) * (c⁻¹ * (![1, z ^ 4, z ^ 3, z ^ 2, z] : Vec) (σ.symm (σ j))) = _
        rw [ha_eq i, Equiv.symm_apply_apply]; simp only [outer]; field_simp [hc]

end Core
end PEqualNP.Outside.L_gct_304_aux

theorem PEqualNP.Outside.L_gct_304 : ∀ (L : Submodule ℂ (Fin 4 → Fin 5 → ℂ))
  (a : Fin 4 → ℂ) (U : Submodule ℂ (Fin 5 → ℂ)),
  a ≠ 0 → 2 ≤ Module.finrank ℂ U →
  (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, (1 + X i (f i))) = 120) →
  (∀ u ∈ U, (fun i j => a i * u j) ∈ L) →
  Module.finrank ℂ L ≤ 4 :=
  PEqualNP.Outside.L_gct_304_aux.Core.main_304
