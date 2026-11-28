import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_306_aux
open scoped BigOperators
variable {n : Nat}
abbrev Vec (n : Nat) := Fin n → ℂ
abbrev Mat (n : Nat) := Fin 4 → Fin n → ℂ
def dot (a b : Vec n) : ℂ := ∑ j, a j * b j
def mult3 (n : Nat) : ℂ := ((n-3 : Nat) : ℂ)
def mult2 (n : Nat) : ℂ := ((n-2 : Nat) : ℂ) * mult3 n
noncomputable def e0 (n : Nat) : ℂ := ∑ _f : Fin 4 ↪ Fin n, (1 : ℂ)

noncomputable def e1 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n, (X 0 (f 0) + X 1 (f 1) + X 2 (f 2) + X 3 (f 3))

noncomputable def e2 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n,
    (X 0 (f 0) * X 1 (f 1) + X 0 (f 0) * X 2 (f 2) + X 0 (f 0) * X 3 (f 3) +
     X 1 (f 1) * X 2 (f 2) + X 1 (f 1) * X 3 (f 3) + X 2 (f 2) * X 3 (f 3))

noncomputable def e3 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n,
    (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) + X 0 (f 0) * X 1 (f 1) * X 3 (f 3) +
     X 0 (f 0) * X 2 (f 2) * X 3 (f 3) + X 1 (f 1) * X 2 (f 2) * X 3 (f 3))

noncomputable def e4 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n, X 0 (f 0) * X 1 (f 1) * X 2 (f 2) * X 3 (f 3)

lemma poly_expand (X : Mat n) (t : ℂ) :
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + (t • X) i (f i))) =
      e0 n + t * e1 X + t ^ 2 * e2 X + t ^ 3 * e3 X + t ^ 4 * e4 X := by
  have hterm : ∀ f : Fin 4 ↪ Fin n,
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

lemma coeffs_zero_of_const (X : Mat n)
    (h : ∀ t : ℂ, (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + (t • X) i (f i))) = e0 n) :
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

def validTuple (t : Fin n × Fin n × Fin n × Fin n) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧
  t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2

instance : DecidablePred (validTuple (n:=n)) := fun t => by
  unfold validTuple; infer_instance

lemma sum_emb_eq_nested (g : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ f : Fin 4 ↪ Fin n, g (f 0) (f 1) (f 2) (f 3)) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
          ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, g j0 j1 j2 j3 := by
  have h1 : (∑ f : Fin 4 ↪ Fin n, g (f 0) (f 1) (f 2) (f 3)) =
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
  have hf1 : ∀ x : Fin n, (∑ j2 : Fin n, ∑ j3 : Fin n,
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
      trans ∑ j2 : Fin n, if j2 ∈ (Finset.univ.erase j0).erase j1 then
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

lemma sum_emb_01 (a b : Vec n) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1)) = -(mult2 n) * dot a b := by
  rw [sum_emb_eq_nested (fun j0 j1 _ _ => a j0 * b j1)]
  have hinner : ∀ (j0 : Fin n) (j1 : Fin n), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1) = (mult2 n) * (a j0 * b j1) := by
    intro j0 j1 hj1
    have hcard1 : ((Finset.univ : Finset (Fin n)).erase j0).card = n-1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hcard2 : (((Finset.univ : Finset (Fin n)).erase j0).erase j1).card = n-2 := by
      rw [Finset.card_erase_of_mem hj1, hcard1]
      omega
    have hstep : ∀ j2 ∈ ((Finset.univ : Finset (Fin n)).erase j0).erase j1,
        (∑ j3 ∈ (((Finset.univ : Finset (Fin n)).erase j0).erase j1).erase j2, a j0 * b j1) =
          (mult3 n) * (a j0 * b j1) := by
      intro j2 hj2
      rw [Finset.sum_const, Finset.card_erase_of_mem hj2, hcard2]
      simp [mult3, nsmul_eq_mul, Nat.sub_sub]
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, hcard2]
    simp [mult2,mult3,nsmul_eq_mul,mul_assoc]
  have h1 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0, (mult2 n) * (a j0 * b j1) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => hinner j0 j1 hj1
  rw [h1]
  have h2 : ∀ j0 : Fin n, (∑ j1 ∈ Finset.univ.erase j0, (mult2 n) * (a j0 * b j1)) = -(mult2 n) * (a j0 * b j0) := by
    intro j0
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb]
    ring
  simp_rw [h2, ← Finset.mul_sum]
  rfl

lemma sum_emb_pair_eq (i1 i2 : Fin 4) (hi : i1 ≠ i2) (a b : Vec n)
    (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2)) = -(mult2 n) * dot a b := by
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
  have hbij : (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2)) =
      ∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) := by
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

lemma e2_eq (X : Mat n) (hr : ∀ i, ∑ j, X i j = 0) (hc : ∀ j, ∑ i, X i j = 0) :
    e2 X = (mult2 n / 2) * (dot (X 0) (X 0) + dot (X 1) (X 1) + dot (X 2) (X 2) + dot (X 3) (X 3)) := by
  unfold e2
  simp_rw [Finset.sum_add_distrib]
  rw [sum_emb_pair_eq 0 1 (by decide) (X 0) (X 1) (hr 0) (hr 1),
      sum_emb_pair_eq 0 2 (by decide) (X 0) (X 2) (hr 0) (hr 2),
      sum_emb_pair_eq 0 3 (by decide) (X 0) (X 3) (hr 0) (hr 3),
      sum_emb_pair_eq 1 2 (by decide) (X 1) (X 2) (hr 1) (hr 2),
      sum_emb_pair_eq 1 3 (by decide) (X 1) (X 3) (hr 1) (hr 3),
      sum_emb_pair_eq 2 3 (by decide) (X 2) (X 3) (hr 2) (hr 3)]
  have hsq : ∑ j : Fin n, (X 0 j + X 1 j + X 2 j + X 3 j) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj := hc j
    rw [Fin.sum_univ_four] at hj
    rw [hj]; ring
  unfold dot
  have hcomb : ∑ j : Fin n,
      ((X 0 j + X 1 j + X 2 j + X 3 j) ^ 2 -
       (X 0 j * X 0 j + X 1 j * X 1 j + X 2 j * X 2 j + X 3 j * X 3 j) -
       2 * (X 0 j * X 1 j + X 0 j * X 2 j + X 0 j * X 3 j +
            X 1 j * X 2 j + X 1 j * X 3 j + X 2 j * X 3 j)) = 0 := by
    apply Finset.sum_eq_zero; intro j _; ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hcomb
  linear_combination (mult2 n / 2) * hcomb - (mult2 n / 2) * hsq

lemma sum_emb_012 (a b c : Vec n) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) * c (f 2)) = (2 * mult3 n) * ∑ j, a j * b j * c j := by
  rw [sum_emb_eq_nested (fun j0 j1 j2 _ => a j0 * b j1 * c j2)]
  have hstep3 : ∀ (j0 : Fin n) (j1 : Fin n) (j2 : Fin n),
      j1 ∈ Finset.univ.erase j0 → j2 ∈ (Finset.univ.erase j0).erase j1 →
      (∑ _j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2) =
        (mult3 n) * (a j0 * b j1 * c j2) := by
    intro j0 j1 j2 hj1 hj2
    have hcard1 : ((Finset.univ : Finset (Fin n)).erase j0).card = n-1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hcard2 : (((Finset.univ : Finset (Fin n)).erase j0).erase j1).card = n-2 := by
      rw [Finset.card_erase_of_mem hj1, hcard1]
      omega
    rw [Finset.sum_const, Finset.card_erase_of_mem hj2, hcard2]
    simp [mult3,nsmul_eq_mul,Nat.sub_sub]
  have h1 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ _j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1, (mult3 n) * (a j0 * b j1 * c j2) :=
    Finset.sum_congr rfl fun j0 _ =>
      Finset.sum_congr rfl fun j1 hj1 =>
        Finset.sum_congr rfl fun j2 hj2 => hstep3 j0 j1 j2 hj1 hj2
  rw [h1]
  have h2 : ∀ (j0 : Fin n) (j1 : Fin n), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1, (mult3 n) * (a j0 * b j1 * c j2)) =
        (mult3 n) * (a j0 * b j1 * (- c j0 - c j1)) := by
    intro j0 j1 hj1
    have : ∀ j2, (mult3 n) * (a j0 * b j1 * c j2) = ((mult3 n) * a j0 * b j1) * c j2 := fun _ => by ring
    simp_rw [this, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hc]
    ring
  have h3 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1, (mult3 n) * (a j0 * b j1 * c j2)) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0, (mult3 n) * (a j0 * b j1 * (- c j0 - c j1)) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => h2 j0 j1 hj1
  rw [h3]
  have h4 : ∀ j0 : Fin n,
      (∑ j1 ∈ Finset.univ.erase j0, (mult3 n) * (a j0 * b j1 * (- c j0 - c j1))) =
        (2 * mult3 n) * (a j0 * b j0 * c j0) - (mult3 n) * a j0 * (∑ j1, b j1 * c j1) := by
    intro j0
    have hsplit : ∀ j1, (mult3 n) * (a j0 * b j1 * (- c j0 - c j1)) =
        (-(mult3 n) * a j0 * c j0) * b j1 - ((mult3 n) * a j0) * (b j1 * c j1) := fun _ => by ring
    simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j0), Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb]
    ring
  simp_rw [h4, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [ha]; ring

lemma sum_emb_triple_eq (i1 i2 i3 : Fin 4) (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3)
    (a b c : Vec n) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2) * c (f i3)) = (2 * mult3 n) * ∑ j, a j * b j * c j := by
  have hperm : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 ∧ σ 1 = i2 ∧ σ 2 = i3 := by
    have hi4 : ∃ i4 : Fin 4, i4 ≠ i1 ∧ i4 ≠ i2 ∧ i4 ≠ i3 := by
      fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;> simp_all <;> decide
    rcases hi4 with ⟨i4, h41, h42, h43⟩
    have hinj : Function.Injective ![i1, i2, i3, i4] := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [Ne.symm]
    refine ⟨Equiv.ofBijective ![i1, i2, i3, i4] (Finite.injective_iff_bijective.mp hinj), rfl, rfl, rfl⟩
  rcases hperm with ⟨σ, hσ0, hσ1, hσ2⟩
  have hbij : (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2) * c (f i3)) =
      ∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) * c (f 2) := by
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

lemma e3_eq (X : Mat n) (hr : ∀ i, ∑ j, X i j = 0) :
    e3 X = (2 * mult3 n) * ∑ j, (X 0 j * X 1 j * X 2 j + X 0 j * X 1 j * X 3 j +
      X 0 j * X 2 j * X 3 j + X 1 j * X 2 j * X 3 j) := by
  unfold e3
  simp_rw [Finset.sum_add_distrib]
  rw [sum_emb_triple_eq 0 1 2 (by decide) (by decide) (by decide) (X 0) (X 1) (X 2) (hr 0) (hr 1) (hr 2),
      sum_emb_triple_eq 0 1 3 (by decide) (by decide) (by decide) (X 0) (X 1) (X 3) (hr 0) (hr 1) (hr 3),
      sum_emb_triple_eq 0 2 3 (by decide) (by decide) (by decide) (X 0) (X 2) (X 3) (hr 0) (hr 2) (hr 3),
      sum_emb_triple_eq 1 2 3 (by decide) (by decide) (by decide) (X 1) (X 2) (X 3) (hr 1) (hr 2) (hr 3)]
  ring

lemma e4_eq (a b c d : Vec n)
    (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) (hd : ∑ j, d j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) * c (f 2) * d (f 3)) =
      dot a b * dot c d + dot a c * dot b d + dot a d * dot b c -
        6 * ∑ j, a j * b j * c j * d j := by
  rw [sum_emb_eq_nested (fun j0 j1 j2 j3 => a j0 * b j1 * c j2 * d j3)]
  have h3 : ∀ (j0 j1 j2 : Fin n), j1 ∈ Finset.univ.erase j0 →
      j2 ∈ (Finset.univ.erase j0).erase j1 →
      (∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2 * d j3) =
        a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) := by
    intro j0 j1 j2 hj1 hj2
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hj2, Finset.sum_erase_eq_sub hj1,
        Finset.sum_erase_eq_sub (Finset.mem_univ j0), hd]
    ring
  have hs3 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2 * d j3) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) :=
    Finset.sum_congr rfl fun j0 _ =>
      Finset.sum_congr rfl fun j1 hj1 =>
        Finset.sum_congr rfl fun j2 hj2 => h3 j0 j1 j2 hj1 hj2
  rw [hs3]
  have h2 : ∀ (j0 j1 : Fin n), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2)) =
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) := by
    intro j0 j1 hj1
    have hsp : ∀ j2, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) =
        (a j0 * b j1 * (- d j0 - d j1)) * c j2 - (a j0 * b j1) * (c j2 * d j2) := fun _ => by ring
    simp_rw [hsp, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hc,
        Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0)]
    unfold dot; ring
  have hs2 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2)) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => h2 j0 j1 hj1
  rw [hs2]
  have h1 : ∀ j0 : Fin n,
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

end PEqualNP.Outside.L_gct_306_aux

namespace PEqualNP.Outside.L_gct_306_aux
open scoped BigOperators
variable {n : Nat}

def Level (L : Submodule ℂ (Mat n)) :=
  ∀ X ∈ L, (∀ i, (∑ j, X i j)=0) ∧ (∀ j, (∑ i, X i j)=0) ∧
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1+X i (f i))) = e0 n

def sqSum (X : Mat n) : ℂ := ∑ j, ((X 0 j)^2 + (X 1 j)^2 + (X 2 j)^2 + (X 3 j)^2)
def cubeSum (X : Mat n) : ℂ := ∑ j, ((X 0 j)^3 + (X 1 j)^3 + (X 2 j)^3 + (X 3 j)^3)
def ringProd (X : Mat n) : ℂ := ∑ j, X 0 j * X 1 j * X 2 j * X 3 j
def pairs (X : Mat n) : ℂ := dot (X 0) (X 1) * dot (X 2) (X 3) +
  dot (X 0) (X 2) * dot (X 1) (X 3) + dot (X 0) (X 3) * dot (X 1) (X 2)

theorem forms (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {X : Mat n} (mem : X∈L) :
    sqSum X=0 ∧ cubeSum X=0 ∧ pairs X=6*ringProd X := by
  obtain ⟨row,col,_⟩ := valid X mem
  obtain ⟨q,c,k⟩ := coeffs_zero_of_const X (fun t => (valid _ (L.smul_mem t mem)).2.2)
  have nz : mult3 n ≠ 0 := by unfold mult3; exact_mod_cast (show n-3≠0 by omega)
  have nz2 : mult2 n ≠ 0 := by unfold mult2; exact mul_ne_zero (by exact_mod_cast (show n-2≠0 by omega)) nz
  rw [e2_eq X row col] at q
  rw [e3_eq X row] at c
  have sqz := (mul_eq_zero.mp q).resolve_left (div_ne_zero nz2 (by norm_num))
  have cub := (mul_eq_zero.mp c).resolve_left (mul_ne_zero (by norm_num) nz)
  refine ⟨?_,?_,?_⟩
  · simpa [dot,sqSum,Finset.sum_add_distrib,pow_two] using sqz
  · have point (j : Fin n) :
        (X 0 j)^3+(X 1 j)^3+(X 2 j)^3+(X 3 j)^3 =
        3*(X 0 j*X 1 j*X 2 j+X 0 j*X 1 j*X 3 j+X 0 j*X 2 j*X 3 j+X 1 j*X 2 j*X 3 j) := by
      have h := col j
      rw [Fin.sum_univ_four] at h
      linear_combination ((X 0 j)^2+(X 1 j)^2+(X 2 j)^2+(X 3 j)^2 -
        (X 0 j * X 1 j + X 0 j * X 2 j + X 0 j * X 3 j + X 1 j * X 2 j + X 1 j * X 3 j + X 2 j * X 3 j)) * h
    simp only [cubeSum,point,← Finset.mul_sum,cub,mul_zero]
  · change (∑ f : Fin 4 ↪ Fin n, X 0 (f 0)*X 1 (f 1)*X 2 (f 2)*X 3 (f 3)) = 0 at k
    rw [e4_eq (X 0) (X 1) (X 2) (X 3) (row 0) (row 1) (row 2) (row 3)] at k
    exact sub_eq_zero.mp k

def pairing (X Y : Mat n) : ℂ := ∑ j, (X 0 j*Y 0 j + X 1 j*Y 1 j + X 2 j*Y 2 j + X 3 j*Y 3 j)

theorem isotropic (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {X Y : Mat n}
    (hx : X∈L) (hy : Y∈L) : pairing X Y = 0 := by
  have id : sqSum (X+Y) = sqSum X + sqSum Y + 2*pairing X Y := by
    simp only [sqSum,pairing,Pi.add_apply,←Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [(forms hn valid (L.add_mem hx hy)).1,(forms hn valid hx).1,(forms hn valid hy).1] at id
  linear_combination -id/2

theorem cubeSlope (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {X Y : Mat n}
    (hx : X∈L) (hy : Y∈L) :
    (∑ j, (X 0 j*(Y 0 j)^2+X 1 j*(Y 1 j)^2+X 2 j*(Y 2 j)^2+X 3 j*(Y 3 j)^2))=0 := by
  have id : cubeSum (X+Y)+cubeSum (X-Y)-2*cubeSum X =
      6*(∑ j, (X 0 j*(Y 0 j)^2+X 1 j*(Y 1 j)^2+X 2 j*(Y 2 j)^2+X 3 j*(Y 3 j)^2)) := by
    simp only [cubeSum,Pi.add_apply,Pi.sub_apply,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [(forms hn valid (L.add_mem hx hy)).2.1,(forms hn valid (L.sub_mem hx hy)).2.1,(forms hn valid hx).2.1] at id
  linear_combination -id/6

def rowScale (w : Fin 4 → ℂ) (v : Vec n) : Mat n := fun i j => w i*v j

theorem dotShift (X : Mat n) (w : Fin 4 → ℂ) (v : Vec n) (null : dot v v=0) (a : ℂ) (i j : Fin 4) :
    dot ((X+a • rowScale w v) i) ((X+a • rowScale w v) j) =
    dot (X i) (X j) + a*(w i*dot v (X j)+w j*dot (X i) v) := by
  have id : dot ((X+a • rowScale w v) i) ((X+a • rowScale w v) j) =
      dot (X i) (X j)+a*(w i*dot v (X j)+w j*dot (X i) v)+a^2*w i*w j*dot v v := by
    simp only [dot,Pi.add_apply,Pi.smul_apply,smul_eq_mul,rowScale,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  simpa [null] using id

theorem quarticSlope (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {X : Mat n} (hx : X∈L)
    (w : Fin 4 → ℂ) (v : Vec n) (null : dot v v=0) (hy : rowScale w v ∈ L) :
    (∑ j, (X 0 j*w 1*w 2*w 3+w 0*X 1 j*w 2*w 3+w 0*w 1*X 2 j*w 3+w 0*w 1*w 2*X 3 j)*(v j)^3)=0 := by
  let B (s : ℂ) := X + s • rowScale w v
  let F := ∑ j, (X 0 j*w 1*w 2*w 3+w 0*X 1 j*w 2*w 3+w 0*w 1*X 2 j*w 3+w 0*w 1*w 2*X 3 j)*(v j)^3
  have eq (s : ℂ) : pairs (B s)=6*ringProd (B s) := (forms hn valid (L.add_mem hx (L.smul_mem s hy))).2.2
  have lhs : pairs (B 2)-pairs (B (-2))-2*pairs (B 1)+2*pairs (B (-1))=0 := by
    simp only [B,pairs,dotShift X w v null]
    ring
  have rhs : ringProd (B 2)-ringProd (B (-2))-2*ringProd (B 1)+2*ringProd (B (-1))=12*F := by
    simp only [F,B,ringProd,rowScale,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,
      ←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  change F=0
  linear_combination (lhs - eq 2 + eq (-2) + 2*eq 1 - 2*eq (-1) - 6*rhs)/72

end PEqualNP.Outside.L_gct_306_aux

namespace PEqualNP.Outside.L_gct_306_aux
open scoped BigOperators
variable {n : Nat}
abbrev Space (n : Nat) := Fin 3 × Fin n → ℂ

def channel (X : Mat n) (k : Fin 3) (j : Fin n) : ℂ :=
  ![X 0 j-X 1 j+X 2 j-X 3 j, X 0 j-X 1 j-X 2 j+X 3 j, X 0 j+X 1 j-X 2 j-X 3 j] k

def encode (n : Nat) : Mat n →ₗ[ℂ] Space n where
  toFun X := fun w => channel X w.1 w.2
  map_add' X Y := by ext ⟨k,j⟩; fin_cases k <;> simp [channel] <;> ring
  map_smul' a X := by ext ⟨k,j⟩; fin_cases k <;> simp [channel] <;> ring

def coords (L : Submodule ℂ (Mat n)) : L →ₗ[ℂ] Space n := (encode n).comp L.subtype

theorem encodeIdent {X Y : Mat n} (cx : ∀ j, (∑ i, X i j)=0) (cy : ∀ j, (∑ i, Y i j)=0)
    (eq : encode n X = encode n Y) : X=Y := by
  funext i j
  have e (k : Fin 3) : channel X k j=channel Y k j := congrFun eq (k,j)
  have ea := e 0; have eb := e 1; have ec := e 2
  have ax := cx j; have ay := cy j
  simp [channel,Fin.sum_univ_four] at ea eb ec ax ay
  fin_cases i
  · change X 0 j=Y 0 j
    linear_combination (ea+eb+ec+ax-ay)/4
  · change X 1 j=Y 1 j
    linear_combination (-ea-eb+ec+ax-ay)/4
  · change X 2 j=Y 2 j
    linear_combination (ea-eb-ec+ax-ay)/4
  · change X 3 j=Y 3 j
    linear_combination (-ea+eb-ec+ax-ay)/4

theorem coordsInj {L : Submodule ℂ (Mat n)} (valid : Level L) : Function.Injective (coords L) := by
  intro x y eq
  exact Subtype.ext (encodeIdent (valid _ x.property).2.1 (valid _ y.property).2.1 eq)

def B (n : Nat) : LinearMap.BilinForm ℂ (Space n) := dotProductBilin ℂ ℂ

theorem proj (a b : Space n) : (B n) a b =
    ∑ j, (a (0,j)*b (0,j)+a (1,j)*b (1,j)+a (2,j)*b (2,j)) := by
  change (∑ w : Fin 3 × Fin n, a w * b w) = _
  simp [Fintype.sum_prod_type,Fin.sum_univ_three,Finset.sum_add_distrib]

theorem bNondeg : (B n).Nondegenerate := by
  constructor
  · intro x hx; funext i
    have h := hx (Pi.single i 1)
    change dotProduct x (Pi.single i 1) = 0 at h
    simpa using h
  · intro y hy; funext i
    have h := hy (Pi.single i 1)
    change dotProduct (Pi.single i 1) y = 0 at h
    simpa using h

theorem gram (X Y : Mat n) (cx : ∀ j, (∑ i, X i j)=0) (cy : ∀ j, (∑ i, Y i j)=0) :
    (B n) (encode n X) (encode n Y) = 4*pairing X Y := by
  rw [proj]
  simp only [pairing,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have ax := cx j; have ay := cy j
  rw [Fin.sum_univ_four] at ax ay
  change channel X 0 j*channel Y 0 j+channel X 1 j*channel Y 1 j+channel X 2 j*channel Y 2 j = _
  simp [channel]
  linear_combination -(X 0 j + X 1 j + X 2 j + X 3 j)*ay

theorem rankCriterion (S T : Submodule ℂ (Space n)) (dimT : Module.finrank ℂ T=5)
    (dis : Disjoint S T) (orth : S ≤ (B n).orthogonal (S ⊔ T)) :
    2*Module.finrank ℂ S+5≤3*n ∧
    (2*Module.finrank ℂ S+5=3*n → S=(B n).orthogonal (S⊔T)) := by
  have ambient : Module.finrank ℂ (Space n) = 3*n := by simp [Space]
  have sup := S.finrank_sup_add_finrank_inf_eq T
  rw [dis.eq_bot,finrank_bot,add_zero,dimT] at sup
  have perp := LinearMap.BilinForm.finrank_orthogonal (B:=B n) bNondeg (S⊔T)
  rw [ambient,sup] at perp
  have le := Submodule.finrank_mono orth
  have cap := (S⊔T : Submodule ℂ (Space n)).finrank_le
  rw [sup,ambient] at cap
  exact ⟨by omega,fun eq => Submodule.eq_of_le_of_finrank_eq orth (by omega)⟩

end PEqualNP.Outside.L_gct_306_aux

namespace PEqualNP.Outside.L_gct_306_aux
open scoped BigOperators
variable {n : Nat}
def mom (u : Vec n) (k : Nat) : ℂ := ∑ j, (u j)^k
def mass (v : Space n) (i : Fin 3) := ∑ j, v (i,j)
def weighted (v : Space n) (i : Fin 3) (u : Vec n) (k : Nat) := ∑ j, v (i,j) * (u j)^k

def cleanSpace (u : Vec n) (v : Space n) := (∀ i, mass v i=0) ∧ weighted v 0 u 3=0 ∧ weighted v 1 u 3=0
def plane (L : Submodule ℂ (Mat n)) (u : Vec n) := ∀ s t : ℂ, rowScale ![s,-s,t,-t] u ∈ L

theorem directions (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {u : Vec n}
    (planeMem : plane L u) (p2 : mom u 2=0) {X : Mat n} (hx : X∈L) :
    cleanSpace u (encode n X) ∧ weighted (encode n X) 2 u 2=0 := by
  have row := (valid X hx).1
  have null : dot u u=0 := by simpa [dot,mom,pow_two] using p2
  have h0 := quarticSlope hn valid hx _ u null (planeMem 1 1)
  have h1 := quarticSlope hn valid hx _ u null (planeMem 1 (-1))
  have a := cubeSlope hn valid hx (planeMem 1 0)
  have b := cubeSlope hn valid hx (planeMem 0 1)
  have eq (i : Fin 3) : mass (encode n X) i=0 := by
    fin_cases i <;> simp [mass,encode,channel,Finset.sum_add_distrib,Finset.sum_sub_distrib,row]
  refine ⟨⟨eq,?_,?_⟩,?_⟩
  · change (∑ j, channel X 0 j*(u j)^3)=0
    convert h0 using 1
    apply Finset.sum_congr rfl; intro j _; simp [channel] <;> first | exact Or.inl trivial | ring_nf <;> simp
  · change (∑ j, channel X 1 j*(u j)^3)=0
    convert h1 using 1
    apply Finset.sum_congr rfl; intro j _; simp [channel] <;> first | exact Or.inl trivial | ring_nf <;> simp
  · have eq : weighted (encode n X) 2 u 2 =
        (∑ j, (X 0 j*(u j)^2 + X 1 j*(u j)^2)) - (∑ j, (X 2 j*(u j)^2 + X 3 j*(u j)^2)) := by
      rw [←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; simp [encode,channel]; ring
    simp [rowScale] at a b
    rw [eq,a,b,sub_self]

def noiseAt (u : Vec n) (c : Fin 5 → ℂ) (i : Fin 3) (j : Fin n) :=
  ![c 0+c 3*(u j)^3,c 1+c 4*(u j)^3,c 2] i

def noise (u : Vec n) : (Fin 5 → ℂ) →ₗ[ℂ] Space n where
  toFun c := fun w => noiseAt u c w.1 w.2
  map_add' a b := by ext ⟨i,j⟩; fin_cases i <;> simp [noiseAt] <;> ring
  map_smul' a b := by ext ⟨i,j⟩; fin_cases i <;> simp [noiseAt] <;> ring

theorem noiseEval (u : Vec n) (c : Fin 5 → ℂ) (v : Space n) :
    (B n) (noise u c) v = c 0*mass v 0+c 1*mass v 1+c 2*mass v 2+
      c 3*weighted v 0 u 3+c 4*weighted v 1 u 3 := by
  rw [proj]
  simp only [mass,weighted,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _; simp [noise,noiseAt]; ring

theorem noNoise (hn : 4≤n) (u : Vec n) (det : (n:ℂ)*mom u 6 ≠ (mom u 3)^2)
    (c : Fin 5 → ℂ) (hc : cleanSpace u (noise u c)) : c=0 := by
  obtain ⟨mean,a,b⟩ := hc
  have m0 := mean 0; have m1 := mean 1; have m2 := mean 2
  have npos : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by omega)
  simp [mass,noise,noiseAt,Finset.sum_add_distrib,←Finset.mul_sum] at m0 m1 m2
  have weight (i l : Fin 5) : (∑ j, (c i + c l * (u j)^3) * (u j)^3)=c i*mom u 3+c l*mom u 6 := by
    simp only [mom,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  change (∑ j, (c 0+c 3*(u j)^3)*(u j)^3)=0 at a
  change (∑ j, (c 1+c 4*(u j)^3)*(u j)^3)=0 at b
  rw [weight] at a b
  have elim (x y : ℂ) (h : (n:ℂ)*x + y*mom u 3=0) (h' : x*mom u 3+y*mom u 6=0) : x=0 ∧ y=0 := by
    have z : ((n:ℂ)*mom u 6-(mom u 3)^2)*y=0 := by linear_combination (n:ℂ)*h' - mom u 3*h
    have yz := (mul_eq_zero.mp z).resolve_left (sub_ne_zero.mpr det)
    rw [yz,zero_mul,add_zero] at h
    exact ⟨(mul_eq_zero.mp h).resolve_left npos,yz⟩
  obtain ⟨c0,c3⟩ := elim (c 0) (c 3) m0 a
  obtain ⟨c1,c4⟩ := elim (c 1) (c 4) m1 b
  have c2 := m2.resolve_left (show n≠0 by omega)
  funext i; fin_cases i <;> assumption

theorem zeroClean (u : Vec n) : cleanSpace u (0 : Space n) := by simp [cleanSpace,mass,weighted]
theorem injNoise (hn : 4≤n) (u : Vec n) (det : (n:ℂ)*mom u 6 ≠ (mom u 3)^2) : Function.Injective (noise u) := by
  intro a b eq; apply sub_eq_zero.mp; apply noNoise hn u det
  rw [map_sub,eq,sub_self]; exact zeroClean u

end PEqualNP.Outside.L_gct_306_aux

namespace PEqualNP.Outside.L_gct_306_aux
open scoped BigOperators
variable {n : Nat}
def Z (v : Vec n) : Mat n := rowScale ![1,1,-1,-1] v

theorem zcols (v : Vec n) (j : Fin n) : (∑ i, Z v i j)=0 := by simp [Z,rowScale,Fin.sum_univ_four]

theorem zChannel (v : Vec n) (k : Fin 3) (j : Fin n) :
    encode n (Z v) (k,j) = if k=2 then 4*v j else 0 := by
  fin_cases k <;> simp [encode,channel,Z,rowScale] <;> ring

theorem zClean (v u : Vec n) (hv : (∑ j, v j)=0) : cleanSpace u (encode n (Z v)) := by
  have mean (i : Fin 3) : mass (encode n (Z v)) i=0 := by
    fin_cases i <;> simp [mass,zChannel,←Finset.mul_sum,hv]
  exact ⟨mean,by simp [weighted,zChannel],by simp [weighted,zChannel]⟩

theorem zGram (v : Vec n) (a : Space n) : (B n) a (encode n (Z v)) = 4*∑ j, a (2,j)*v j := by
  rw [proj,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _; simp [zChannel]; ring

theorem rankAndRadical (hn : 4≤n) {u : Vec n} {L : Submodule ℂ (Mat n)} (valid : Level L)
    (hplane : plane L u) (p2 : mom u 2=0) (det : (n:ℂ)*mom u 6 ≠ (mom u 3)^2) :
    2*Module.finrank ℂ L + 5 ≤ 3*n ∧
    (2*Module.finrank ℂ L+5=3*n → ∀ v : Vec n, (∑ j, v j)=0 →
      (∀ X∈L, (∑ j, (encode n X) (2,j)*v j)=0) → Z v∈L) := by
  let S := LinearMap.range (coords L)
  let T := LinearMap.range (noise u)
  have s : Module.finrank ℂ S=Module.finrank ℂ L := LinearMap.finrank_range_of_inj (coordsInj valid)
  have t : Module.finrank ℂ T=5 := by
    change Module.finrank ℂ (LinearMap.range _)=_
    rw [LinearMap.finrank_range_of_inj (injNoise hn u det)]
    simp
  have allClean (v : Space n) (h : v∈S) : cleanSpace u v := by
    obtain ⟨X,rfl⟩ := h
    exact (directions hn valid hplane p2 X.property).1
  have dis : Disjoint S T := by
    apply Submodule.disjoint_def.mpr
    intro v hs ht
    obtain ⟨c,rfl⟩ := ht
    have zero := noNoise hn u det c (allClean _ hs)
    simp [zero]
  have ortho : S ≤ (B n).orthogonal (S⊔T) := by
    intro v hv
    obtain ⟨Y,rfl⟩ := hv
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro w hw
    obtain ⟨a,⟨X,rfl⟩,b,⟨c,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add,LinearMap.add_apply,noiseEval]
    have eq := gram (X : Mat n) Y (valid _ X.property).2.1 (valid _ Y.property).2.1
    rw [isotropic hn valid X.property Y.property,mul_zero] at eq
    obtain ⟨m,d0,d1⟩ := (directions hn valid hplane p2 Y.property).1
    change (B n) (encode n X) (encode n Y) + _ = 0
    simp only [coords,LinearMap.comp_apply,Submodule.subtype_apply,eq,m,d0,d1,mul_zero,add_zero]
  obtain ⟨upper,full⟩ := rankCriterion S T t dis ortho
  refine ⟨by simpa [s] using upper,?_⟩
  intro equality v mean orthv
  have present : encode n (Z v) ∈ S := by
    rw [full (by rwa [s])]
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro w hw
    obtain ⟨a,⟨X,rfl⟩,b,⟨c,rfl⟩,rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add,LinearMap.add_apply,zGram,noiseEval]
    obtain ⟨m,d0,d1⟩ := zClean v u mean
    have h := orthv X X.property
    simpa only [coords,LinearMap.comp_apply,Submodule.subtype_apply,h,m,d0,d1,mul_zero,add_zero]
  obtain ⟨X,hX⟩ := present
  have eq := encodeIdent (valid _ X.property).2.1 (zcols v) hX
  exact eq ▸ X.property

theorem finish (hn : 4≤n) {u : Vec n} {L : Submodule ℂ (Mat n)} (valid : Level L)
    (hplane : plane L u) (p2 : mom u 2=0) (p4 : mom u 4=0) (det : (n:ℂ)*mom u 6 ≠ (mom u 3)^2) :
    2*Module.finrank ℂ L + 5 ≤ 3*n ∧
    (2*Module.finrank ℂ L+5=3*n → mom u 8=0 ∧ (n:ℂ)*mom u 12=(mom u 6)^2) := by
  obtain ⟨upper,atEq⟩ := rankAndRadical hn valid hplane p2 det
  refine ⟨upper,?_⟩
  intro equality
  have zMem := atEq equality
  let v : Vec n := fun j => (u j)^2
  have zv : Z v ∈ L := zMem v p2 (fun X hx => (directions hn valid hplane p2 hx).2)
  have null : dot v v=0 := by simpa [v,dot,mom,←pow_add] using p4
  have sixth (X : Mat n) (hX : X∈L) : weighted (encode n X) 2 u 6=0 := by
    have h := quarticSlope hn valid hX ![1,1,-1,-1] v null zv
    convert h using 1
    apply Finset.sum_congr rfl; intro j _
    change channel X 2 j * (u j)^6 = _
    simp [channel,v]; ring
  have p8 := sixth _ zv
  have z8 : weighted (encode n (Z v)) 2 u 6=4*mom u 8 := by
    simp only [weighted,zChannel,if_true,mom,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; dsimp [v]; ring
  rw [z8] at p8
  refine ⟨(mul_eq_zero.mp p8).resolve_left (by norm_num),?_⟩
  let avg := mom u 6 / (n:ℂ)
  let w : Vec n := fun j => (u j)^6 - avg
  have nz : (n:ℂ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have center : (∑ j, w j)=0 := by
    simp only [w,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change mom u 6-(n:ℂ)*avg=0
    dsimp [avg]; field_simp <;> ring
  have ort (X : Mat n) (hX : X∈L) : (∑ j, encode n X (2,j)*w j)=0 := by
    have clean := (directions hn valid hplane p2 hX).1.1 2
    have sixthX := sixth X hX
    change (∑ j, (encode n X) (2,j))=0 at clean
    change (∑ j, (encode n X) (2,j)*(u j)^6)=0 at sixthX
    simp only [w,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,sixthX,clean,zero_mul,sub_zero]
  have h := sixth _ (zMem w center ort)
  have id : weighted (encode n (Z w)) 2 u 6 = 4*(mom u 12 - avg*mom u 6) := by
    simp only [weighted,zChannel,if_true,mom,Finset.mul_sum,←Finset.sum_sub_distrib,mul_sub]
    apply Finset.sum_congr rfl; intro j _; dsimp [w]; ring
  rw [id] at h
  have z := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num))
  rw [z]; dsimp [avg]; field_simp

end PEqualNP.Outside.L_gct_306_aux

theorem PEqualNP.Outside.L_gct_306 : (∀ (n : ℕ), 4 ≤ n →
  ∀ (u : Fin n → ℂ) (L : Submodule ℂ (Fin 4 → Fin n → ℂ)),
  let p := fun k : ℕ => ∑ j, (u j)^k
  p 1 = 0 → p 2 = 0 → p 4 = 0 → (n : ℂ) * p 6 ≠ (p 3)^2 →
  (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + X i (f i))) =
      (∑ _f : Fin 4 ↪ Fin n, (1 : ℂ))) →
  (∀ s t : ℂ, (fun i j => (![s,-s,t,-t] : Fin 4 → ℂ) i * u j) ∈ L) →
  2 * Module.finrank ℂ L + 5 ≤ 3 * n ∧
    (2 * Module.finrank ℂ L + 5 = 3 * n →
      p 8 = 0 ∧ (n : ℂ) * p 12 = (p 6)^2)) := by
  intro n hn u L
  dsimp only
  intro _ p2 p4 determinant valid shared
  exact PEqualNP.Outside.L_gct_306_aux.finish hn valid shared p2 p4 determinant
