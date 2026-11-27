import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_638_aux

open scoped BigOperators

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

def vdot {d : ℕ} (a x : Fin d → ZMod 2) : ZMod 2 :=
  ∑ i : Fin d, a i * x i

def vspin {d : ℕ} (a x : Fin d → ZMod 2) : ℤ :=
  if vdot a x = 0 then 1 else -1

lemma vdot_add_left {d : ℕ} (a b x : Fin d → ZMod 2) :
    vdot (a + b) x = vdot a x + vdot b x := by
  simp only [vdot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma vdot_add_right {d : ℕ} (a x y : Fin d → ZMod 2) :
    vdot a (x + y) = vdot a x + vdot a y := by
  simp only [vdot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma vdot_smul_left {d : ℕ} (c : ZMod 2) (a x : Fin d → ZMod 2) :
    vdot (c • a) x = c * vdot a x := by
  simp only [vdot, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]

lemma vspin_add_left {d : ℕ} (a b x : Fin d → ZMod 2) :
    vspin (a + b) x = vspin a x * vspin b x := by
  simp only [vspin, vdot_add_left]
  generalize vdot a x = u
  generalize vdot b x = v
  fin_cases u <;> fin_cases v <;> decide

lemma vspin_add_right {d : ℕ} (a x y : Fin d → ZMod 2) :
    vspin a (x + y) = vspin a x * vspin a y := by
  simp only [vspin, vdot_add_right]
  generalize vdot a x = u
  generalize vdot a y = v
  fin_cases u <;> fin_cases v <;> decide

lemma vspin_eq_iff {d : ℕ} (a x y : Fin d → ZMod 2) :
    vspin a x = vspin a y ↔ vdot a x = vdot a y := by
  simp only [vspin]
  have h : ∀ u v : ZMod 2, ((if u = 0 then (1 : ℤ) else -1) = (if v = 0 then (1 : ℤ) else -1)) ↔ u = v := by
    decide
  exact h (vdot a x) (vdot a y)

lemma sum_vspin_submodule {d : ℕ} (S : Submodule (ZMod 2) (Fin d → ZMod 2))
    [Fintype S] (x : Fin d → ZMod 2) :
    (∑ a : S, vspin a.1 x) =
      @ite ℤ (∀ a ∈ S, vdot a x = 0) (Classical.propDecidable _) (Fintype.card S : ℤ) 0 := by
  classical
  split_ifs with h0
  · have hall : ∀ a : S, vspin a.1 x = 1 := fun a => by simp [vspin, h0 a.1 a.2]
    simp [hall]
  · push Not at h0
    rcases h0 with ⟨a0, ha0S, ha0⟩
    have hneg : vspin a0 x = -1 := by simp [vspin, ha0]
    let a0' : S := ⟨a0, ha0S⟩
    have hbij : Function.Bijective (fun a : S => a + a0') := by
      refine Function.bijective_iff_has_inverse.mpr ⟨fun a => a + a0', ?_, ?_⟩
      · intro a; apply Subtype.ext; ext i
        change a.1 i + a0 i + a0 i = a.1 i
        rw [add_assoc, zmod2_add_self, add_zero]
      · intro a; apply Subtype.ext; ext i
        change a.1 i + a0 i + a0 i = a.1 i
        rw [add_assoc, zmod2_add_self, add_zero]
    have hshift : (∑ a : S, vspin a.1 x) = ∑ a : S, vspin (a + a0').1 x :=
      (Fintype.sum_bijective (fun a : S => a + a0') hbij _ _ fun _ => rfl).symm
    have hmul : (∑ a : S, vspin (a + a0').1 x) = -(∑ a : S, vspin a.1 x) := by
      have hterm : ∀ a : S, vspin (a + a0').1 x = -(vspin a.1 x) := fun a => by
        change vspin (a.1 + a0) x = -vspin a.1 x
        rw [vspin_add_left, hneg, mul_neg_one]
      simp_rw [hterm, Finset.sum_neg_distrib]
    linarith

lemma sum_vspin_univ {d : ℕ} (x : Fin d → ZMod 2) :
    (∑ a : Fin d → ZMod 2, vspin a x) = if x = 0 then (2 : ℤ) ^ d else 0 := by
  classical
  by_cases hx : x = 0
  · subst hx
    simp only [↓reduceIte, vspin, vdot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    norm_cast
  · simp only [hx, ↓reduceIte]
    have hex : ∃ i : Fin d, x i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx (funext hall)
    rcases hex with ⟨i0, hi0⟩
    let e0 : Fin d → ZMod 2 := Pi.single i0 1
    have he0 : vdot e0 x = 1 := by
      dsimp only [vdot, e0]
      rw [Finset.sum_eq_single i0]
      · simp [zmod2_eq_one_of_ne_zero hi0]
      · intro j _ hji; simp [Pi.single_eq_of_ne hji]
      · intro h; exact absurd (Finset.mem_univ i0) h
    have hneg : vspin e0 x = -1 := by simp [vspin, he0]
    have hbij : Function.Bijective (fun a : Fin d → ZMod 2 => a + e0) := by
      refine Function.bijective_iff_has_inverse.mpr ⟨fun a => a + e0, ?_, ?_⟩
      · intro a; ext i; simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero]
      · intro a; ext i; simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero]
    have hshift : (∑ a : Fin d → ZMod 2, vspin a x) =
        ∑ a : Fin d → ZMod 2, vspin (a + e0) x :=
      (Fintype.sum_bijective (fun a => a + e0) hbij _ _ fun _ => rfl).symm
    have hmul : (∑ a : Fin d → ZMod 2, vspin (a + e0) x) =
        -(∑ a : Fin d → ZMod 2, vspin a x) := by
      have hterm : ∀ a : Fin d → ZMod 2, vspin (a + e0) x = -vspin a x := fun a => by
        rw [vspin_add_left, hneg, mul_neg_one]
      simp_rw [hterm, Finset.sum_neg_distrib]
    linarith

lemma card_submodule_zmod2 {d : ℕ} (S : Submodule (ZMod 2) (Fin d → ZMod 2)) [Fintype S] :
    Fintype.card S = 2 ^ (Module.finrank (ZMod 2) S) := by
  let b := Module.finBasis (ZMod 2) S
  have hcard := Fintype.card_congr b.equivFun.toEquiv
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
  exact hcard

end PEqualNP.Outside.L_lib_638_aux

open PEqualNP.Outside.L_lib_638_aux

theorem PEqualNP.Outside.L_lib_638 :
    ∀ d : ℕ,
      let V := Fin d → ZMod 2
      let dot := fun (a x : V) => ∑ i, a i * x i
      let spin := fun (a x : V) => if dot a x = 0 then (1 : ℤ) else -1
      ∀ F : V → ℕ, (∑ x, F x) = 2^d →
        ((∀ a : V, (2^d : ℤ) ∣ ∑ x : V, (F x : ℤ) * spin a x) ↔
          ∃ (U : Submodule (ZMod 2) V) (z : V),
            ∀ x : V, F x = @ite ℕ (∀ a ∈ U, dot a x = dot a z)
              (Classical.propDecidable _) (2^(Module.finrank (ZMod 2) U)) 0) := by
  intro d V dot spin F hsumF
  classical
  have hvadd_self : ∀ v : V, v + v = 0 := fun v => funext fun i => zmod2_add_self (v i)
  have hsumF_int : (∑ x : V, (F x : ℤ)) = (2 : ℤ) ^ d := by exact_mod_cast hsumF
  have h2d_pos : (0 : ℤ) < (2 : ℤ) ^ d := by positivity
  constructor
  · intro hdvd
    have hex_z : ∃ z : V, F z ≠ 0 := by
      by_contra hall
      push Not at hall
      have h0 : (∑ x : V, F x) = 0 := Finset.sum_eq_zero fun x _ => hall x
      have : (2 : ℕ) ^ d = 0 := hsumF.symm.trans h0
      exact (Nat.ne_of_gt (by positivity : 0 < 2 ^ d)) this
    rcases hex_z with ⟨z, hz⟩
    let U : Submodule (ZMod 2) V :=
      { carrier := {a : V | ∀ x : V, F x ≠ 0 → vdot a x = vdot a z}
        zero_mem' := fun x _ => by
          change (∑ i : Fin d, (0 : ZMod 2) * x i) = ∑ i : Fin d, (0 : ZMod 2) * z i
          simp, add_mem' := fun {a b} ha hb x hx => by
          rw [vdot_add_left, vdot_add_left, ha x hx, hb x hx]
        smul_mem' := fun c {a} ha x hx => by
          rw [vdot_smul_left, vdot_smul_left, ha x hx] }
    have hhat : ∀ a : V, (∑ x : V, (F x : ℤ) * vspin a x) =
        if a ∈ U then (2 : ℤ) ^ d * vspin a z else 0 := by
      intro a
      by_cases ha : a ∈ U
      · simp only [ha, ↓reduceIte]
        have hterm : ∀ x : V, (F x : ℤ) * vspin a x = (F x : ℤ) * vspin a z := by
          intro x
          by_cases hx : F x = 0
          · simp [hx]
          · rw [(vspin_eq_iff a x z).mpr (ha x hx)]
        rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_mul, hsumF_int]
      · simp only [ha, ↓reduceIte]
        rcases hdvd a with ⟨q, hq⟩
        change (∑ x : V, (F x : ℤ) * vspin a x) = (2 : ℤ) ^ d * q at hq
        have hub : (∑ x : V, (F x : ℤ) * vspin a x) ≤ (2 : ℤ) ^ d := by
          calc
            (∑ x : V, (F x : ℤ) * vspin a x) ≤ ∑ x : V, (F x : ℤ) := by
              refine Finset.sum_le_sum fun x _ => ?_
              have hle : vspin a x ≤ 1 := by dsimp only [vspin]; split_ifs <;> omega
              have hnn : (0 : ℤ) ≤ (F x : ℤ) := Int.natCast_nonneg _
              nlinarith
            _ = (2 : ℤ) ^ d := hsumF_int
        have hlb : -((2 : ℤ) ^ d) ≤ ∑ x : V, (F x : ℤ) * vspin a x := by
          calc
            -((2 : ℤ) ^ d) = ∑ x : V, -((F x : ℤ)) := by rw [Finset.sum_neg_distrib, hsumF_int]
            _ ≤ ∑ x : V, (F x : ℤ) * vspin a x := by
              refine Finset.sum_le_sum fun x _ => ?_
              have hge : (-1 : ℤ) ≤ vspin a x := by dsimp only [vspin]; split_ifs <;> omega
              have hnn : (0 : ℤ) ≤ (F x : ℤ) := Int.natCast_nonneg _
              nlinarith
        have hq_range : -1 ≤ q ∧ q ≤ 1 := by
          constructor <;> nlinarith
        have hq_cases : q = -1 ∨ q = 0 ∨ q = 1 := by omega
        rcases hq_cases with rfl | rfl | rfl
        · exfalso
          apply ha
          have hsum_zero : (∑ x : V, (F x : ℤ) * (vspin a x + 1)) = 0 := by
            have h1 : ∀ x : V, (F x : ℤ) * (vspin a x + 1) = (F x : ℤ) * vspin a x + (F x : ℤ) :=
              fun x => by ring
            rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_add_distrib, hq, hsumF_int]
            ring
          have hnn : ∀ x ∈ (Finset.univ : Finset V), (0 : ℤ) ≤ (F x : ℤ) * (vspin a x + 1) := by
            intro x _
            have : (0 : ℤ) ≤ vspin a x + 1 := by dsimp only [vspin]; split_ifs <;> omega
            exact mul_nonneg (Int.natCast_nonneg _) this
          have hall0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_zero
          have hval : ∀ x : V, F x ≠ 0 → vspin a x = -1 := by
            intro x hx
            have h1 := hall0 x (Finset.mem_univ x)
            rcases mul_eq_zero.mp h1 with hFx | hsp
            · exact absurd (Int.ofNat_eq_zero.mp hFx) hx
            · linarith
          intro x hx
          exact (vspin_eq_iff a x z).mp ((hval x hx).trans (hval z hz).symm)
        · rw [hq, mul_zero]
        · exfalso
          apply ha
          have hsum_zero : (∑ x : V, (F x : ℤ) * (1 - vspin a x)) = 0 := by
            have h1 : ∀ x : V, (F x : ℤ) * (1 - vspin a x) = (F x : ℤ) - (F x : ℤ) * vspin a x :=
              fun x => by ring
            rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_sub_distrib, hq, hsumF_int]
            ring
          have hnn : ∀ x ∈ (Finset.univ : Finset V), (0 : ℤ) ≤ (F x : ℤ) * (1 - vspin a x) := by
            intro x _
            have : (0 : ℤ) ≤ 1 - vspin a x := by dsimp only [vspin]; split_ifs <;> omega
            exact mul_nonneg (Int.natCast_nonneg _) this
          have hall0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum_zero
          have hval : ∀ x : V, F x ≠ 0 → vspin a x = 1 := by
            intro x hx
            have h1 := hall0 x (Finset.mem_univ x)
            rcases mul_eq_zero.mp h1 with hFx | hsp
            · exact absurd (Int.ofNat_eq_zero.mp hFx) hx
            · linarith
          intro x hx
          exact (vspin_eq_iff a x z).mp ((hval x hx).trans (hval z hz).symm)
    refine ⟨U, z, fun x => ?_⟩
    have hinv : (2 : ℤ) ^ d * (F x : ℤ) =
        ∑ a : V, (∑ y : V, (F y : ℤ) * vspin a y) * vspin a x := by
      have h1 : (∑ a : V, (∑ y : V, (F y : ℤ) * vspin a y) * vspin a x) =
          ∑ y : V, (F y : ℤ) * ∑ a : V, vspin a (y + x) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by rw [vspin_add_right]; ring
      rw [h1]
      have hsum_v : ∀ y : V, (∑ a : V, vspin a (y + x)) = if y + x = 0 then (2 : ℤ) ^ d else 0 :=
        fun y => sum_vspin_univ (y + x)
      simp_rw [hsum_v]
      rw [Finset.sum_eq_single x]
      · have hxx : x + x = 0 := hvadd_self x
        rw [hxx]
        simp [mul_comm]
      · intro y _ hyx
        have hne : y + x ≠ 0 := by
          intro h0
          apply hyx
          ext i
          have hi : y i + x i = 0 := congrFun h0 i
          have h2 := congrArg (fun t : ZMod 2 => t + x i) hi
          simp only [add_assoc, zmod2_add_self, add_zero, zero_add] at h2
          exact h2
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ x) h
    simp_rw [hhat] at hinv
    have hUsum : (∑ a : V, (if a ∈ U then (2 : ℤ) ^ d * vspin a z else 0) * vspin a x) =
        (2 : ℤ) ^ d * ∑ a : U, vspin a.1 (x + z) := by
      have h1 : ∀ a : V, (if a ∈ U then (2 : ℤ) ^ d * vspin a z else 0) * vspin a x =
          if a ∈ U then (2 : ℤ) ^ d * vspin a (x + z) else 0 := fun a => by
        split_ifs
        · rw [vspin_add_right]; ring
        · ring
      simp_rw [h1, ← Finset.sum_filter, ← Finset.mul_sum]
      congr 1
      exact (Finset.sum_subtype (Finset.univ.filter (fun a : V => a ∈ U))
        (fun a => by simp) (fun a => vspin a (x + z)))
    rw [hUsum] at hinv
    have hFx_int : (F x : ℤ) = ∑ a : U, vspin a.1 (x + z) :=
      mul_left_cancel₀ (ne_of_gt h2d_pos) hinv
    rw [sum_vspin_submodule U (x + z), card_submodule_zmod2 U] at hFx_int
    have hiff : (∀ a ∈ U, vdot a (x + z) = 0) ↔ (∀ a ∈ U, dot a x = dot a z) := by
      constructor
      · intro h a ha
        have h1 := h a ha
        rw [vdot_add_right] at h1
        have h2 := congrArg (fun t : ZMod 2 => t + vdot a z) h1
        simp only [add_assoc, zmod2_add_self, add_zero, zero_add] at h2
        exact h2
      · intro h a ha
        rw [vdot_add_right, show vdot a x = vdot a z from h a ha, zmod2_add_self]
    split_ifs at hFx_int ⊢ with h1 h2 h2
    · exact_mod_cast hFx_int
    · exact absurd (hiff.mpr h1) h2
    · exact absurd (hiff.mp h2) h1
    · exact_mod_cast hFx_int
  · rintro ⟨U, z, hF⟩ a
    let Uperp : Submodule (ZMod 2) V :=
      { carrier := {y : V | ∀ b ∈ U, vdot b y = 0}
        zero_mem' := fun b _ => by
          change (∑ i : Fin d, b i * (0 : ZMod 2)) = 0
          simp, add_mem' := fun {x y} hx hy b hb => by
          rw [vdot_add_right, hx b hb, hy b hb, add_zero]
        smul_mem' := fun c {x} hx b hb => by
          have : vdot b (c • x) = c * vdot b x := by
            change (∑ i : Fin d, b i * (c * x i)) = c * ∑ i : Fin d, b i * x i
            simp_rw [mul_left_comm, ← Finset.mul_sum]
          rw [this, hx b hb, mul_zero] }
    have hmem_iff : ∀ x : V, (∀ b ∈ U, dot b x = dot b z) ↔ x + z ∈ Uperp := by
      intro x
      constructor
      · intro h b hb
        change vdot b (x + z) = 0
        rw [vdot_add_right, show vdot b x = vdot b z from h b hb, zmod2_add_self]
      · intro h b hb
        have h1 : vdot b (x + z) = 0 := h b hb
        rw [vdot_add_right] at h1
        have h2 := congrArg (fun t : ZMod 2 => t + vdot b z) h1
        simp only [add_assoc, zmod2_add_self, add_zero, zero_add] at h2
        exact h2
    have hcard_mul : (Fintype.card Uperp : ℤ) * (2 : ℤ) ^ (Module.finrank (ZMod 2) U) = (2 : ℤ) ^ d := by
      have h1 : (∑ x : V, F x) =
          (Finset.univ.filter (fun x : V => x + z ∈ Uperp)).card * 2 ^ (Module.finrank (ZMod 2) U) := by
        have hterm : ∀ x : V, F x =
            if x + z ∈ Uperp then 2 ^ (Module.finrank (ZMod 2) U) else 0 := fun x => by
          rw [hF x]
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd ((hmem_iff x).mp h1) h2
          · exact absurd ((hmem_iff x).mpr h2) h1
          · rfl
        simp_rw [hterm, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      have hcard_eq : (Finset.univ.filter (fun x : V => x + z ∈ Uperp)).card = Fintype.card Uperp := by
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun x hx => (⟨x + z, (Finset.mem_filter.mp hx).2⟩ : Uperp))
          (fun _ _ => Finset.mem_univ _) ?_ ?_
        · intro x1 _ x2 _ heq
          have h2 : x1 + z = x2 + z := congrArg Subtype.val heq
          have h3 := congrArg (fun t : V => t + z) h2
          simpa only [add_assoc, hvadd_self, add_zero] using h3
        · intro y _
          refine ⟨y.1 + z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · rw [add_assoc, hvadd_self, add_zero]; exact y.2
          · apply Subtype.ext
            change y.1 + z + z = y.1
            rw [add_assoc, hvadd_self, add_zero]
      rw [hcard_eq] at h1
      have h2 : Fintype.card Uperp * 2 ^ (Module.finrank (ZMod 2) U) = 2 ^ d := h1.symm.trans hsumF
      exact_mod_cast h2
    have hhat_eq : (∑ x : V, (F x : ℤ) * spin a x) =
        (2 : ℤ) ^ (Module.finrank (ZMod 2) U) * vspin a z * ∑ y : Uperp, vspin y.1 a := by
      have hterm : ∀ x : V, (F x : ℤ) * spin a x =
          if x + z ∈ Uperp then ((2 : ℤ) ^ (Module.finrank (ZMod 2) U) * vspin a z) *
            vspin (x + z) a else 0 := by
        intro x
        rw [hF x]
        split_ifs with h1 h2 h2
        · have hsym : vspin (x + z) a = vspin a (x + z) := by
            simp only [vspin, vdot]
            congr 2; refine Finset.sum_congr rfl fun i _ => mul_comm _ _
          have hsp : vspin a z * vspin a (x + z) = vspin a x := by
            rw [← vspin_add_right]
            have : z + (x + z) = x := by
              rw [add_comm x z, ← add_assoc, hvadd_self, zero_add]
            rw [this]
          change ((2 ^ Module.finrank (ZMod 2) U : ℕ) : ℤ) * vspin a x = _
          rw [Nat.cast_pow, Nat.cast_ofNat, hsym, mul_assoc, hsp]
        · exact absurd ((hmem_iff x).mp h1) h2
        · exact absurd ((hmem_iff x).mpr h2) h1
        · simp
      simp_rw [hterm, ← Finset.sum_filter, ← Finset.mul_sum]
      congr 1
      refine Finset.sum_bij (fun x hx => (⟨x + z, (Finset.mem_filter.mp hx).2⟩ : Uperp))
        (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
      · intro x1 _ x2 _ heq
        have h2 : x1 + z = x2 + z := congrArg Subtype.val heq
        have h3 := congrArg (fun t : V => t + z) h2
        simpa only [add_assoc, hvadd_self, add_zero] using h3
      · intro y _
        refine ⟨y.1 + z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [add_assoc, hvadd_self, add_zero]; exact y.2
        · apply Subtype.ext
          change y.1 + z + z = y.1
          rw [add_assoc, hvadd_self, add_zero]
    rw [hhat_eq, sum_vspin_submodule Uperp a]
    split_ifs with h0
    · refine ⟨vspin a z, ?_⟩
      calc
        (2 : ℤ) ^ Module.finrank (ZMod 2) U * vspin a z * (Fintype.card Uperp : ℤ)
            = ((Fintype.card Uperp : ℤ) * (2 : ℤ) ^ Module.finrank (ZMod 2) U) * vspin a z := by
              ring
        _ = (2 : ℤ) ^ d * vspin a z := by rw [hcard_mul]
    · simp only [mul_zero, dvd_zero]
