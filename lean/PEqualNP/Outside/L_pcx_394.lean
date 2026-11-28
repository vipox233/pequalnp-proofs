import PEqualNP.Defs
import PEqualNP.ProofComplexity.Helpers.BoolVanish

namespace PEqualNP.Outside.L_pcx_394

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers

abbrev Poly (V : Type) := MvPolynomial V (ZMod 2)

def b2z {V : Type} (x : V → Bool) : V → ZMod 2 :=
  fun v => (x v).toNat

def z2b {V : Type} (y : V → ZMod 2) : V → Bool :=
  fun v => decide (y v = 1)

lemma b2z_z2b {V : Type} (y : V → ZMod 2) : b2z (z2b y) = y := by
  funext v
  simp only [b2z, z2b]
  generalize y v = c
  revert c
  decide

lemma z2b_b2z {V : Type} (x : V → Bool) : z2b (b2z x) = x := by
  funext v
  simp only [b2z, z2b]
  have h : ∀ b : Bool, decide ((b.toNat : ZMod 2) = 1) = b := by decide
  exact h (x v)

lemma eval_bind1 {V : Type} (y : V → ZMod 2) (φ : V → Poly V) (p : Poly V) :
    eval y (bind₁ φ p) = eval (fun v => eval y (φ v)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q ihp ihq => simp [map_add, ihp, ihq]
  | mul_X p v ihp => simp [map_mul, bind₁_X_right, ihp]

lemma zmod2_eq_one_of_ne_zero {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  revert hc
  revert c
  decide

lemma zmod2_add_self {V : Type} (p : Poly V) : p + p = 0 := by
  rw [← two_smul (ZMod 2) p, show (2 : ZMod 2) = 0 from rfl, zero_smul]

lemma zmod2_add_cancel_left {V : Type} (p q : Poly V) : p + (p + q) = q := by
  rw [← add_assoc, zmod2_add_self, zero_add]

lemma zmod2_add_cancel_right {V : Type} (p q : Poly V) : (p + q) + q = p := by
  rw [add_assoc, zmod2_add_self, add_zero]

lemma zmod2_mul_diff {V : Type} (P P' Q Q' : Poly V) :
    P * Q + P' * Q' = Q * (P + P') + P' * (Q + Q') := by
  have h1 : Q * (P + P') + P' * (Q + Q') = P * Q + (Q * P' + Q * P') + P' * Q' := by ring
  rw [h1, zmod2_add_self, add_zero]

lemma refutable_zero_of_sat {V : Type} {F E0 : Set (Poly V)} {a0 : V → ZMod 2}
    (hsat : ∀ e ∈ E0, eval a0 e = 0) {r : Poly V} (hr : PCDerivable (F ∪ E0) 0 r) :
    PCDerivable F 0 r := by
  induction hr with
  | @ax p hp hdeg =>
    rcases hp with hF | hE
    · exact .ax hF hdeg
    · have hC : p = C (constantCoeff p) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
      have hev := hsat p hE
      rw [hC, eval_C] at hev
      rw [hC, hev, map_zero]
      exact .zero
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      rw [mul_zero]
      exact .zero
    · have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
        rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
      omega

lemma pcDerivable_cut {V : Type} {G H : Set (Poly V)} {d B : ℕ}
    (hd : d ≤ B) (hax : ∀ a ∈ G, a.totalDegree ≤ d → PCDerivable H B a)
    {r : Poly V} (hr : PCDerivable G d r) : PCDerivable H B r := by
  induction hr with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hd)

lemma with_factor {V : Type} {A G : Set (Poly V)} {d B : ℕ}
    (q : Poly V) (hq : q.totalDegree + d ≤ B)
    (base : ∀ p ∈ A, p.totalDegree ≤ d → PCDerivable G B (q * p))
    {p : Poly V} (h : PCDerivable A d p) : PCDerivable G B (q * p) := by
  induction h with
  | ax hp hd => exact base _ hp hd
  | zero => simpa only [mul_zero] using (PCDerivable.zero : PCDerivable G B 0)
  | add _ _ ih1 ih2 =>
    rw [mul_add]
    exact .add ih1 ih2
  | @mulX j r _ hd ih =>
    rw [mul_left_comm q (X j) r]
    refine .mulX j ih ?_
    rw [← mul_left_comm q (X j) r]
    exact (totalDegree_mul q (X j * r)).trans ((Nat.add_le_add_left hd _).trans hq)

lemma merge_linear_split_le {V : Type} {G : Set (Poly V)}
    (hG_bool : ∀ v : V, X v * X v + X v ∈ G)
    {g : Poly V} (hg : g.totalDegree ≤ 1)
    {d0 d1 : ℕ} (hd0 : 1 ≤ d0) (hd01 : d0 ≤ d1)
    (h0 : PCRefutable (G ∪ {g}) d0)
    (h1 : PCRefutable (G ∪ {1 + g}) d1) :
    ∃ d : ℕ, 1 ≤ d ∧ 2 ^ d ≤ 2 ^ d0 + 2 ^ d1 ∧ PCRefutable G d := by
  set d : ℕ := if d0 = d1 then d1 + 1 else d1 with hd_def
  have hd_ge1 : 1 ≤ d := by
    rw [hd_def]
    split_ifs <;> omega
  have hd_ge2 : 2 ≤ d := by
    rw [hd_def]
    split_ifs <;> omega
  have hd1_le : d1 ≤ d := by
    rw [hd_def]
    split_ifs <;> omega
  have hd0_add : d0 + 1 ≤ d := by
    rw [hd_def]
    split_ifs <;> omega
  have hpow : 2 ^ d ≤ 2 ^ d0 + 2 ^ d1 := by
    rw [hd_def]
    split_ifs with heq
    · subst heq
      rw [pow_succ]
      omega
    · exact Nat.le_add_left _ _
  have h1g_deg : (1 + g).totalDegree ≤ 1 :=
    (totalDegree_add 1 g).trans (max_le (by simp) hg)
  have h1g : PCDerivable G d (1 + g) := by
    have hmul : PCDerivable G d ((1 + g) * 1) := by
      refine with_factor (1 + g) (by omega) ?_ h0
      intro p hp hdeg
      rcases hp with hpG | hpg
      · have hpa : PCDerivable G d0 p := .ax hpG hdeg
        have hpm := pcDerivable_mul_left hpa (1 + g)
        exact pcDerivable_mono hpm (max_le (by omega) (by omega)) subset_rfl
      · rw [Set.mem_singleton_iff] at hpg
        rw [hpg]
        refine BoolVanish.vanish_derivable V G d ((1 + g) * g) hG_bool ?_ ?_
        · exact (totalDegree_mul (1 + g) g).trans (by omega)
        · intro y
          simp only [map_mul, map_add, map_one]
          generalize eval y g = c
          revert c
          decide
    simpa only [mul_one] using hmul
  refine ⟨d, hd_ge1, hpow, ?_⟩
  refine pcDerivable_cut hd1_le ?_ h1
  intro a ha hdeg
  rcases ha with haG | ha1g
  · exact .ax haG (hdeg.trans hd1_le)
  · rw [Set.mem_singleton_iff] at ha1g
    subst ha1g
    exact h1g

lemma merge_linear_split {V : Type} {G : Set (Poly V)}
    (hG_bool : ∀ v : V, X v * X v + X v ∈ G)
    {g : Poly V} (hg : g.totalDegree ≤ 1)
    {d0 d1 : ℕ} (hd0 : 1 ≤ d0) (hd1 : 1 ≤ d1)
    (h0 : PCRefutable (G ∪ {g}) d0)
    (h1 : PCRefutable (G ∪ {1 + g}) d1) :
    ∃ d : ℕ, 1 ≤ d ∧ 2 ^ d ≤ 2 ^ d0 + 2 ^ d1 ∧ PCRefutable G d := by
  by_cases hle : d0 ≤ d1
  · exact merge_linear_split_le hG_bool hg hd0 hle h0 h1
  · have hle' : d1 ≤ d0 := by omega
    have h1g_deg : (1 + g).totalDegree ≤ 1 :=
      (totalDegree_add 1 g).trans (max_le (by simp) hg)
    have h11g : (1 : Poly V) + (1 + g) = g := zmod2_add_cancel_left 1 g
    have h0' : PCRefutable (G ∪ {1 + (1 + g)}) d0 := by
      rwa [h11g]
    obtain ⟨d, hd, hpow, href⟩ := merge_linear_split_le hG_bool h1g_deg hd1 hle' h1 h0'
    exact ⟨d, hd, by omega, href⟩

lemma finsupp_eq_zero_or_single {V : Type} (m : V →₀ ℕ) (hm : (m.sum fun _ e => e) ≤ 1) :
    m = 0 ∨ ∃ v : V, m = Finsupp.single v 1 := by
  classical
  by_cases hm0 : m = 0
  · exact Or.inl hm0
  · right
    have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm0
    obtain ⟨v, hv⟩ := hne
    refine ⟨v, ?_⟩
    have hv1 : 1 ≤ m v := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
    have hle : m v ≤ m.sum (fun _ e => e) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
    have hmv : m v = 1 := by omega
    ext w
    by_cases hw : w = v
    · subst hw
      simp [hmv]
    · rw [Finsupp.single_eq_of_ne hw]
      by_contra hmw
      have hws : w ∈ m.support := Finsupp.mem_support_iff.mpr hmw
      have hsub : ({v, w} : Finset V) ⊆ m.support := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      have hpair : m v + m w ≤ ∑ u ∈ m.support, m u := by
        have hsum : ∑ u ∈ ({v, w} : Finset V), m u ≤ ∑ u ∈ m.support, m u :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
        rwa [Finset.sum_pair (Ne.symm hw)] at hsum
      have hmw1 : 1 ≤ m w := Nat.pos_of_ne_zero hmw
      have hmsum : m.sum (fun _ e => e) = ∑ u ∈ m.support, m u := rfl
      omega

lemma deg_le_one_add_bind1 {V : Type} {G : Set (Poly V)} {B : ℕ}
    (φ : V → Poly V) (hφ : ∀ v : V, PCDerivable G B (X v + φ v))
    {h : Poly V} (hh : h.totalDegree ≤ 1) :
    PCDerivable G B (h + bind₁ φ h) := by
  have heq : h + bind₁ φ h = ∑ m ∈ h.support, (monomial m (h.coeff m) + bind₁ φ (monomial m (h.coeff m))) := by
    conv_lhs => rw [h.as_sum]
    rw [map_sum, ← Finset.sum_add_distrib]
  rw [heq]
  refine pcDerivable_sum _ _ fun m hm => ?_
  have hc : h.coeff m = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp hm)
  rw [hc]
  have hmdeg : (m.sum fun _ e => e) ≤ 1 := (le_totalDegree hm).trans hh
  rcases finsupp_eq_zero_or_single m hmdeg with rfl | ⟨v, rfl⟩
  · have h1 : (monomial (0 : V →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [h1, map_one, zmod2_add_self]
    exact .zero
  · have hx : (monomial (Finsupp.single v 1) (1 : ZMod 2)) = X v := rfl
    rw [hx, bind₁_X_right]
    exact hφ v

lemma elim_affine {V : Type} :
    ∀ (k : ℕ) (A : Finset (Poly V)), A.card = k →
      (∀ g ∈ A, g.totalDegree ≤ 1) →
      PCDerivable (A : Set (Poly V)) 1 1 ∨
      ∃ φ : V → Poly V,
        (∀ v : V, (φ v).totalDegree ≤ 1) ∧
        (∀ v : V, PCDerivable (A : Set (Poly V)) 1 (X v + φ v)) ∧
        (∀ y : V → ZMod 2, ∀ g ∈ A, eval (fun v => eval y (φ v)) g = 0) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro A hcard hA
  by_cases hnz : ∃ g ∈ A, g ≠ 0
  · obtain ⟨g, hgA, hg0⟩ := hnz
    by_cases hv0 : ∃ v0 : V, g.coeff (Finsupp.single v0 1) ≠ 0
    · obtain ⟨v0, hv0_ne⟩ := hv0
      have hv0_one : g.coeff (Finsupp.single v0 1) = 1 := zmod2_eq_one_of_ne_zero hv0_ne
      set r : Poly V := g + X v0 with hr_def
      have hr_deg : r.totalDegree ≤ 1 :=
        (totalDegree_add g (X v0)).trans (max_le (hA g hgA) (by simp))
      have hr_no_v0 : ∀ m ∈ r.support, m v0 = 0 := by
        intro m hm
        have hmdeg : (m.sum fun _ e => e) ≤ 1 := (le_totalDegree hm).trans hr_deg
        rcases finsupp_eq_zero_or_single m hmdeg with rfl | ⟨w, rfl⟩
        · simp
        · by_cases hw : w = v0
          · subst hw
            exfalso
            have hne : r.coeff (Finsupp.single w 1) ≠ 0 := mem_support_iff.mp hm
            have hcoef : r.coeff (Finsupp.single w 1) = 0 := by
              have hadd : r.coeff (Finsupp.single w 1) =
                  g.coeff (Finsupp.single w 1) + (X w : Poly V).coeff (Finsupp.single w 1) := by
                rw [hr_def, AddMonoidAlgebra.coeff_add]
                rfl
              rw [hadd, hv0_one]
              have hcx : (X w : Poly V).coeff (Finsupp.single w 1) = 1 := by
                rw [X, coeff_monomial]
                simp
              rw [hcx]
              decide
            exact hne hcoef
          · simp [hw]
      set ψ : V → Poly V := Function.update X v0 r with hψ_def
      have hψ_deg : ∀ w : V, (ψ w).totalDegree ≤ 1 := by
        intro w
        by_cases hw : w = v0
        · subst hw
          simp [hψ_def, hr_deg]
        · simp [hψ_def, hw]
      have hbind_r : bind₁ ψ r = r := by
        conv_lhs => rw [r.as_sum]
        conv_rhs => rw [r.as_sum]
        rw [map_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hc : r.coeff m = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp hm)
        rw [hc]
        have hmdeg : (m.sum fun _ e => e) ≤ 1 := (le_totalDegree hm).trans hr_deg
        rcases finsupp_eq_zero_or_single m hmdeg with rfl | ⟨w, rfl⟩
        · have h1 : (monomial (0 : V →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
          rw [h1, map_one]
        · have hne : w ≠ v0 := by
            intro heq
            subst heq
            have := hr_no_v0 (Finsupp.single w 1) hm
            simp at this
          have hx : (monomial (Finsupp.single w 1) (1 : ZMod 2)) = X w := rfl
          rw [hx, bind₁_X_right, hψ_def, Function.update_of_ne hne]
      have hg_eq : g = X v0 + r := by
        rw [hr_def, add_comm g (X v0), zmod2_add_cancel_left]
      have hbind_g : bind₁ ψ g = 0 := by
        rw [hg_eq, map_add, bind₁_X_right, hψ_def, Function.update_self, hbind_r, zmod2_add_self]
      have hψ_der : ∀ w : V, PCDerivable (A : Set (Poly V)) 1 (X w + ψ w) := by
        intro w
        by_cases hw : w = v0
        · subst hw
          rw [hψ_def, Function.update_self, ← hg_eq]
          exact .ax hgA (hA g hgA)
        · rw [hψ_def, Function.update_of_ne hw, zmod2_add_self]
          exact .zero
      set A' : Finset (Poly V) := (A.erase g).image (bind₁ ψ) with hA'_def
      have hA'_card : A'.card < k := by
        rw [← hcard, hA'_def]
        exact Finset.card_image_le.trans_lt (Finset.card_erase_lt_of_mem hgA)
      have hA'_deg : ∀ h' ∈ A', h'.totalDegree ≤ 1 := by
        intro h' hh'
        rw [hA'_def, Finset.mem_image] at hh'
        obtain ⟨h, hh, rfl⟩ := hh'
        have h1 := totalDegree_bind₁_le ψ hψ_deg h
        have h2 := hA h (Finset.mem_of_mem_erase hh)
        omega
      have hA'_der : ∀ h' ∈ A', PCDerivable (A : Set (Poly V)) 1 h' := by
        intro h' hh'
        rw [hA'_def, Finset.mem_image] at hh'
        obtain ⟨h, hh, rfl⟩ := hh'
        have hhA : h ∈ A := Finset.mem_of_mem_erase hh
        have h1 : PCDerivable (A : Set (Poly V)) 1 h := .ax hhA (hA h hhA)
        have h2 : PCDerivable (A : Set (Poly V)) 1 (h + bind₁ ψ h) :=
          deg_le_one_add_bind1 ψ hψ_der (hA h hhA)
        have h3 := PCDerivable.add h1 h2
        rwa [zmod2_add_cancel_left] at h3
      rcases ih A'.card hA'_card A' rfl hA'_deg with hleft | ⟨φ', hφ'_deg, hφ'_der, hφ'_van⟩
      · left
        exact pcDerivable_cut le_rfl (fun a ha _ => hA'_der a ha) hleft
      · right
        set φ : V → Poly V := fun w => bind₁ φ' (ψ w) with hφ_def
        have hφ'_der_A : ∀ w : V, PCDerivable (A : Set (Poly V)) 1 (X w + φ' w) := by
          intro w
          exact pcDerivable_cut le_rfl (fun a ha _ => hA'_der a ha) (hφ'_der w)
        refine ⟨φ, ?_, ?_, ?_⟩
        · intro w
          dsimp only [φ]
          have h1 := totalDegree_bind₁_le φ' hφ'_deg (ψ w)
          have h2 := hψ_deg w
          omega
        · intro w
          by_cases hw : w = v0
          · subst hw
            dsimp only [φ, ψ]
            rw [Function.update_self]
            have hr_der : PCDerivable (A : Set (Poly V)) 1 (r + bind₁ φ' r) :=
              deg_le_one_add_bind1 φ' hφ'_der_A hr_deg
            have hg_der : PCDerivable (A : Set (Poly V)) 1 (X w + r) := by
              rw [← hg_eq]
              exact .ax hgA (hA g hgA)
            have hadd := PCDerivable.add hg_der hr_der
            have hsimp : (X w + r) + (r + bind₁ φ' r) = X w + bind₁ φ' r := by
              rw [add_assoc, zmod2_add_cancel_left]
            rwa [hsimp] at hadd
          · dsimp only [φ, ψ]
            rw [Function.update_of_ne hw, bind₁_X_right]
            exact hφ'_der_A w
        · intro y h hhA
          set y' : V → ZMod 2 := fun w => eval y (φ' w) with hy'_def
          have hz_eq : (fun w => eval y (φ w)) = fun w => eval y' (ψ w) := by
            funext w
            dsimp only [φ]
            rw [eval_bind1]
          rw [hz_eq, ← eval_bind1]
          by_cases hhg : h = g
          · subst hhg
            rw [hbind_g, map_zero]
          · have hmem : bind₁ ψ h ∈ A' := by
              rw [hA'_def, Finset.mem_image]
              exact ⟨h, Finset.mem_erase.mpr ⟨hhg, hhA⟩, rfl⟩
            exact hφ'_van y (bind₁ ψ h) hmem
    · left
      push Not at hv0
      have hsupp : g.support = {0} := by
        ext m
        simp only [Finset.mem_singleton]
        constructor
        · intro hm
          have hmdeg : (m.sum fun _ e => e) ≤ 1 := (le_totalDegree hm).trans (hA g hgA)
          rcases finsupp_eq_zero_or_single m hmdeg with rfl | ⟨v0, rfl⟩
          · rfl
          · exfalso
            exact (mem_support_iff.mp hm) (hv0 v0)
        · rintro rfl
          by_contra h0
          apply hg0
          rw [g.as_sum]
          refine Finset.sum_eq_zero fun m hm => ?_
          have hmdeg : (m.sum fun _ e => e) ≤ 1 := (le_totalDegree hm).trans (hA g hgA)
          rcases finsupp_eq_zero_or_single m hmdeg with rfl | ⟨v0, rfl⟩
          · exact False.elim (h0 hm)
          · exact False.elim ((mem_support_iff.mp hm) (hv0 v0))
      have hg1 : g = 1 := by
        rw [g.as_sum, hsupp, Finset.sum_singleton]
        have h0mem : (0 : V →₀ ℕ) ∈ g.support := by
          rw [hsupp]
          exact Finset.mem_singleton_self 0
        have hc0 : g.coeff 0 = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp h0mem)
        rw [hc0]
        rfl
      rw [← hg1]
      exact .ax hgA (hA g hgA)
  · right
    push Not at hnz
    refine ⟨X, fun v => by simp, fun v => ?_, fun y g hg => ?_⟩
    · rw [zmod2_add_self]
      exact .zero
    · rw [hnz g hg, map_zero]

lemma derive_sub_diff_monomial {V : Type} {G : Set (Poly V)} {B : ℕ} (hB : 1 ≤ B)
    (φ : V → Poly V) (hφ_deg : ∀ v : V, (φ v).totalDegree ≤ 1)
    (hφ_der : ∀ v : V, PCDerivable G 1 (X v + φ v)) :
    ∀ (m : V →₀ ℕ), (m.sum fun _ e => e) ≤ B →
      PCDerivable G B (monomial m 1 + bind₁ φ (monomial m 1)) := by
  intro m
  induction m using Finsupp.induction_linear with
  | zero =>
    intro _
    have h1 : (monomial (0 : V →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [h1, map_one, zmod2_add_self]
    exact .zero
  | add a b iha ihb =>
    intro hdeg
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    set P : Poly V := monomial a 1 with hP_def
    set Q : Poly V := monomial b 1 with hQ_def
    have hPQ : monomial (a + b) (1 : ZMod 2) = P * Q := by
      rw [hP_def, hQ_def, monomial_mul_monomial, one_mul]
    rw [hPQ, map_mul, zmod2_mul_diff P (bind₁ φ P) Q (bind₁ φ Q)]
    have hPa : P.totalDegree ≤ a.sum fun _ e => e := totalDegree_monomial_le a 1
    have hQb : Q.totalDegree ≤ b.sum fun _ e => e := totalDegree_monomial_le b 1
    have hφP : (bind₁ φ P).totalDegree ≤ a.sum fun _ e => e := by
      have := totalDegree_bind₁_le φ hφ_deg P
      omega
    have hφQ : (bind₁ φ Q).totalDegree ≤ b.sum fun _ e => e := by
      have := totalDegree_bind₁_le φ hφ_deg Q
      omega
    have hPdiff : (P + bind₁ φ P).totalDegree ≤ a.sum fun _ e => e :=
      (totalDegree_add _ _).trans (max_le hPa hφP)
    have hQdiff : (Q + bind₁ φ Q).totalDegree ≤ b.sum fun _ e => e :=
      (totalDegree_add _ _).trans (max_le hQb hφQ)
    have h1 := pcDerivable_mul_left (iha (by omega)) Q
    have h2 := pcDerivable_mul_left (ihb (by omega)) (bind₁ φ P)
    refine .add ?_ ?_
    · exact pcDerivable_mono h1 (max_le le_rfl (by omega)) subset_rfl
    · exact pcDerivable_mono h2 (max_le le_rfl (by omega)) subset_rfl
  | single v n =>
    induction n with
    | zero =>
      intro _
      have h1 : (monomial (Finsupp.single v 0) (1 : ZMod 2)) = 1 := by simp
      rw [h1, map_one, zmod2_add_self]
      exact .zero
    | succ n ihn =>
      intro hdeg
      have hd1 : ((Finsupp.single v (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd0 : ((Finsupp.single v n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      set Q : Poly V := monomial (Finsupp.single v n) 1 with hQ_def
      have hXQ : monomial (Finsupp.single v (n + 1)) (1 : ZMod 2) = X v * Q := by
        rw [hQ_def, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
      rw [hXQ, map_mul, bind₁_X_right, zmod2_mul_diff (X v) (φ v) Q (bind₁ φ Q)]
      have hQn : Q.totalDegree ≤ n := (totalDegree_monomial_le _ 1).trans_eq hd0
      have hφQ : (bind₁ φ Q).totalDegree ≤ n := by
        have := totalDegree_bind₁_le φ hφ_deg Q
        omega
      have hXφ : (X v + φ v).totalDegree ≤ 1 :=
        (totalDegree_add (X v) (φ v)).trans (max_le (by simp) (hφ_deg v))
      have hQdiff : (Q + bind₁ φ Q).totalDegree ≤ n :=
        (totalDegree_add _ _).trans (max_le hQn hφQ)
      have h1 := pcDerivable_mul_left (pcDerivable_mono (hφ_der v) hB subset_rfl) Q
      have h2 := pcDerivable_mul_left (ihn (by omega)) (φ v)
      have hφv := hφ_deg v
      refine .add ?_ ?_
      · exact pcDerivable_mono h1 (max_le le_rfl (by omega)) subset_rfl
      · exact pcDerivable_mono h2 (max_le le_rfl (by omega)) subset_rfl

lemma derive_sub_diff {V : Type} {G : Set (Poly V)} {B : ℕ} (hB : 1 ≤ B)
    (φ : V → Poly V) (hφ_deg : ∀ v : V, (φ v).totalDegree ≤ 1)
    (hφ_der : ∀ v : V, PCDerivable G 1 (X v + φ v))
    {e : Poly V} (he : e.totalDegree ≤ B) :
    PCDerivable G B (e + bind₁ φ e) := by
  have heq : e + bind₁ φ e = ∑ m ∈ e.support, (monomial m 1 + bind₁ φ (monomial m 1)) := by
    conv_lhs => rw [e.as_sum]
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hc : e.coeff m = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp hm)
    rw [hc]
  rw [heq]
  refine pcDerivable_sum _ _ fun m hm =>
    derive_sub_diff_monomial hB φ hφ_deg hφ_der m ((le_totalDegree hm).trans he)

lemma leaf_refutable {V : Type} {F E0 : Set (Poly V)} {d : ℕ}
    (hF_bool : ∀ v : V, X v * X v + X v ∈ F)
    (hd : 1 ≤ d)
    (href : PCRefutable (F ∪ E0) d)
    (A : Finset (Poly V))
    (hA_deg : ∀ g ∈ A, g.totalDegree ≤ 1)
    (hE0_van : ∀ y : V → ZMod 2, (∀ g ∈ A, eval y g = 0) → ∀ e ∈ E0, eval y e = 0) :
    PCRefutable (F ∪ (A : Set (Poly V))) d := by
  rcases elim_affine A.card A rfl hA_deg with hleft | ⟨φ, hφ_deg, hφ_der, hφ_van⟩
  · exact pcDerivable_mono hleft hd Set.subset_union_right
  · refine pcDerivable_cut le_rfl ?_ href
    intro e he hdeg
    rcases he with heF | heE
    · exact .ax (Or.inl heF) hdeg
    · have hφ_der' : ∀ v : V, PCDerivable (F ∪ (A : Set (Poly V))) 1 (X v + φ v) :=
        fun v => pcDerivable_mono (hφ_der v) le_rfl Set.subset_union_right
      have hdiff : PCDerivable (F ∪ (A : Set (Poly V))) d (e + bind₁ φ e) :=
        derive_sub_diff hd φ hφ_deg hφ_der' hdeg
      have hbind_deg : (bind₁ φ e).totalDegree ≤ d := by
        have := totalDegree_bind₁_le φ hφ_deg e
        omega
      have hbind_van : ∀ y : V → ZMod 2, eval y (bind₁ φ e) = 0 := by
        intro y
        rw [eval_bind1]
        exact hE0_van (fun v => eval y (φ v)) (hφ_van y) e heE
      have hbind_der : PCDerivable (F ∪ (A : Set (Poly V))) d (bind₁ φ e) :=
        pcDerivable_mono
          (BoolVanish.vanish_derivable V F d (bind₁ φ e) hF_bool hbind_deg hbind_van)
          le_rfl Set.subset_union_left
      have hadd := PCDerivable.add hdiff hbind_der
      rwa [zmod2_add_cancel_right] at hadd

noncomputable def linPoly {V : Type} (e : LinEq V) : Poly V :=
  (∑ v ∈ e.1, X v) + C ((e.2).toNat : ZMod 2)

lemma totalDegree_linPoly {V : Type} (e : LinEq V) : (linPoly e).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine totalDegree_finsetSum_le fun v _ => ?_
    simp
  · rw [totalDegree_C]
    exact Nat.zero_le 1

lemma eval_linPoly_eq_zero_iff {V : Type} (y : V → ZMod 2) (e : LinEq V) :
    eval y (linPoly e) = 0 ↔ LinEqSat (z2b y) e := by
  classical
  have hsum : eval y (∑ v ∈ e.1, (X v : Poly V)) =
      ((e.1.filter (fun v => z2b y v = true)).card : ZMod 2) := by
    rw [map_sum]
    have hterm : ∀ v ∈ e.1, eval y (X v : Poly V) =
        if z2b y v = true then (1 : ZMod 2) else 0 := by
      intro v _
      rw [eval_X]
      simp only [z2b]
      have h : ∀ c : ZMod 2, c = if decide (c = 1) = true then (1 : ZMod 2) else 0 := by decide
      exact h (y v)
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  simp only [linPoly, map_add, eval_C, hsum, LinEqSat]
  set n : ℕ := (e.1.filter (fun v => z2b y v = true)).card with hn_def
  have hcast : (n : ZMod 2) = ((n % 2 : ℕ) : ZMod 2) := by
    conv_lhs => rw [← Nat.div_add_mod n 2]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  rw [hcast, Nat.odd_iff]
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
  rcases e.2 with _ | _
  · interval_cases (n % 2) <;> decide
  · interval_cases (n % 2) <;> decide

lemma eval_one_add_linPoly_eq_zero_iff {V : Type} (y : V → ZMod 2) (e : LinEq V) :
    eval y (1 + linPoly e) = 0 ↔ ¬ LinEqSat (z2b y) e := by
  rw [← eval_linPoly_eq_zero_iff y e, map_add, map_one]
  generalize eval y (linPoly e) = c
  revert c
  decide

lemma merge_linTerm_list {V : Type} (S_false S_true : ℕ) :
    ∀ (L : List (LinEq V)), L ≠ [] →
      ∀ (G : Set (Poly V)), (∀ v : V, X v * X v + X v ∈ G) →
      (∃ d_t, 1 ≤ d_t ∧ 2 ^ d_t ≤ S_true ∧
        PCRefutable (G ∪ {p | ∃ e ∈ L, p = linPoly e}) d_t) →
      (∀ k : Fin L.length, ∃ d_f, 1 ≤ d_f ∧ 2 ^ d_f ≤ S_false ∧
        PCRefutable (G ∪ {p | ∃ e ∈ L.take k.val, p = linPoly e} ∪ {1 + linPoly (L.get k)}) d_f) →
      ∃ d, 1 ≤ d ∧ 2 ^ d ≤ L.length * S_false + S_true ∧ PCRefutable G d := by
  intro L
  induction L with
  | nil =>
    intro hne
    exact False.elim (hne rfl)
  | cons e rest ih =>
    intro _ G hG_bool htrue hfalse
    by_cases hrest : rest = []
    · subst hrest
      obtain ⟨d_t, hdt1, hdt_pow, hdt_ref⟩ := htrue
      obtain ⟨d_f, hdf1, hdf_pow, hdf_ref⟩ := hfalse ⟨0, by simp⟩
      have ht_set : G ∪ {p | ∃ e' ∈ [e], p = linPoly e'} = G ∪ {linPoly e} := by
        ext p
        simp
      have hf_set : G ∪ {p | ∃ e' ∈ List.take 0 [e], p = linPoly e'} ∪
          {1 + linPoly ([e].get ⟨0, by simp⟩)} = G ∪ {1 + linPoly e} := by
        ext p
        simp
      rw [ht_set] at hdt_ref
      rw [hf_set] at hdf_ref
      obtain ⟨d, hd1, hd_pow, hd_ref⟩ :=
        merge_linear_split hG_bool (totalDegree_linPoly e) hdt1 hdf1 hdt_ref hdf_ref
      refine ⟨d, hd1, ?_, hd_ref⟩
      simp only [List.length_singleton, one_mul]
      omega
    · set G' : Set (Poly V) := G ∪ {linPoly e} with hG'_def
      have hG'_bool : ∀ v : V, X v * X v + X v ∈ G' := fun v => Or.inl (hG_bool v)
      have htrue' : ∃ d_t, 1 ≤ d_t ∧ 2 ^ d_t ≤ S_true ∧
          PCRefutable (G' ∪ {p | ∃ e' ∈ rest, p = linPoly e'}) d_t := by
        obtain ⟨d_t, hdt1, hdt_pow, hdt_ref⟩ := htrue
        refine ⟨d_t, hdt1, hdt_pow, ?_⟩
        have hset : G' ∪ {p | ∃ e' ∈ rest, p = linPoly e'} =
            G ∪ {p | ∃ e' ∈ e :: rest, p = linPoly e'} := by
          ext p
          simp only [hG'_def, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq,
            List.mem_cons]
          constructor
          · rintro ((hG | rfl) | ⟨e', he', rfl⟩)
            · exact Or.inl hG
            · exact Or.inr ⟨e, Or.inl rfl, rfl⟩
            · exact Or.inr ⟨e', Or.inr he', rfl⟩
          · rintro (hG | ⟨e', rfl | he', rfl⟩)
            · exact Or.inl (Or.inl hG)
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr ⟨e', he', rfl⟩
        rwa [hset]
      have hfalse' : ∀ k : Fin rest.length, ∃ d_f, 1 ≤ d_f ∧ 2 ^ d_f ≤ S_false ∧
          PCRefutable (G' ∪ {p | ∃ e' ∈ rest.take k.val, p = linPoly e'} ∪
            {1 + linPoly (rest.get k)}) d_f := by
        intro k
        obtain ⟨d_f, hdf1, hdf_pow, hdf_ref⟩ := hfalse k.succ
        refine ⟨d_f, hdf1, hdf_pow, ?_⟩
        have hset : G' ∪ {p | ∃ e' ∈ rest.take k.val, p = linPoly e'} ∪
              {1 + linPoly (rest.get k)} =
            G ∪ {p | ∃ e' ∈ (e :: rest).take k.succ.val, p = linPoly e'} ∪
              {1 + linPoly ((e :: rest).get k.succ)} := by
          ext p
          simp only [hG'_def, Fin.val_succ, List.take_succ_cons,
            Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons]
          constructor
          · rintro (((hG | rfl) | ⟨e', he', rfl⟩) | h1)
            · exact Or.inl (Or.inl hG)
            · exact Or.inl (Or.inr ⟨e, Or.inl rfl, rfl⟩)
            · exact Or.inl (Or.inr ⟨e', Or.inr he', rfl⟩)
            · exact Or.inr h1
          · rintro ((hG | ⟨e', rfl | he', rfl⟩) | h1)
            · exact Or.inl (Or.inl (Or.inl hG))
            · exact Or.inl (Or.inl (Or.inr rfl))
            · exact Or.inl (Or.inr ⟨e', he', rfl⟩)
            · exact Or.inr h1
        rwa [hset]
      obtain ⟨d1, hd1_1, hd1_pow, hd1_ref⟩ := ih hrest G' hG'_bool htrue' hfalse'
      obtain ⟨d0, hd0_1, hd0_pow, hd0_ref⟩ := hfalse ⟨0, by simp⟩
      have hf0_set : G ∪ {p | ∃ e' ∈ List.take 0 (e :: rest), p = linPoly e'} ∪
          {1 + linPoly ((e :: rest).get ⟨0, by simp⟩)} = G ∪ {1 + linPoly e} := by
        ext p
        simp
      rw [hf0_set] at hd0_ref
      obtain ⟨d, hd_1, hd_pow, hd_ref⟩ :=
        merge_linear_split hG_bool (totalDegree_linPoly e) hd1_1 hd0_1 hd1_ref hd0_ref
      refine ⟨d, hd_1, ?_, hd_ref⟩
      simp only [List.length_cons, Nat.add_mul, one_mul]
      omega

def follows {V : Type} (ask : List Bool → LinTerm V) (p : List Bool) (x : V → Bool) : Prop :=
  ∀ i : Fin p.length, p.get i = true ↔ LinTermSat x (ask (p.take i.val))

lemma follows_of_isPrefix {V : Type} {ask : List Bool → LinTerm V} {r p : List Bool} {x : V → Bool}
    (hrp : List.IsPrefix r p) (hp : follows ask p x) : follows ask r x := by
  obtain ⟨t, rfl⟩ := hrp
  intro i
  have hi : i.val < (r ++ t).length := Nat.lt_of_lt_of_le i.isLt (by simp)
  have h1 := hp ⟨i.val, hi⟩
  have hget : (r ++ t).get ⟨i.val, hi⟩ = r.get i := by
    simp [List.get_eq_getElem, List.getElem_append_left i.isLt]
  have htake : (r ++ t).take i.val = r.take i.val :=
    List.take_append_of_le_length (Nat.le_of_lt i.isLt)
  rwa [hget, htake] at h1

lemma follows_append_singleton {V : Type} {ask : List Bool → LinTerm V} {q : List Bool}
    {b : Bool} {x : V → Bool} (hq : follows ask q x)
    (hb : b = true ↔ LinTermSat x (ask q)) :
    follows ask (q ++ [b]) x := by
  intro i
  by_cases hi : i.val < q.length
  · have hget : (q ++ [b]).get i = q.get ⟨i.val, hi⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_left hi]
    have htake : (q ++ [b]).take i.val = q.take i.val :=
      List.take_append_of_le_length (Nat.le_of_lt hi)
    rw [hget, htake]
    exact hq ⟨i.val, hi⟩
  · have heq : i.val = q.length := by
      have hlt := i.isLt
      simp only [List.length_append, List.length_singleton] at hlt
      omega
    have hget : (q ++ [b]).get i = b := by
      simp [List.get_eq_getElem, heq]
    have htake : (q ++ [b]).take i.val = q := by
      rw [heq, List.take_left]
    rw [hget, htake]
    exact hb

noncomputable def leavesUnder (leaves : Finset (List Bool)) (q : List Bool) :
    Finset (List Bool) := by
  classical
  exact leaves.filter (fun p => List.IsPrefix q p)

lemma mem_leavesUnder {leaves : Finset (List Bool)} {q p : List Bool} :
    p ∈ leavesUnder leaves q ↔ p ∈ leaves ∧ List.IsPrefix q p := by
  classical
  simp [leavesUnder]

lemma leavesUnder_eq_singleton {leaves : Finset (List Bool)}
    (hpfree : ∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q)
    {q : List Bool} (hq : q ∈ leaves) :
    leavesUnder leaves q = {q} := by
  ext p
  rw [mem_leavesUnder, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hqp⟩
    exact (hpfree q hq p hp hqp).symm
  · rintro rfl
    exact ⟨hq, List.prefix_rfl⟩

lemma leavesUnder_disjoint {leaves : Finset (List Bool)} (q : List Bool) :
    Disjoint (leavesUnder leaves (q ++ [false])) (leavesUnder leaves (q ++ [true])) := by
  rw [Finset.disjoint_left]
  intro p hpf hpt
  rw [mem_leavesUnder] at hpf hpt
  obtain ⟨s1, hs1⟩ := hpf.2
  obtain ⟨s2, hs2⟩ := hpt.2
  have heq : q ++ (false :: s1) = q ++ (true :: s2) := by
    simpa [List.append_assoc] using hs1.trans hs2.symm
  have hcons := List.append_cancel_left heq
  simp at hcons

lemma leavesUnder_split {leaves : Finset (List Bool)} {q : List Bool} (hq : q ∉ leaves) :
    leavesUnder leaves q =
      leavesUnder leaves (q ++ [false]) ∪ leavesUnder leaves (q ++ [true]) := by
  ext p
  simp only [Finset.mem_union, mem_leavesUnder]
  constructor
  · rintro ⟨hp, hqp⟩
    obtain ⟨t, rfl⟩ := hqp
    cases t with
    | nil =>
      simp at hp
      exact False.elim (hq hp)
    | cons b t' =>
      have hpr : List.IsPrefix (q ++ [b]) (q ++ b :: t') :=
        ⟨t', by simp [List.append_assoc]⟩
      cases b
      · exact Or.inl ⟨hp, hpr⟩
      · exact Or.inr ⟨hp, hpr⟩
  · rintro (⟨hp, hqp⟩ | ⟨hp, hqp⟩)
    · exact ⟨hp, (List.prefix_append q [false]).trans hqp⟩
    · exact ⟨hp, (List.prefix_append q [true]).trans hqp⟩

lemma unique_leaf_under {V : Type} {leaves : Finset (List Bool)} {ask : List Bool → LinTerm V}
    (hpfree : ∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q)
    (hcover : ∀ x : V → Bool, ∃ p ∈ leaves, follows ask p x)
    {q : List Bool} (hne : (leavesUnder leaves q).Nonempty)
    {x : V → Bool} (hq : follows ask q x) :
    ∃ p ∈ leavesUnder leaves q, follows ask p x := by
  obtain ⟨p, hp_mem, hp_fol⟩ := hcover x
  obtain ⟨p', hp'_mem⟩ := hne
  rw [mem_leavesUnder] at hp'_mem
  have hget_eq : ∀ j : ℕ, (hjp : j < p.length) → (hjq : j < q.length) → p[j] = q[j] := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hjp hjq
    have htake : p.take j = q.take j := by
      refine List.ext_getElem ?_ ?_
      · simp [Nat.le_of_lt hjp, Nat.le_of_lt hjq]
      · intro t ht1 ht2
        have htj : t < j := by
          simp [Nat.le_of_lt hjp] at ht1
          exact ht1
        simp only [List.getElem_take]
        exact ih t htj (Nat.lt_trans htj hjp) (Nat.lt_trans htj hjq)
    have h1 := hp_fol ⟨j, hjp⟩
    have h2 := hq ⟨j, hjq⟩
    rw [htake] at h1
    have hiff : p[j] = true ↔ q[j] = true := by
      simpa [List.get_eq_getElem] using h1.trans h2.symm
    cases hpi : p[j] <;> cases hqi : q[j] <;> simp_all
  have hcomp : List.IsPrefix p q ∨ List.IsPrefix q p := by
    by_cases hlen : p.length ≤ q.length
    · left
      refine ⟨q.drop p.length, ?_⟩
      have htk : q.take p.length = p := by
        refine List.ext_getElem ?_ ?_
        · simp [hlen]
        · intro t ht1 ht2
          simp only [List.getElem_take]
          exact (hget_eq t ht2 (Nat.lt_of_lt_of_le ht2 hlen)).symm
      simpa only [htk] using List.take_append_drop p.length q
    · right
      have hlen' : q.length ≤ p.length := by omega
      refine ⟨p.drop q.length, ?_⟩
      have htk : p.take q.length = q := by
        refine List.ext_getElem ?_ ?_
        · simp [hlen']
        · intro t ht1 ht2
          simp only [List.getElem_take]
          exact hget_eq t (Nat.lt_of_lt_of_le ht2 hlen') ht2
      simpa only [htk] using List.take_append_drop q.length p
  rcases hcomp with hpq | hqp
  · have hpp' : List.IsPrefix p p' := hpq.trans hp'_mem.2
    have heq : p = p' := hpfree p hp_mem p' hp'_mem.1 hpp'
    refine ⟨p, mem_leavesUnder.mpr ⟨hp_mem, ?_⟩, hp_fol⟩
    rw [heq]
    exact hp'_mem.2
  · exact ⟨p, mem_leavesUnder.mpr ⟨hp_mem, hqp⟩, hp_fol⟩

def remCopies {V : Type} (ask : List Bool → LinTerm V) (k : ℕ) (p : List Bool) : ℕ :=
  ∏ i ∈ (Finset.univ : Finset (Fin p.length)).filter (fun i => k ≤ i.val),
    if p.get i then 1 else max 1 (ask (p.take i.val)).card

lemma remCopies_zero {V : Type} (ask : List Bool → LinTerm V) (p : List Bool) :
    remCopies ask 0 p =
      ∏ i : Fin p.length, if p.get i then 1 else max 1 (ask (p.take i.val)).card := by
  simp [remCopies]

lemma remCopies_self {V : Type} (ask : List Bool → LinTerm V) (p : List Bool) :
    remCopies ask p.length p = 1 := by
  unfold remCopies
  have hempty : (Finset.univ : Finset (Fin p.length)).filter (fun i => p.length ≤ i.val) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_le]
    exact i.isLt
  rw [hempty, Finset.prod_empty]

lemma remCopies_step {V : Type} (ask : List Bool → LinTerm V) {q p : List Bool} {b : Bool}
    (hp : List.IsPrefix (q ++ [b]) p) :
    remCopies ask q.length p =
      (if b then 1 else max 1 (ask q).card) * remCopies ask (q.length + 1) p := by
  obtain ⟨t, rfl⟩ := hp
  have hlt : q.length < (q ++ [b] ++ t).length := by
    simp
  set i0 : Fin (q ++ [b] ++ t).length := ⟨q.length, hlt⟩
  have hfilt : (Finset.univ : Finset (Fin (q ++ [b] ++ t).length)).filter
        (fun i => q.length ≤ i.val) =
      insert i0 ((Finset.univ : Finset (Fin (q ++ [b] ++ t).length)).filter
        (fun i => q.length + 1 ≤ i.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, i0]
    omega
  have hnotmem : i0 ∉ (Finset.univ : Finset (Fin (q ++ [b] ++ t).length)).filter
      (fun i => q.length + 1 ≤ i.val) := by
    simp [i0]
  have hget : (q ++ [b] ++ t).get i0 = b := by
    simp [i0, List.get_eq_getElem, List.append_assoc]
  have htake : (q ++ [b] ++ t).take i0.val = q := by
    simp [i0, List.append_assoc]
  unfold remCopies
  rw [hfilt, Finset.prod_insert hnotmem, hget, htake]

lemma tree_solve {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (Poly V)) (leaves : Finset (List Bool))
    (ask : List Bool → LinTerm V) (E : List Bool → Set (Poly V)) (D : List Bool → ℕ)
    (hpfree : ∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q)
    (hcover : ∀ x : V → Bool, ∃ p ∈ leaves, follows ask p x)
    (hsat : ∀ p ∈ leaves, ∃ x : V → Bool, follows ask p x)
    (hF_bool : ∀ v : V, X v * X v + X v ∈ F)
    (heval : ∀ p ∈ leaves, ∀ x : V → Bool, follows ask p x → ∀ e ∈ E p, eval (b2z x) e = 0)
    (href : ∀ p ∈ leaves, PCRefutable (F ∪ E p) (D p))
    (hDpos : ∀ p ∈ leaves, 1 ≤ D p) :
    ∀ (fuel : ℕ) (q : List Bool),
      leaves.sup List.length - q.length ≤ fuel →
      (leavesUnder leaves q).Nonempty →
      ∀ (A : Finset (Poly V)),
        (∀ g ∈ A, g.totalDegree ≤ 1) →
        (∀ y : V → ZMod 2, (∀ g ∈ A, eval y g = 0) → follows ask q (z2b y)) →
        ∃ d : ℕ, 1 ≤ d ∧
          2 ^ d ≤ ∑ p ∈ leavesUnder leaves q, remCopies ask q.length p * 2 ^ (D p) ∧
          PCRefutable (F ∪ (A : Set (Poly V))) d := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro q hfuel hne A hA_deg hA_fol
    obtain ⟨p0, hp0⟩ := hne
    rw [mem_leavesUnder] at hp0
    have hplen : p0.length ≤ leaves.sup List.length := Finset.le_sup hp0.1
    have hqle : q.length ≤ p0.length := hp0.2.length_le
    have hqeq : q.length = p0.length := by omega
    obtain ⟨t, ht⟩ := hp0.2
    have ht0 : t = [] := by
      have hlen : q.length + t.length = p0.length := by
        rw [← List.length_append, ht]
      have : t.length = 0 := by omega
      exact List.eq_nil_of_length_eq_zero this
    subst ht0
    simp only [List.append_nil] at ht
    subst ht
    have hq_mem : q ∈ leaves := hp0.1
    rw [leavesUnder_eq_singleton hpfree hq_mem, Finset.sum_singleton, remCopies_self, one_mul]
    refine ⟨D q, hDpos q hq_mem, le_rfl, ?_⟩
    refine leaf_refutable hF_bool (hDpos q hq_mem) (href q hq_mem) A hA_deg ?_
    intro y hy e he
    have hfol := hA_fol y hy
    have h0 := heval q hq_mem (z2b y) hfol e he
    rwa [b2z_z2b] at h0
  | succ fuel ih =>
    intro q hfuel hne A hA_deg hA_fol
    by_cases hq_mem : q ∈ leaves
    · rw [leavesUnder_eq_singleton hpfree hq_mem, Finset.sum_singleton, remCopies_self, one_mul]
      refine ⟨D q, hDpos q hq_mem, le_rfl, ?_⟩
      refine leaf_refutable hF_bool (hDpos q hq_mem) (href q hq_mem) A hA_deg ?_
      intro y hy e he
      have hfol := hA_fol y hy
      have h0 := heval q hq_mem (z2b y) hfol e he
      rwa [b2z_z2b] at h0
    · set Lf := leavesUnder leaves (q ++ [false]) with hLf_def
      set Lt := leavesUnder leaves (q ++ [true]) with hLt_def
      have hsplit : leavesUnder leaves q = Lf ∪ Lt := leavesUnder_split hq_mem
      have hdisj : Disjoint Lf Lt := leavesUnder_disjoint q
      set Sf : ℕ := ∑ p ∈ Lf, remCopies ask (q.length + 1) p * 2 ^ (D p) with hSf_def
      set St : ℕ := ∑ p ∈ Lt, remCopies ask (q.length + 1) p * 2 ^ (D p) with hSt_def
      have hsum_eq :
          ∑ p ∈ leavesUnder leaves q, remCopies ask q.length p * 2 ^ (D p) =
            max 1 (ask q).card * Sf + St := by
        rw [hsplit, Finset.sum_union hdisj]
        have hLf_sum : ∑ p ∈ Lf, remCopies ask q.length p * 2 ^ (D p) =
            max 1 (ask q).card * Sf := by
          rw [hSf_def, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hLf_def, mem_leavesUnder] at hp
          rw [remCopies_step ask hp.2]
          simp [mul_assoc]
        have hLt_sum : ∑ p ∈ Lt, remCopies ask q.length p * 2 ^ (D p) = St := by
          rw [hSt_def]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hLt_def, mem_leavesUnder] at hp
          rw [remCopies_step ask hp.2]
          simp
        rw [hLf_sum, hLt_sum]
      have hq_lt_sup : q.length < leaves.sup List.length := by
        obtain ⟨p0, hp0⟩ := hne
        rw [mem_leavesUnder] at hp0
        have hplen : p0.length ≤ leaves.sup List.length := Finset.le_sup hp0.1
        obtain ⟨t, rfl⟩ := hp0.2
        cases t with
        | nil =>
          simp at hp0
          exact False.elim (hq_mem hp0)
        | cons b t' =>
          simp only [List.length_append, List.length_cons] at hplen
          omega
      have hfuel' : ∀ b : Bool, leaves.sup List.length - (q ++ [b]).length ≤ fuel := by
        intro b
        simp only [List.length_append, List.length_singleton]
        omega
      by_cases hLf_ne : Lf.Nonempty
      · by_cases hLt_ne : Lt.Nonempty
        · have hask_ne : (ask q).Nonempty := by
            obtain ⟨p0, hp0⟩ := hLf_ne
            rw [hLf_def, mem_leavesUnder] at hp0
            obtain ⟨x0, hx0⟩ := hsat p0 hp0.1
            have hx0' := follows_of_isPrefix hp0.2 hx0
            have hi := hx0' ⟨q.length, by simp⟩
            have hget : (q ++ [false]).get ⟨q.length, by simp⟩ = false := by
              simp [List.get_eq_getElem]
            have htake : (q ++ [false]).take q.length = q := by
              simp
            rw [hget, htake] at hi
            by_contra hempty
            rw [Finset.not_nonempty_iff_eq_empty] at hempty
            have htr : LinTermSat x0 (ask q) := by
              rw [hempty]
              intro e he
              simp at he
            have := hi.mpr htr
            simp at this
          set L : List (LinEq V) := (ask q).toList with hL_def
          have hL_ne : L ≠ [] := by
            intro hnil
            have hcard0 : (ask q).card = 0 := by
              rw [← Finset.length_toList (s := ask q), ← hL_def, hnil, List.length_nil]
            exact hask_ne.ne_empty (Finset.card_eq_zero.mp hcard0)
          have hL_len : L.length = (ask q).card := Finset.length_toList (ask q)
          have hmax : max 1 (ask q).card = L.length := by
            have hpos : 1 ≤ (ask q).card := Finset.card_pos.mpr hask_ne
            omega
          have htrue_branch : ∃ d_t, 1 ≤ d_t ∧ 2 ^ d_t ≤ St ∧
              PCRefutable ((F ∪ (A : Set (Poly V))) ∪ {p | ∃ e ∈ L, p = linPoly e}) d_t := by
            set At : Finset (Poly V) := A ∪ (L.map linPoly).toFinset with hAt_def
            have hAt_deg : ∀ g ∈ At, g.totalDegree ≤ 1 := by
              intro g hg
              rw [hAt_def, Finset.mem_union] at hg
              rcases hg with hgA | hgL
              · exact hA_deg g hgA
              · rw [List.mem_toFinset, List.mem_map] at hgL
                obtain ⟨e, _, rfl⟩ := hgL
                exact totalDegree_linPoly e
            have hAt_fol : ∀ y : V → ZMod 2, (∀ g ∈ At, eval y g = 0) →
                follows ask (q ++ [true]) (z2b y) := by
              intro y hy
              refine follows_append_singleton
                (hA_fol y (fun g hg => hy g (Finset.mem_union_left _ hg))) ?_
              simp only [true_iff]
              intro e he
              have heL : e ∈ L := Finset.mem_toList.mpr he
              have hmem : linPoly e ∈ At := by
                rw [hAt_def]
                exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, heL, rfl⟩))
              exact (eval_linPoly_eq_zero_iff y e).mp (hy (linPoly e) hmem)
            obtain ⟨d_t, hdt1, hdt_pow, hdt_ref⟩ :=
              ih (q ++ [true]) (hfuel' true) hLt_ne At hAt_deg hAt_fol
            have hset : F ∪ (At : Set (Poly V)) =
                (F ∪ (A : Set (Poly V))) ∪ {p | ∃ e ∈ L, p = linPoly e} := by
              ext p
              simp only [hAt_def, Finset.coe_union, Set.mem_union, Finset.mem_coe,
                List.mem_toFinset, List.mem_map, Set.mem_ofPred_eq]
              constructor
              · rintro (hF | (hA | ⟨e, he, rfl⟩))
                · exact Or.inl (Or.inl hF)
                · exact Or.inl (Or.inr hA)
                · exact Or.inr ⟨e, he, rfl⟩
              · rintro ((hF | hA) | ⟨e, he, rfl⟩)
                · exact Or.inl hF
                · exact Or.inr (Or.inl hA)
                · exact Or.inr (Or.inr ⟨e, he, rfl⟩)
            rw [hset] at hdt_ref
            have hlen_t : (q ++ [true]).length = q.length + 1 := by simp
            rw [hlen_t] at hdt_pow
            exact ⟨d_t, hdt1, hdt_pow, hdt_ref⟩
          have hfalse_branch : ∀ k : Fin L.length, ∃ d_f, 1 ≤ d_f ∧ 2 ^ d_f ≤ Sf ∧
              PCRefutable ((F ∪ (A : Set (Poly V))) ∪
                {p | ∃ e ∈ L.take k.val, p = linPoly e} ∪
                {1 + linPoly (L.get k)}) d_f := by
            intro k
            set Af : Finset (Poly V) :=
              A ∪ ((L.take k.val).map linPoly).toFinset ∪ {1 + linPoly (L.get k)} with hAf_def
            have hAf_deg : ∀ g ∈ Af, g.totalDegree ≤ 1 := by
              intro g hg
              rw [hAf_def, Finset.mem_union, Finset.mem_union, Finset.mem_singleton] at hg
              rcases hg with (hgA | hgL) | rfl
              · exact hA_deg g hgA
              · rw [List.mem_toFinset, List.mem_map] at hgL
                obtain ⟨e, _, rfl⟩ := hgL
                exact totalDegree_linPoly e
              · exact (totalDegree_add 1 _).trans (max_le (by simp) (totalDegree_linPoly _))
            have hAf_fol : ∀ y : V → ZMod 2, (∀ g ∈ Af, eval y g = 0) →
                follows ask (q ++ [false]) (z2b y) := by
              intro y hy
              refine follows_append_singleton
                (hA_fol y (fun g hg => hy g (by rw [hAf_def]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hg)))) ?_
              simp only [Bool.false_eq_true, false_iff]
              intro hsat_term
              have hmem_e : L.get k ∈ ask q := Finset.mem_toList.mp (List.get_mem L k)
              have hsat_e : LinEqSat (z2b y) (L.get k) := hsat_term (L.get k) hmem_e
              have hmem_p : 1 + linPoly (L.get k) ∈ Af := by
                rw [hAf_def]
                exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
              have hnot := (eval_one_add_linPoly_eq_zero_iff y (L.get k)).mp (hy _ hmem_p)
              exact hnot hsat_e
            obtain ⟨d_f, hdf1, hdf_pow, hdf_ref⟩ :=
              ih (q ++ [false]) (hfuel' false) hLf_ne Af hAf_deg hAf_fol
            have hset : F ∪ (Af : Set (Poly V)) =
                (F ∪ (A : Set (Poly V))) ∪
                  {p | ∃ e ∈ L.take k.val, p = linPoly e} ∪
                  {1 + linPoly (L.get k)} := by
              ext p
              simp only [hAf_def, Finset.coe_union, Finset.coe_singleton, Set.mem_union,
                Finset.mem_coe, List.mem_toFinset, List.mem_map, Set.mem_ofPred_eq,
                Set.mem_singleton_iff]
              constructor
              · rintro (hF | ((hA | ⟨e, he, rfl⟩) | rfl))
                · exact Or.inl (Or.inl (Or.inl hF))
                · exact Or.inl (Or.inl (Or.inr hA))
                · exact Or.inl (Or.inr ⟨e, he, rfl⟩)
                · exact Or.inr rfl
              · rintro (((hF | hA) | ⟨e, he, rfl⟩) | rfl)
                · exact Or.inl hF
                · exact Or.inr (Or.inl (Or.inl hA))
                · exact Or.inr (Or.inl (Or.inr ⟨e, he, rfl⟩))
                · exact Or.inr (Or.inr rfl)
            rw [hset] at hdf_ref
            have hlen_f : (q ++ [false]).length = q.length + 1 := by simp
            rw [hlen_f] at hdf_pow
            exact ⟨d_f, hdf1, hdf_pow, hdf_ref⟩
          obtain ⟨d, hd1, hd_pow, hd_ref⟩ :=
            merge_linTerm_list Sf St L hL_ne (F ∪ (A : Set (Poly V)))
              (fun v => Or.inl (hF_bool v)) htrue_branch hfalse_branch
          refine ⟨d, hd1, ?_, hd_ref⟩
          rw [hsum_eq, hmax]
          exact hd_pow
        · rw [Finset.not_nonempty_iff_eq_empty] at hLt_ne
          have hA_fol' : ∀ y : V → ZMod 2, (∀ g ∈ A, eval y g = 0) →
              follows ask (q ++ [false]) (z2b y) := by
            intro y hy
            obtain ⟨p, hp_mem, hp_fol⟩ :=
              unique_leaf_under hpfree hcover hne (hA_fol y hy)
            rw [hsplit, hLt_ne, Finset.union_empty, hLf_def, mem_leavesUnder] at hp_mem
            exact follows_of_isPrefix hp_mem.2 hp_fol
          obtain ⟨d, hd1, hd_pow, hd_ref⟩ :=
            ih (q ++ [false]) (hfuel' false) hLf_ne A hA_deg hA_fol'
          have hlen_f : (q ++ [false]).length = q.length + 1 := by simp
          rw [hlen_f] at hd_pow
          refine ⟨d, hd1, ?_, hd_ref⟩
          rw [hsum_eq]
          have h1le : 1 ≤ max 1 (ask q).card := le_max_left 1 _
          calc 2 ^ d ≤ Sf := hd_pow
            _ = 1 * Sf := (one_mul Sf).symm
            _ ≤ max 1 (ask q).card * Sf := Nat.mul_le_mul_right Sf h1le
            _ ≤ max 1 (ask q).card * Sf + St := Nat.le_add_right _ _
      · rw [Finset.not_nonempty_iff_eq_empty] at hLf_ne
        have hLt_ne : Lt.Nonempty := by
          obtain ⟨p, hp⟩ := hne
          rw [hsplit, hLf_ne, Finset.empty_union] at hp
          exact ⟨p, hp⟩
        have hA_fol' : ∀ y : V → ZMod 2, (∀ g ∈ A, eval y g = 0) →
            follows ask (q ++ [true]) (z2b y) := by
          intro y hy
          obtain ⟨p, hp_mem, hp_fol⟩ :=
            unique_leaf_under hpfree hcover hne (hA_fol y hy)
          rw [hsplit, hLf_ne, Finset.empty_union, hLt_def, mem_leavesUnder] at hp_mem
          exact follows_of_isPrefix hp_mem.2 hp_fol
        obtain ⟨d, hd1, hd_pow, hd_ref⟩ :=
          ih (q ++ [true]) (hfuel' true) hLt_ne A hA_deg hA_fol'
        have hlen_t : (q ++ [true]).length = q.length + 1 := by simp
        rw [hlen_t] at hd_pow
        refine ⟨d, hd1, ?_, hd_ref⟩
        rw [hsum_eq]
        exact hd_pow.trans (Nat.le_add_left _ _)

end PEqualNP.Outside.L_pcx_394

theorem PEqualNP.Outside.L_pcx_394 : (∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (MvPolynomial V (ZMod 2)))
    (leaves : Finset (List Bool)) (ask : List Bool → PEqualNP.ProofComplexity.LinTerm V)
    (E : List Bool → Set (MvPolynomial V (ZMod 2))) (D : List Bool → ℕ),
    let follows := fun (p : List Bool) (x : V → Bool) =>
      ∀ i : Fin p.length, p.get i = true ↔
        PEqualNP.ProofComplexity.LinTermSat x (ask (p.take i.val))
    (∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q) →
    (∀ x : V → Bool, ∃ p ∈ leaves, follows p x) →
    (∀ p ∈ leaves, ∃ x : V → Bool, follows p x) →
    (∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) →
    (∀ p ∈ leaves, ∀ x : V → Bool, follows p x → ∀ e ∈ E p,
      MvPolynomial.eval (fun v => (x v).toNat : V → ZMod 2) e = 0) →
    (∀ p ∈ leaves, PEqualNP.ProofComplexity.PCRefutable (F ∪ E p) (D p)) →
    let copies := fun p : List Bool => ∏ i : Fin p.length,
      if p.get i then 1 else max 1 (ask (p.take i.val)).card
    PEqualNP.ProofComplexity.PCRefutable F
      (Nat.log 2 (∑ p ∈ leaves, copies p * 2^(D p)))) := by
  intro V _ _ F leaves ask E D follows hpfree hcover hsat hF_bool heval href copies
  by_cases hD0 : ∃ p ∈ leaves, D p = 0
  · obtain ⟨p0, hp0, hDp0⟩ := hD0
    obtain ⟨x0, hx0⟩ := hsat p0 hp0
    have href0 : PEqualNP.ProofComplexity.PCRefutable (F ∪ E p0) 0 := hDp0 ▸ href p0 hp0
    have hF0 : PEqualNP.ProofComplexity.PCRefutable F 0 :=
      PEqualNP.Outside.L_pcx_394.refutable_zero_of_sat (heval p0 hp0 x0 hx0) href0
    exact PEqualNP.ProofComplexity.Helpers.pcDerivable_mono hF0 (Nat.zero_le _) subset_rfl
  · push Not at hD0
    have hDpos : ∀ p ∈ leaves, 1 ≤ D p := fun p hp => Nat.pos_of_ne_zero (hD0 p hp)
    have hne : (PEqualNP.Outside.L_pcx_394.leavesUnder leaves []).Nonempty := by
      obtain ⟨p, hp, _⟩ := hcover (fun _ => false)
      exact ⟨p, PEqualNP.Outside.L_pcx_394.mem_leavesUnder.mpr ⟨hp, List.nil_prefix⟩⟩
    obtain ⟨d, _, hd_pow, hd_ref⟩ :=
      PEqualNP.Outside.L_pcx_394.tree_solve F leaves ask E D
        hpfree hcover hsat hF_bool heval href hDpos
        (leaves.sup List.length) [] (by simp) hne ∅
        (fun _ hg => False.elim (Finset.notMem_empty _ hg))
        (fun _ _ i => Fin.elim0 i)
    have hlu_nil : PEqualNP.Outside.L_pcx_394.leavesUnder leaves [] = leaves := by
      ext p
      simp [PEqualNP.Outside.L_pcx_394.mem_leavesUnder]
    rw [hlu_nil, List.length_nil] at hd_pow
    have hsum_eq :
        (∑ p ∈ leaves, PEqualNP.Outside.L_pcx_394.remCopies ask 0 p * 2 ^ (D p)) =
          ∑ p ∈ leaves, copies p * 2 ^ (D p) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [PEqualNP.Outside.L_pcx_394.remCopies_zero]
    rw [hsum_eq] at hd_pow
    have hF_eq : F ∪ ((∅ : Finset (PEqualNP.Outside.L_pcx_394.Poly V)) :
        Set (PEqualNP.Outside.L_pcx_394.Poly V)) = F := by
      simp
    rw [hF_eq] at hd_ref
    exact PEqualNP.ProofComplexity.Helpers.pcDerivable_mono hd_ref
      (Nat.le_log_of_pow_le (by norm_num) hd_pow) subset_rfl
