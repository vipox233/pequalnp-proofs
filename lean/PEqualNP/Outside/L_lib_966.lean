import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_966
namespace aux

open scoped Classical
noncomputable section

abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

lemma zmod2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_self (a : F) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_sub_eq_add (a b : F) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma vec_add_self {n : ℕ} (v : Vec n) : v + v = 0 := by
  ext i; exact zmod2_add_self (v i)

lemma vec_sub_eq_add {n : ℕ} (u v : Vec n) : u - v = u + v := by
  ext i; exact zmod2_sub_eq_add (u i) (v i)

def chi {n : ℕ} (v x : Vec n) : ℤ :=
  if dotProduct v x = 0 then 1 else -1

lemma chi_zero_left {n : ℕ} (x : Vec n) : chi (0 : Vec n) x = 1 := by
  simp [chi]

lemma chi_add_left {n : ℕ} (u v x : Vec n) : chi (u + v) x = chi u x * chi v x := by
  simp only [chi, add_dotProduct]
  rcases zmod2_cases (dotProduct u x) with hu | hu <;>
  rcases zmod2_cases (dotProduct v x) with hv | hv <;>
  (simp [hu, hv]; try decide)

lemma chi_add_right {n : ℕ} (v x y : Vec n) : chi v (x + y) = chi v x * chi v y := by
  simp only [chi, dotProduct_add]
  rcases zmod2_cases (dotProduct v x) with hx | hx <;>
  rcases zmod2_cases (dotProduct v y) with hy | hy <;>
  (simp [hx, hy]; try decide)

lemma chi_mul_self {n : ℕ} (v x : Vec n) : chi v x * chi v x = 1 := by
  simp only [chi]; split_ifs <;> norm_num

def signZ (a : F) : ℤ := if a = 0 then 1 else -1

lemma signZ_add (a b : F) : signZ (a + b) = signZ a * signZ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma signZ_mul_chi {n : ℕ} (a : F) (v x : Vec n) :
    signZ a * chi v x = if dotProduct v x = a then 1 else -1 := by
  simp only [signZ, chi]
  rcases zmod2_cases a with rfl | rfl <;>
  rcases zmod2_cases (dotProduct v x) with h | h <;>
  simp [h]

lemma exists_dot_eq_one {n : ℕ} {v : Vec n} (hv : v ≠ 0) :
    ∃ y : Vec n, dotProduct v y = 1 := by
  have hne : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hne
  have hvi : v i = 1 := by
    rcases zmod2_cases (v i) with h0 | h1
    · exact absurd h0 hi
    · exact h1
  refine ⟨Pi.single i 1, ?_⟩
  simp [dotProduct, Pi.single_apply, hvi]

lemma sum_chi {n : ℕ} (v : Vec n) :
    (∑ x : Vec n, chi v x) = if v = 0 then (2 ^ n : ℤ) else 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [chi_zero_left, Fintype.card_pi, ZMod.card]
  · simp only [hv, ite_false]
    obtain ⟨y, hy⟩ := exists_dot_eq_one hv
    have hcy : chi v y = -1 := by simp [chi, hy]
    have hshift : (∑ x : Vec n, chi v (x + y)) = ∑ x : Vec n, chi v x :=
      Fintype.sum_equiv (Equiv.addRight y) (fun x => chi v (x + y)) (fun x => chi v x) (fun _ => rfl)
    have hneg : (∑ x : Vec n, chi v (x + y)) = -(∑ x : Vec n, chi v x) := by
      calc (∑ x : Vec n, chi v (x + y))
          = ∑ x : Vec n, chi v x * chi v y := by simp_rw [chi_add_right]
        _ = ∑ x : Vec n, -(chi v x) := by simp [hcy]
        _ = -(∑ x : Vec n, chi v x) := by rw [Finset.sum_neg_distrib]
    linarith

lemma sum_chi_subspace {n : ℕ} (V : Submodule F (Vec n)) (v : Vec n) :
    (∑ x : Vec n, if x ∈ V then chi v x else 0) =
      if (∀ y ∈ V, dotProduct v y = 0) then (Fintype.card V : ℤ) else 0 := by
  by_cases hV : ∀ y ∈ V, dotProduct v y = 0
  · rw [if_pos hV]
    have : (∑ x : Vec n, if x ∈ V then chi v x else 0) =
        ∑ x : Vec n, if x ∈ V then (1 : ℤ) else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with hx
      · simp [chi, hV x hx]
      · rfl
    rw [this, Finset.sum_boole]
    simp [Fintype.card_subtype]
  · rw [if_neg hV]
    push Not at hV
    obtain ⟨y, hyV, hyne⟩ := hV
    have hy1 : dotProduct v y = 1 := by
      rcases zmod2_cases (dotProduct v y) with h0 | h1
      · exact absurd h0 hyne
      · exact h1
    have hcy : chi v y = -1 := by simp [chi, hy1]
    have hshift : (∑ x : Vec n, if x + y ∈ V then chi v (x + y) else 0) =
        ∑ x : Vec n, if x ∈ V then chi v x else 0 :=
      Fintype.sum_equiv (Equiv.addRight y)
        (fun x => if x + y ∈ V then chi v (x + y) else 0)
        (fun x => if x ∈ V then chi v x else 0) (fun _ => rfl)
    have hneg : (∑ x : Vec n, if x + y ∈ V then chi v (x + y) else 0) =
        -(∑ x : Vec n, if x ∈ V then chi v x else 0) := by
      have hmem : ∀ x : Vec n, (x + y ∈ V) ↔ (x ∈ V) := fun x =>
        ⟨fun h => by
          have := V.sub_mem h hyV
          rwa [add_sub_cancel_right] at this,
         fun h => V.add_mem h hyV⟩
      calc (∑ x : Vec n, if x + y ∈ V then chi v (x + y) else 0)
          = ∑ x : Vec n, if x ∈ V then -(chi v x) else 0 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hmem x]
            split_ifs
            · rw [chi_add_right, hcy]; ring
            · rfl
        _ = ∑ x : Vec n, -(if x ∈ V then chi v x else 0) := by
            refine Finset.sum_congr rfl fun x _ => by split_ifs <;> ring
        _ = -(∑ x : Vec n, if x ∈ V then chi v x else 0) := by rw [Finset.sum_neg_distrib]
    linarith

def perpSub {n : ℕ} (H : Submodule F (Vec n)) : Submodule F (Vec n) :=
  { carrier := {x | ∀ v ∈ H, dotProduct v x = 0}, add_mem' := fun hx hy v hv => by rw [dotProduct_add, hx v hv, hy v hv, add_zero]
    zero_mem' := fun v _ => by simp
    smul_mem' := fun c x hx v hv => by rw [dotProduct_smul, hx v hv, smul_zero] }

lemma dot_eq_zero_of_mem_perpSub {n : ℕ} {H : Submodule F (Vec n)} {v x : Vec n}
    (hv : v ∈ H) (hx : x ∈ perpSub H) : dotProduct v x = 0 := hx v hv

lemma mem_perpSub_iff {n : ℕ} {H : Submodule F (Vec n)} {x : Vec n} :
    x ∈ perpSub H ↔ ∀ v ∈ H, dotProduct v x = 0 := Iff.rfl

def dotDualMap (n : ℕ) : Vec n →ₗ[F] (Vec n →ₗ[F] F) where
  toFun := fun x =>
    { toFun := fun u => dotProduct u x
      map_add' := fun u1 u2 => add_dotProduct u1 u2 x
      map_smul' := fun c u => by simp [smul_dotProduct] }
  map_add' := fun x1 x2 => by
    ext u
    simp [dotProduct_add]
  map_smul' := fun c x => by
    ext u
    simp [dotProduct_smul]

lemma dotDualMap_bijective (n : ℕ) : Function.Bijective (dotDualMap n) := by
  have hinj : Function.Injective (dotDualMap n) := by
    intro x1 x2 h
    ext i
    have hi := LinearMap.congr_fun h (Pi.single i 1)
    simpa [dotDualMap, dotProduct, Pi.single_apply] using hi
  have hfin : Module.finrank F (Vec n) = Module.finrank F (Vec n →ₗ[F] F) :=
    Subspace.dual_finrank_eq.symm
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩

lemma mem_of_forall_perpSub {n : ℕ} (H : Submodule F (Vec n)) (v : Vec n)
    (hv : ∀ x ∈ perpSub H, dotProduct v x = 0) : v ∈ H := by
  by_contra hnot
  have hq : Submodule.Quotient.mk (p := H) v ≠ 0 :=
    mt (Submodule.Quotient.mk_eq_zero H).mp hnot
  let B := Module.Basis.ofVectorSpace F (Vec n ⧸ H)
  have hrepr : B.repr (Submodule.Quotient.mk (p := H) v) ≠ 0 := by
    intro h
    exact hq (B.repr.injective (by simpa using h))
  have hex : ∃ i, B.repr (Submodule.Quotient.mk (p := H) v) i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hrepr (Finsupp.ext hall)
  obtain ⟨i, hi⟩ := hex
  let g : (Vec n ⧸ H) →ₗ[F] F := (Finsupp.lapply i).comp B.repr.toLinearMap
  have hg : g (Submodule.Quotient.mk (p := H) v) ≠ 0 := hi
  let f : Vec n →ₗ[F] F := g.comp (Submodule.mkQ H)
  obtain ⟨x, hx⟩ := (dotDualMap_bijective n).2 f
  have hxperp : x ∈ perpSub H := by
    intro u hu
    have := LinearMap.congr_fun hx u
    simp only [dotDualMap, f, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Submodule.mkQ_apply] at this
    rw [this, (Submodule.Quotient.mk_eq_zero H).mpr hu, map_zero]
  have hv0 := hv x hxperp
  have hfv : dotProduct v x = g (Submodule.Quotient.mk v) := by
    have := LinearMap.congr_fun hx v
    simpa [dotDualMap, f] using this
  rw [hv0] at hfv
  exact hg hfv.symm

lemma card_perpSub {n : ℕ} (H : Submodule F (Vec n)) :
    Fintype.card (perpSub H) * 2 ^ (Module.finrank F H) = 2 ^ n := by
  let L : Vec n →ₗ[F] (H →ₗ[F] F) :=
    { toFun := fun x => (dotDualMap n x).comp H.subtype
      map_add' := fun x1 x2 => by ext u; simp [dotDualMap, dotProduct_add]
      map_smul' := fun c x => by ext u; simp [dotDualMap, dotProduct_smul] }
  have hker : LinearMap.ker L = perpSub H := by
    ext x
    simp [L, dotDualMap, perpSub, LinearMap.mem_ker, LinearMap.ext_iff]
  have hsurj : Function.Surjective L := by
    intro f
    obtain ⟨f', hf'⟩ := f.exists_extend
    obtain ⟨x, hx⟩ := (dotDualMap_bijective n).2 f'
    refine ⟨x, ?_⟩
    ext u
    have h1 := LinearMap.congr_fun hx u.1
    have h2 := LinearMap.congr_fun hf' u
    simpa [L, dotDualMap] using h1.trans h2
  have hrk := LinearMap.finrank_range_add_finrank_ker L
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker] at hrk
  have hdual : Module.finrank F (H →ₗ[F] F) = Module.finrank F H :=
    Subspace.dual_finrank_eq
  rw [hdual] at hrk
  have hcardV : Fintype.card (perpSub H) = 2 ^ Module.finrank F (perpSub H) := by
    have := Module.card_eq_pow_finrank (K := F) (V := perpSub H)
    simpa [ZMod.card] using this
  have hfinW : Module.finrank F (Vec n) = n := by simp [Vec]
  rw [hcardV, ← pow_add, add_comm, hrk, hfinW]

lemma four_mul_coset_ind {n : ℕ} (a b x : Vec n) (α β : F) :
    (4 : ℤ) * (if dotProduct a x = α ∧ dotProduct b x = β then 1 else 0) =
      1 + signZ α * chi a x + signZ β * chi b x + signZ (α + β) * chi (a + b) x := by
  rw [signZ_mul_chi, signZ_mul_chi, signZ_mul_chi, add_dotProduct]
  rcases zmod2_cases α with rfl | rfl <;>
  rcases zmod2_cases β with rfl | rfl <;>
  rcases zmod2_cases (dotProduct a x) with ha | ha <;>
  rcases zmod2_cases (dotProduct b x) with hb | hb <;>
  (simp [ha, hb]; try decide)

def bestP {n : ℕ} (a b : Vec n) (α β : F) : Vec n :=
  if α = 1 ∧ β = 1 then 0
  else if α = 1 ∧ β = 0 then a
  else if α = 0 ∧ β = 1 then b
  else a + b

def bestD (α β : F) : F :=
  if α = 0 ∧ β = 0 then 1 else 0

lemma best_err_iff {n : ℕ} (a b x : Vec n) (α β : F) :
    (dotProduct (bestP a b α β) x + bestD α β ≠ dotProduct a x * dotProduct b x) ↔
      (dotProduct a x = α ∧ dotProduct b x = β) := by
  rcases zmod2_cases α with rfl | rfl <;>
  rcases zmod2_cases β with rfl | rfl <;>
  simp only [bestP, bestD, add_dotProduct, zero_dotProduct] <;>
  rcases zmod2_cases (dotProduct a x) with ha | ha <;>
  rcases zmod2_cases (dotProduct b x) with hb | hb <;>
  (simp [ha, hb]; try decide)

lemma quad_coset_err_ge {n : ℕ} (H : Submodule F (Vec n)) (x0 a b p : Vec n) (d : F)
    (ha : a ∉ H) (hb : b ∉ H) (hab : a + b ∉ H) :
    (Fintype.card (perpSub H) : ℤ) ≤
      4 * ((Finset.univ.filter (fun y : perpSub H =>
        dotProduct a (x0 + y.1) * dotProduct b (x0 + y.1) ≠
        dotProduct p (x0 + y.1) + d)).card : ℤ) := by
  let V := perpSub H
  have hsum : ∀ v : Vec n, v ∉ H → (∑ y : V, chi v y.1) = 0 := by
    intro v hv
    have hnot : ¬ ∀ y ∈ V, dotProduct v y = 0 := fun h => hv (mem_of_forall_perpSub H v h)
    have h1 := sum_chi_subspace V v
    rw [if_neg hnot] at h1
    have h2 : (∑ y : V, chi v y.1) = ∑ x : Vec n, if x ∈ V then chi v x else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter (· ∈ V)) (fun _ => by simp) (fun x => chi v x)).symm
    rw [h2, h1]
  have hq : ∀ x : Vec n, 2 * signZ (dotProduct a x * dotProduct b x) =
      1 + chi a x + chi b x - chi (a + b) x := by
    intro x
    simp only [signZ, chi, add_dotProduct]
    rcases zmod2_cases (dotProduct a x) with h1 | h1 <;>
    rcases zmod2_cases (dotProduct b x) with h2 | h2 <;>
    (simp [h1, h2]; try decide)
  have herr : ∀ x : Vec n,
      (4 : ℤ) * (if dotProduct a x * dotProduct b x ≠ dotProduct p x + d then 1 else 0) =
        2 - signZ d * chi p x * (1 + chi a x + chi b x - chi (a + b) x) := by
    intro x
    have h1 : (2 : ℤ) * (if dotProduct a x * dotProduct b x ≠ dotProduct p x + d then 1 else 0) =
        1 - signZ (dotProduct a x * dotProduct b x) * (signZ d * chi p x) := by
      have : signZ d * chi p x = signZ (dotProduct p x + d) := by
        rw [signZ_add, mul_comm]; congr 1
      rw [this]
      rcases zmod2_cases (dotProduct a x * dotProduct b x) with h1 | h1 <;>
      rcases zmod2_cases (dotProduct p x + d) with h2 | h2 <;>
      simp [signZ, h1, h2]
    calc (4 : ℤ) * (if dotProduct a x * dotProduct b x ≠ dotProduct p x + d then 1 else 0)
        = 2 * (2 * (if dotProduct a x * dotProduct b x ≠ dotProduct p x + d then 1 else 0)) := by ring
      _ = 2 - (2 * signZ (dotProduct a x * dotProduct b x)) * (signZ d * chi p x) := by rw [h1]; ring
      _ = 2 - signZ d * chi p x * (1 + chi a x + chi b x - chi (a + b) x) := by rw [hq]; ring
  have htot : (4 : ℤ) * ((Finset.univ.filter (fun y : V =>
      dotProduct a (x0 + y.1) * dotProduct b (x0 + y.1) ≠
      dotProduct p (x0 + y.1) + d)).card : ℤ) =
      2 * (Fintype.card V : ℤ) - signZ d * (
        chi p x0 * (∑ y : V, chi p y.1) +
        chi (p + a) x0 * (∑ y : V, chi (p + a) y.1) +
        chi (p + b) x0 * (∑ y : V, chi (p + b) y.1) -
        chi (p + (a + b)) x0 * (∑ y : V, chi (p + (a + b)) y.1)) := by
    have hcard : ((Finset.univ.filter (fun y : V =>
        dotProduct a (x0 + y.1) * dotProduct b (x0 + y.1) ≠
        dotProduct p (x0 + y.1) + d)).card : ℤ) =
        ∑ y : V, (if dotProduct a (x0 + y.1) * dotProduct b (x0 + y.1) ≠
          dotProduct p (x0 + y.1) + d then (1 : ℤ) else 0) := by
      rw [Finset.card_filter]; simp
    rw [hcard, Finset.mul_sum]
    simp_rw [herr]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm _ (2 : ℤ)]
    congr 1
    have hexp : ∀ y : V,
        signZ d * chi p (x0 + y.1) * (1 + chi a (x0 + y.1) + chi b (x0 + y.1) - chi (a + b) (x0 + y.1)) =
        signZ d * (chi p x0 * chi p y.1 + chi (p + a) x0 * chi (p + a) y.1 +
          chi (p + b) x0 * chi (p + b) y.1 - chi (p + (a + b)) x0 * chi (p + (a + b)) y.1) := by
      intro y
      simp only [chi_add_left, chi_add_right]
      ring
    simp_rw [hexp, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [htot]
  have hval : ∀ v : Vec n, (∑ y : V, chi v y.1) = if v ∈ H then (Fintype.card V : ℤ) else 0 := by
    intro v
    by_cases hv : v ∈ H
    · rw [if_pos hv]
      have : ∀ y : V, chi v y.1 = 1 := fun y => by simp [chi, y.2 v hv]
      simp [this]
    · rw [if_neg hv]
      exact hsum v hv
  have h1 : ¬ (p ∈ H ∧ p + a ∈ H) := fun ⟨hp, hpa⟩ => ha (by
    have := H.add_mem hp hpa
    rwa [← add_assoc, vec_add_self, zero_add] at this)
  have h2 : ¬ (p ∈ H ∧ p + b ∈ H) := fun ⟨hp, hpb⟩ => hb (by
    have := H.add_mem hp hpb
    rwa [← add_assoc, vec_add_self, zero_add] at this)
  have h3 : ¬ (p ∈ H ∧ p + (a + b) ∈ H) := fun ⟨hp, hpab⟩ => hab (by
    have := H.add_mem hp hpab
    rwa [← add_assoc, vec_add_self, zero_add] at this)
  have h4 : ¬ (p + a ∈ H ∧ p + b ∈ H) := fun ⟨hpa, hpb⟩ => hab (by
    have := H.add_mem hpa hpb
    have heq : (p + a) + (p + b) = a + b := by
      ext i; have := zmod2_add_self (p i); simp only [Pi.add_apply]; linear_combination this
    rwa [heq] at this)
  have h5 : ¬ (p + a ∈ H ∧ p + (a + b) ∈ H) := fun ⟨hpa, hpab⟩ => hb (by
    have := H.add_mem hpa hpab
    have heq : (p + a) + (p + (a + b)) = b := by
      ext i; have h1 := zmod2_add_self (p i); have h2 := zmod2_add_self (a i)
      simp only [Pi.add_apply]; linear_combination h1 + h2
    rwa [heq] at this)
  have h6 : ¬ (p + b ∈ H ∧ p + (a + b) ∈ H) := fun ⟨hpb, hpab⟩ => ha (by
    have := H.add_mem hpb hpab
    have heq : (p + b) + (p + (a + b)) = a := by
      ext i; have h1 := zmod2_add_self (p i); have h2 := zmod2_add_self (b i)
      simp only [Pi.add_apply]; linear_combination h1 + h2
    rwa [heq] at this)
  have hchi_pm : ∀ u : Vec n, chi u x0 = 1 ∨ chi u x0 = -1 := fun u => by
    simp only [chi]; split_ifs <;> simp
  have hsd_pm : signZ d = 1 ∨ signZ d = -1 := by
    simp only [signZ]; split_ifs <;> simp
  have hcard_nonneg : (0 : ℤ) ≤ Fintype.card V := Nat.cast_nonneg _
  rw [hval p, hval (p + a), hval (p + b), hval (p + (a + b))]
  by_cases hp : p ∈ H
  · have hpa : p + a ∉ H := fun h => h1 ⟨hp, h⟩
    have hpb : p + b ∉ H := fun h => h2 ⟨hp, h⟩
    have hpab : p + (a + b) ∉ H := fun h => h3 ⟨hp, h⟩
    simp only [hp, hpa, hpb, hpab, ite_true, ite_false, mul_zero, add_zero, sub_zero]
    rcases hsd_pm with hsd | hsd <;> rcases hchi_pm p with hc | hc <;> rw [hsd, hc] <;> linarith
  · by_cases hpa : p + a ∈ H
    · have hpb : p + b ∉ H := fun h => h4 ⟨hpa, h⟩
      have hpab : p + (a + b) ∉ H := fun h => h5 ⟨hpa, h⟩
      simp only [hp, hpa, hpb, hpab, ite_true, ite_false, mul_zero, zero_add, add_zero, sub_zero]
      rcases hsd_pm with hsd | hsd <;> rcases hchi_pm (p + a) with hc | hc <;> rw [hsd, hc] <;> linarith
    · by_cases hpb : p + b ∈ H
      · have hpab : p + (a + b) ∉ H := fun h => h6 ⟨hpb, h⟩
        simp only [hp, hpa, hpb, hpab, ite_true, ite_false, mul_zero, zero_add, sub_zero]
        rcases hsd_pm with hsd | hsd <;> rcases hchi_pm (p + b) with hc | hc <;> rw [hsd, hc] <;> linarith
      · by_cases hpab : p + (a + b) ∈ H
        · simp only [hp, hpa, hpb, hpab, ite_true, ite_false, mul_zero, zero_add, zero_sub]
          rcases hsd_pm with hsd | hsd <;> rcases hchi_pm (p + (a + b)) with hc | hc <;> rw [hsd, hc] <;> linarith
        · simp only [hp, hpa, hpb, hpab, ite_false, mul_zero, add_zero, sub_zero]
          linarith

lemma quad_full_err_ge {n : ℕ} (a b p : Vec n) (d : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (2 ^ n : ℤ) ≤ 4 * ((Finset.univ.filter (fun x : Vec n =>
      dotProduct a x * dotProduct b x ≠ dotProduct p x + d)).card : ℤ) := by
  have hab0 : a + b ≠ 0 := by
    intro h; apply hab; ext i
    have hi := congrFun h i; simp only [Pi.add_apply, Pi.zero_apply] at hi
    rcases zmod2_cases (a i) with h1 | h1 <;> rcases zmod2_cases (b i) with h2 | h2 <;> simp [h1, h2] at hi ⊢
  have h := quad_coset_err_ge (⊥ : Submodule F (Vec n)) 0 a b p d
    (by simpa using ha) (by simpa using hb) (by simpa using hab0)
  have hperp : perpSub (⊥ : Submodule F (Vec n)) = ⊤ := by
    ext x; simp [perpSub]
  have hcard1 : Fintype.card (perpSub (⊥ : Submodule F (Vec n))) = 2 ^ n := by
    have hc := card_perpSub (⊥ : Submodule F (Vec n))
    simpa using hc
  have hcard2 : (Finset.univ.filter (fun y : perpSub (⊥ : Submodule F (Vec n)) =>
      dotProduct a (0 + y.1) * dotProduct b (0 + y.1) ≠ dotProduct p (0 + y.1) + d)).card =
      (Finset.univ.filter (fun x : Vec n =>
      dotProduct a x * dotProduct b x ≠ dotProduct p x + d)).card := by
    refine Finset.card_bij (fun y _ => y.1) ?_ ?_ ?_
    · intro y hy; simp only [Finset.mem_filter, Finset.mem_univ, true_and, zero_add] at hy ⊢; exact hy
    · intro y1 _ y2 _ h; exact Subtype.ext h
    · intro x hx
      refine ⟨⟨x, by rw [hperp]; trivial⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, zero_add] at hx ⊢; exact hx
  rw [hcard1, hcard2] at h
  simpa using h

lemma quad_full_err_eq_iff {n : ℕ} (a b p : Vec n) (d : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    4 * ((Finset.univ.filter (fun x : Vec n =>
      dotProduct a x * dotProduct b x ≠ dotProduct p x + d)).card : ℤ) = (2 ^ n : ℤ) ↔
    ∃ α β : F, p = bestP a b α β ∧ d = bestD α β := by
  have hab0 : a + b ≠ 0 := by
    intro h; apply hab; ext i
    have hi := congrFun h i; simp only [Pi.add_apply, Pi.zero_apply] at hi
    rcases zmod2_cases (a i) with h1 | h1 <;> rcases zmod2_cases (b i) with h2 | h2 <;> simp [h1, h2] at hi ⊢
  have hq : ∀ x : Vec n, 2 * signZ (dotProduct a x * dotProduct b x) =
      1 + chi a x + chi b x - chi (a + b) x := by
    intro x; simp only [signZ, chi, add_dotProduct]
    rcases zmod2_cases (dotProduct a x) with h1 | h1 <;>
    rcases zmod2_cases (dotProduct b x) with h2 | h2 <;>
    (simp [h1, h2]; try decide)
  have herr : ∀ x : Vec n,
      (4 : ℤ) * (if dotProduct a x * dotProduct b x ≠ dotProduct p x + d then 1 else 0) =
        2 - signZ d * (chi p x + chi (p + a) x + chi (p + b) x - chi (p + (a + b)) x) := by
    intro x
    have h1 : (2 : ℤ) * (if dotProduct a x * dotProduct b x ≠ dotProduct p x + d then 1 else 0) =
        1 - signZ (dotProduct a x * dotProduct b x) * (signZ d * chi p x) := by
      have : signZ d * chi p x = signZ (dotProduct p x + d) := by
        rw [signZ_add, mul_comm]; congr 1
      rw [this]
      rcases zmod2_cases (dotProduct a x * dotProduct b x) with h1 | h1 <;>
      rcases zmod2_cases (dotProduct p x + d) with h2 | h2 <;>
      simp [signZ, h1, h2]
    have h2 : (4 : ℤ) * (if dotProduct a x * dotProduct b x ≠ dotProduct p x + d then 1 else 0) =
        2 - signZ d * chi p x * (1 + chi a x + chi b x - chi (a + b) x) := by
      calc (4 : ℤ) * (if dotProduct a x * dotProduct b x ≠ dotProduct p x + d then 1 else 0)
          = 2 * (2 * (if dotProduct a x * dotProduct b x ≠ dotProduct p x + d then 1 else 0)) := by ring
        _ = 2 - (2 * signZ (dotProduct a x * dotProduct b x)) * (signZ d * chi p x) := by rw [h1]; ring
        _ = 2 - signZ d * chi p x * (1 + chi a x + chi b x - chi (a + b) x) := by rw [hq]; ring
    rw [h2]
    simp only [chi_add_left]
    ring
  have hsum : 4 * ((Finset.univ.filter (fun x : Vec n =>
      dotProduct a x * dotProduct b x ≠ dotProduct p x + d)).card : ℤ) =
      2 * (2 ^ n : ℤ) - signZ d * (
        (if p = 0 then (2 ^ n : ℤ) else 0) +
        (if p + a = 0 then (2 ^ n : ℤ) else 0) +
        (if p + b = 0 then (2 ^ n : ℤ) else 0) -
        (if p + (a + b) = 0 then (2 ^ n : ℤ) else 0)) := by
    have hcard : ((Finset.univ.filter (fun x : Vec n =>
        dotProduct a x * dotProduct b x ≠ dotProduct p x + d)).card : ℤ) =
        ∑ x : Vec n, (if dotProduct a x * dotProduct b x ≠ dotProduct p x + d then (1 : ℤ) else 0) := by
      rw [Finset.card_filter]; simp
    rw [hcard, Finset.mul_sum]
    simp_rw [herr]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [mul_comm _ (2 : ℤ)]
    congr 1
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      sum_chi, sum_chi, sum_chi, sum_chi]
  have h2pos : (0 : ℤ) < 2 ^ n := by positivity
  rw [hsum]
  constructor
  · intro heq
    by_cases hp0 : p = 0
    · subst p
      simp only [ite_true, zero_add, ha, hb, hab0, ite_false, add_zero, sub_zero] at heq
      have hd : d = 0 := by
        rcases zmod2_cases d with rfl | rfl
        · rfl
        · simp only [signZ, one_ne_zero, ite_false] at heq; linarith
      exact ⟨1, 1, by simp [bestP], by simp [bestD, hd]⟩
    · by_cases hpa : p + a = 0
      · have hp_eq : p = a := by
          ext i; have hi := congrFun hpa i; simp only [Pi.add_apply, Pi.zero_apply] at hi
          rcases zmod2_cases (p i) with h1 | h1 <;> rcases zmod2_cases (a i) with h2 | h2 <;>
          (simp [h1, h2] at hi ⊢; try exact absurd hi (by decide))
        rw [hp_eq] at heq ⊢
        have hpb : a + b ≠ 0 := hab0
        have hpab : a + (a + b) ≠ 0 := by rwa [← add_assoc, vec_add_self, zero_add]
        simp only [ha, vec_add_self, hpb, hpab, ite_true, ite_false, zero_add, add_zero, sub_zero] at heq
        have hd : d = 0 := by
          rcases zmod2_cases d with rfl | rfl
          · rfl
          · simp only [signZ, one_ne_zero, ite_false] at heq; linarith
        exact ⟨1, 0, by simp [bestP], by simp [bestD, hd]⟩
      · by_cases hpb : p + b = 0
        · have hp_eq : p = b := by
            ext i; have hi := congrFun hpb i; simp only [Pi.add_apply, Pi.zero_apply] at hi
            rcases zmod2_cases (p i) with h1 | h1 <;> rcases zmod2_cases (b i) with h2 | h2 <;>
            (simp [h1, h2] at hi ⊢; try exact absurd hi (by decide))
          rw [hp_eq] at heq ⊢
          have hba : b + a ≠ 0 := by rwa [add_comm]
          have hpab : b + (a + b) ≠ 0 := by
            have : b + (a + b) = a := by
              ext i; have := zmod2_add_self (b i); simp only [Pi.add_apply]; linear_combination this
            rwa [this]
          simp only [hb, hba, vec_add_self, hpab, ite_true, ite_false, zero_add, sub_zero] at heq
          have hd : d = 0 := by
            rcases zmod2_cases d with rfl | rfl
            · rfl
            · simp only [signZ, one_ne_zero, ite_false, zero_add, add_zero, sub_zero] at heq; linarith
          exact ⟨0, 1, by simp [bestP], by simp [bestD, hd]⟩
        · by_cases hpab : p + (a + b) = 0
          · have hp_eq : p = a + b := by
              calc p = p + 0 := (add_zero p).symm
                _ = p + ((a + b) + (a + b)) := by rw [vec_add_self]
                _ = (p + (a + b)) + (a + b) := (add_assoc _ _ _).symm
                _ = a + b := by rw [hpab, zero_add]
            rw [hp_eq] at heq ⊢
            have h1 : (a + b) + a ≠ 0 := by
              have : (a + b) + a = b := by
                ext i; have := zmod2_add_self (a i); simp only [Pi.add_apply]; linear_combination this
              rwa [this]
            have h2 : (a + b) + b ≠ 0 := by
              have : (a + b) + b = a := by
                ext i; have := zmod2_add_self (b i); simp only [Pi.add_apply]; linear_combination this
              rwa [this]
            simp only [hab0, h1, h2, vec_add_self, ite_true, ite_false, zero_add, zero_sub] at heq
            have hd : d = 1 := by
              rcases zmod2_cases d with rfl | rfl
              · simp only [signZ, ite_true] at heq; linarith
              · rfl
            exact ⟨0, 0, by simp [bestP], by simp [bestD, hd]⟩
          · simp only [hp0, hpa, hpb, hpab, ite_false, add_zero, sub_zero, mul_zero] at heq
            linarith
  · rintro ⟨α, β, rfl, rfl⟩
    rcases zmod2_cases α with rfl | rfl <;> rcases zmod2_cases β with rfl | rfl <;>
    simp only [bestP, bestD, signZ]
    · have h1 : (a + b) + a = b := by
        ext i; have := zmod2_add_self (a i); simp only [Pi.add_apply]; linear_combination this
      have h2 : (a + b) + b = a := by
        ext i; have := zmod2_add_self (b i); simp only [Pi.add_apply]; linear_combination this
      simp [hab0, h1, h2, hb, ha, vec_add_self]; ring
    · have h1 : b + a ≠ 0 := by rwa [add_comm]
      have h2 : b + (a + b) = a := by
        ext i; have := zmod2_add_self (b i); simp only [Pi.add_apply]; linear_combination this
      simp [hb, h1, vec_add_self, h2, ha]; ring
    · have h1 : a + (a + b) = b := by rw [← add_assoc, vec_add_self, zero_add]
      simp [ha, vec_add_self, hab0, h1, hb]; ring
    · simp [ha, hb, hab0]; ring

lemma best_injective {n : ℕ} {a b : Vec n} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective (fun ab : F × F => (bestP a b ab.1 ab.2, bestD ab.1 ab.2)) := by
  have hab0 : a + b ≠ 0 := by
    intro h; apply hab; ext i
    have hi := congrFun h i; simp only [Pi.add_apply, Pi.zero_apply] at hi
    rcases zmod2_cases (a i) with h1 | h1 <;> rcases zmod2_cases (b i) with h2 | h2 <;> simp [h1, h2] at hi ⊢
  rintro ⟨α1, β1⟩ ⟨α2, β2⟩ h
  have h1 : bestP a b α1 β1 = bestP a b α2 β2 := congrArg Prod.fst h
  have h2 : bestD α1 β1 = bestD α2 β2 := congrArg Prod.snd h
  rcases zmod2_cases α1 with rfl | rfl <;> rcases zmod2_cases β1 with rfl | rfl <;>
  rcases zmod2_cases α2 with rfl | rfl <;> rcases zmod2_cases β2 with rfl | rfl <;>
  simp only [bestP, bestD, ite_true, ite_false, true_and, false_and, and_true, and_false,
    one_ne_zero, zero_ne_one] at h1 h2 <;>
  first | rfl | exact absurd h1 ha | exact absurd h1.symm ha | exact absurd h1 hb | exact absurd h1.symm hb |
    exact absurd h1 hab | exact absurd h1.symm hab | exact absurd h1 hab0 | exact absurd h1.symm hab0 |
    exact absurd h2 (by decide)

def freqOf {n : ℕ} {I : Type*} (a b : I → Vec n) (i : I) : Finset (Vec n) :=
  {a i, b i, a i + b i}

def adjOf {n : ℕ} {I : Type*} (a b : I → Vec n) (i j : I) : Prop :=
  ∃ v ∈ freqOf a b i, v ∈ freqOf a b j

def compOf {n e : ℕ} (a b : Fin (4 * e) → Vec n) (i : Fin (4 * e)) : Finset (Fin (4 * e)) :=
  Finset.univ.filter (fun j => @decide (Relation.EqvGen (adjOf a b) i j) (Classical.propDecidable _) = true)

def partsOf {n e : ℕ} (a b : Fin (4 * e) → Vec n) : Finset (Finset (Fin (4 * e))) :=
  Finset.univ.image (compOf a b)

def spanOf {n : ℕ} {I : Type*} (a b : I → Vec n) (S : Finset I) : Submodule F (Vec n) :=
  Submodule.span F (↑(S.image a ∪ S.image b) : Set (Vec n))

def rkOf {n : ℕ} {I : Type*} (a b : I → Vec n) (S : Finset I) : ℕ :=
  Module.finrank F (spanOf a b S)

def freqsOf {n : ℕ} {I : Type*} (a b : I → Vec n) (S : Finset I) : Finset (Vec n) :=
  S.biUnion (freqOf a b)

def rowCoeff {n : ℕ} {I : Type*} (a b : I → Vec n) (α β : I → F) (i : I) (v : Vec n) : ℤ :=
  (if a i = v then signZ (α i) else 0) +
  (if b i = v then signZ (β i) else 0) +
  (if a i + b i = v then signZ (α i + β i) else 0)

def IsTiling {n : ℕ} {I : Type*} (a b : I → Vec n) (α β : I → F) (C : Finset I) : Prop :=
  ∀ v : Vec n, v ≠ 0 → (∑ i ∈ C, rowCoeff a b α β i v) = 0

lemma valid_ab_add_ne_zero {n : ℕ} {a b : Vec n} (hab : a ≠ b) : a + b ≠ 0 := by
  intro h; apply hab; ext i
  have hi := congrFun h i; simp only [Pi.add_apply, Pi.zero_apply] at hi
  rcases zmod2_cases (a i) with h1 | h1 <;> rcases zmod2_cases (b i) with h2 | h2 <;> simp [h1, h2] at hi ⊢

lemma freqOf_card {n : ℕ} {I : Type*} {a b : I → Vec n} {i : I}
    (h : a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) : (freqOf a b i).card = 3 := by
  have h1 : a i ≠ b i := h.2.2
  have h2 : a i ≠ a i + b i := fun heq => h.2.1 (by
    have := congrArg (a i + ·) heq
    simpa [← add_assoc, vec_add_self] using this.symm)
  have h3 : b i ≠ a i + b i := fun heq => h.1 (by
    have := congrArg (· + b i) heq
    simpa [add_assoc, vec_add_self] using this.symm)
  simp [freqOf, h1, h2, h3]

lemma rowCoeff_eq_zero_of_not_mem {n : ℕ} {I : Type*} {a b : I → Vec n} {α β : I → F} {i : I} {v : Vec n}
    (hv : v ∉ freqOf a b i) : rowCoeff a b α β i v = 0 := by
  simp only [freqOf, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  simp [rowCoeff, Ne.symm hv.1, Ne.symm hv.2.1, Ne.symm hv.2.2]

lemma rowCoeff_pm_one {n : ℕ} {I : Type*} {a b : I → Vec n} {α β : I → F} {i : I} {v : Vec n}
    (h : a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) (hv : v ∈ freqOf a b i) :
    rowCoeff a b α β i v = 1 ∨ rowCoeff a b α β i v = -1 := by
  have h1 : a i ≠ b i := h.2.2
  have h2 : a i ≠ a i + b i := fun heq => h.2.1 (by
    have := congrArg (a i + ·) heq
    simpa [← add_assoc, vec_add_self] using this.symm)
  have h3 : b i ≠ a i + b i := fun heq => h.1 (by
    have := congrArg (· + b i) heq
    simpa [add_assoc, vec_add_self] using this.symm)
  simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · simp only [rowCoeff, h1.symm, h2.symm, ite_true, ite_false, add_zero, signZ]; split_ifs <;> simp
  · simp only [rowCoeff, h1, h3.symm, ite_true, ite_false, zero_add, add_zero, signZ]; split_ifs <;> simp
  · simp only [rowCoeff, h2, h3, ite_true, ite_false, zero_add, signZ]; split_ifs <;> simp

lemma four_mul_coset_sum {n : ℕ} {I : Type*} (a b : I → Vec n) (α β : I → F) (C : Finset I) (x : Vec n) :
    (4 : ℤ) * ((C.filter (fun i => dotProduct (a i) x = α i ∧ dotProduct (b i) x = β i)).card : ℤ) =
      (C.card : ℤ) + ∑ v ∈ freqsOf a b C, (∑ i ∈ C, rowCoeff a b α β i v) * chi v x := by
  have h1 : ((C.filter (fun i => dotProduct (a i) x = α i ∧ dotProduct (b i) x = β i)).card : ℤ) =
      ∑ i ∈ C, (if dotProduct (a i) x = α i ∧ dotProduct (b i) x = β i then (1 : ℤ) else 0) := by
    rw [Finset.card_filter]; simp
  rw [h1, Finset.mul_sum]
  simp_rw [four_mul_coset_ind]
  have hsplit : ∀ i ∈ C,
      (1 + signZ (α i) * chi (a i) x + signZ (β i) * chi (b i) x + signZ (α i + β i) * chi (a i + b i) x) =
      1 + ∑ v ∈ freqsOf a b C, rowCoeff a b α β i v * chi v x := by
    intro i hi
    have ha_mem : a i ∈ freqsOf a b C := Finset.mem_biUnion.mpr ⟨i, hi, by simp [freqOf]⟩
    have hb_mem : b i ∈ freqsOf a b C := Finset.mem_biUnion.mpr ⟨i, hi, by simp [freqOf]⟩
    have hab_mem : a i + b i ∈ freqsOf a b C := Finset.mem_biUnion.mpr ⟨i, hi, by simp [freqOf]⟩
    simp only [rowCoeff, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
    have hfa : (∑ v ∈ freqsOf a b C, if a i = v then signZ (α i) * chi v x else 0) = signZ (α i) * chi (a i) x := by
      rw [Finset.sum_ite_eq]; simp [ha_mem]
    have hfb : (∑ v ∈ freqsOf a b C, if b i = v then signZ (β i) * chi v x else 0) = signZ (β i) * chi (b i) x := by
      rw [Finset.sum_ite_eq]; simp [hb_mem]
    have hfab : (∑ v ∈ freqsOf a b C, if a i + b i = v then signZ (α i + β i) * chi v x else 0) = signZ (α i + β i) * chi (a i + b i) x := by
      rw [Finset.sum_ite_eq]; simp [hab_mem]
    rw [hfa, hfb, hfab]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul]

lemma isTiling_iff_const_count {n : ℕ} {I : Type*} (a b : I → Vec n) (α β : I → F) (C : Finset I)
    (hvalid : ∀ i ∈ C, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) :
    IsTiling a b α β C ↔
      ∀ x : Vec n, (4 : ℤ) * ((C.filter (fun i => dotProduct (a i) x = α i ∧ dotProduct (b i) x = β i)).card : ℤ) = (C.card : ℤ) := by
  constructor
  · intro ht x
    rw [four_mul_coset_sum]
    have hz : ∀ v ∈ freqsOf a b C, (∑ i ∈ C, rowCoeff a b α β i v) * chi v x = 0 := by
      intro v hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
      have hv0 : v ≠ 0 := by
        have hvi' := hvalid i hi
        simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hvi
        rcases hvi with rfl | rfl | rfl
        · exact hvi'.1
        · exact hvi'.2.1
        · exact valid_ab_add_ne_zero hvi'.2.2
      rw [ht v hv0, zero_mul]
    rw [Finset.sum_eq_zero hz, add_zero]
  · intro hconst v hv

    have hsum0 : (∑ x : Vec n,
        ((4 : ℤ) * ((C.filter (fun i => dotProduct (a i) x = α i ∧ dotProduct (b i) x = β i)).card : ℤ) - (C.card : ℤ)) * chi v x) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [hconst x, sub_self, zero_mul]
    have hsum1 : (∑ x : Vec n,
        ((4 : ℤ) * ((C.filter (fun i => dotProduct (a i) x = α i ∧ dotProduct (b i) x = β i)).card : ℤ) - (C.card : ℤ)) * chi v x) =
        (if v ∈ freqsOf a b C then (∑ i ∈ C, rowCoeff a b α β i v) * (2 ^ n : ℤ) else 0) := by
      have hsub1 : ∀ x : Vec n,
          ((4 : ℤ) * ((C.filter (fun i => dotProduct (a i) x = α i ∧ dotProduct (b i) x = β i)).card : ℤ) - (C.card : ℤ)) * chi v x =
          ∑ u ∈ freqsOf a b C, (∑ i ∈ C, rowCoeff a b α β i u) * chi u x * chi v x := by
        intro x
        rw [four_mul_coset_sum, add_sub_cancel_left, Finset.sum_mul]
      simp_rw [hsub1]
      rw [Finset.sum_comm]
      have hinner : ∀ u ∈ freqsOf a b C,
          (∑ x : Vec n, (∑ i ∈ C, rowCoeff a b α β i u) * chi u x * chi v x) =
            (if u = v then (∑ i ∈ C, rowCoeff a b α β i u) * (2 ^ n : ℤ) else 0) := by
        intro u _
        have : ∀ x : Vec n, (∑ i ∈ C, rowCoeff a b α β i u) * chi u x * chi v x =
            (∑ i ∈ C, rowCoeff a b α β i u) * chi (u + v) x := fun x => by
          rw [chi_add_left]; ring
        simp_rw [this, ← Finset.mul_sum, sum_chi]
        have huv : (u + v = 0) ↔ (u = v) := by
          constructor
          · intro h; ext j; have hj := congrFun h j; simp only [Pi.add_apply, Pi.zero_apply] at hj
            rcases zmod2_cases (u j) with h1 | h1 <;> rcases zmod2_cases (v j) with h2 | h2 <;>
            (simp [h1, h2] at hj ⊢; try exact absurd hj (by decide))
          · rintro rfl; exact vec_add_self u
        simp only [huv]; split_ifs <;> ring
      rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
    rw [hsum1] at hsum0
    by_cases hvmem : v ∈ freqsOf a b C
    · rw [if_pos hvmem] at hsum0
      have h2pos : (2 ^ n : ℤ) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hsum0).resolve_right h2pos
    · refine Finset.sum_eq_zero fun i hi => ?_
      apply rowCoeff_eq_zero_of_not_mem
      intro hvi
      exact hvmem (Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩)

lemma isTiling_deg_even_pos {n : ℕ} {I : Type*} {a b : I → Vec n} {α β : I → F} {C : Finset I}
    (hvalid : ∀ i ∈ C, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (ht : IsTiling a b α β C) {v : Vec n} (hv : v ∈ freqsOf a b C) :
    2 ∣ (C.filter (fun i => v ∈ freqOf a b i)).card ∧
    2 ≤ (C.filter (fun i => v ∈ freqOf a b i)).card := by
  obtain ⟨i0, hi0, hvi0⟩ := Finset.mem_biUnion.mp hv
  have hv0 : v ≠ 0 := by
    have hvi' := hvalid i0 hi0
    simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hvi0
    rcases hvi0 with rfl | rfl | rfl
    · exact hvi'.1
    · exact hvi'.2.1
    · exact valid_ab_add_ne_zero hvi'.2.2
  have hsum := ht v hv0
  let S := C.filter (fun i => v ∈ freqOf a b i)
  have hsumS : (∑ i ∈ S, rowCoeff a b α β i v) = 0 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ C) fun i hi hni => ?_
    simp only [S, Finset.mem_filter, not_and] at hni
    exact rowCoeff_eq_zero_of_not_mem (hni hi)
  have hevenZ : (2 : ℤ) ∣ (S.card : ℤ) := by
    have h1 : (∑ i ∈ S, (rowCoeff a b α β i v + 1)) % 2 = 0 := by
      have : ∀ i ∈ S, (2 : ℤ) ∣ (rowCoeff a b α β i v + 1) := by
        intro i hi
        have hiC := (Finset.mem_filter.mp hi).1
        have hvi := (Finset.mem_filter.mp hi).2
        rcases rowCoeff_pm_one (hvalid i hiC) hvi with h | h <;> rw [h] <;> decide
      exact Int.emod_eq_zero_of_dvd (Finset.dvd_sum this)
    rw [Finset.sum_add_distrib, hsumS, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
    exact Int.dvd_of_emod_eq_zero h1
  have heven : 2 ∣ S.card := by
    exact_mod_cast hevenZ
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i0, Finset.mem_filter.mpr ⟨hi0, hvi0⟩⟩
  refine ⟨heven, ?_⟩
  obtain ⟨m, hm⟩ := heven
  dsimp only [S] at hm hpos
  omega

lemma compOf_mem_self {n e : ℕ} (a b : Fin (4 * e) → Vec n) (i : Fin (4 * e)) :
    i ∈ compOf a b i := by
  simp [compOf, Relation.EqvGen.refl]

lemma compOf_eq_of_mem {n e : ℕ} (a b : Fin (4 * e) → Vec n) {i j : Fin (4 * e)}
    (h : j ∈ compOf a b i) : compOf a b j = compOf a b i := by
  simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at h
  ext k
  simp only [compOf, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
  exact ⟨fun hjk => Relation.EqvGen.trans _ _ _ h hjk,
         fun hik => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hik⟩

lemma partsOf_disjoint {n e : ℕ} (a b : Fin (4 * e) → Vec n) {C1 C2 : Finset (Fin (4 * e))}
    (h1 : C1 ∈ partsOf a b) (h2 : C2 ∈ partsOf a b) (hne : C1 ≠ C2) : Disjoint C1 C2 := by
  obtain ⟨i1, _, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨i2, _, rfl⟩ := Finset.mem_image.mp h2
  rw [Finset.disjoint_left]
  intro j hj1 hj2
  exact hne ((compOf_eq_of_mem a b hj1).symm.trans (compOf_eq_of_mem a b hj2))

lemma partsOf_biUnion {n e : ℕ} (a b : Fin (4 * e) → Vec n) :
    (partsOf a b).biUnion id = Finset.univ := by
  ext i
  simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
  exact ⟨compOf a b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, compOf_mem_self a b i⟩

lemma partsOf_sum_card {n e : ℕ} (a b : Fin (4 * e) → Vec n) :
    (∑ C ∈ partsOf a b, C.card) = 4 * e := by
  have hdisj : (partsOf a b : Set (Finset (Fin (4 * e)))).PairwiseDisjoint id := by
    intro C1 h1 C2 h2 hne
    exact partsOf_disjoint a b h1 h2 hne
  have h := Finset.card_biUnion hdisj
  simp only [id_eq, partsOf_biUnion] at h
  rw [← h]
  simp

lemma partsOf_freq_disjoint {n e : ℕ} (a b : Fin (4 * e) → Vec n) {C1 C2 : Finset (Fin (4 * e))}
    (h1 : C1 ∈ partsOf a b) (h2 : C2 ∈ partsOf a b) (hne : C1 ≠ C2) :
    Disjoint (freqsOf a b C1) (freqsOf a b C2) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  obtain ⟨i1, hi1, hvi1⟩ := Finset.mem_biUnion.mp hv1
  obtain ⟨i2, hi2, hvi2⟩ := Finset.mem_biUnion.mp hv2
  obtain ⟨r1, _, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨r2, _, rfl⟩ := Finset.mem_image.mp h2
  have hadj : adjOf a b i1 i2 := ⟨v, hvi1, hvi2⟩
  have heqv : Relation.EqvGen (adjOf a b) i1 i2 := Relation.EqvGen.rel _ _ hadj
  have hi2_in : i2 ∈ compOf a b i1 := by simp [compOf, heqv]
  have heq1 : compOf a b i1 = compOf a b r1 := compOf_eq_of_mem a b hi1
  have heq2 : compOf a b i2 = compOf a b r2 := compOf_eq_of_mem a b hi2
  have heq3 : compOf a b i2 = compOf a b i1 := compOf_eq_of_mem a b hi2_in
  exact hne (heq1.symm.trans (heq3.symm.trans heq2))

lemma isTiling_restrict_part {n e : ℕ} {a b : Fin (4 * e) → Vec n} {α β : Fin (4 * e) → F}
    (ht : IsTiling a b α β Finset.univ) {C : Finset (Fin (4 * e))} (hC : C ∈ partsOf a b) :
    IsTiling a b α β C := by
  intro v hv0
  by_cases hv : v ∈ freqsOf a b C
  · have htot := ht v hv0
    have hdisj : (partsOf a b : Set (Finset (Fin (4 * e)))).PairwiseDisjoint id := fun C1 h1 C2 h2 hne =>
      partsOf_disjoint a b h1 h2 hne
    rw [← partsOf_biUnion a b, Finset.sum_biUnion hdisj] at htot
    simp only [id_eq] at htot
    have hzero : ∀ C' ∈ partsOf a b, C' ≠ C → (∑ i ∈ C', rowCoeff a b α β i v) = 0 := by
      intro C' hC' hne
      refine Finset.sum_eq_zero fun i hi => rowCoeff_eq_zero_of_not_mem fun hvi => ?_
      have hv' : v ∈ freqsOf a b C' := Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩
      exact Finset.disjoint_left.mp (partsOf_freq_disjoint a b hC hC' hne.symm) hv hv'
    rw [Finset.sum_eq_single C hzero (fun h => absurd hC h)] at htot
    exact htot
  · refine Finset.sum_eq_zero fun i hi => rowCoeff_eq_zero_of_not_mem fun hvi =>
      hv (Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩)

lemma part_card_dvd_four {n e : ℕ} {a b : Fin (4 * e) → Vec n} {α β : Fin (4 * e) → F}
    (hvalid : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (ht : IsTiling a b α β Finset.univ) {C : Finset (Fin (4 * e))} (hC : C ∈ partsOf a b) :
    ∃ c : ℕ, C.card = 4 * c ∧ 1 ≤ c := by
  have htC := isTiling_restrict_part ht hC
  have hconst := (isTiling_iff_const_count a b α β C (fun i _ => hvalid i)).mp htC 0
  have hnat : 4 * (C.filter (fun i => dotProduct (a i) 0 = α i ∧ dotProduct (b i) 0 = β i)).card = C.card := by
    exact_mod_cast hconst
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hC
  have hpos : 0 < (compOf a b r).card := Finset.card_pos.mpr ⟨r, compOf_mem_self a b r⟩
  refine ⟨(compOf a b r).filter (fun i => dotProduct (a i) 0 = α i ∧ dotProduct (b i) 0 = β i) |>.card, hnat.symm, ?_⟩
  omega

lemma good_iff_tiling {n e : ℕ} {a b : Fin (4 * e) → Vec n}
    (hvalid : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (P : Fin (4 * e) → Vec n) (d : Fin (4 * e) → F) :
    (∀ x : Vec n, (Finset.univ.filter (fun i : Fin (4 * e) =>
      dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card ≤ e) ↔
    ∃ α β : Fin (4 * e) → F,
      (∀ i, P i = bestP (a i) (b i) (α i) (β i) ∧ d i = bestD (α i) (β i)) ∧
      IsTiling a b α β Finset.univ := by
  constructor
  · intro hle
    have hsum_le : (∑ x : Vec n,
        ((Finset.univ.filter (fun i : Fin (4 * e) =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ)) ≤
        (e : ℤ) * (2 ^ n : ℤ) := by
      calc (∑ x : Vec n, ((Finset.univ.filter (fun i : Fin (4 * e) =>
              dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ))
          ≤ ∑ _x : Vec n, (e : ℤ) := Finset.sum_le_sum fun x _ => by exact_mod_cast hle x
        _ = (2 ^ n : ℤ) * (e : ℤ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
              Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            simp
        _ = (e : ℤ) * (2 ^ n : ℤ) := mul_comm _ _
    have hswap : (∑ x : Vec n,
        ((Finset.univ.filter (fun i : Fin (4 * e) =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ)) =
        ∑ i : Fin (4 * e),
        ((Finset.univ.filter (fun x : Vec n =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ) := by
      simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact Finset.sum_comm
    have hrow_ge : ∀ i : Fin (4 * e), (2 ^ n : ℤ) ≤
        4 * ((Finset.univ.filter (fun x : Vec n =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ) :=
      fun i => quad_full_err_ge (a i) (b i) (P i) (d i) (hvalid i).1 (hvalid i).2.1 (hvalid i).2.2
    have hsum_ge : (4 * e : ℤ) * (2 ^ n : ℤ) ≤
        ∑ i : Fin (4 * e), 4 * ((Finset.univ.filter (fun x : Vec n =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ) := by
      calc (4 * e : ℤ) * (2 ^ n : ℤ)
          = ∑ _i : Fin (4 * e), (2 ^ n : ℤ) := by simp [Finset.sum_const]
        _ ≤ _ := Finset.sum_le_sum fun i _ => hrow_ge i
    have hsum_eq : (∑ i : Fin (4 * e), 4 * ((Finset.univ.filter (fun x : Vec n =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ)) =
        ∑ _i : Fin (4 * e), (2 ^ n : ℤ) := by
      have h1 : (∑ i : Fin (4 * e), 4 * ((Finset.univ.filter (fun x : Vec n =>
            dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ)) ≤
          (4 * e : ℤ) * (2 ^ n : ℤ) := by
        rw [← Finset.mul_sum, ← hswap]; linarith
      have h2 : (∑ _i : Fin (4 * e), (2 ^ n : ℤ)) = (4 * e : ℤ) * (2 ^ n : ℤ) := by
        simp [Finset.sum_const]
      linarith
    have hrow_eq : ∀ i : Fin (4 * e),
        4 * ((Finset.univ.filter (fun x : Vec n =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ) = (2 ^ n : ℤ) := by
      intro i
      by_contra hne
      have hlt : (2 ^ n : ℤ) < 4 * ((Finset.univ.filter (fun x : Vec n =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ) :=
        lt_of_le_of_ne (hrow_ge i) (Ne.symm hne)
      have hstrict : (∑ _j : Fin (4 * e), (2 ^ n : ℤ)) <
          ∑ j : Fin (4 * e), 4 * ((Finset.univ.filter (fun x : Vec n =>
            dotProduct (a j) x * dotProduct (b j) x ≠ dotProduct (P j) x + d j)).card : ℤ) :=
        Finset.sum_lt_sum (fun j _ => hrow_ge j) ⟨i, Finset.mem_univ i, hlt⟩
      linarith
    have hex : ∀ i : Fin (4 * e), ∃ α β : F, P i = bestP (a i) (b i) α β ∧ d i = bestD α β :=
      fun i => (quad_full_err_eq_iff (a i) (b i) (P i) (d i) (hvalid i).1 (hvalid i).2.1 (hvalid i).2.2).mp (hrow_eq i)
    choose α β hαβ using hex
    refine ⟨α, β, hαβ, ?_⟩
    rw [isTiling_iff_const_count a b α β Finset.univ (fun i _ => hvalid i)]
    have hx_eq : ∀ x : Vec n, ((Finset.univ.filter (fun i : Fin (4 * e) =>
        dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ) = (e : ℤ) := by
      intro x
      by_contra hne
      have hlt : ((Finset.univ.filter (fun i : Fin (4 * e) =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)).card : ℤ) < (e : ℤ) :=
        lt_of_le_of_ne (by exact_mod_cast hle x) hne
      have hstrict : (∑ y : Vec n, ((Finset.univ.filter (fun i : Fin (4 * e) =>
          dotProduct (a i) y * dotProduct (b i) y ≠ dotProduct (P i) y + d i)).card : ℤ)) <
          ∑ _y : Vec n, (e : ℤ) :=
        Finset.sum_lt_sum (fun y _ => by exact_mod_cast hle y) ⟨x, Finset.mem_univ x, hlt⟩
      have htot_eq : (∑ _y : Vec n, (e : ℤ)) = (e : ℤ) * (2 ^ n : ℤ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        simp [mul_comm]
      rw [hswap] at hstrict
      have h4 : 4 * (∑ i : Fin (4 * e), ((Finset.univ.filter (fun y : Vec n =>
          dotProduct (a i) y * dotProduct (b i) y ≠ dotProduct (P i) y + d i)).card : ℤ)) =
          (4 * e : ℤ) * (2 ^ n : ℤ) := by
        rw [Finset.mul_sum, hsum_eq]; simp [Finset.sum_const]
      linarith
    intro x
    have hfilt : (Finset.univ.filter (fun i : Fin (4 * e) => dotProduct (a i) x = α i ∧ dotProduct (b i) x = β i)) =
        (Finset.univ.filter (fun i : Fin (4 * e) => dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hαβ i).1, (hαβ i).2, ne_comm]
      exact (best_err_iff (a i) (b i) x (α i) (β i)).symm
    rw [hfilt, hx_eq x]
    simp
  · rintro ⟨α, β, hαβ, ht⟩ x
    have hconst := (isTiling_iff_const_count a b α β Finset.univ (fun i _ => hvalid i)).mp ht x
    have hfilt : (Finset.univ.filter (fun i : Fin (4 * e) => dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P i) x + d i)) =
        (Finset.univ.filter (fun i : Fin (4 * e) => dotProduct (a i) x = α i ∧ dotProduct (b i) x = β i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [(hαβ i).1, (hαβ i).2, ne_comm]
      exact best_err_iff (a i) (b i) x (α i) (β i)
    rw [hfilt]
    have hnat : 4 * (Finset.univ.filter (fun i : Fin (4 * e) => dotProduct (a i) x = α i ∧ dotProduct (b i) x = β i)).card = 4 * e := by
      have : ((Finset.univ : Finset (Fin (4 * e))).card : ℤ) = (4 * e : ℤ) := by simp
      rw [this] at hconst
      exact_mod_cast hconst
    omega

lemma freqOf_subset_spanOf {n : ℕ} {I : Type*} (a b : I → Vec n) {S : Finset I} {i : I}
    (hi : i ∈ S) : ∀ v ∈ freqOf a b i, v ∈ spanOf a b S := by
  intro v hv
  have ha : a i ∈ spanOf a b S :=
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem a hi)))
  have hb : b i ∈ spanOf a b S :=
    Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem b hi)))
  simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact (spanOf a b S).add_mem ha hb

lemma freqsOf_subset_spanOf {n : ℕ} {I : Type*} (a b : I → Vec n) (S : Finset I) :
    ∀ v ∈ freqsOf a b S, v ∈ spanOf a b S := by
  intro v hv
  obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
  exact freqOf_subset_spanOf a b hi v hvi

lemma spanOf_insert {n : ℕ} {I : Type*} (a b : I → Vec n) (S : Finset I) (i : I) :
    spanOf a b (insert i S) = spanOf a b S ⊔ Submodule.span F {a i, b i} := by
  unfold spanOf
  rw [Finset.image_insert, Finset.image_insert]
  have hset : (↑(insert (a i) (S.image a) ∪ insert (b i) (S.image b)) : Set (Vec n)) =
      (↑(S.image a ∪ S.image b) : Set (Vec n)) ∪ {a i, b i} := by
    ext v; simp [or_comm, or_left_comm, or_assoc]
  rw [hset, Submodule.span_union]

lemma rkOf_singleton {n : ℕ} {I : Type*} (a b : I → Vec n) (i : I)
    (h : a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) : rkOf a b {i} = 2 := by
  unfold rkOf spanOf
  have hset : (↑(({i} : Finset I).image a ∪ ({i} : Finset I).image b) : Set (Vec n)) = {a i, b i} := by
    ext v; simp
  rw [hset]
  have hli : LinearIndependent F ![a i, b i] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hsum : g 0 • a i + g 1 • b i = 0 := by
      simpa [Fin.sum_univ_two] using hg
    have h01 : g 0 = 0 ∧ g 1 = 0 := by
      rcases zmod2_cases (g 0) with h0 | h0 <;> rcases zmod2_cases (g 1) with h1 | h1
      · exact ⟨h0, h1⟩
      · simp [h0, h1] at hsum; exact absurd hsum h.2.1
      · simp [h0, h1] at hsum; exact absurd hsum h.1
      · simp [h0, h1] at hsum; exact absurd hsum (valid_ab_add_ne_zero h.2.2)
    fin_cases j
    · exact h01.1
    · exact h01.2
  have hrange : Set.range ![a i, b i] = ({a i, b i} : Set (Vec n)) := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm]
  rw [← hrange, finrank_span_eq_card hli]
  simp

lemma rkOf_insert_step {n : ℕ} {I : Type*} (a b : I → Vec n) (S : Finset I) (i : I)
    (hvalid : a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hconn : ∃ v ∈ freqOf a b i, v ∈ spanOf a b S) :
    (rkOf a b (insert i S) = rkOf a b S) ∨
    (rkOf a b (insert i S) = rkOf a b S + 1 ∧
      (freqsOf a b S).card + 2 ≤ (freqsOf a b (insert i S)).card) := by
  have hle_rk : rkOf a b S ≤ rkOf a b (insert i S) :=
    Submodule.finrank_mono (by rw [spanOf_insert]; exact le_sup_left)
  obtain ⟨v0, hv0_freq, hv0_span⟩ := hconn
  have hspan_i : Submodule.span F {a i, b i} ≤ spanOf a b S ⊔ Submodule.span F {a i} ∨
      Submodule.span F {a i, b i} ≤ spanOf a b S ⊔ Submodule.span F {b i} := by
    simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv0_freq
    rcases hv0_freq with rfl | rfl | rfl
    · right
      rw [Submodule.span_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact Submodule.mem_sup_left hv0_span
      · exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    · left
      rw [Submodule.span_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact Submodule.mem_sup_right (Submodule.subset_span rfl)
      · exact Submodule.mem_sup_left hv0_span
    · left
      rw [Submodule.span_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl
      · exact Submodule.mem_sup_right (Submodule.subset_span rfl)
      · have hba : b i = (a i + b i) + a i := by
          ext j; have := zmod2_add_self (a i j); simp only [Pi.add_apply]; linear_combination -this
        rw [hba]
        exact (spanOf a b S ⊔ Submodule.span F {a i}).add_mem
          (Submodule.mem_sup_left hv0_span) (Submodule.mem_sup_right (Submodule.subset_span rfl))
  have hstep_le : rkOf a b (insert i S) ≤ rkOf a b S + 1 := by
    unfold rkOf
    rw [spanOf_insert]
    rcases hspan_i with h | h
    · have h1 : spanOf a b S ⊔ Submodule.span F {a i, b i} ≤ spanOf a b S ⊔ Submodule.span F {a i} :=
        sup_le le_sup_left h
      have h2 := Submodule.finrank_mono h1
      have h3 := Submodule.finrank_sup_add_finrank_inf_eq (spanOf a b S) (Submodule.span F {a i})
      have h4 : Module.finrank F (Submodule.span F {a i}) ≤ 1 := by
        rw [finrank_span_singleton hvalid.1]
      omega
    · have h1 : spanOf a b S ⊔ Submodule.span F {a i, b i} ≤ spanOf a b S ⊔ Submodule.span F {b i} :=
        sup_le le_sup_left h
      have h2 := Submodule.finrank_mono h1
      have h3 := Submodule.finrank_sup_add_finrank_inf_eq (spanOf a b S) (Submodule.span F {b i})
      have h4 : Module.finrank F (Submodule.span F {b i}) ≤ 1 := by
        rw [finrank_span_singleton hvalid.2.1]
      omega
  by_cases heq : rkOf a b (insert i S) = rkOf a b S
  · exact Or.inl heq
  · right
    have hrk1 : rkOf a b (insert i S) = rkOf a b S + 1 := by omega
    refine ⟨hrk1, ?_⟩

    have hnot_both : ¬ (a i ∈ spanOf a b S ∧ b i ∈ spanOf a b S) := by
      intro ⟨haS, hbS⟩
      have hle : spanOf a b (insert i S) ≤ spanOf a b S := by
        rw [spanOf_insert]
        refine sup_le le_rfl ?_
        rw [Submodule.span_le]
        intro u hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rcases hu with rfl | rfl <;> assumption
      have := Submodule.finrank_mono hle
      unfold rkOf at hrk1
      omega
    have htwo_out : ∃ u w : Vec n, u ≠ w ∧ u ∈ freqOf a b i ∧ w ∈ freqOf a b i ∧
        u ∉ spanOf a b S ∧ w ∉ spanOf a b S := by
      simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv0_freq
      rcases hv0_freq with rfl | rfl | rfl
      · have hb_out : b i ∉ spanOf a b S := fun hbS => hnot_both ⟨hv0_span, hbS⟩
        have hab_out : a i + b i ∉ spanOf a b S := fun habS => hb_out (by
          have := (spanOf a b S).add_mem hv0_span habS
          rwa [← add_assoc, vec_add_self, zero_add] at this)
        have hne : b i ≠ a i + b i := fun h => hvalid.1 (by
          have := congrArg (· + b i) h
          simpa [add_assoc, vec_add_self] using this.symm)
        exact ⟨b i, a i + b i, hne, by simp [freqOf], by simp [freqOf], hb_out, hab_out⟩
      · have ha_out : a i ∉ spanOf a b S := fun haS => hnot_both ⟨haS, hv0_span⟩
        have hab_out : a i + b i ∉ spanOf a b S := fun habS => ha_out (by
          have := (spanOf a b S).add_mem habS hv0_span
          rwa [add_assoc, vec_add_self, add_zero] at this)
        have hne : a i ≠ a i + b i := fun h => hvalid.2.1 (by
          have := congrArg (a i + ·) h
          simpa [← add_assoc, vec_add_self] using this.symm)
        exact ⟨a i, a i + b i, hne, by simp [freqOf], by simp [freqOf], ha_out, hab_out⟩
      · have ha_out : a i ∉ spanOf a b S := fun haS => hnot_both ⟨haS, by
          have := (spanOf a b S).add_mem haS hv0_span
          rwa [← add_assoc, vec_add_self, zero_add] at this⟩
        have hb_out : b i ∉ spanOf a b S := fun hbS => hnot_both ⟨by
          have := (spanOf a b S).add_mem hv0_span hbS
          rwa [add_assoc, vec_add_self, add_zero] at this, hbS⟩
        exact ⟨a i, b i, hvalid.2.2, by simp [freqOf], by simp [freqOf], ha_out, hb_out⟩
    obtain ⟨u, w, huw, hu_f, hw_f, hu_out, hw_out⟩ := htwo_out
    have hu_nmem : u ∉ freqsOf a b S := fun h => hu_out (freqsOf_subset_spanOf a b S u h)
    have hw_nmem : w ∉ freqsOf a b S := fun h => hw_out (freqsOf_subset_spanOf a b S w h)
    have hsub : insert u (insert w (freqsOf a b S)) ⊆ freqsOf a b (insert i S) := by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_insert_self i S, hu_f⟩
      · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_insert_self i S, hw_f⟩
      · obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp hz
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_insert_of_mem hj, hzj⟩
    have hcard_le := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp [huw, hu_nmem]),
      Finset.card_insert_of_notMem hw_nmem] at hcard_le
    omega

lemma two_rk_le_freqs_add_one {n : ℕ} {I : Type*} [Fintype I]
    (a b : I → Vec n) (C : Finset I)
    (hvalid : ∀ i ∈ C, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hconn : ∀ i ∈ C, ∀ j ∈ C, Relation.EqvGen (fun x y => x ∈ C ∧ y ∈ C ∧ adjOf a b x y) i j)
    (hne : C.Nonempty) :
    2 * rkOf a b C ≤ (freqsOf a b C).card + 1 := by
  let R : I → I → Prop := fun x y => x ∈ C ∧ y ∈ C ∧ adjOf a b x y
  have hmain : ∀ m : ℕ, ∀ S : Finset I, S ⊆ C → S.Nonempty →
      (C \ S).card = m → 2 * rkOf a b S ≤ (freqsOf a b S).card + 1 →
      2 * rkOf a b C ≤ (freqsOf a b C).card + 1 := by
    intro m
    induction m with
    | zero =>
      intro S hSC _ hdiff hS
      have hSC_eq : S = C := Finset.Subset.antisymm hSC (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hdiff))
      rwa [← hSC_eq]
    | succ m ih =>
      intro S hSC hSne hdiff hS
      have hbridge : ∃ i ∈ C \ S, ∃ j ∈ S, adjOf a b j i := by
        obtain ⟨j0, hj0⟩ := hSne
        obtain ⟨i0, hi0⟩ := Finset.card_pos.mp (by omega : 0 < (C \ S).card)
        have hi0C : i0 ∈ C := (Finset.mem_sdiff.mp hi0).1
        have heqv := hconn j0 (hSC hj0) i0 hi0C
        have hR_iff : ∀ x y : I, Relation.EqvGen R x y → (x ∈ C ↔ y ∈ C) := by
          intro x y hxy
          induction hxy with
          | rel _ _ h => exact ⟨fun _ => h.2.1, fun _ => h.1⟩
          | refl _ => exact Iff.rfl
          | symm _ _ _ ih => exact ih.symm
          | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
        have hR_mem : ∀ x y : I, Relation.EqvGen R x y → x ∈ C → y ∈ C :=
          fun x y hxy hx => (hR_iff x y hxy).mp hx
        have hcross : ∀ x y : I, Relation.EqvGen R x y →
            ((x ∈ S ∧ y ∈ C \ S) ∨ (y ∈ S ∧ x ∈ C \ S)) →
            ∃ u ∈ C \ S, ∃ v ∈ S, adjOf a b v u := by
          intro x y hxy
          induction hxy with
          | rel x y h =>
            rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
            · exact ⟨y, hy, x, hx, h.2.2⟩
            · obtain ⟨v, hvx, hvy⟩ := h.2.2
              exact ⟨x, hx, y, hy, ⟨v, hvy, hvx⟩⟩
          | refl x =>
            rintro (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> exact absurd hx (Finset.mem_sdiff.mp hy).2
          | symm x y _ ih_s =>
            rintro (h | h)
            · exact ih_s (Or.inr h)
            · exact ih_s (Or.inl h)
          | trans x y z hxy hyz ih1 ih2 =>
            rintro (⟨hx, hz⟩ | ⟨hz, hx⟩)
            · by_cases hyS : y ∈ S
              · exact ih2 (Or.inl ⟨hyS, hz⟩)
              · have hyC : y ∈ C := hR_mem x y hxy (hSC hx)
                exact ih1 (Or.inl ⟨hx, Finset.mem_sdiff.mpr ⟨hyC, hyS⟩⟩)
            · by_cases hyS : y ∈ S
              · exact ih1 (Or.inr ⟨hyS, hx⟩)
              · have hyC : y ∈ C := hR_mem z y (Relation.EqvGen.symm _ _ hyz) (hSC hz)
                exact ih2 (Or.inr ⟨hz, Finset.mem_sdiff.mpr ⟨hyC, hyS⟩⟩)
        exact hcross j0 i0 heqv (Or.inl ⟨hj0, hi0⟩)
      obtain ⟨i, hi_sdiff, j, hjS, v, hvj, hvi⟩ := hbridge
      have hiC : i ∈ C := (Finset.mem_sdiff.mp hi_sdiff).1
      have hS' : 2 * rkOf a b (insert i S) ≤ (freqsOf a b (insert i S)).card + 1 := by
        rcases rkOf_insert_step a b S i (hvalid i hiC) ⟨v, hvi, freqOf_subset_spanOf a b hjS v hvj⟩ with h1 | ⟨h1, h2⟩
        · have hmono : (freqsOf a b S).card ≤ (freqsOf a b (insert i S)).card :=
            Finset.card_le_card (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.subset_insert i S))
          rw [h1]; omega
        · rw [h1]; omega
      have hdiff' : (C \ insert i S).card = m := by
        have : C \ insert i S = (C \ S).erase i := by ext x; simp [and_left_comm, and_comm]
        rw [this, Finset.card_erase_of_mem hi_sdiff, hdiff]
        omega
      exact ih (insert i S) (Finset.insert_subset hiC hSC) (Finset.insert_nonempty i S) hdiff' hS'
  obtain ⟨r, hr⟩ := hne
  have hbase : 2 * rkOf a b {r} ≤ (freqsOf a b {r}).card + 1 := by
    rw [rkOf_singleton a b r (hvalid r hr)]
    have : freqsOf a b {r} = freqOf a b r := by simp [freqsOf]
    rw [this, freqOf_card (hvalid r hr)]
  exact hmain (C \ {r}).card {r} (Finset.singleton_subset_iff.mpr hr) (Finset.singleton_nonempty r) rfl hbase

lemma two_freqs_le_three_card {n : ℕ} {I : Type*} [DecidableEq I]
    {a b : I → Vec n} {α β : I → F} {C : Finset I}
    (hvalid : ∀ i ∈ C, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (ht : IsTiling a b α β C) :
    2 * (freqsOf a b C).card ≤ 3 * C.card := by
  have hsum_deg : (∑ v ∈ freqsOf a b C, (C.filter (fun i => v ∈ freqOf a b i)).card) = 3 * C.card := by
    have h1 : (∑ v ∈ freqsOf a b C, (C.filter (fun i => v ∈ freqOf a b i)).card) =
        ∑ v ∈ freqsOf a b C, ∑ i ∈ C, if v ∈ freqOf a b i then 1 else 0 := by
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.card_filter]
    rw [h1, Finset.sum_comm]
    have h2 : ∀ i ∈ C, (∑ v ∈ freqsOf a b C, if v ∈ freqOf a b i then 1 else 0) = 3 := by
      intro i hi
      rw [← Finset.card_filter]
      have hfilt : (freqsOf a b C).filter (fun v => v ∈ freqOf a b i) = freqOf a b i := by
        ext v
        simp only [Finset.mem_filter, and_iff_right_iff_imp]
        intro hv
        exact Finset.mem_biUnion.mpr ⟨i, hi, hv⟩
      rw [hfilt, freqOf_card (hvalid i hi)]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hge : 2 * (freqsOf a b C).card ≤ ∑ v ∈ freqsOf a b C, (C.filter (fun i => v ∈ freqOf a b i)).card := by
    calc 2 * (freqsOf a b C).card
        = ∑ _v ∈ freqsOf a b C, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ freqsOf a b C, (C.filter (fun i => v ∈ freqOf a b i)).card :=
          Finset.sum_le_sum fun v hv => (isTiling_deg_even_pos hvalid ht hv).2
  omega

lemma four_rk_le_three_card_conn {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {a b : I → Vec n} {α β : I → F} {C : Finset I}
    (hvalid : ∀ i ∈ C, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hconn : ∀ i ∈ C, ∀ j ∈ C, Relation.EqvGen (fun x y => x ∈ C ∧ y ∈ C ∧ adjOf a b x y) i j)
    (ht : IsTiling a b α β C) (hne : C.Nonempty) :
    4 * rkOf a b C ≤ 3 * C.card := by
  have h1 := two_rk_le_freqs_add_one a b C hvalid hconn hne
  have h2 := two_freqs_le_three_card hvalid ht
  have hconst := (isTiling_iff_const_count a b α β C hvalid).mp ht 0
  have hdvd : 4 * (C.filter (fun i => dotProduct (a i) 0 = α i ∧ dotProduct (b i) 0 = β i)).card = C.card := by
    exact_mod_cast hconst
  omega

lemma spanOf_biUnion {n : ℕ} {I : Type*} [DecidableEq I]
    (a b : I → Vec n) (P : Finset (Finset I)) :
    spanOf a b (P.biUnion id) = P.sup (spanOf a b) := by
  apply le_antisymm
  · unfold spanOf
    rw [Submodule.span_le]
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, id_eq] at hv
    rcases hv with ⟨i, ⟨C, hCP, hiC⟩, rfl⟩ | ⟨i, ⟨C, hCP, hiC⟩, rfl⟩
    · exact (Finset.le_sup (f := spanOf a b) hCP) (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem a hiC))))
    · exact (Finset.le_sup (f := spanOf a b) hCP) (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem b hiC))))
  · rw [Finset.sup_le_iff]
    intro C hCP
    unfold spanOf
    apply Submodule.span_mono
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, id_eq] at hv ⊢
    rcases hv with ⟨i, hiC, rfl⟩ | ⟨i, hiC, rfl⟩
    · exact Or.inl ⟨i, ⟨C, hCP, hiC⟩, rfl⟩
    · exact Or.inr ⟨i, ⟨C, hCP, hiC⟩, rfl⟩

lemma finrank_finset_sup_le {n : ℕ} {α : Type*} [DecidableEq α]
    (P : Finset α) (f : α → Submodule F (Vec n)) :
    Module.finrank F (P.sup f : Submodule F (Vec n)) ≤ ∑ x ∈ P, Module.finrank F (f x) := by
  induction P using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sup_insert, Finset.sum_insert hx]
    have h := Submodule.finrank_sup_add_finrank_inf_eq (f x) (s.sup f)
    omega

lemma four_rk_le_three_card_any {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    {a b : I → Vec n} {α β : I → F} {S : Finset I}
    (hvalid : ∀ i ∈ S, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (ht : IsTiling a b α β S) :
    4 * rkOf a b S ≤ 3 * S.card := by
  let R : I → I → Prop := fun x y => x ∈ S ∧ y ∈ S ∧ adjOf a b x y
  let comp : I → Finset I := fun i => S.filter (fun j => decide (Relation.EqvGen R i j))
  let P : Finset (Finset I) := S.image comp
  have hcomp_sub : ∀ i ∈ S, comp i ⊆ S := fun i _ => Finset.filter_subset _ S
  have hcomp_self : ∀ i ∈ S, i ∈ comp i := fun i hi => by simp [comp, hi, Relation.EqvGen.refl]
  have hcomp_eq : ∀ i ∈ S, ∀ j ∈ comp i, comp j = comp i := by
    intro i hi j hj
    simp only [comp, Finset.mem_filter, decide_eq_true_eq] at hj
    ext k
    simp only [comp, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨fun ⟨hk, hjk⟩ => ⟨hk, Relation.EqvGen.trans _ _ _ hj.2 hjk⟩,
           fun ⟨hk, hik⟩ => ⟨hk, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hj.2) hik⟩⟩
  have hdisj : (P : Set (Finset I)).PairwiseDisjoint id := by
    intro C1 h1 C2 h2 hne
    obtain ⟨i1, hi1, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨i2, hi2, rfl⟩ := Finset.mem_image.mp h2
    change Disjoint (comp i1) (comp i2)
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    exact hne ((hcomp_eq i1 hi1 j hj1).symm.trans (hcomp_eq i2 hi2 j hj2))
  have hbiU : P.biUnion id = S := by
    ext i
    simp only [Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨C, hCP, hiC⟩
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hCP
      exact hcomp_sub r hr hiC
    · intro hi
      exact ⟨comp i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hcomp_self i hi⟩
  have hfreq_disj : ∀ C1 ∈ P, ∀ C2 ∈ P, C1 ≠ C2 → Disjoint (freqsOf a b C1) (freqsOf a b C2) := by
    intro C1 h1 C2 h2 hne
    obtain ⟨i1, hi1, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨i2, hi2, rfl⟩ := Finset.mem_image.mp h2
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    obtain ⟨j1, hj1, hvj1⟩ := Finset.mem_biUnion.mp hv1
    obtain ⟨j2, hj2, hvj2⟩ := Finset.mem_biUnion.mp hv2
    have hj1S : j1 ∈ S := hcomp_sub i1 hi1 hj1
    have hj2S : j2 ∈ S := hcomp_sub i2 hi2 hj2
    have hrel : Relation.EqvGen R j1 j2 := Relation.EqvGen.rel _ _ ⟨hj1S, hj2S, v, hvj1, hvj2⟩
    have hj2_in : j2 ∈ comp j1 := Finset.mem_filter.mpr ⟨hj2S, decide_eq_true hrel⟩
    exact hne ((hcomp_eq i1 hi1 j1 hj1).symm.trans ((hcomp_eq j1 hj1S j2 hj2_in).symm.trans (hcomp_eq i2 hi2 j2 hj2)))
  have htC : ∀ C ∈ P, IsTiling a b α β C := by
    intro C hCP v hv0
    by_cases hv : v ∈ freqsOf a b C
    · have htot := ht v hv0
      rw [← hbiU, Finset.sum_biUnion hdisj] at htot
      simp only [id_eq] at htot
      have hz : ∀ C' ∈ P, C' ≠ C → (∑ i ∈ C', rowCoeff a b α β i v) = 0 := by
        intro C' hC' hne
        refine Finset.sum_eq_zero fun i hi => rowCoeff_eq_zero_of_not_mem fun hvi => ?_
        exact Finset.disjoint_left.mp (hfreq_disj C hCP C' hC' hne.symm) hv (Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩)
      rw [Finset.sum_eq_single C hz (fun h => absurd hCP h)] at htot
      exact htot
    · refine Finset.sum_eq_zero fun i hi => rowCoeff_eq_zero_of_not_mem fun hvi =>
        hv (Finset.mem_biUnion.mpr ⟨i, hi, hvi⟩)
  have hC_bound : ∀ C ∈ P, 4 * rkOf a b C ≤ 3 * C.card := by
    intro C hCP
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hCP
    refine four_rk_le_three_card_conn (fun i hi => hvalid i (hcomp_sub r hr hi)) ?_ (htC _ hCP) ⟨r, hcomp_self r hr⟩
    intro i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    simp only [decide_eq_true_eq] at hi' hj'
    have hR_to_C : ∀ x y : I, Relation.EqvGen R x y → x ∈ comp r →
        Relation.EqvGen (fun u w => u ∈ comp r ∧ w ∈ comp r ∧ adjOf a b u w) x y := by
      intro x y hxy
      induction hxy with
      | rel x y h =>
        intro hx
        have hy : y ∈ comp r := by
          have hx' := (Finset.mem_filter.mp hx).2
          simp only [decide_eq_true_eq] at hx'
          exact Finset.mem_filter.mpr ⟨h.2.1, decide_eq_true (Relation.EqvGen.trans _ _ _ hx' (Relation.EqvGen.rel _ _ h))⟩
        exact Relation.EqvGen.rel _ _ ⟨hx, hy, h.2.2⟩
      | refl x => intro _; exact Relation.EqvGen.refl x
      | symm x y hxy ih =>
        intro hy
        have hx : x ∈ comp r := by
          have hy' := (Finset.mem_filter.mp hy).2
          simp only [decide_eq_true_eq] at hy'
          have hS_iff : ∀ u w, Relation.EqvGen R u w → (u ∈ S ↔ w ∈ S) := by
            intro u w huw
            induction huw with
            | rel _ _ h => exact ⟨fun _ => h.2.1, fun _ => h.1⟩
            | refl _ => exact Iff.rfl
            | symm _ _ _ ih0 => exact ih0.symm
            | trans _ _ _ _ _ i1 i2 => exact i1.trans i2
          exact Finset.mem_filter.mpr ⟨(hS_iff x y hxy).mpr (hcomp_sub r hr hy),
            decide_eq_true (Relation.EqvGen.trans _ _ _ hy' (Relation.EqvGen.symm _ _ hxy))⟩
        exact Relation.EqvGen.symm _ _ (ih hx)
      | trans x y z hxy _ ih1 ih2 =>
        intro hx
        have hy : y ∈ comp r := by
          have hx' := (Finset.mem_filter.mp hx).2
          simp only [decide_eq_true_eq] at hx'
          have hS_iff : ∀ u w, Relation.EqvGen R u w → (u ∈ S ↔ w ∈ S) := by
            intro u w huw
            induction huw with
            | rel _ _ h => exact ⟨fun _ => h.2.1, fun _ => h.1⟩
            | refl _ => exact Iff.rfl
            | symm _ _ _ ih0 => exact ih0.symm
            | trans _ _ _ _ _ i1 i2 => exact i1.trans i2
          exact Finset.mem_filter.mpr ⟨(hS_iff x y hxy).mp (hcomp_sub r hr hx),
            decide_eq_true (Relation.EqvGen.trans _ _ _ hx' hxy)⟩
        exact Relation.EqvGen.trans _ _ _ (ih1 hx) (ih2 hy)
    exact hR_to_C i j (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hi') hj') hi
  have hrk_le : rkOf a b S ≤ ∑ C ∈ P, rkOf a b C := by
    rw [rkOf, ← hbiU, spanOf_biUnion]
    exact finrank_finset_sup_le P (spanOf a b)
  have hcard_eq : S.card = ∑ C ∈ P, C.card := by
    have h := Finset.card_biUnion hdisj
    simp only [id_eq, hbiU] at h
    exact h
  calc 4 * rkOf a b S
      ≤ 4 * ∑ C ∈ P, rkOf a b C := Nat.mul_le_mul_left 4 hrk_le
    _ = ∑ C ∈ P, 4 * rkOf a b C := Finset.mul_sum _ _ _
    _ ≤ ∑ C ∈ P, 3 * C.card := Finset.sum_le_sum hC_bound
    _ = 3 * ∑ C ∈ P, C.card := (Finset.mul_sum _ _ _).symm
    _ = 3 * S.card := by rw [← hcard_eq]

lemma mem_spanOf_singleton_iff {n : ℕ} {I : Type*} (a b : I → Vec n) (i : I) (v : Vec n) :
    v ∈ spanOf a b {i} ↔ v = 0 ∨ v ∈ freqOf a b i := by
  unfold spanOf freqOf
  have hset : (↑(({i} : Finset I).image a ∪ ({i} : Finset I).image b) : Set (Vec n)) = {a i, b i} := by
    ext u; simp
  rw [hset, Submodule.mem_span_pair]
  constructor
  · rintro ⟨x, y, rfl⟩
    rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl <;> simp
  · rintro (rfl | h)
    · exact ⟨0, 0, by simp⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
      · exact ⟨1, 1, by simp⟩

lemma exists_coset_point {n : ℕ} {a b : Vec n} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) (α β : F) :
    ∃ x0 : Vec n, dotProduct a x0 = α ∧ dotProduct b x0 = β := by

  let U := Submodule.span F ({a, b} : Set (Vec n))
  have hli : LinearIndependent F ![a, b] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hsum : g 0 • a + g 1 • b = 0 := by simpa [Fin.sum_univ_two] using hg
    have h01 : g 0 = 0 ∧ g 1 = 0 := by
      rcases zmod2_cases (g 0) with h0 | h0 <;> rcases zmod2_cases (g 1) with h1 | h1
      · exact ⟨h0, h1⟩
      · simp [h0, h1] at hsum; exact absurd hsum hb
      · simp [h0, h1] at hsum; exact absurd hsum ha
      · simp [h0, h1] at hsum; exact absurd hsum (valid_ab_add_ne_zero hab)
    fin_cases j
    · exact h01.1
    · exact h01.2
  have hrange : Set.range ![a, b] = ({a, b} : Set (Vec n)) := by
    ext v; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, Fin.exists_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm]
  let B : Module.Basis (Fin 2) F U := Module.Basis.span hli |>.map (LinearEquiv.ofEq _ _ (by rw [hrange]))
  let f0 : U →ₗ[F] F := B.constr F ![α, β]
  obtain ⟨f, hf⟩ := f0.exists_extend
  obtain ⟨x0, hx0⟩ := (dotDualMap_bijective n).2 f
  refine ⟨x0, ?_, ?_⟩
  · have h1 := LinearMap.congr_fun hx0 a
    have haU : a ∈ U := Submodule.subset_span (by simp)
    have h2 := LinearMap.congr_fun hf ⟨a, haU⟩
    have hB0 : B 0 = ⟨a, haU⟩ := by
      ext; simp [B, Module.Basis.span_apply]
    have hf0a : f0 ⟨a, haU⟩ = α := by rw [← hB0]; simp [f0]
    simpa [dotDualMap, hf0a] using h1.trans h2
  · have h1 := LinearMap.congr_fun hx0 b
    have hbU : b ∈ U := Submodule.subset_span (by simp)
    have h2 := LinearMap.congr_fun hf ⟨b, hbU⟩
    have hB1 : B 1 = ⟨b, hbU⟩ := by
      ext; simp [B, Module.Basis.span_apply]
    have hf0b : f0 ⟨b, hbU⟩ = β := by rw [← hB1]; simp [f0]
    simpa [dotDualMap, hf0b] using h1.trans h2

set_option maxHeartbeats 1200000 in
lemma rk_eq_three_c_imp_c_eq_one {n e : ℕ} {a b : Fin (4 * e) → Vec n} {α β : Fin (4 * e) → F}
    (hvalid : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (ht : IsTiling a b α β Finset.univ)
    {C : Finset (Fin (4 * e))} (hC : C ∈ partsOf a b) {c : ℕ}
    (hcard : C.card = 4 * c) (hc1 : 1 ≤ c) (hrk : rkOf a b C = 3 * c) :
    c = 1 := by
  by_contra hcne
  have hc2 : 2 ≤ c := by omega
  have htC : IsTiling a b α β C := isTiling_restrict_part ht hC
  obtain ⟨r0, _, hCeq⟩ := Finset.mem_image.mp hC
  have hC_conn : ∀ i ∈ C, ∀ j ∈ C, Relation.EqvGen (fun x y => x ∈ C ∧ y ∈ C ∧ adjOf a b x y) i j := by
    intro i hi j hj
    rw [← hCeq] at hi hj ⊢
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    simp only [decide_eq_true_eq] at hi' hj'
    have hEqv : Relation.EqvGen (adjOf a b) i j := Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hi') hj'
    have hlift : ∀ x y, Relation.EqvGen (adjOf a b) x y → x ∈ compOf a b r0 →
        Relation.EqvGen (fun u w => u ∈ compOf a b r0 ∧ w ∈ compOf a b r0 ∧ adjOf a b u w) x y := by
      intro x y hxy
      induction hxy with
      | rel x y h =>
        intro hx
        have hx' := (Finset.mem_filter.mp hx).2
        simp only [decide_eq_true_eq] at hx'
        have hy : y ∈ compOf a b r0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          decide_eq_true (Relation.EqvGen.trans _ _ _ hx' (Relation.EqvGen.rel _ _ h))⟩
        exact Relation.EqvGen.rel _ _ ⟨hx, hy, h⟩
      | refl x => intro _; exact Relation.EqvGen.refl x
      | symm x y hxy ih =>
        intro hy
        have hy' := (Finset.mem_filter.mp hy).2
        simp only [decide_eq_true_eq] at hy'
        have hx : x ∈ compOf a b r0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          decide_eq_true (Relation.EqvGen.trans _ _ _ hy' (Relation.EqvGen.symm _ _ hxy))⟩
        exact Relation.EqvGen.symm _ _ (ih hx)
      | trans x y z hxy _ ih1 ih2 =>
        intro hx
        have hx' := (Finset.mem_filter.mp hx).2
        simp only [decide_eq_true_eq] at hx'
        have hy : y ∈ compOf a b r0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          decide_eq_true (Relation.EqvGen.trans _ _ _ hx' hxy)⟩
        exact Relation.EqvGen.trans _ _ _ (ih1 hx) (ih2 hy)
    exact hlift i j hEqv hi
  have hC_ne : C.Nonempty := ⟨r0, by rw [← hCeq]; exact compOf_mem_self a b r0⟩
  have hfreqs_ge : 6 * c - 1 ≤ (freqsOf a b C).card := by
    have h := two_rk_le_freqs_add_one a b C (fun i _ => hvalid i) hC_conn hC_ne
    omega
  let deg : Vec n → ℕ := fun v => (C.filter (fun i => v ∈ freqOf a b i)).card
  have hdeg_sum : (∑ v ∈ freqsOf a b C, deg v) = 12 * c := by
    have h1 : (∑ v ∈ freqsOf a b C, deg v) =
        ∑ v ∈ freqsOf a b C, ∑ i ∈ C, if v ∈ freqOf a b i then 1 else 0 :=
      Finset.sum_congr rfl fun v _ => Finset.card_filter _ _
    rw [h1, Finset.sum_comm]
    have h2 : ∀ i ∈ C, (∑ v ∈ freqsOf a b C, if v ∈ freqOf a b i then 1 else 0) = 3 := by
      intro i hi
      rw [← Finset.card_filter]
      have hfilt : (freqsOf a b C).filter (fun v => v ∈ freqOf a b i) = freqOf a b i := by
        ext v; simp only [Finset.mem_filter, and_iff_right_iff_imp]
        exact fun hv => Finset.mem_biUnion.mpr ⟨i, hi, hv⟩
      rw [hfilt, freqOf_card (hvalid i)]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, hcard]
    ring
  have hdeg_even : ∀ v ∈ freqsOf a b C, 2 ∣ deg v ∧ 2 ≤ deg v :=
    fun v hv => isTiling_deg_even_pos (fun i _ => hvalid i) htC hv
  let high : Finset (Vec n) := (freqsOf a b C).filter (fun v => 2 < deg v)
  have hhigh_deg_ge4 : ∀ v ∈ high, 4 ≤ deg v := by
    intro v hv
    have hv1 := (Finset.mem_filter.mp hv).1
    have hv2 := (Finset.mem_filter.mp hv).2
    obtain ⟨⟨m, hm⟩, _⟩ := hdeg_even v hv1
    omega
  have hhigh_sum_le : (∑ v ∈ high, (deg v - 2)) ≤ 2 := by
    have hle1 : (∑ v ∈ high, (deg v - 2)) ≤ ∑ v ∈ freqsOf a b C, (deg v - 2) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hadd : (∑ v ∈ freqsOf a b C, (deg v - 2)) + 2 * (freqsOf a b C).card = 12 * c := by
      have hsub : (∑ v ∈ freqsOf a b C, (deg v - 2)) + ∑ _v ∈ freqsOf a b C, 2 =
          ∑ v ∈ freqsOf a b C, deg v := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v hv => ?_
        have := (hdeg_even v hv).2; omega
      rw [Finset.sum_const, smul_eq_mul] at hsub
      omega
    omega
  have hhigh_card : high.card ≤ 1 := by
    have h1 : 2 * high.card ≤ ∑ v ∈ high, (deg v - 2) := by
      calc 2 * high.card = ∑ _v ∈ high, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ v ∈ high, (deg v - 2) := Finset.sum_le_sum fun v hv => by have := hhigh_deg_ge4 v hv; omega
    omega
  have hhigh_deg_eq4 : ∀ v ∈ high, deg v = 4 := by
    intro v hv
    have hge := hhigh_deg_ge4 v hv
    have hle : deg v - 2 ≤ ∑ u ∈ high, (deg u - 2) :=
      Finset.single_le_sum (f := fun u => deg u - 2) (fun _ _ => Nat.zero_le _) hv
    omega

  let badRows : Finset (Fin (4 * e)) := C.filter (fun i => ∃ v ∈ high, v ∈ freqOf a b i)
  have hbad_le : badRows.card ≤ 4 := by
    have hsub : badRows ⊆ high.biUnion (fun v => C.filter (fun i => v ∈ freqOf a b i)) := by
      intro i hi
      obtain ⟨hiC, v, hv, hvi⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨hiC, hvi⟩⟩
    calc badRows.card
        ≤ (high.biUnion (fun v => C.filter (fun i => v ∈ freqOf a b i))).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ high, deg v := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ high, 4 := Finset.sum_le_sum fun v hv => by rw [hhigh_deg_eq4 v hv]
      _ = 4 * high.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 4 := by omega
  have hex_i0 : ∃ i0 ∈ C, ∀ v ∈ freqOf a b i0, deg v = 2 := by
    have hlt : badRows.card < C.card := by omega
    obtain ⟨i0, hi0C, hi0_nbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨i0, hi0C, fun v hvi0 => ?_⟩
    have hv_mem : v ∈ freqsOf a b C := Finset.mem_biUnion.mpr ⟨i0, hi0C, hvi0⟩
    have hge2 := (hdeg_even v hv_mem).2
    by_contra hne2
    have hvh : v ∈ high := Finset.mem_filter.mpr ⟨hv_mem, by omega⟩
    exact hi0_nbad (Finset.mem_filter.mpr ⟨hi0C, v, hvh, hvi0⟩)
  obtain ⟨i0, hi0C, hi0_deg⟩ := hex_i0
  let U0 : Submodule F (Vec n) := spanOf a b {i0}
  let N0 : Finset (Fin (4 * e)) := C.filter (fun j => j ≠ i0 ∧ ¬ Disjoint (freqOf a b j) (freqOf a b i0))
  let C2 : Finset (Fin (4 * e)) := (C.erase i0) \ N0
  have hN0_le : N0.card ≤ 3 := by
    have hsub : N0 ⊆ (freqOf a b i0).biUnion (fun v => (C.filter (fun j => v ∈ freqOf a b j)).erase i0) := by
      intro j hj
      obtain ⟨hjC, hjne, hnd⟩ := Finset.mem_filter.mp hj
      rw [Finset.not_disjoint_iff] at hnd
      obtain ⟨v, hvj, hvi0⟩ := hnd
      exact Finset.mem_biUnion.mpr ⟨v, hvi0, Finset.mem_erase.mpr ⟨hjne, Finset.mem_filter.mpr ⟨hjC, hvj⟩⟩⟩
    calc N0.card
        ≤ ((freqOf a b i0).biUnion (fun v => (C.filter (fun j => v ∈ freqOf a b j)).erase i0)).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ freqOf a b i0, ((C.filter (fun j => v ∈ freqOf a b j)).erase i0).card := Finset.card_biUnion_le
      _ = ∑ _v ∈ freqOf a b i0, 1 := by
          refine Finset.sum_congr rfl fun v hvi0 => ?_
          have hmem : i0 ∈ C.filter (fun j => v ∈ freqOf a b j) := Finset.mem_filter.mpr ⟨hi0C, hvi0⟩
          rw [Finset.card_erase_of_mem hmem]
          have := hi0_deg v hvi0
          dsimp only [deg] at this
          omega
      _ = (freqOf a b i0).card := by simp
      _ = 3 := freqOf_card (hvalid i0)
  have hN0_sub : N0 ⊆ C.erase i0 := fun j hj =>
    Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2.1, (Finset.mem_filter.mp hj).1⟩
  have hC2_card_ge : 4 * (c - 1) ≤ C2.card := by
    have h1 : C2.card + N0.card = (C.erase i0).card := Finset.card_sdiff_add_card_eq_card hN0_sub
    rw [Finset.card_erase_of_mem hi0C, hcard] at h1
    omega

  obtain ⟨x0, hx0a, hx0b⟩ := exists_coset_point (hvalid i0).1 (hvalid i0).2.1 (hvalid i0).2.2 (α i0) (β i0)
  let V0 := perpSub U0
  have hE0_i0 : ∀ y : V0, dotProduct (a i0) (x0 + y.1) = α i0 ∧ dotProduct (b i0) (x0 + y.1) = β i0 := by
    intro y
    have ha0 : dotProduct (a i0) y.1 = 0 :=
      dot_eq_zero_of_mem_perpSub (freqOf_subset_spanOf a b (Finset.mem_singleton_self i0) (a i0) (by simp [freqOf])) y.2
    have hb0 : dotProduct (b i0) y.1 = 0 :=
      dot_eq_zero_of_mem_perpSub (freqOf_subset_spanOf a b (Finset.mem_singleton_self i0) (b i0) (by simp [freqOf])) y.2
    simp [dotProduct_add, hx0a, hx0b, ha0, hb0]
  have hC2_out : ∀ j ∈ C2, a j ∉ U0 ∧ b j ∉ U0 ∧ a j + b j ∉ U0 := by
    intro j hj
    have hj_er : j ∈ C.erase i0 := (Finset.mem_sdiff.mp hj).1
    have hj_nN : j ∉ N0 := (Finset.mem_sdiff.mp hj).2
    have hdisj : Disjoint (freqOf a b j) (freqOf a b i0) := by
      by_contra hnd
      exact hj_nN (Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hj_er).2, (Finset.mem_erase.mp hj_er).1, hnd⟩)
    refine ⟨?_, ?_, ?_⟩
    · intro h; rcases (mem_spanOf_singleton_iff a b i0 (a j)).mp h with h0 | hf
      · exact (hvalid j).1 h0
      · exact Finset.disjoint_left.mp hdisj (by simp [freqOf]) hf
    · intro h; rcases (mem_spanOf_singleton_iff a b i0 (b j)).mp h with h0 | hf
      · exact (hvalid j).2.1 h0
      · exact Finset.disjoint_left.mp hdisj (by simp [freqOf]) hf
    · intro h; rcases (mem_spanOf_singleton_iff a b i0 (a j + b j)).mp h with h0 | hf
      · exact valid_ab_add_ne_zero (hvalid j).2.2 h0
      · exact Finset.disjoint_left.mp hdisj (by simp [freqOf]) hf
  have hC2_row_sum : ∀ j ∈ C2,
      (4 : ℤ) * ((Finset.univ.filter (fun y : V0 =>
        dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) =
      (Fintype.card V0 : ℤ) := by
    intro j hj
    have hsum_zero : ∀ v : Vec n, v ∉ U0 → (∑ y : V0, chi v (x0 + y.1)) = 0 := by
      intro v hv
      have hnot : ¬ ∀ y ∈ V0, dotProduct v y = 0 := fun h => hv (mem_of_forall_perpSub U0 v h)
      have h1 := sum_chi_subspace V0 v
      rw [if_neg hnot] at h1
      have h2 : (∑ y : V0, chi v y.1) = ∑ x : Vec n, if x ∈ V0 then chi v x else 0 := by
        rw [← Finset.sum_filter]
        exact (Finset.sum_subtype (Finset.univ.filter (· ∈ V0)) (fun _ => by simp) (fun x => chi v x)).symm
      calc (∑ y : V0, chi v (x0 + y.1))
          = ∑ y : V0, chi v x0 * chi v y.1 := by simp_rw [chi_add_right]
        _ = chi v x0 * ∑ y : V0, chi v y.1 := (Finset.mul_sum _ _ _).symm
        _ = 0 := by rw [h2, h1, mul_zero]
    have hcard : ((Finset.univ.filter (fun y : V0 =>
        dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) =
        ∑ y : V0, (if dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j then (1 : ℤ) else 0) := by
      rw [Finset.card_filter]; simp
    rw [hcard, Finset.mul_sum]
    simp_rw [four_mul_coset_ind]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hsum_zero (a j) (hC2_out j hj).1, hsum_zero (b j) (hC2_out j hj).2.1,
      hsum_zero (a j + b j) (hC2_out j hj).2.2]
    ring

  have hC_split : ∀ y : V0,
      (C.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card =
      1 + (N0.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card +
          (C2.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card := by
    intro y
    have h1 : C = insert i0 (C.erase i0) := (Finset.insert_erase hi0C).symm
    have h2 : C.erase i0 = N0 ∪ C2 := by
      ext j; simp only [C2, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hj; by_cases h : j ∈ N0 <;> simp [h, hj]
      · rintro (hj | ⟨hj, _⟩); exact hN0_sub hj; exact hj
    have hd : Disjoint N0 C2 := Finset.disjoint_sdiff
    conv_lhs => rw [h1, Finset.filter_insert, if_pos (hE0_i0 y), Finset.card_insert_of_notMem (by simp)]
    rw [h2, Finset.filter_union, Finset.card_union_of_disjoint (hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    omega
  have hconst_y : ∀ y : V0,
      (C.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card = c := by
    intro y
    have h := (isTiling_iff_const_count a b α β C (fun i _ => hvalid i)).mp htC (x0 + y.1)
    rw [hcard] at h
    have hnat : 4 * (C.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card = 4 * c := by
      exact_mod_cast h
    omega
  have hV0_pos : (0 : ℤ) < Fintype.card V0 := by
    have : 0 < Fintype.card V0 := Fintype.card_pos_iff.mpr ⟨⟨0, V0.zero_mem⟩⟩
    exact_mod_cast this
  have hC2_total : (4 : ℤ) * (∑ y : V0, ((C2.filter (fun j =>
      dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ)) =
      (C2.card : ℤ) * (Fintype.card V0 : ℤ) := by
    have hswap : (∑ y : V0, ((C2.filter (fun j =>
        dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ)) =
        ∑ j ∈ C2, ((Finset.univ.filter (fun y : V0 =>
        dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) := by
      simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      exact Finset.sum_comm
    rw [hswap, Finset.mul_sum, Finset.sum_congr rfl hC2_row_sum, Finset.sum_const, nsmul_eq_mul]
  have hN0_sum_zero : (∑ y : V0, ((N0.filter (fun j =>
      dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ)) = 0 ∧
      C2.card = 4 * (c - 1) := by
    have hsum_eq : (∑ y : V0, (4 : ℤ) * ((N0.filter (fun j =>
        dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ)) +
        (C2.card : ℤ) * (Fintype.card V0 : ℤ) = (4 * (c - 1) : ℤ) * (Fintype.card V0 : ℤ) := by
      rw [← hC2_total, Finset.mul_sum, ← Finset.sum_add_distrib]
      have hterm : ∀ y : V0,
          (4 : ℤ) * ((N0.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) +
          (4 : ℤ) * ((C2.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) =
          (4 * (c - 1) : ℤ) := by
        intro y
        have hs := hC_split y
        have hc := hconst_y y
        have : (N0.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card +
            (C2.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card = c - 1 := by
          omega
        have hZ : ((N0.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) +
            ((C2.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) =
            ((c - 1 : ℕ) : ℤ) := by exact_mod_cast this
        rw [Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_one] at hZ
        linarith
      rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    have hnn : (0 : ℤ) ≤ ∑ y : V0, ((N0.filter (fun j =>
        dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hC2Z : (4 * (c - 1) : ℤ) ≤ (C2.card : ℤ) := by
      have : ((4 * (c - 1) : ℕ) : ℤ) ≤ (C2.card : ℤ) := by exact_mod_cast hC2_card_ge
      rwa [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_one] at this
    rw [← Finset.mul_sum] at hsum_eq
    have hmul_le : (4 * (c - 1) : ℤ) * (Fintype.card V0 : ℤ) ≤ (C2.card : ℤ) * (Fintype.card V0 : ℤ) :=
      mul_le_mul_of_nonneg_right hC2Z (le_of_lt hV0_pos)
    have hzero : (∑ y : V0, ((N0.filter (fun j =>
        dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ)) = 0 := by linarith
    have hC2_eqZ : (C2.card : ℤ) * (Fintype.card V0 : ℤ) = (4 * (c - 1) : ℤ) * (Fintype.card V0 : ℤ) := by linarith
    have hC2_eqZ' : (C2.card : ℤ) = (4 * (c - 1) : ℤ) := mul_right_cancel₀ (ne_of_gt hV0_pos) hC2_eqZ
    have hC2_eq : C2.card = 4 * (c - 1) := by
      have : (C2.card : ℤ) = ((4 * (c - 1) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : 1 ≤ c), Nat.cast_one]; exact hC2_eqZ'
      exact_mod_cast this
    exact ⟨hzero, hC2_eq⟩
  have hC2_const : ∀ y : V0,
      4 * (C2.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card = C2.card := by
    intro y
    have hN0_y : (N0.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card = 0 := by
      have hle : ((N0.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) ≤
          ∑ z : V0, ((N0.filter (fun j => dotProduct (a j) (x0 + z.1) = α j ∧ dotProduct (b j) (x0 + z.1) = β j)).card : ℤ) :=
        Finset.single_le_sum
          (f := fun z : V0 => ((N0.filter (fun j => dotProduct (a j) (x0 + z.1) = α j ∧ dotProduct (b j) (x0 + z.1) = β j)).card : ℤ))
          (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ y)
      rw [hN0_sum_zero.1] at hle
      have hnn : (0 : ℤ) ≤ ((N0.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) :=
        Nat.cast_nonneg _
      have hz : ((N0.filter (fun j => dotProduct (a j) (x0 + y.1) = α j ∧ dotProduct (b j) (x0 + y.1) = β j)).card : ℤ) = 0 := by linarith
      exact_mod_cast hz
    have hs := hC_split y
    have hc := hconst_y y
    rw [hN0_y] at hs
    rw [hN0_sum_zero.2]
    omega

  let m := Module.finrank F (Vec n ⧸ U0)
  let eQ : (Vec n ⧸ U0) ≃ₗ[F] Vec m := (Module.finBasis F (Vec n ⧸ U0)).equivFun
  let q : Vec n →ₗ[F] Vec m := eQ.toLinearMap.comp (Submodule.mkQ U0)
  have hker_q : LinearMap.ker q = U0 := by
    ext v
    simp only [q, LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      map_eq_zero_iff _ eQ.injective, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

  let qT_fun : Vec m → Vec n := fun z => ((dotDualMap_bijective n).2 ((dotDualMap m z).comp q)).choose
  have hqT_spec : ∀ z : Vec m, dotDualMap n (qT_fun z) = (dotDualMap m z).comp q :=
    fun z => ((dotDualMap_bijective n).2 ((dotDualMap m z).comp q)).choose_spec
  let qT : Vec m →ₗ[F] Vec n :=
    { toFun := qT_fun
      map_add' := fun z1 z2 => by
        apply (dotDualMap_bijective n).1
        rw [hqT_spec, map_add (dotDualMap n), hqT_spec, hqT_spec]
        ext v; simp [dotDualMap, dotProduct_add]
      map_smul' := fun s z => by
        apply (dotDualMap_bijective n).1
        rw [hqT_spec, RingHom.id_apply, map_smul (dotDualMap n), hqT_spec]
        ext v; simp [dotDualMap, dotProduct_smul] }
  have hqT_dot : ∀ (v : Vec n) (z : Vec m), dotProduct (q v) z = dotProduct v (qT z) := by
    intro v z
    have h := LinearMap.congr_fun (hqT_spec z) v
    simpa [qT, dotDualMap] using h.symm
  have hqT_mem : ∀ z : Vec m, qT z ∈ V0 := by
    intro z
    rw [mem_perpSub_iff]
    intro u hu
    rw [← hqT_dot u z]
    have hqu : q u = 0 := LinearMap.mem_ker.mp (hker_q.symm ▸ hu)
    simp [hqu]
  let a' : Fin (4 * e) → Vec m := fun j => q (a j)
  let b' : Fin (4 * e) → Vec m := fun j => q (b j)
  let α' : Fin (4 * e) → F := fun j => α j + dotProduct (a j) x0
  let β' : Fin (4 * e) → F := fun j => β j + dotProduct (b j) x0
  have hvalid' : ∀ j ∈ C2, a' j ≠ 0 ∧ b' j ≠ 0 ∧ a' j ≠ b' j := by
    intro j hj
    refine ⟨?_, ?_, ?_⟩
    · intro h; exact (hC2_out j hj).1 (hker_q ▸ LinearMap.mem_ker.mpr h)
    · intro h; exact (hC2_out j hj).2.1 (hker_q ▸ LinearMap.mem_ker.mpr h)
    · intro h
      have h0 : q (a j + b j) = 0 := by
        rw [map_add]; dsimp only [a', b'] at h; rw [h, vec_add_self]
      exact (hC2_out j hj).2.2 (hker_q ▸ LinearMap.mem_ker.mpr h0)
  have htC2' : IsTiling a' b' α' β' C2 := by
    rw [isTiling_iff_const_count a' b' α' β' C2 hvalid']
    intro z
    have hfilt : C2.filter (fun j => dotProduct (a' j) z = α' j ∧ dotProduct (b' j) z = β' j) =
        C2.filter (fun j => dotProduct (a j) (x0 + qT z) = α j ∧ dotProduct (b j) (x0 + qT z) = β j) := by
      ext j
      simp only [Finset.mem_filter, and_congr_right_iff]
      intro _
      simp only [a', b', α', β', hqT_dot, dotProduct_add]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · rw [h1]; have := zmod2_add_self (dotProduct (a j) x0); linear_combination this
        · rw [h2]; have := zmod2_add_self (dotProduct (b j) x0); linear_combination this
      · rintro ⟨h1, h2⟩
        refine ⟨?_, ?_⟩
        · have := zmod2_add_self (dotProduct (a j) x0); linear_combination h1 - this
        · have := zmod2_add_self (dotProduct (b j) x0); linear_combination h2 - this
    rw [hfilt]
    exact_mod_cast hC2_const ⟨qT z, hqT_mem z⟩
  have hrkC2' : 4 * rkOf a' b' C2 ≤ 3 * C2.card := four_rk_le_three_card_any hvalid' htC2'
  have hrk_C2_q : Module.finrank F ((spanOf a b C2).map q) ≤ 3 * (c - 1) := by
    have hmap : (spanOf a b C2).map q = spanOf a' b' C2 := by
      unfold spanOf
      rw [Submodule.map_span]
      congr 1
      ext v
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨u, (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩), rfl⟩
        · exact Or.inl ⟨j, hj, rfl⟩
        · exact Or.inr ⟨j, hj, rfl⟩
      · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
        · exact ⟨a j, Or.inl ⟨j, hj, rfl⟩, rfl⟩
        · exact ⟨b j, Or.inr ⟨j, hj, rfl⟩, rfl⟩
    rw [hmap]
    unfold rkOf at hrkC2'
    rw [hN0_sum_zero.2] at hrkC2'
    omega

  have hU0_sup_C2 : Module.finrank F (U0 ⊔ spanOf a b C2 : Submodule F (Vec n)) ≤ 3 * c - 1 := by
    have hker_inf : LinearMap.ker (q.domRestrict (spanOf a b C2)) =
        (U0 ⊓ spanOf a b C2).comap (spanOf a b C2).subtype := by
      ext ⟨v, hv⟩
      simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_comap,
        Submodule.coe_subtype, Submodule.mem_inf, hv, and_true]
      exact SetLike.ext_iff.mp hker_q v
    have hrange : LinearMap.range (q.domRestrict (spanOf a b C2)) = (spanOf a b C2).map q := by
      ext v
      simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Submodule.mem_map, Subtype.exists]
      exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, h⟩⟩
    have hrk_dom := LinearMap.finrank_range_add_finrank_ker (q.domRestrict (spanOf a b C2))
    rw [hrange, hker_inf] at hrk_dom
    have hcomap : Module.finrank F ((U0 ⊓ spanOf a b C2).comap (spanOf a b C2).subtype) =
        Module.finrank F (U0 ⊓ spanOf a b C2 : Submodule F (Vec n)) := by
      have hmap_eq : ((U0 ⊓ spanOf a b C2).comap (spanOf a b C2).subtype).map (spanOf a b C2).subtype =
          U0 ⊓ spanOf a b C2 := by
        rw [Submodule.map_comap_eq, Submodule.range_subtype]
        exact inf_eq_right.mpr inf_le_right
      calc Module.finrank F ((U0 ⊓ spanOf a b C2).comap (spanOf a b C2).subtype)
          = Module.finrank F (((U0 ⊓ spanOf a b C2).comap (spanOf a b C2).subtype).map (spanOf a b C2).subtype) :=
            (Submodule.finrank_map_subtype_eq (spanOf a b C2) _).symm
        _ = Module.finrank F (U0 ⊓ spanOf a b C2 : Submodule F (Vec n)) := by rw [hmap_eq]
    rw [hcomap] at hrk_dom
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq U0 (spanOf a b C2)
    have hU0_rk : Module.finrank F U0 = 2 := rkOf_singleton a b i0 (hvalid i0)
    omega

  have hN0_le_sup : ∀ j ∈ N0, spanOf a b {j} ≤ U0 ⊔ spanOf a b C2 := by
    let S := U0 ⊔ spanOf a b C2

    have hN0_card3 : N0.card = 3 := by
      have h1 : C2.card + N0.card = (C.erase i0).card := Finset.card_sdiff_add_card_eq_card hN0_sub
      rw [Finset.card_erase_of_mem hi0C, hcard, hN0_sum_zero.2] at h1
      omega

    have hN0_unique_v : ∀ j ∈ N0, ∃ v ∈ freqOf a b i0, v ∈ freqOf a b j ∧
        ∀ v' ∈ freqOf a b i0, v' ∈ freqOf a b j → v' = v := by
      intro j hj
      have hj_er := hN0_sub hj
      have hjC := (Finset.mem_erase.mp hj_er).2
      have hjne := (Finset.mem_erase.mp hj_er).1
      have hnd := (Finset.mem_filter.mp hj).2.2
      rw [Finset.not_disjoint_iff] at hnd
      obtain ⟨v, hvj, hvi0⟩ := hnd
      refine ⟨v, hvi0, hvj, fun v' hv'i0 hv'j => ?_⟩
      by_contra hvne

      have h3rd : v + v' ∈ freqOf a b i0 ∧ v + v' ∈ freqOf a b j := by
        have hmem_f : ∀ (k : Fin (4 * e)) (x y : Vec n), x ∈ freqOf a b k → y ∈ freqOf a b k → x ≠ y →
            x + y ∈ freqOf a b k := by
          intro k x y hx hy hxy
          simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
          rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
          · exact absurd rfl hxy
          · exact Or.inr (Or.inr rfl)
          · exact Or.inr (Or.inl (by rw [← add_assoc, vec_add_self, zero_add]))
          · exact Or.inr (Or.inr (add_comm _ _))
          · exact absurd rfl hxy
          · exact Or.inl (by ext t; have := zmod2_add_self (b k t); simp only [Pi.add_apply]; linear_combination this)
          · exact Or.inr (Or.inl (by ext t; have := zmod2_add_self (a k t); simp only [Pi.add_apply]; linear_combination this))
          · exact Or.inl (by rw [add_assoc, vec_add_self, add_zero])
          · exact absurd rfl hxy
        exact ⟨hmem_f i0 v v' hvi0 hv'i0 (Ne.symm hvne), hmem_f j v v' hvj hv'j (Ne.symm hvne)⟩

      have hN0_sub_j : N0 ⊆ {j} := by
        intro j' hj'
        rw [Finset.mem_singleton]
        have hj'_er := hN0_sub hj'
        have hj'C := (Finset.mem_erase.mp hj'_er).2
        have hj'ne := (Finset.mem_erase.mp hj'_er).1
        obtain ⟨w, hwj', hwi0⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hj').2.2
        have hwj : w ∈ freqOf a b j := by
          have hsub_i0 : {v, v', v + v'} ⊆ freqOf a b i0 := by
            intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl; exact hvi0; exact hv'i0; exact h3rd.1
          have hcard3 : ({v, v', v + v'} : Finset (Vec n)).card = 3 := by
            have h1 : v ≠ v' := Ne.symm hvne
            have hv0 : v ≠ 0 := by
              rcases (Finset.mem_insert.mp hvi0) with rfl | h
              · exact (hvalid i0).1
              · rcases Finset.mem_insert.mp h with rfl | h
                · exact (hvalid i0).2.1
                · rw [Finset.mem_singleton.mp h]; exact valid_ab_add_ne_zero (hvalid i0).2.2
            have hv'0 : v' ≠ 0 := by
              rcases (Finset.mem_insert.mp hv'i0) with rfl | h
              · exact (hvalid i0).1
              · rcases Finset.mem_insert.mp h with rfl | h
                · exact (hvalid i0).2.1
                · rw [Finset.mem_singleton.mp h]; exact valid_ab_add_ne_zero (hvalid i0).2.2
            have h2 : v ≠ v + v' := fun h => hv'0 (by
              have := congrArg (v + ·) h; simpa [← add_assoc, vec_add_self] using this.symm)
            have h3 : v' ≠ v + v' := fun h => hv0 (by
              have := congrArg (· + v') h; simpa [add_assoc, vec_add_self] using this.symm)
            simp [h1, h2, h3]
          have heq_i0 : ({v, v', v + v'} : Finset (Vec n)) = freqOf a b i0 :=
            Finset.eq_of_subset_of_card_le hsub_i0 (by rw [hcard3, freqOf_card (hvalid i0)])
          rw [← heq_i0] at hwi0
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwi0
          rcases hwi0 with rfl | rfl | rfl
          · exact hvj
          · exact hv'j
          · exact h3rd.2

        have hpair : ({i0, j} : Finset (Fin (4 * e))) ⊆ C.filter (fun k => w ∈ freqOf a b k) := by
          intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hi0C, hwi0⟩
          · exact Finset.mem_filter.mpr ⟨hjC, hwj⟩
        have hpair_eq : ({i0, j} : Finset (Fin (4 * e))) = C.filter (fun k => w ∈ freqOf a b k) :=
          Finset.eq_of_subset_of_card_le hpair (by rw [Finset.card_pair hjne.symm]; exact (hi0_deg w hwi0).le)
        have hj'_in : j' ∈ ({i0, j} : Finset (Fin (4 * e))) := by
          rw [hpair_eq]; exact Finset.mem_filter.mpr ⟨hj'C, hwj'⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj'_in
        exact hj'_in.resolve_left hj'ne
      have := Finset.card_le_card hN0_sub_j
      rw [hN0_card3, Finset.card_singleton] at this
      omega

    have hhigh_in_C2 : ∀ v ∈ high, ∃ k ∈ C2, v ∈ freqOf a b k := by
      intro v hv
      by_contra hnone
      push Not at hnone
      have hsub : C.filter (fun k => v ∈ freqOf a b k) ⊆ N0 := by
        intro k hk
        have hkC := (Finset.mem_filter.mp hk).1
        have hvk := (Finset.mem_filter.mp hk).2
        have hkne : k ≠ i0 := by
          rintro rfl
          have h2 := hi0_deg v hvk
          have h4 := hhigh_deg_eq4 v hv
          omega
        by_contra hknN
        exact hnone k (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hkne, hkC⟩, hknN⟩) hvk
      have hle := Finset.card_le_card hsub
      have h4 := hhigh_deg_eq4 v hv
      dsimp only [deg] at h4
      omega

    intro j1 hj1
    by_contra hnot_le

    obtain ⟨v1, hv1_i0, hv1_j1, hv1_uniq⟩ := hN0_unique_v j1 hj1
    have hout_S : ∀ j ∈ N0, ¬ spanOf a b {j} ≤ S →
        ∀ w ∈ freqOf a b j, w ∉ freqOf a b i0 → w ∉ S := by
      intro j hj hnj w hwj hwi0 hwS
      obtain ⟨vj, hvj_i0, hvj_j, _⟩ := hN0_unique_v j hj
      have hvj_S : vj ∈ S := Submodule.mem_sup_left (freqOf_subset_spanOf a b (Finset.mem_singleton_self i0) vj hvj_i0)
      have hvj_ne_w : vj ≠ w := fun h => hwi0 (h ▸ hvj_i0)

      apply hnj
      unfold spanOf
      rw [Submodule.span_le]
      intro u hu
      have hu_f : u ∈ freqOf a b j := by
        simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hu
        rcases hu with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ <;> simp [freqOf]
      have hsub3 : ({vj, w, vj + w} : Finset (Vec n)) ⊆ freqOf a b j := by
        intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hvj_j
        · exact hwj
        · simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hvj_j hwj ⊢
          rcases hvj_j with rfl | rfl | rfl <;> rcases hwj with rfl | rfl | rfl
          · exact absurd rfl hvj_ne_w
          · exact Or.inr (Or.inr rfl)
          · exact Or.inr (Or.inl (by rw [← add_assoc, vec_add_self, zero_add]))
          · exact Or.inr (Or.inr (add_comm _ _))
          · exact absurd rfl hvj_ne_w
          · exact Or.inl (by ext t; have := zmod2_add_self (b j t); simp only [Pi.add_apply]; linear_combination this)
          · exact Or.inr (Or.inl (by ext t; have := zmod2_add_self (a j t); simp only [Pi.add_apply]; linear_combination this))
          · exact Or.inl (by rw [add_assoc, vec_add_self, add_zero])
          · exact absurd rfl hvj_ne_w
      have hvj0 : vj ≠ 0 := by
        rcases Finset.mem_insert.mp hvj_j with rfl | h
        · exact (hvalid j).1
        · rcases Finset.mem_insert.mp h with rfl | h
          · exact (hvalid j).2.1
          · rw [Finset.mem_singleton.mp h]; exact valid_ab_add_ne_zero (hvalid j).2.2
      have hw0 : w ≠ 0 := by
        rcases Finset.mem_insert.mp hwj with rfl | h
        · exact (hvalid j).1
        · rcases Finset.mem_insert.mp h with rfl | h
          · exact (hvalid j).2.1
          · rw [Finset.mem_singleton.mp h]; exact valid_ab_add_ne_zero (hvalid j).2.2
      have hcard3 : ({vj, w, vj + w} : Finset (Vec n)).card = 3 := by
        have h2 : vj ≠ vj + w := fun h => hw0 (by
          have := congrArg (vj + ·) h; simpa [← add_assoc, vec_add_self] using this.symm)
        have h3 : w ≠ vj + w := fun h => hvj0 (by
          have := congrArg (· + w) h; simpa [add_assoc, vec_add_self] using this.symm)
        simp [hvj_ne_w, h2, h3]
      have heq : ({vj, w, vj + w} : Finset (Vec n)) = freqOf a b j :=
        Finset.eq_of_subset_of_card_le hsub3 (by rw [hcard3, freqOf_card (hvalid j)])
      rw [← heq] at hu_f
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu_f
      rcases hu_f with rfl | rfl | rfl
      · exact hvj_S
      · exact hwS
      · exact S.add_mem hvj_S hwS

    have hmatch_N0 : ∀ j ∈ N0, ¬ spanOf a b {j} ≤ S →
        ∀ w ∈ freqOf a b j, w ∉ freqOf a b i0 → ∃ j' ∈ N0, j' ≠ j ∧ w ∈ freqOf a b j' ∧ ¬ spanOf a b {j'} ≤ S := by
      intro j hj hnj w hwj hwi0
      have hw_notS : w ∉ S := hout_S j hj hnj w hwj hwi0
      have hjC : j ∈ C := (Finset.mem_erase.mp (hN0_sub hj)).2
      have hw_mem : w ∈ freqsOf a b C := Finset.mem_biUnion.mpr ⟨j, hjC, hwj⟩
      have hdeg2 : deg w = 2 := by
        have hge2 := (hdeg_even w hw_mem).2
        by_contra hne2
        have hwh : w ∈ high := Finset.mem_filter.mpr ⟨hw_mem, by omega⟩
        obtain ⟨k, hkC2, hwk⟩ := hhigh_in_C2 w hwh
        exact hw_notS (Submodule.mem_sup_right (freqOf_subset_spanOf a b hkC2 w hwk))
      have hpos : 0 < ((C.filter (fun k => w ∈ freqOf a b k)).erase j).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hjC, hwj⟩)]
        dsimp only [deg] at hdeg2; omega
      obtain ⟨j', hj'⟩ := Finset.card_pos.mp hpos
      have hj'ne : j' ≠ j := (Finset.mem_erase.mp hj').1
      have hj'C : j' ∈ C := (Finset.mem_filter.mp (Finset.mem_erase.mp hj').2).1
      have hwj' : w ∈ freqOf a b j' := (Finset.mem_filter.mp (Finset.mem_erase.mp hj').2).2
      have hj'ne_i0 : j' ≠ i0 := fun h => hwi0 (h ▸ hwj')
      have hj'N0 : j' ∈ N0 := by
        by_contra hnotN0
        have hj'C2 : j' ∈ C2 := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hj'ne_i0, hj'C⟩, hnotN0⟩
        exact hw_notS (Submodule.mem_sup_right (freqOf_subset_spanOf a b hj'C2 w hwj'))
      have hnj' : ¬ spanOf a b {j'} ≤ S := fun hle =>
        hw_notS (hle (freqOf_subset_spanOf a b (Finset.mem_singleton_self j') w hwj'))
      exact ⟨j', hj'N0, hj'ne, hwj', hnj'⟩

    have h2freqs : ∀ j ∈ N0, ∃ w1 w2 : Vec n, w1 ≠ w2 ∧ w1 ∈ freqOf a b j ∧ w2 ∈ freqOf a b j ∧
        w1 ∉ freqOf a b i0 ∧ w2 ∉ freqOf a b i0 := by
      intro j hj
      obtain ⟨vj, hvj_i0, hvj_j, hvj_u⟩ := hN0_unique_v j hj
      have hcard2 : ((freqOf a b j).erase vj).card = 2 := by
        rw [Finset.card_erase_of_mem hvj_j, freqOf_card (hvalid j)]
      obtain ⟨w1, w2, hne, heq⟩ := Finset.card_eq_two.mp hcard2
      have hw1 : w1 ∈ (freqOf a b j).erase vj := by rw [heq]; simp
      have hw2 : w2 ∈ (freqOf a b j).erase vj := by rw [heq]; simp
      exact ⟨w1, w2, hne, (Finset.mem_erase.mp hw1).2, (Finset.mem_erase.mp hw2).2,
        fun h => (Finset.mem_erase.mp hw1).1 (hvj_u w1 h (Finset.mem_erase.mp hw1).2),
        fun h => (Finset.mem_erase.mp hw2).1 (hvj_u w2 h (Finset.mem_erase.mp hw2).2)⟩
    obtain ⟨w1, w2, hw12, hw1_j1, hw2_j1, hw1_ni0, hw2_ni0⟩ := h2freqs j1 hj1
    obtain ⟨j2, hj2N0, hj2_ne1, hw1_j2, hnj2⟩ := hmatch_N0 j1 hj1 hnot_le w1 hw1_j1 hw1_ni0
    obtain ⟨j3, hj3N0, hj3_ne1, hw2_j3, hnj3⟩ := hmatch_N0 j1 hj1 hnot_le w2 hw2_j1 hw2_ni0
    have hj2_ne3 : j2 ≠ j3 := by
      rintro rfl

      have hsum_in : ∀ (k : Fin (4 * e)), w1 ∈ freqOf a b k → w2 ∈ freqOf a b k → w1 + w2 ∈ freqOf a b k := by
        intro k h1 h2
        simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at h1 h2 ⊢
        rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl
        · exact absurd rfl hw12
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl (by rw [← add_assoc, vec_add_self, zero_add]))
        · exact Or.inr (Or.inr (add_comm _ _))
        · exact absurd rfl hw12
        · exact Or.inl (by ext t; have := zmod2_add_self (b k t); simp only [Pi.add_apply]; linear_combination this)
        · exact Or.inr (Or.inl (by ext t; have := zmod2_add_self (a k t); simp only [Pi.add_apply]; linear_combination this))
        · exact Or.inl (by rw [add_assoc, vec_add_self, add_zero])
        · exact absurd rfl hw12
      have hsum_j1 := hsum_in j1 hw1_j1 hw2_j1
      have hsum_j2 := hsum_in j2 hw1_j2 hw2_j3
      have hw12_eq_v1 : w1 + w2 = v1 := by
        have hcard_er : ((freqOf a b j1).erase v1).card = 2 := by
          rw [Finset.card_erase_of_mem hv1_j1, freqOf_card (hvalid j1)]
        have hsub_er : ({w1, w2} : Finset (Vec n)) ⊆ (freqOf a b j1).erase v1 := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact Finset.mem_erase.mpr ⟨fun h => hw1_ni0 (h ▸ hv1_i0), hw1_j1⟩
          · exact Finset.mem_erase.mpr ⟨fun h => hw2_ni0 (h ▸ hv1_i0), hw2_j1⟩
        have heq_er := Finset.eq_of_subset_of_card_le hsub_er (by rw [Finset.card_pair hw12, hcard_er])
        by_contra hne_v1
        have hmem_er : w1 + w2 ∈ (freqOf a b j1).erase v1 := Finset.mem_erase.mpr ⟨hne_v1, hsum_j1⟩
        rw [← heq_er] at hmem_er
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem_er
        rcases hmem_er with h | h
        · have hw2_0 : w2 = 0 := by
            have := congrArg (w1 + ·) h; simpa [← add_assoc, vec_add_self] using this
          rcases Finset.mem_insert.mp hw2_j1 with h0 | h0
          · exact (hvalid j1).1 (h0 ▸ hw2_0)
          · rcases Finset.mem_insert.mp h0 with h0 | h0
            · exact (hvalid j1).2.1 (h0 ▸ hw2_0)
            · exact valid_ab_add_ne_zero (hvalid j1).2.2 ((Finset.mem_singleton.mp h0) ▸ hw2_0)
        · have hw1_0 : w1 = 0 := by
            have := congrArg (· + w2) h; simpa [add_assoc, vec_add_self] using this
          rcases Finset.mem_insert.mp hw1_j1 with h0 | h0
          · exact (hvalid j1).1 (h0 ▸ hw1_0)
          · rcases Finset.mem_insert.mp h0 with h0 | h0
            · exact (hvalid j1).2.1 (h0 ▸ hw1_0)
            · exact valid_ab_add_ne_zero (hvalid j1).2.2 ((Finset.mem_singleton.mp h0) ▸ hw1_0)
      rw [hw12_eq_v1] at hsum_j2
      have h3sub : ({i0, j1, j2} : Finset (Fin (4 * e))) ⊆ C.filter (fun k => v1 ∈ freqOf a b k) := by
        intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hi0C, hv1_i0⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp (hN0_sub hj1)).2, hv1_j1⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp (hN0_sub hj2N0)).2, hsum_j2⟩
      have hcard3 : ({i0, j1, j2} : Finset (Fin (4 * e))).card = 3 := by
        have h1 : i0 ≠ j1 := (Finset.mem_erase.mp (hN0_sub hj1)).1.symm
        have h2 : i0 ≠ j2 := (Finset.mem_erase.mp (hN0_sub hj2N0)).1.symm
        simp [h1, h2, hj2_ne1.symm]
      have hle := Finset.card_le_card h3sub
      have hd2 := hi0_deg v1 hv1_i0
      dsimp only [deg] at hd2
      omega

    have hN0_eq : N0 = {j1, j2, j3} := by
      have hsub : ({j1, j2, j3} : Finset (Fin (4 * e))) ⊆ N0 := by
        intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> assumption
      have hcard3 : ({j1, j2, j3} : Finset (Fin (4 * e))).card = 3 := by
        simp [hj2_ne1.symm, hj3_ne1.symm, hj2_ne3]
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard3, hN0_card3])).symm

    have hno_cross : ∀ x ∈ insert i0 N0, ∀ y ∈ C2, ¬ adjOf a b x y := by
      intro x hx y hy ⟨v, hvx, hvy⟩
      have hvS : v ∈ S := Submodule.mem_sup_right (freqOf_subset_spanOf a b hy v hvy)
      simp only [Finset.mem_insert] at hx
      rcases hx with hxi0 | hxN0
      · rw [hxi0] at hvx
        have hy_nN : y ∉ N0 := (Finset.mem_sdiff.mp hy).2
        have hy_er : y ∈ C.erase i0 := (Finset.mem_sdiff.mp hy).1
        exact hy_nN (Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hy_er).2, (Finset.mem_erase.mp hy_er).1,
          Finset.not_disjoint_iff.mpr ⟨v, hvy, hvx⟩⟩)
      · have hnx : ¬ spanOf a b {x} ≤ S := by
          rw [hN0_eq] at hxN0; simp only [Finset.mem_insert, Finset.mem_singleton] at hxN0
          rcases hxN0 with rfl | rfl | rfl <;> assumption
        have hv_ni0 : v ∉ freqOf a b i0 := by
          intro hvi0
          have hy_nN : y ∉ N0 := (Finset.mem_sdiff.mp hy).2
          have hy_er : y ∈ C.erase i0 := (Finset.mem_sdiff.mp hy).1
          exact hy_nN (Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hy_er).2, (Finset.mem_erase.mp hy_er).1,
            Finset.not_disjoint_iff.mpr ⟨v, hvy, hvi0⟩⟩)
        exact hout_S x hxN0 hnx v hvx hv_ni0 hvS

    obtain ⟨y0, hy0⟩ := Finset.card_pos.mp (by rw [hN0_sum_zero.2]; omega : 0 < C2.card)
    have hy0C : y0 ∈ C := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hy0).1).2
    have heqv := hC_conn i0 hi0C y0 hy0C
    have hstay : ∀ u w, Relation.EqvGen (fun p q => p ∈ C ∧ q ∈ C ∧ adjOf a b p q) u w →
        (u ∈ insert i0 N0 ↔ w ∈ insert i0 N0) := by
      intro u w huw
      induction huw with
      | rel u w h =>
        constructor
        · intro hu
          by_contra hw
          have hwC2 : w ∈ C2 := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨fun heq => hw (heq ▸ Finset.mem_insert_self _ _), h.2.1⟩,
            fun hN => hw (Finset.mem_insert_of_mem hN)⟩
          exact hno_cross u hu w hwC2 h.2.2
        · intro hw
          by_contra hu
          have huC2 : u ∈ C2 := Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨fun heq => hu (heq ▸ Finset.mem_insert_self _ _), h.1⟩,
            fun hN => hu (Finset.mem_insert_of_mem hN)⟩
          obtain ⟨v, hvu, hvw⟩ := h.2.2
          exact hno_cross w hw u huC2 ⟨v, hvw, hvu⟩
      | refl _ => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ i1 i2 => exact i1.trans i2
    have hy0_in : y0 ∈ insert i0 N0 := (hstay i0 y0 heqv).mp (Finset.mem_insert_self _ _)
    simp only [Finset.mem_insert] at hy0_in
    rcases hy0_in with rfl | hN
    · exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp hy0).1).1 rfl
    · exact (Finset.mem_sdiff.mp hy0).2 hN

  have hC_le : spanOf a b C ≤ U0 ⊔ spanOf a b C2 := by
    unfold spanOf
    rw [Submodule.span_le]
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_image] at hv
    rcases hv with ⟨j, hjC, rfl⟩ | ⟨j, hjC, rfl⟩
    · by_cases hji0 : j = i0
      · subst hji0; exact Submodule.mem_sup_left (freqOf_subset_spanOf a b (Finset.mem_singleton_self j) (a j) (by simp [freqOf]))
      · by_cases hjN0 : j ∈ N0
        · exact hN0_le_sup j hjN0 (freqOf_subset_spanOf a b (Finset.mem_singleton_self j) (a j) (by simp [freqOf]))
        · exact Submodule.mem_sup_right (freqOf_subset_spanOf a b (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hji0, hjC⟩, hjN0⟩) (a j) (by simp [freqOf]))
    · by_cases hji0 : j = i0
      · subst hji0; exact Submodule.mem_sup_left (freqOf_subset_spanOf a b (Finset.mem_singleton_self j) (b j) (by simp [freqOf]))
      · by_cases hjN0 : j ∈ N0
        · exact hN0_le_sup j hjN0 (freqOf_subset_spanOf a b (Finset.mem_singleton_self j) (b j) (by simp [freqOf]))
        · exact Submodule.mem_sup_right (freqOf_subset_spanOf a b (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hji0, hjC⟩, hjN0⟩) (b j) (by simp [freqOf]))
  have hrk_le := Submodule.finrank_mono hC_le
  unfold rkOf at hrk
  omega

lemma sum_finrank_inf_le_of_finrank_sup_eq {n : ℕ} {α : Type*} [DecidableEq α]
    (P : Finset α) (f : α → Submodule F (Vec n))
    (heq : Module.finrank F (P.sup f : Submodule F (Vec n)) = ∑ x ∈ P, Module.finrank F (f x))
    (H : Submodule F (Vec n)) :
    (∑ x ∈ P, Module.finrank F (H ⊓ f x : Submodule F (Vec n))) ≤ Module.finrank F H := by
  have hmain : ∀ Q : Finset α, Q ⊆ P →
      Module.finrank F (Q.sup f : Submodule F (Vec n)) = ∑ x ∈ Q, Module.finrank F (f x) →
      (∑ x ∈ Q, Module.finrank F (H ⊓ f x : Submodule F (Vec n))) ≤
        Module.finrank F (Q.sup (fun x => H ⊓ f x) : Submodule F (Vec n)) := by
    intro Q
    induction Q using Finset.induction with
    | empty => intro _ _; simp
    | insert x s hx ih =>
      intro hsub hQeq
      rw [Finset.sup_insert, Finset.sum_insert hx] at hQeq
      have hle_s := finrank_finset_sup_le s f
      have hsup_eq := Submodule.finrank_sup_add_finrank_inf_eq (f x) (s.sup f)
      have hs_eq : Module.finrank F (s.sup f : Submodule F (Vec n)) = ∑ y ∈ s, Module.finrank F (f y) := by omega
      have hinf0 : Module.finrank F (f x ⊓ s.sup f : Submodule F (Vec n)) = 0 := by omega
      have hdisj_inf : (H ⊓ f x) ⊓ s.sup (fun y => H ⊓ f y) ≤ f x ⊓ s.sup f := by
        refine le_inf (inf_le_left.trans inf_le_right) ?_
        exact inf_le_right.trans (Finset.sup_mono_fun fun y _ => inf_le_right)
      have hinfH0 : Module.finrank F ((H ⊓ f x) ⊓ s.sup (fun y => H ⊓ f y) : Submodule F (Vec n)) = 0 := by
        have := Submodule.finrank_mono hdisj_inf; omega
      have hsupH := Submodule.finrank_sup_add_finrank_inf_eq (H ⊓ f x) (s.sup (fun y => H ⊓ f y))
      rw [Finset.sum_insert hx, Finset.sup_insert]
      have ihs := ih ((Finset.subset_insert x s).trans hsub) hs_eq
      omega
  have h1 := hmain P (Finset.Subset.refl P) heq
  have hleH : P.sup (fun x => H ⊓ f x) ≤ H := Finset.sup_le fun _ _ => inf_le_left
  have h2 := Submodule.finrank_mono hleH
  omega

lemma rk_univ_3e_structure {n e : ℕ} {a b : Fin (4 * e) → Vec n} {α β : Fin (4 * e) → F}
    (hvalid : ∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (ht : IsTiling a b α β Finset.univ)
    (hrk : rkOf a b Finset.univ = 3 * e) :
    (∀ C ∈ partsOf a b, C.card = 4 ∧ rkOf a b C = 3) ∧
    (partsOf a b).card = e ∧
    Module.finrank F ((partsOf a b).sup (spanOf a b) : Submodule F (Vec n)) =
      ∑ C ∈ partsOf a b, rkOf a b C := by
  have hC_bound : ∀ C ∈ partsOf a b, 4 * rkOf a b C ≤ 3 * C.card := fun C hC =>
    four_rk_le_three_card_any (fun i _ => hvalid i) (isTiling_restrict_part ht hC)
  have hsup_eq_univ : (partsOf a b).sup (spanOf a b) = spanOf a b Finset.univ := by
    rw [← spanOf_biUnion, partsOf_biUnion]
  have hsum_rk_ge : 3 * e ≤ ∑ C ∈ partsOf a b, rkOf a b C := by
    have h1 := finrank_finset_sup_le (partsOf a b) (spanOf a b)
    rw [hsup_eq_univ] at h1
    unfold rkOf at hrk ⊢
    omega
  have hsum_rk_le : 4 * (∑ C ∈ partsOf a b, rkOf a b C) ≤ 3 * (4 * e) := by
    calc 4 * (∑ C ∈ partsOf a b, rkOf a b C)
        = ∑ C ∈ partsOf a b, 4 * rkOf a b C := Finset.mul_sum _ _ _
      _ ≤ ∑ C ∈ partsOf a b, 3 * C.card := Finset.sum_le_sum hC_bound
      _ = 3 * ∑ C ∈ partsOf a b, C.card := (Finset.mul_sum _ _ _).symm
      _ = 3 * (4 * e) := by rw [partsOf_sum_card]
  have hsum_rk_eq : (∑ C ∈ partsOf a b, rkOf a b C) = 3 * e := by omega
  have hC_eq : ∀ C ∈ partsOf a b, 4 * rkOf a b C = 3 * C.card := by
    intro C hC
    by_contra hne
    have hlt : 4 * rkOf a b C < 3 * C.card := lt_of_le_of_ne (hC_bound C hC) hne
    have hstrict : (∑ C' ∈ partsOf a b, 4 * rkOf a b C') < ∑ C' ∈ partsOf a b, 3 * C'.card :=
      Finset.sum_lt_sum hC_bound ⟨C, hC, hlt⟩
    rw [← Finset.mul_sum, ← Finset.mul_sum, hsum_rk_eq, partsOf_sum_card] at hstrict
    omega
  have hall43 : ∀ C ∈ partsOf a b, C.card = 4 ∧ rkOf a b C = 3 := by
    intro C hC
    obtain ⟨c, hc_card, hc1⟩ := part_card_dvd_four hvalid ht hC
    have h4 := hC_eq C hC
    have hrkC : rkOf a b C = 3 * c := by omega
    have hc_eq1 : c = 1 := rk_eq_three_c_imp_c_eq_one hvalid ht hC hc_card hc1 hrkC
    subst hc_eq1
    exact ⟨hc_card, hrkC⟩
  have hparts_card : (partsOf a b).card = e := by
    have h := partsOf_sum_card a b
    have h4 : (∑ C ∈ partsOf a b, C.card) = ∑ _C ∈ partsOf a b, 4 :=
      Finset.sum_congr rfl fun C hC => (hall43 C hC).1
    rw [h4, Finset.sum_const, smul_eq_mul] at h
    omega
  refine ⟨hall43, hparts_card, ?_⟩
  rw [hsup_eq_univ]
  unfold rkOf at hrk hsum_rk_eq ⊢
  rw [hrk, hsum_rk_eq]

lemma sec5_zmod2_add_self (a : F) : a + a = 0 := by
  fin_cases a <;> decide

lemma sec5_vec_add_self {n : ℕ} (x : Vec n) : x + x = 0 := by
  ext i
  exact sec5_zmod2_add_self (x i)

lemma zmod2_eq_of_add_eq_zero : ∀ a b : F, a + b = 0 → a = b := by
  decide

lemma zmod2_eq_of_decide_ne_zero :
    ∀ a b : F, decide (a ≠ 0) = decide (b ≠ 0) → a = b := by
  decide

lemma zmod2_mul_of_add_eq :
    ∀ u v c : F, u + v = c → u * v = (c + 1) * u := by
  decide

def step {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n) (bias : List Bool → F)
    (x : Vec n) (p : List Bool) : List Bool :=
  if p ∈ T then p ++ [decide (dotProduct (ask p) x + bias p ≠ 0)] else p

def run {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n) (bias : List Bool → F)
    (x : Vec n) : List Bool :=
  (List.range T.card).foldl
    (fun (p : List Bool) _ =>
      if p ∈ T then p ++ [decide (dotProduct (ask p) x + bias p ≠ 0)] else p) []

def runStep {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n) (bias : List Bool → F)
    (x : Vec n) (k : ℕ) : List Bool :=
  (step T ask bias x)^[k] []

lemma foldl_range_const {α : Type*} (f : α → α) :
    ∀ k (a : α), (List.range k).foldl (fun p _ => f p) a = f^[k] a
  | 0, a => rfl
  | k + 1, a => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_range_const f k a, Function.iterate_succ_apply']

lemma run_eq_runStep {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) (x : Vec n) :
    run T ask bias x = runStep T ask bias x T.card := by
  simpa [run, runStep, step] using foldl_range_const (step T ask bias x) T.card []

lemma step_of_not_mem {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) (x : Vec n) {p : List Bool} (hp : p ∉ T) :
    step T ask bias x p = p := by
  simp [step, hp]

lemma iterate_step_of_not_mem {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) (x : Vec n) {p : List Bool} (hp : p ∉ T) :
    ∀ m, (step T ask bias x)^[m] p = p
  | 0 => rfl
  | m + 1 => by
    rw [Function.iterate_succ_apply, step_of_not_mem T ask bias x hp,
      iterate_step_of_not_mem T ask bias x hp m]

lemma runStep_invariant {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) (x : Vec n) :
    ∀ k,
      let p := runStep T ask bias x k
      p.length ≤ k ∧
      (p.length < k → p ∉ T) ∧
      (∀ j < p.length, p.take j ∈ T) ∧
      (∀ j < p.length,
        p.take (j + 1) =
          p.take j ++ [decide (dotProduct (ask (p.take j)) x + bias (p.take j) ≠ 0)])
  | 0 => by
    simp [runStep]
  | k + 1 => by
    obtain ⟨hlen, hstop, hpre, hbit⟩ := runStep_invariant T ask bias x k
    set p := runStep T ask bias x k with hp_def
    have hsucc : runStep T ask bias x (k + 1) = step T ask bias x p := by
      simp [runStep, hp_def, Function.iterate_succ_apply']
    dsimp only
    rw [hsucc]
    by_cases hmem : p ∈ T
    · have hlen_eq : p.length = k := by
        by_contra hne
        exact hstop (lt_of_le_of_ne hlen hne) hmem
      have hstep : step T ask bias x p =
          p ++ [decide (dotProduct (ask p) x + bias p ≠ 0)] := by
        simp [step, hmem]
      rw [hstep]
      have hlen' : (p ++ [decide (dotProduct (ask p) x + bias p ≠ 0)]).length = k + 1 := by
        simp [hlen_eq]
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro j hj
        rw [hlen'] at hj
        by_cases hjk : j < k
        · rw [List.take_append_of_le_length (by omega)]
          exact hpre j (by omega)
        · have hjeq : j = k := by omega
          subst hjeq
          rw [← hlen_eq, List.take_left]
          exact hmem
      · intro j hj
        rw [hlen'] at hj
        by_cases hjk : j < k
        · rw [List.take_append_of_le_length (by omega),
            List.take_append_of_le_length (by omega)]
          exact hbit j (by omega)
        · have hjeq : j = k := by omega
          subst hjeq
          have htk : (p ++ [decide (dotProduct (ask p) x + bias p ≠ 0)]).take j = p := by
            rw [List.take_append_of_le_length (by omega), ← hlen_eq, List.take_length]
          rw [List.take_of_length_le (by omega), htk]
    · rw [step_of_not_mem T ask bias x hmem]
      refine ⟨by omega, fun _ => hmem, hpre, hbit⟩

lemma run_not_mem {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) (x : Vec n) :
    run T ask bias x ∉ T := by
  rw [run_eq_runStep]
  obtain ⟨hlen, hstop, hpre, _⟩ := runStep_invariant T ask bias x T.card
  set p := runStep T ask bias x T.card
  intro hpT
  have hlen_eq : p.length = T.card := by
    by_contra hne
    exact hstop (lt_of_le_of_ne hlen hne) hpT
  let f : Fin (T.card + 1) → List Bool := fun j => p.take j.val
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : (p.take a.val).length = (p.take b.val).length := congrArg List.length hab
    simp only [List.length_take, hlen_eq] at h1
    have ha : min a.val T.card = a.val := Nat.min_eq_left (by omega)
    have hb : min b.val T.card = b.val := Nat.min_eq_left (by omega)
    rw [ha, hb] at h1
    exact Fin.ext h1
  have hsub : Finset.univ.image f ⊆ T := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨j, _, rfl⟩
    by_cases hj : j.val < T.card
    · exact hpre j.val (by omega)
    · have hjeq : j.val = T.card := by omega
      have : f j = p := by simp [f, hjeq, ← hlen_eq]
      rw [this]
      exact hpT
  have hcard : (Finset.univ.image f).card ≤ T.card := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hfinj, Finset.card_fin] at hcard
  omega

lemma run_prefix_mem {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) (x : Vec n) {j : ℕ} (hj : j < (run T ask bias x).length) :
    (run T ask bias x).take j ∈ T := by
  rw [run_eq_runStep] at hj ⊢
  exact (runStep_invariant T ask bias x T.card).2.2.1 j hj

lemma run_take_succ {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) (x : Vec n) {j : ℕ} (hj : j < (run T ask bias x).length) :
    (run T ask bias x).take (j + 1) =
      (run T ask bias x).take j ++
        [decide (dotProduct (ask ((run T ask bias x).take j)) x +
          bias ((run T ask bias x).take j) ≠ 0)] := by
  rw [run_eq_runStep] at hj ⊢
  exact (runStep_invariant T ask bias x T.card).2.2.2 j hj

lemma run_length_le {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) (x : Vec n) :
    (run T ask bias x).length ≤ T.card := by
  rw [run_eq_runStep]
  exact (runStep_invariant T ask bias x T.card).1

theorem leaf_count_le {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) :
    (Finset.univ.image (run T ask bias)).card ≤ T.card + 1 := by
  set L : Finset (List Bool) := Finset.univ.image (run T ask bias)
  set R : Finset (List Bool) :=
    L.biUnion (fun p => (Finset.range (p.length + 1)).image (fun j => p.take j))
  have hLR : L ⊆ R := by
    intro p hp
    refine Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩
    refine Finset.mem_image.mpr ⟨p.length, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
    exact List.take_length
  have hL_not_T : ∀ p ∈ L, p ∉ T := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨x, _, rfl⟩
    exact run_not_mem T ask bias x
  have hL_sub_sdiff : L ⊆ R \ T := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨hLR hp, hL_not_T p hp⟩
  have hL_add : L.card + (R ∩ T).card ≤ R.card := by
    calc
      L.card + (R ∩ T).card ≤ (R \ T).card + (R ∩ T).card :=
        Nat.add_le_add_right (Finset.card_le_card hL_sub_sdiff) _
      _ = R.card := Finset.card_sdiff_add_card_inter R T
  have hR_sub :
      R ⊆ insert [] (((R ∩ T) ×ˢ (Finset.univ : Finset Bool)).image (fun ub => ub.1 ++ [ub.2])) := by
    intro q hq
    by_cases hq_nil : q = []
    · exact Finset.mem_insert.mpr (Or.inl hq_nil)
    · apply Finset.mem_insert_of_mem
      rcases Finset.mem_biUnion.mp hq with ⟨p, hpL, hqp⟩
      rcases Finset.mem_image.mp hqp with ⟨j, hj, rfl⟩
      have hj_le : j ≤ p.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hj_pos : 0 < j := by
        by_contra h0
        have : j = 0 := by omega
        subst this
        exact hq_nil rfl
      rcases Finset.mem_image.mp hpL with ⟨x, _, rfl⟩
      set j' := j - 1
      have hj'_lt : j' < (run T ask bias x).length := by omega
      have hj_eq : j = j' + 1 := by omega
      rw [hj_eq, run_take_succ T ask bias x hj'_lt]
      refine Finset.mem_image.mpr ⟨((run T ask bias x).take j',
        decide (dotProduct (ask ((run T ask bias x).take j')) x +
          bias ((run T ask bias x).take j') ≠ 0)), ?_, rfl⟩
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      refine Finset.mem_inter.mpr ⟨?_, run_prefix_mem T ask bias x hj'_lt⟩
      refine Finset.mem_biUnion.mpr ⟨run T ask bias x, hpL, ?_⟩
      exact Finset.mem_image.mpr ⟨j', Finset.mem_range.mpr (by omega), rfl⟩
  have hR_card : R.card ≤ 1 + (R ∩ T).card * 2 := by
    calc
      R.card ≤ (insert [] (((R ∩ T) ×ˢ (Finset.univ : Finset Bool)).image
          (fun ub => ub.1 ++ [ub.2]))).card := Finset.card_le_card hR_sub
      _ ≤ 1 + (((R ∩ T) ×ˢ (Finset.univ : Finset Bool)).image
          (fun ub => ub.1 ++ [ub.2])).card := by
        rw [add_comm]
        exact Finset.card_insert_le _ _
      _ ≤ 1 + ((R ∩ T) ×ˢ (Finset.univ : Finset Bool)).card :=
        Nat.add_le_add_left Finset.card_image_le 1
      _ = 1 + (R ∩ T).card * 2 := by
        simp [Finset.card_product]
  have hRT_le : (R ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
  omega

def pathSpan {n : ℕ} (ask : List Bool → Vec n) (p : List Bool) : Submodule F (Vec n) :=
  Submodule.span F {v : Vec n | ∃ k < p.length, v = ask (p.take k)}

theorem run_eq_iff_add_mem_perpSub {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) {p : List Bool} {x0 : Vec n}
    (hx0 : run T ask bias x0 = p) (x : Vec n) :
    run T ask bias x = p ↔ x + x0 ∈ perpSub (pathSpan ask p) := by
  constructor
  · intro hx
    rw [mem_perpSub_iff]
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k, hk, rfl⟩
      have hk_x : k < (run T ask bias x).length := by rwa [hx]
      have hk_x0 : k < (run T ask bias x0).length := by rwa [hx0]
      have h1 := run_take_succ T ask bias x hk_x
      have h2 := run_take_succ T ask bias x0 hk_x0
      rw [hx] at h1
      rw [hx0] at h2
      have h3 := h1.symm.trans h2
      have hdec :
          decide (dotProduct (ask (p.take k)) x + bias (p.take k) ≠ 0) =
          decide (dotProduct (ask (p.take k)) x0 + bias (p.take k) ≠ 0) := by
        have := List.append_cancel_left h3
        exact List.cons.inj this |>.1
      have heq := zmod2_eq_of_decide_ne_zero _ _ hdec
      have hdot : dotProduct (ask (p.take k)) x = dotProduct (ask (p.take k)) x0 := add_right_cancel heq
      rw [dotProduct_add, hdot, sec5_zmod2_add_self]
    · exact zero_dotProduct _
    · intro u w _ _ hu hw
      rw [add_dotProduct, hu, hw, add_zero]
    · intro c u _ hu
      rw [smul_dotProduct, hu, smul_zero]
  · intro hmem
    have hdot_eq : ∀ k < p.length,
        dotProduct (ask (p.take k)) x = dotProduct (ask (p.take k)) x0 := by
      intro k hk
      have hgen : ask (p.take k) ∈ pathSpan ask p :=
        Submodule.subset_span ⟨k, hk, rfl⟩
      have h0 : dotProduct (ask (p.take k)) (x + x0) = 0 := dot_eq_zero_of_mem_perpSub hgen hmem
      rw [dotProduct_add] at h0
      exact zmod2_eq_of_add_eq_zero _ _ h0
    have hprefix : ∀ j ≤ p.length, runStep T ask bias x j = p.take j := by
      intro j
      induction j with
      | zero =>
        intro _
        rfl
      | succ j ih =>
        intro hj
        have hjlt : j < p.length := Nat.lt_of_succ_le hj
        have hprev : runStep T ask bias x j = p.take j := ih (Nat.le_of_lt hjlt)
        have hstep_eq : runStep T ask bias x (j + 1) = step T ask bias x (p.take j) := by
          simp [runStep, Function.iterate_succ_apply', ← hprev]
        rw [hstep_eq]
        have hmemT : p.take j ∈ T := by
          rw [← hx0]
          exact run_prefix_mem T ask bias x0 (by rwa [hx0])
        simp only [step, hmemT, ↓reduceIte]
        rw [hdot_eq j hjlt]
        have hsucc0 := run_take_succ T ask bias x0 (by rwa [hx0])
        rw [hx0] at hsucc0
        exact hsucc0.symm
    have hlen_le : p.length ≤ T.card := by
      rw [← hx0]
      exact run_length_le T ask bias x0
    have hp_not_T : p ∉ T := by
      rw [← hx0]
      exact run_not_mem T ask bias x0
    rw [run_eq_runStep, runStep]
    have hsplit : T.card = (T.card - p.length) + p.length := by omega
    rw [hsplit, Function.iterate_add_apply]
    have hplen : (step T ask bias x)^[p.length] [] = p := by
      simpa [runStep] using hprefix p.length le_rfl
    rw [hplen]
    exact iterate_step_of_not_mem T ask bias x hp_not_T (T.card - p.length)

theorem run_eq_iff_sub_mem_perpSub {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) {p : List Bool} {x0 : Vec n}
    (hx0 : run T ask bias x0 = p) (x : Vec n) :
    run T ask bias x = p ↔ x - x0 ∈ perpSub (pathSpan ask p) := by
  have hsub : x - x0 = x + x0 := by
    ext i
    have h1 : x i - x0 i = x i + x0 i := by
      generalize x i = a
      generalize x0 i = b
      fin_cases a <;> fin_cases b <;> decide
    exact h1
  rw [hsub]
  exact run_eq_iff_add_mem_perpSub T ask bias hx0 x

theorem fiber_eq_coset_card {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) {p : List Bool} {x0 : Vec n}
    (hx0 : run T ask bias x0 = p)  :
    (Finset.univ.filter (fun x => run T ask bias x = p)).card =
      Fintype.card (perpSub (pathSpan ask p)) := by
  symm
  rw [← Finset.card_univ]
  refine Finset.card_bij (fun (y : perpSub (pathSpan ask p)) _ => x0 + y.1) ?_ ?_ ?_
  · intro y _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [run_eq_iff_add_mem_perpSub T ask bias hx0]
    have hcancel : x0 + y.1 + x0 = y.1 := by
      rw [add_comm x0 y.1, add_assoc, sec5_vec_add_self, add_zero]
    rw [hcancel]
    exact y.2
  · intro y1 _ y2 _ h
    exact Subtype.ext (add_left_cancel h)
  · intro x hx
    have hxp : run T ask bias x = p := (Finset.mem_filter.mp hx).2
    have hmem : x + x0 ∈ perpSub (pathSpan ask p) :=
      (run_eq_iff_add_mem_perpSub T ask bias hx0 x).mp hxp
    refine ⟨⟨x + x0, hmem⟩, Finset.mem_univ _, ?_⟩
    dsimp only
    rw [add_comm x x0, ← add_assoc, sec5_vec_add_self, zero_add]

theorem fiber_card_mul_pow_finrank {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) {p : List Bool} {x0 : Vec n}
    (hx0 : run T ask bias x0 = p) :
    (Finset.univ.filter (fun x => run T ask bias x = p)).card *
      2 ^ Module.finrank F (pathSpan ask p) = 2 ^ n := by
  classical
  rw [fiber_eq_coset_card T ask bias hx0, card_perpSub]

theorem parity_tree_lower {n : ℕ} (T : Finset (List Bool)) (ask : List Bool → Vec n)
    (bias : List Bool → F) (e t k L : ℕ)
    (hT : T.card < L)
    (h_rank : ∀ p ∈ Finset.univ.image (run T ask bias),
      (e - t) + ((e - t) - k) ≤ Module.finrank F (pathSpan ask p)) :
    2 ^ ((e - t) + ((e - t) - k)) ≤ L := by
  set s := e - t
  set d := s + (s - k)
  set leaves := Finset.univ.image (run T ask bias)
  have hpart :
      ∑ p ∈ leaves, (Finset.univ.filter (fun x => run T ask bias x = p)).card = 2 ^ n := by
    have h1 := Finset.card_eq_sum_card_fiberwise
      (f := run T ask bias) (s := Finset.univ) (t := leaves)
      (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x))
    rw [← h1, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    simp [F, ZMod.card]
  have hmul : 2 ^ n * 2 ^ d ≤ leaves.card * 2 ^ n := by
    calc
      2 ^ n * 2 ^ d
          = (∑ p ∈ leaves, (Finset.univ.filter (fun x => run T ask bias x = p)).card) * 2 ^ d := by
            rw [hpart]
      _ = ∑ p ∈ leaves,
            (Finset.univ.filter (fun x => run T ask bias x = p)).card * 2 ^ d := by
            rw [Finset.sum_mul]
      _ ≤ ∑ p ∈ leaves, 2 ^ n := by
            refine Finset.sum_le_sum ?_
            intro p hp
            rcases Finset.mem_image.mp hp with ⟨x0, _, hx0⟩
            have hpow : 2 ^ d ≤ 2 ^ Module.finrank F (pathSpan ask p) :=
              Nat.pow_le_pow_right (by omega) (h_rank p hp)
            calc
              (Finset.univ.filter (fun x => run T ask bias x = p)).card * 2 ^ d
                  ≤ (Finset.univ.filter (fun x => run T ask bias x = p)).card *
                      2 ^ Module.finrank F (pathSpan ask p) :=
                    Nat.mul_le_mul_left _ hpow
              _ = 2 ^ n := fiber_card_mul_pow_finrank T ask bias hx0
      _ = leaves.card * 2 ^ n := by
            simp
  have hle_leaves : 2 ^ d ≤ leaves.card := by
    have hpos : 0 < 2 ^ n := by positivity
    rw [mul_comm (2 ^ n) (2 ^ d)] at hmul
    exact Nat.le_of_mul_le_mul_right hmul hpos
  have hleaves_le : leaves.card ≤ T.card + 1 := leaf_count_le T ask bias
  omega

def boolListsOfLen (k : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin k → Bool)).image List.ofFn

def completeTree (q : ℕ) : Finset (List Bool) :=
  (Finset.range q).biUnion boolListsOfLen

lemma mem_boolListsOfLen {k : ℕ} {p : List Bool} :
    p ∈ boolListsOfLen k ↔ p.length = k := by
  simp only [boolListsOfLen, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f, rfl⟩
    exact List.length_ofFn
  · intro hp
    refine ⟨fun i => p.get (i.cast hp.symm), ?_⟩
    apply List.ext_get
    · simp [hp]
    · intro i h1 h2
      simp

lemma card_boolListsOfLen (k : ℕ) : (boolListsOfLen k).card = 2 ^ k := by
  rw [boolListsOfLen, Finset.card_image_of_injective _ List.ofFn_injective,
    Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

lemma mem_completeTree {q : ℕ} {p : List Bool} :
    p ∈ completeTree q ↔ p.length < q := by
  simp only [completeTree, Finset.mem_biUnion, Finset.mem_range, mem_boolListsOfLen]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro hp
    exact ⟨p.length, hp, rfl⟩

lemma card_completeTree_add_one (q : ℕ) : (completeTree q).card + 1 = 2 ^ q := by
  have hdisj : Set.PairwiseDisjoint (Finset.range q : Set ℕ) boolListsOfLen := by
    intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hpi hpj
    rw [mem_boolListsOfLen] at hpi hpj
    exact hij (hpi.symm.trans hpj)
  rw [completeTree, Finset.card_biUnion hdisj]
  have hsum : ∀ m, (∑ k ∈ Finset.range m, (boolListsOfLen k).card) + 1 = 2 ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, card_boolListsOfLen, pow_succ]
      omega
  exact hsum q

def completeAsk {n q : ℕ} (w : Fin q → Vec n) (p : List Bool) : Vec n :=
  if h : p.length < q then w ⟨p.length, h⟩ else 0

lemma list_take_succ_eq_append_getD (p : List Bool) {j : ℕ} (hj : j < p.length) :
    p.take (j + 1) = p.take j ++ [p.getD j false] := by
  have hget : p.getD j false = p[j] := by
    simp [List.getD, List.getElem?_eq_getElem hj]
  rw [hget, List.take_succ_eq_append_getElem hj]

theorem parity_tree_upper {n q L : ℕ} (hL : 2 ^ q ≤ L) (w : Fin q → Vec n) :
    (completeTree q).card < L ∧
    ∀ x : Vec n,
      let p := run (completeTree q) (completeAsk w) (fun _ => 0) x
      p.length = q ∧
      ∀ j : Fin q, p.getD j.val false = decide (dotProduct (w j) x ≠ 0) := by
  refine ⟨?_, ?_⟩
  · have hc := card_completeTree_add_one q
    omega
  · intro x
    set p := run (completeTree q) (completeAsk w) (fun _ => 0) x with hp_def
    have hnot : p ∉ completeTree q := run_not_mem _ _ _ x
    have hge : q ≤ p.length := by
      rw [mem_completeTree] at hnot
      omega
    have hle : p.length ≤ q := by
      by_contra hgt
      have hqlt : q < p.length := by omega
      have hpre := run_prefix_mem (completeTree q) (completeAsk w) (fun _ => 0) x hqlt
      rw [mem_completeTree, List.length_take, Nat.min_eq_left (Nat.le_of_lt hqlt)] at hpre
      omega
    have hlen : p.length = q := le_antisymm hle hge
    refine ⟨hlen, ?_⟩
    intro j
    have hjlt : j.val < p.length := by omega
    have h1 := run_take_succ (completeTree q) (completeAsk w) (fun _ => 0) x hjlt
    have h2 := list_take_succ_eq_append_getD p hjlt
    have h3 : p.take j.val ++ [p.getD j.val false] =
        p.take j.val ++ [decide (dotProduct (completeAsk w (p.take j.val)) x + 0 ≠ 0)] :=
      h2.symm.trans h1
    have hbit : p.getD j.val false =
        decide (dotProduct (completeAsk w (p.take j.val)) x + 0 ≠ 0) :=
      (List.cons.inj (List.append_cancel_left h3)).1
    have htklen : (p.take j.val).length = j.val := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    have hask : completeAsk w (p.take j.val) = w j := by
      have hlt : (p.take j.val).length < q := by omega
      simp only [completeAsk, hlt, ↓reduceDIte]
      congr 1
      exact Fin.ext htklen
    rw [hbit, hask, add_zero]

theorem affine_of_mem_span {n m q : ℕ} (w : Fin q → Vec n)
    (a b : Fin m → Vec n) (i : Fin m) (v : Vec n)
    (hv_span : v ∈ Submodule.span F (Set.range w))
    (hv_freq : v ∈ freqOf a b i)
    {p : List Bool} {x0 : Vec n}
    (hx0 : run (completeTree q) (completeAsk w) (fun _ => 0) x0 = p) :
    ∃ P_i : Vec n, ∃ d_i : F,
      ∀ x : Vec n, run (completeTree q) (completeAsk w) (fun _ => 0) x = p →
        dotProduct (a i) x * dotProduct (b i) x = dotProduct P_i x + d_i := by
  have hplen : p.length = q := by
    have h := (parity_tree_upper (L := 2 ^ q) le_rfl w).2 x0
    simpa [hx0] using h.1
  have hsub : Submodule.span F (Set.range w) ≤ pathSpan (completeAsk w) p := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ?_
    refine ⟨j.val, by omega, ?_⟩
    have htklen : (p.take j.val).length = j.val := by
      rw [List.length_take, Nat.min_eq_left (by omega)]
    have hlt : (p.take j.val).length < q := by omega
    simp only [completeAsk, hlt, ↓reduceDIte]
    congr 1
    exact (Fin.ext htklen).symm
  have hv_path : v ∈ pathSpan (completeAsk w) p := hsub hv_span
  have hv_const : ∀ x : Vec n,
      run (completeTree q) (completeAsk w) (fun _ => 0) x = p →
      dotProduct v x = dotProduct v x0 := by
    intro x hx
    have hmem := (run_eq_iff_add_mem_perpSub (completeTree q) (completeAsk w) (fun _ => 0) hx0 x).mp hx
    have h0 : dotProduct v (x + x0) = 0 := dot_eq_zero_of_mem_perpSub hv_path hmem
    rw [dotProduct_add] at h0
    exact zmod2_eq_of_add_eq_zero _ _ h0
  set c := dotProduct v x0
  simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv_freq
  rcases hv_freq with rfl | rfl | rfl
  · refine ⟨c • b i, 0, ?_⟩
    intro x hx
    rw [hv_const x hx, smul_dotProduct, smul_eq_mul, add_zero]
  · refine ⟨c • a i, 0, ?_⟩
    intro x hx
    rw [hv_const x hx, mul_comm, smul_dotProduct, smul_eq_mul, add_zero]
  · refine ⟨(c + 1) • a i, 0, ?_⟩
    intro x hx
    have hsum : dotProduct (a i) x + dotProduct (b i) x = c := by
      simpa [add_dotProduct] using hv_const x hx
    rw [zmod2_mul_of_add_eq _ _ _ hsum, smul_dotProduct, smul_eq_mul, add_zero]

end

end aux

namespace sec4

open scoped Classical
noncomputable section

abbrev F := ZMod 2
abbrev Vec (n : ℕ) := Fin n → F

lemma zmod2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_self (a : F) : a + a = 0 := by
  fin_cases a <;> decide

lemma vec_add_self {n : ℕ} (v : Vec n) : v + v = 0 := by
  ext i; exact zmod2_add_self (v i)

def signZ (a : F) : ℤ := if a = 0 then 1 else -1

lemma signZ_add (a b : F) : signZ (a + b) = signZ a * signZ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma signZ_inj {a b : F} (h : signZ a = signZ b) : a = b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [signZ] at h ⊢

lemma signZ_pm_one (a : F) : signZ a = 1 ∨ signZ a = -1 := by
  fin_cases a <;> decide

lemma exists_signZ {s : ℤ} (hs : s = 1 ∨ s = -1) : ∃ a : F, signZ a = s := by
  rcases hs with rfl | rfl
  · exact ⟨0, by simp [signZ]⟩
  · exact ⟨1, by simp [signZ]⟩

def freqOf {n : ℕ} {I : Type*} (a b : I → Vec n) (i : I) : Finset (Vec n) :=
  {a i, b i, a i + b i}

def spanOf {n : ℕ} {I : Type*} (a b : I → Vec n) (S : Finset I) : Submodule F (Vec n) :=
  Submodule.span F (↑(S.image a ∪ S.image b) : Set (Vec n))

def rkOf {n : ℕ} {I : Type*} (a b : I → Vec n) (S : Finset I) : ℕ :=
  Module.finrank F (spanOf a b S)

def freqsOf {n : ℕ} {I : Type*} (a b : I → Vec n) (S : Finset I) : Finset (Vec n) :=
  S.biUnion (freqOf a b)

def rowCoeff {n : ℕ} {I : Type*} (a b : I → Vec n) (α β : I → F) (i : I) (v : Vec n) : ℤ :=
  (if a i = v then signZ (α i) else 0) +
  (if b i = v then signZ (β i) else 0) +
  (if a i + b i = v then signZ (α i + β i) else 0)

def IsTiling {n : ℕ} {I : Type*} (a b : I → Vec n) (α β : I → F) (C : Finset I) : Prop :=
  ∀ v : Vec n, v ≠ 0 → (∑ i ∈ C, rowCoeff a b α β i v) = 0

lemma valid_ab_add_ne_zero {n : ℕ} {a b : Vec n} (hab : a ≠ b) : a + b ≠ 0 := by
  intro h; apply hab; ext i
  have hi := congrFun h i; simp only [Pi.add_apply, Pi.zero_apply] at hi
  rcases zmod2_cases (a i) with h1 | h1 <;> rcases zmod2_cases (b i) with h2 | h2 <;>
    simp [h1, h2] at hi ⊢

lemma valid_ab_distinct {n : ℕ} {a b : Vec n} (h : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) :
    a ≠ b ∧ a ≠ a + b ∧ b ≠ a + b ∧ a + b ≠ 0 := by
  refine ⟨h.2.2, ?_, ?_, valid_ab_add_ne_zero h.2.2⟩
  · intro heq; apply h.2.1
    have := congrArg (a + ·) heq
    simpa [← add_assoc, vec_add_self] using this.symm
  · intro heq; apply h.1
    have := congrArg (· + b) heq
    simpa [add_assoc, vec_add_self] using this.symm

lemma mem_freqOf_ne_zero {n : ℕ} {I : Type*} {a b : I → Vec n} {i : I} {v : Vec n}
    (h : a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) (hv : v ∈ freqOf a b i) : v ≠ 0 := by
  simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact h.1
  · exact h.2.1
  · exact valid_ab_add_ne_zero h.2.2

lemma freqOf_card {n : ℕ} {I : Type*} {a b : I → Vec n} {i : I}
    (h : a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) : (freqOf a b i).card = 3 := by
  obtain ⟨h1, h2, h3, _⟩ := valid_ab_distinct h
  simp [freqOf, h1, h2, h3]

lemma mem_spanOf_of_mem_freqOf {n : ℕ} {I : Type*} {a b : I → Vec n} {C : Finset I}
    {i : I} {v : Vec n} (hi : i ∈ C) (hv : v ∈ freqOf a b i) : v ∈ spanOf a b C := by
  have ha : a i ∈ spanOf a b C :=
    Submodule.subset_span (by simp; exact Or.inl ⟨i, hi, rfl⟩)
  have hb : b i ∈ spanOf a b C :=
    Submodule.subset_span (by simp; exact Or.inr ⟨i, hi, rfl⟩)
  simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact (spanOf a b C).add_mem ha hb

lemma rowCoeff_eq_zero_of_not_mem {n : ℕ} {I : Type*} {a b : I → Vec n} {α β : I → F} {i : I} {v : Vec n}
    (hv : v ∉ freqOf a b i) : rowCoeff a b α β i v = 0 := by
  simp only [freqOf, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  simp [rowCoeff, Ne.symm hv.1, Ne.symm hv.2.1, Ne.symm hv.2.2]

lemma rowCoeff_pm_one {n : ℕ} {I : Type*} {a b : I → Vec n} {α β : I → F} {i : I} {v : Vec n}
    (h : a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) (hv : v ∈ freqOf a b i) :
    rowCoeff a b α β i v = 1 ∨ rowCoeff a b α β i v = -1 := by
  obtain ⟨h1, h2, h3, _⟩ := valid_ab_distinct h
  simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · simp only [rowCoeff, h1.symm, h2.symm, ite_true, ite_false, add_zero, signZ]; split_ifs <;> simp
  · simp only [rowCoeff, h1, h3.symm, ite_true, ite_false, zero_add, add_zero, signZ]; split_ifs <;> simp
  · simp only [rowCoeff, h2, h3, ite_true, ite_false, zero_add, signZ]; split_ifs <;> simp

lemma even_card_of_sum_pm_one_eq_zero {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ)
    (hpm : ∀ i ∈ S, f i = 1 ∨ f i = -1) (hsum : ∑ i ∈ S, f i = 0) :
    Even S.card := by
  let P := S.filter (fun i => f i = 1)
  let N := S.filter (fun i => f i = -1)
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro i hiP hiN
    simp only [P, N, Finset.mem_filter] at hiP hiN
    omega
  have hunion : P ∪ N = S := by
    ext i
    simp only [P, N, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
    · intro hi; rcases hpm i hi with h1 | h2
      · exact Or.inl ⟨hi, h1⟩
      · exact Or.inr ⟨hi, h2⟩
  have hcard : S.card = P.card + N.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hsum' : ∑ i ∈ S, f i = (P.card : ℤ) - (N.card : ℤ) := by
    rw [← hunion, Finset.sum_union hdisj]
    have hP : ∑ i ∈ P, f i = (P.card : ℤ) := by
      calc ∑ i ∈ P, f i = ∑ _i ∈ P, (1 : ℤ) :=
            Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2
        _ = (P.card : ℤ) := by simp
    have hN : ∑ i ∈ N, f i = -(N.card : ℤ) := by
      calc ∑ i ∈ N, f i = ∑ _i ∈ N, (-1 : ℤ) :=
            Finset.sum_congr rfl fun i hi => (Finset.mem_filter.mp hi).2
        _ = -(N.card : ℤ) := by simp
    omega
  have hPN : P.card = N.card := by omega
  refine ⟨P.card, ?_⟩
  omega

lemma deg_even_of_isTiling {n : ℕ} {I : Type*} [DecidableEq I]
    {a b : I → Vec n} {α β : I → F} {C : Finset I}
    (hvalid : ∀ i ∈ C, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (htil : IsTiling a b α β C) {v : Vec n} (hv : v ≠ 0) :
    Even (C.filter (fun i => v ∈ freqOf a b i)).card := by
  apply even_card_of_sum_pm_one_eq_zero _ (fun i => rowCoeff a b α β i v)
  · intro i hi
    simp only [Finset.mem_filter] at hi
    exact rowCoeff_pm_one (hvalid i hi.1) hi.2
  · have h1 := htil v hv
    rw [← h1]
    refine Finset.sum_subset (Finset.filter_subset _ C) fun i hiC hnot => ?_
    simp only [Finset.mem_filter] at hnot
    exact rowCoeff_eq_zero_of_not_mem (fun hvmem => hnot ⟨hiC, hvmem⟩)

theorem comp4_affined_bounds {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → Vec n) (C : Finset I)
    (hvalid : ∀ i ∈ C, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hcard : C.card = 4)
    (_hrk : rkOf a b C = 3)
    (hex : ∃ α0 β0 : I → F, IsTiling a b α0 β0 C)
    (H : Submodule F (Vec n)) :
    let M := C.filter (fun i => ∃ v ∈ freqOf a b i, v ∈ H)
    let hC := Module.finrank F (H ⊓ spanOf a b C : Submodule F (Vec n))
    M.card ≤ 4 * hC ∧
    M.card ≤ 2 * hC + if (∃ v : Vec n, ∀ i ∈ C, v ∈ freqOf a b i) then 2 else 0 := by
  intro M hC
  have hMle4 : M.card ≤ 4 := (Finset.card_le_card (Finset.filter_subset _ C)).trans_eq hcard
  by_cases h0 : hC = 0
  · have hM0 : M = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro i hi
      simp only [M, Finset.mem_filter] at hi
      obtain ⟨hiC, v, hvfreq, hvH⟩ := hi
      have hvS : v ∈ spanOf a b C := mem_spanOf_of_mem_freqOf hiC hvfreq
      have hvInf : v ∈ (H ⊓ spanOf a b C : Submodule F (Vec n)) := ⟨hvH, hvS⟩
      have hbot : (H ⊓ spanOf a b C : Submodule F (Vec n)) = ⊥ :=
        Submodule.finrank_eq_zero.mp h0
      rw [hbot, Submodule.mem_bot] at hvInf
      exact mem_freqOf_ne_zero (hvalid i hiC) hvfreq hvInf
    rw [hM0, Finset.card_empty]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  · by_cases h1 : hC = 1
    · refine ⟨by omega, ?_⟩
      let S := (H ⊓ spanOf a b C : Submodule F (Vec n))
      have hcardS : Fintype.card S = 2 := by
        have hp := Module.card_eq_pow_finrank (K := F) (V := S)
        simpa [S, hC, h1, ZMod.card] using hp
      have herase1 : ((Finset.univ : Finset S).erase 0).card = 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, hcardS]
      obtain ⟨v0, hv0eq⟩ := Finset.card_eq_one.mp herase1
      have hv0mem : v0 ∈ (Finset.univ : Finset S).erase 0 := by rw [hv0eq]; simp
      have hv0ne : v0 ≠ 0 := (Finset.mem_erase.mp hv0mem).1
      have hv0_ne_zero : (v0 : Vec n) ≠ 0 := fun hz => hv0ne (Subtype.ext hz)
      have hMeq : M = C.filter (fun i => (v0 : Vec n) ∈ freqOf a b i) := by
        ext i
        simp only [M, Finset.mem_filter]
        constructor
        · rintro ⟨hiC, v, hvfreq, hvH⟩
          refine ⟨hiC, ?_⟩
          have hvInf : v ∈ S := ⟨hvH, mem_spanOf_of_mem_freqOf hiC hvfreq⟩
          have hvne : (⟨v, hvInf⟩ : S) ≠ 0 := fun hz =>
            mem_freqOf_ne_zero (hvalid i hiC) hvfreq (congrArg Subtype.val hz)
          have hmem : (⟨v, hvInf⟩ : S) ∈ (Finset.univ : Finset S).erase 0 :=
            Finset.mem_erase.mpr ⟨hvne, Finset.mem_univ _⟩
          rw [hv0eq, Finset.mem_singleton] at hmem
          have hveq : v = (v0 : Vec n) := congrArg Subtype.val hmem
          rwa [← hveq]
        · rintro ⟨hiC, hv0freq⟩
          exact ⟨hiC, v0.1, hv0freq, v0.2.1⟩
      obtain ⟨α0, β0, htil⟩ := hex
      have heven : Even M.card := by
        rw [hMeq]
        exact deg_even_of_isTiling hvalid htil hv0_ne_zero
      obtain ⟨k, hk⟩ := heven
      split_ifs with hcommon
      · omega
      · have hne4 : M.card ≠ 4 := by
          intro hM4
          apply hcommon
          refine ⟨v0.1, fun i hiC => ?_⟩
          have hsub : M ⊆ C := Finset.filter_subset _ C
          have hMC : M = C := Finset.eq_of_subset_of_card_le hsub (by omega)
          have hiM : i ∈ M := by rwa [hMC]
          rw [hMeq, Finset.mem_filter] at hiM
          exact hiM.2
        omega
    · have hge2 : 2 ≤ hC := by omega
      exact ⟨by omega, by omega⟩

theorem comp4_kill_questions {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → Vec n) (C : Finset I)
    (_hvalid : ∀ i ∈ C, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (_hcard : C.card = 4)
    (hrk : rkOf a b C = 3)
    (_hex : ∃ α0 β0 : I → F, IsTiling a b α0 β0 C) :
    ((∃ v : Vec n, ∀ i ∈ C, v ∈ freqOf a b i) →
      ∃ w : Vec n, ∀ i ∈ C, ∃ v ∈ freqOf a b i, v ∈ Submodule.span F ({w} : Set (Vec n))) ∧
    (∃ w1 w2 : Vec n, ∀ i ∈ C, ∃ v ∈ freqOf a b i, v ∈ Submodule.span F ({w1, w2} : Set (Vec n))) := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, fun i hi => ⟨v, hv i hi, Submodule.subset_span (Set.mem_singleton v)⟩⟩
  · have hfin : Module.finrank F (spanOf a b C) = Module.finrank F (Vec 3) := by
      dsimp [rkOf] at hrk; rw [hrk]; simp [Vec]
    let e : spanOf a b C ≃ₗ[F] Vec 3 := LinearEquiv.ofFinrankEq (spanOf a b C) (Vec 3) hfin
    let u1 : Vec 3 := ![1, 0, 0]
    let u2 : Vec 3 := ![0, 1, 0]
    refine ⟨(e.symm u1).1, (e.symm u2).1, fun i hi => ?_⟩
    have haS : a i ∈ spanOf a b C := mem_spanOf_of_mem_freqOf hi (by simp [freqOf])
    have hbS : b i ∈ spanOf a b C := mem_spanOf_of_mem_freqOf hi (by simp [freqOf])
    let x : Vec 3 := e ⟨a i, haS⟩
    let y : Vec 3 := e ⟨b i, hbS⟩
    have hmem_span : ∀ z : Vec 3, z 2 = 0 →
        (e.symm z).1 ∈ Submodule.span F ({(e.symm u1).1, (e.symm u2).1} : Set (Vec n)) := by
      intro z hz
      have hzeq : z = z 0 • u1 + z 1 • u2 := by
        ext j
        fin_cases j <;> simp [u1, u2, hz]
      have hsymm : (e.symm z).1 = z 0 • (e.symm u1).1 + z 1 • (e.symm u2).1 := by
        have := congrArg (fun t => (e.symm t).1) hzeq
        simpa [map_add, map_smul] using this
      rw [hsymm]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    rcases zmod2_cases (x 2) with hx0 | hx1
    · refine ⟨a i, by simp [freqOf], ?_⟩
      have heq : (e.symm x).1 = a i := by simp [x]
      rw [← heq]
      exact hmem_span x hx0
    · rcases zmod2_cases (y 2) with hy0 | hy1
      · refine ⟨b i, by simp [freqOf], ?_⟩
        have heq : (e.symm y).1 = b i := by simp [y]
        rw [← heq]
        exact hmem_span y hy0
      · refine ⟨a i + b i, by simp [freqOf], ?_⟩
        have hxy2 : (x + y) 2 = 0 := by simp [hx1, hy1]; decide
        have heq : (e.symm (x + y)).1 = a i + b i := by
          have : e.symm (x + y) = ⟨a i, haS⟩ + ⟨b i, hbS⟩ := by
            rw [map_add]; simp [x, y]
          exact congrArg Subtype.val this
        rw [← heq]
        exact hmem_span (x + y) hxy2

private def rc (a b : Vec 3) (α β : F) (v : Vec 3) : ℤ :=
  (if a = v then signZ α else 0) +
  (if b = v then signZ β else 0) +
  (if a + b = v then signZ (α + β) else 0)

private lemma rc_a {a b : Vec 3} (h : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) (α β : F) :
    rc a b α β a = signZ α := by
  obtain ⟨h1, h2, _, _⟩ := valid_ab_distinct h
  simp [rc, h1.symm, h2.symm]

private lemma rc_b {a b : Vec 3} (h : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) (α β : F) :
    rc a b α β b = signZ β := by
  obtain ⟨h1, _, h3, _⟩ := valid_ab_distinct h
  simp [rc, h1, h3.symm]

private lemma rc_ab {a b : Vec 3} (h : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) (α β : F) :
    rc a b α β (a + b) = signZ α * signZ β := by
  obtain ⟨_, h2, h3, _⟩ := valid_ab_distinct h
  simp [rc, h2, h3, signZ_add]

private lemma rc_prod {a b : Vec 3} (h : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) (α β : F)
    {u v w : Vec 3}
    (hu : u ∈ ({a, b, a + b} : Finset (Vec 3)))
    (hv : v ∈ ({a, b, a + b} : Finset (Vec 3)))
    (hw : w ∈ ({a, b, a + b} : Finset (Vec 3)))
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    rc a b α β w = rc a b α β u * rc a b α β v := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl <;>
  rcases hv with rfl | rfl | rfl <;>
  rcases hw with rfl | rfl | rfl
  all_goals
    first
    | exact absurd rfl huv
    | exact absurd rfl huw
    | exact absurd rfl hvw
    | (simp only [rc_a h, rc_b h, rc_ab h]; done)
    | (simp only [rc_a h, rc_b h, rc_ab h];
       rcases signZ_pm_one α with hα | hα <;> rcases signZ_pm_one β with hβ | hβ <;>
         simp [hα, hβ])

private lemma rc_exists_unique_pair {a b : Vec 3} (h : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)
    {u v : Vec 3}
    (hu : u ∈ ({a, b, a + b} : Finset (Vec 3)))
    (hv : v ∈ ({a, b, a + b} : Finset (Vec 3)))
    (huv : u ≠ v) {su sv : ℤ}
    (hsu : su = 1 ∨ su = -1) (hsv : sv = 1 ∨ sv = -1) :
    ∃! p : F × F, rc a b p.1 p.2 u = su ∧ rc a b p.1 p.2 v = sv := by
  obtain ⟨αu, hαu⟩ := exists_signZ hsu
  obtain ⟨αv, hαv⟩ := exists_signZ hsv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact absurd rfl huv
  · refine ⟨(αu, αv), ⟨by rw [rc_a h, hαu], by rw [rc_b h, hαv]⟩, ?_⟩
    rintro ⟨p1, p2⟩ ⟨hp1, hp2⟩
    rw [rc_a h, ← hαu] at hp1; rw [rc_b h, ← hαv] at hp2
    exact Prod.ext (signZ_inj hp1) (signZ_inj hp2)
  · refine ⟨(αu, αu + αv), ⟨by rw [rc_a h, hαu], ?_⟩, ?_⟩
    · rw [rc_ab h, ← signZ_add, ← add_assoc, zmod2_add_self, zero_add, hαv]
    · rintro ⟨p1, p2⟩ ⟨hp1, hp2⟩
      rw [rc_a h, ← hαu] at hp1
      have hp1' : p1 = αu := signZ_inj hp1
      subst hp1'
      rw [rc_ab h, ← signZ_add, ← hαv] at hp2
      have h12 : p1 + p2 = αv := signZ_inj hp2
      have hp2' : p2 = p1 + αv := by
        have := congrArg (p1 + ·) h12
        simpa [← add_assoc, zmod2_add_self] using this
      exact Prod.ext rfl hp2'
  · refine ⟨(αv, αu), ⟨by rw [rc_b h, hαu], by rw [rc_a h, hαv]⟩, ?_⟩
    rintro ⟨p1, p2⟩ ⟨hp1, hp2⟩
    rw [rc_b h, ← hαu] at hp1; rw [rc_a h, ← hαv] at hp2
    exact Prod.ext (signZ_inj hp2) (signZ_inj hp1)
  · exact absurd rfl huv
  · refine ⟨(αu + αv, αu), ⟨by rw [rc_b h, hαu], ?_⟩, ?_⟩
    · rw [rc_ab h, ← signZ_add, add_comm αu αv, add_assoc, zmod2_add_self, add_zero, hαv]
    · rintro ⟨p1, p2⟩ ⟨hp1, hp2⟩
      rw [rc_b h, ← hαu] at hp1
      have hp2' : p2 = αu := signZ_inj hp1
      subst hp2'
      rw [rc_ab h, ← signZ_add, ← hαv] at hp2
      have h12 : p1 + p2 = αv := signZ_inj hp2
      have hp1' : p1 = p2 + αv := by
        have := congrArg (· + p2) h12
        have hp1'' : p1 = αv + p2 := by simpa [add_assoc, zmod2_add_self] using this
        rw [hp1'', add_comm]
      exact Prod.ext hp1' rfl
  · refine ⟨(αv, αu + αv), ⟨?_, by rw [rc_a h, hαv]⟩, ?_⟩
    · rw [rc_ab h, ← signZ_add, add_comm αu αv, ← add_assoc, zmod2_add_self, zero_add, hαu]
    · rintro ⟨p1, p2⟩ ⟨hp1, hp2⟩
      rw [rc_a h, ← hαv] at hp2
      have hp1' : p1 = αv := signZ_inj hp2
      subst hp1'
      rw [rc_ab h, ← signZ_add, ← hαu] at hp1
      have h12 : p1 + p2 = αu := signZ_inj hp1
      have hp2' : p2 = αu + p1 := by
        have := congrArg (p1 + ·) h12
        simpa [← add_assoc, zmod2_add_self, add_comm] using this
      exact Prod.ext rfl hp2'
  · refine ⟨(αu + αv, αv), ⟨?_, by rw [rc_b h, hαv]⟩, ?_⟩
    · rw [rc_ab h, ← signZ_add, add_assoc, zmod2_add_self, add_zero, hαu]
    · rintro ⟨p1, p2⟩ ⟨hp1, hp2⟩
      rw [rc_b h, ← hαv] at hp2
      have hp2' : p2 = αv := signZ_inj hp2
      subst hp2'
      rw [rc_ab h, ← signZ_add, ← hαu] at hp1
      have h12 : p1 + p2 = αu := signZ_inj hp1
      have hp1' : p1 = αu + p2 := by
        have := congrArg (· + p2) h12
        simpa [add_assoc, zmod2_add_self] using this
      exact Prod.ext hp1' rfl
  · exact absurd rfl huv

private lemma rc_card_single {a b : Vec 3} (h : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)
    {u : Vec 3} (hu : u ∈ ({a, b, a + b} : Finset (Vec 3)))
    {su : ℤ} (hsu : su = 1 ∨ su = -1) :
    ((Finset.univ : Finset (F × F)).filter (fun p => rc a b p.1 p.2 u = su)).card = 2 := by
  have hcard3 : ({a, b, a + b} : Finset (Vec 3)).card = 3 := by
    obtain ⟨h1, h2, h3, _⟩ := valid_ab_distinct h
    simp [h1, h2, h3]
  have hexv : ∃ v ∈ ({a, b, a + b} : Finset (Vec 3)), v ≠ u := by
    by_contra hall
    push Not at hall
    have hsub : ({a, b, a + b} : Finset (Vec 3)) ⊆ {u} := fun x hx =>
      Finset.mem_singleton.mpr (hall x hx)
    have := Finset.card_le_card hsub
    simp [hcard3] at this
  obtain ⟨v, hv, hvu⟩ := hexv
  let S := (Finset.univ : Finset (F × F)).filter (fun p => rc a b p.1 p.2 u = su)
  have hbij : S.card = (Finset.univ : Finset Bool).card := by
    refine Finset.card_bij (fun p _ => decide (rc a b p.1 p.2 v = 1)) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro p1 hp1 p2 hp2 heq
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
      have hpm1 : rc a b p1.1 p1.2 v = 1 ∨ rc a b p1.1 p1.2 v = -1 := by
        have := rowCoeff_pm_one (a := fun _ : Unit => a) (b := fun _ : Unit => b)
          (α := fun _ => p1.1) (β := fun _ => p1.2) (i := ()) h hv
        simpa [rowCoeff, rc] using this
      have hpm2 : rc a b p2.1 p2.2 v = 1 ∨ rc a b p2.1 p2.2 v = -1 := by
        have := rowCoeff_pm_one (a := fun _ : Unit => a) (b := fun _ : Unit => b)
          (α := fun _ => p2.1) (β := fun _ => p2.2) (i := ()) h hv
        simpa [rowCoeff, rc] using this
      have hveq : rc a b p1.1 p1.2 v = rc a b p2.1 p2.2 v := by
        rcases hpm1 with h1 | h1 <;> rcases hpm2 with h2 | h2 <;> simp [h1, h2] at heq ⊢
      obtain ⟨p0, _, huniq⟩ := rc_exists_unique_pair h hu hv hvu.symm hsu hpm1
      have e1 := huniq p1 ⟨hp1, rfl⟩
      have e2 := huniq p2 ⟨hp2, hveq.symm⟩
      exact e1.trans e2.symm
    · intro c _
      let sv : ℤ := if c then 1 else -1
      have hsv : sv = 1 ∨ sv = -1 := by cases c <;> simp [sv]
      obtain ⟨p, ⟨hpu, hpv⟩, _⟩ := rc_exists_unique_pair h hu hv hvu.symm hsu hsv
      refine ⟨p, by simp [S, hpu], ?_⟩
      cases c <;> simp [sv] at hpv ⊢ <;> omega
  simpa using hbij

private lemma plane_eq_of_two_mem {a b u v : Vec 3} (h : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)
    (hu : u ∈ ({a, b, a + b} : Finset (Vec 3)))
    (hv : v ∈ ({a, b, a + b} : Finset (Vec 3)))
    (huv : u ≠ v) :
    ({a, b, a + b} : Finset (Vec 3)) = {u, v, u + v} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  have h1 : a + (a + b) = b := by rw [← add_assoc, vec_add_self, zero_add]
  have h2 : b + (a + b) = a := by rw [add_comm a b, ← add_assoc, vec_add_self, zero_add]
  have h3 : (a + b) + a = b := by rw [add_comm, h1]
  have h4 : (a + b) + b = a := by rw [add_comm, h2]
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact absurd rfl huv
  · rfl
  · ext x; simp [h1]; tauto
  · ext x; simp [add_comm]; tauto
  · exact absurd rfl huv
  · ext x; simp [h2]; tauto
  · ext x; simp [h3]; tauto
  · ext x; simp [h4]; tauto
  · exact absurd rfl huv

private lemma span_plane_mem {a b : Vec 3} (x : Vec 3) :
    x ∈ Submodule.span F ({a, b} : Set (Vec 3)) ↔ x = 0 ∨ x ∈ ({a, b, a + b} : Finset (Vec 3)) := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨c1, c2, rfl⟩
    rcases zmod2_cases c1 with rfl | rfl <;> rcases zmod2_cases c2 with rfl | rfl <;> simp
  · rintro (rfl | hx)
    · exact ⟨0, 0, by simp⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
      · exact ⟨1, 1, by simp⟩

private lemma finrank_plane {a b : Vec 3} (h : a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) :
    Module.finrank F (Submodule.span F ({a, b} : Set (Vec 3))) = 2 := by
  have hcard : Fintype.card (Submodule.span F ({a, b} : Set (Vec 3))) = 4 := by
    have hset : (Finset.univ.filter (fun x : Vec 3 => x ∈ Submodule.span F ({a, b} : Set (Vec 3)))) =
        {0, a, b, a + b} := by
      ext x
      simp [span_plane_mem]
    rw [Fintype.card_subtype, hset]
    obtain ⟨h1, h2, h3, h4⟩ := valid_ab_distinct h
    simp [h.1.symm, h.2.1.symm, h4.symm, h1, h2, h3]
  have hpow := Module.card_eq_pow_finrank (K := F) (V := Submodule.span F ({a, b} : Set (Vec 3)))
  simp only [ZMod.card] at hpow
  rw [hcard] at hpow
  have hpow2 : (2 : ℕ) ^ 2 = 2 ^ Module.finrank F (Submodule.span F ({a, b} : Set (Vec 3))) := by
    omega
  exact (Nat.pow_right_injective (by norm_num) hpow2).symm

private lemma planes_inter_nonempty {a1 b1 a2 b2 : Vec 3}
    (h1 : a1 ≠ 0 ∧ b1 ≠ 0 ∧ a1 ≠ b1) (h2 : a2 ≠ 0 ∧ b2 ≠ 0 ∧ a2 ≠ b2) :
    ∃ v : Vec 3, v ∈ ({a1, b1, a1 + b1} : Finset (Vec 3)) ∧
      v ∈ ({a2, b2, a2 + b2} : Finset (Vec 3)) := by
  let P1 := Submodule.span F ({a1, b1} : Set (Vec 3))
  let P2 := Submodule.span F ({a2, b2} : Set (Vec 3))
  have hr1 : Module.finrank F P1 = 2 := finrank_plane h1
  have hr2 : Module.finrank F P2 = 2 := finrank_plane h2
  have hsup : Module.finrank F (P1 ⊔ P2 : Submodule F (Vec 3)) ≤ 3 := by
    calc Module.finrank F (P1 ⊔ P2 : Submodule F (Vec 3))
        ≤ Module.finrank F (Vec 3) := Submodule.finrank_le _
      _ = 3 := by simp [Vec]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq P1 P2
  have hinf : 0 < Module.finrank F (P1 ⊓ P2 : Submodule F (Vec 3)) := by omega
  have hne : (P1 ⊓ P2 : Submodule F (Vec 3)) ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hinf
    omega
  obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hv1 : v ∈ ({a1, b1, a1 + b1} : Finset (Vec 3)) := by
    rcases (span_plane_mem v).mp hv.1 with rfl | hmem
    · exact absurd rfl hvne
    · exact hmem
  have hv2 : v ∈ ({a2, b2, a2 + b2} : Finset (Vec 3)) := by
    rcases (span_plane_mem v).mp hv.2 with rfl | hmem
    · exact absurd rfl hvne
    · exact hmem
  exact ⟨v, hv1, hv2⟩

private lemma vec3_tiling_card (a b : Fin 4 → Vec 3)
    (hvalid : ∀ k : Fin 4, a k ≠ 0 ∧ b k ≠ 0 ∧ a k ≠ b k)
    (hnotall : ∃ k1 k2 : Fin 4, freqOf a b k1 ≠ freqOf a b k2)
    (hex : ∃ α0 β0 : Fin 4 → F, IsTiling a b α0 β0 Finset.univ) :
    ((Finset.univ : Finset ((Fin 4 → F) × (Fin 4 → F))).filter
      (fun p => IsTiling a b p.1 p.2 Finset.univ)).card = 8 := by
  let Til := (Finset.univ : Finset ((Fin 4 → F) × (Fin 4 → F))).filter
    (fun p => IsTiling a b p.1 p.2 Finset.univ)
  let deg : Vec 3 → ℕ := fun v => (Finset.univ.filter (fun k : Fin 4 => v ∈ freqOf a b k)).card
  have hdeg_even : ∀ v : Vec 3, v ≠ 0 → Even (deg v) := by
    intro v hv
    obtain ⟨α0, β0, htil⟩ := hex
    exact deg_even_of_isTiling (fun k _ => hvalid k) htil hv
  have hrc_eq : ∀ (α β : Fin 4 → F) (k : Fin 4) (v : Vec 3),
      rowCoeff a b α β k v = rc (a k) (b k) (α k) (β k) v := fun _ _ _ _ => rfl
  by_cases hcommon : ∃ v0 : Vec 3, v0 ≠ 0 ∧ deg v0 = 4
  ·
    obtain ⟨v0, hv0ne, hv0deg⟩ := hcommon
    have hv0all : ∀ k : Fin 4, v0 ∈ freqOf a b k := by
      have heq : Finset.univ.filter (fun k : Fin 4 => v0 ∈ freqOf a b k) = Finset.univ :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simpa [deg] using hv0deg.ge)
      intro k
      have hk : k ∈ Finset.univ.filter (fun k : Fin 4 => v0 ∈ freqOf a b k) := by
        rw [heq]; exact Finset.mem_univ k
      exact (Finset.mem_filter.mp hk).2

    have hmult2 : ∀ k : Fin 4, (Finset.univ.filter (fun j : Fin 4 => freqOf a b j = freqOf a b k)).card = 2 := by
      intro k
      have hcard3 := freqOf_card (hvalid k)
      have hexu : ∃ u ∈ freqOf a b k, u ≠ v0 := by
        by_contra hall; push Not at hall
        have := Finset.card_le_card (show freqOf a b k ⊆ {v0} from fun x hx =>
          Finset.mem_singleton.mpr (hall x hx))
        simp [hcard3] at this
      obtain ⟨u, huk, huv0⟩ := hexu
      have hf_eq : Finset.univ.filter (fun j : Fin 4 => freqOf a b j = freqOf a b k) =
          Finset.univ.filter (fun j : Fin 4 => u ∈ freqOf a b j) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hjk; rwa [hjk]
        · intro huj
          have h1 := plane_eq_of_two_mem (hvalid j) (hv0all j) huj huv0.symm
          have h2 := plane_eq_of_two_mem (hvalid k) (hv0all k) huk huv0.symm
          exact h1.trans h2.symm
      rw [hf_eq]
      have hune : u ≠ 0 := mem_freqOf_ne_zero (hvalid k) huk
      have hev := hdeg_even u hune
      have hpos : 0 < deg u := Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, huk⟩⟩
      have hle4 : deg u ≤ 4 := by
        calc deg u ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = 4 := by simp
      have hne4 : deg u ≠ 4 := by
        intro h4
        have hall : ∀ j : Fin 4, freqOf a b j = freqOf a b k := by
          have heq' : Finset.univ.filter (fun j : Fin 4 => freqOf a b j = freqOf a b k) = Finset.univ :=
            Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by rw [hf_eq]; simpa [deg] using h4.ge)
          intro j
          have hj : j ∈ Finset.univ.filter (fun j : Fin 4 => freqOf a b j = freqOf a b k) := by
            rw [heq']; exact Finset.mem_univ j
          exact (Finset.mem_filter.mp hj).2
        obtain ⟨k1, k2, hne⟩ := hnotall
        exact hne ((hall k1).trans (hall k2).symm)
      obtain ⟨m, hm⟩ := hev
      dsimp only [deg] at hpos hle4 hne4 hm ⊢
      omega

    let i0 : Fin 4 := 0
    have hS0 : (Finset.univ.filter (fun j : Fin 4 => freqOf a b j = freqOf a b i0)).card = 2 := hmult2 i0
    have hex_i1 : ∃ i1 : Fin 4, i1 ≠ i0 ∧ freqOf a b i1 = freqOf a b i0 := by
      have hi0m : i0 ∈ Finset.univ.filter (fun j : Fin 4 => freqOf a b j = freqOf a b i0) := by simp
      have hpos : 0 < ((Finset.univ.filter (fun j : Fin 4 => freqOf a b j = freqOf a b i0)).erase i0).card := by
        rw [Finset.card_erase_of_mem hi0m, hS0]; omega
      obtain ⟨i1, hi1⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_erase, Finset.mem_filter] at hi1
      exact ⟨i1, hi1.1, hi1.2.2⟩
    obtain ⟨i1, hi10, hPi1⟩ := hex_i1
    have hex_i2 : ∃ i2 : Fin 4, freqOf a b i2 ≠ freqOf a b i0 := by
      by_contra hall; push Not at hall
      obtain ⟨k1, k2, hne⟩ := hnotall
      exact hne ((hall k1).trans (hall k2).symm)
    obtain ⟨i2, hPi2⟩ := hex_i2
    have hS2 : (Finset.univ.filter (fun j : Fin 4 => freqOf a b j = freqOf a b i2)).card = 2 := hmult2 i2
    have hex_i3 : ∃ i3 : Fin 4, i3 ≠ i2 ∧ freqOf a b i3 = freqOf a b i2 := by
      have hi2m : i2 ∈ Finset.univ.filter (fun j : Fin 4 => freqOf a b j = freqOf a b i2) := by simp
      have hpos : 0 < ((Finset.univ.filter (fun j : Fin 4 => freqOf a b j = freqOf a b i2)).erase i2).card := by
        rw [Finset.card_erase_of_mem hi2m, hS2]; omega
      obtain ⟨i3, hi3⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_erase, Finset.mem_filter] at hi3
      exact ⟨i3, hi3.1, hi3.2.2⟩
    obtain ⟨i3, hi32, hPi3⟩ := hex_i3
    have hi20 : i2 ≠ i0 := fun h => hPi2 (by rw [h])
    have hi21 : i2 ≠ i1 := fun h => hPi2 (by rw [h, hPi1])
    have hi30 : i3 ≠ i0 := fun h => hPi2 (by rw [← hPi3, h])
    have hi31 : i3 ≠ i1 := fun h => hPi2 (by rw [← hPi3, h, hPi1])
    have huniv4 : (Finset.univ : Finset (Fin 4)) = {i0, i1, i2, i3} := by
      symm
      refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
      have hc : ({i0, i1, i2, i3} : Finset (Fin 4)).card = 4 := by
        simp [hi10.symm, hi20.symm, hi30.symm, hi21.symm, hi31.symm, hi32.symm]
      simp [hc]

    have hpair_other : ∀ k : Fin 4, ∃ u1 u2 : Vec 3,
        u1 ∈ freqOf a b k ∧ u2 ∈ freqOf a b k ∧ u1 ≠ v0 ∧ u2 ≠ v0 ∧ u1 ≠ u2 ∧
        freqOf a b k = {v0, u1, u2} := by
      intro k
      have hc : ((freqOf a b k).erase v0).card = 2 := by
        rw [Finset.card_erase_of_mem (hv0all k), freqOf_card (hvalid k)]
      obtain ⟨u1, u2, hu12, hset⟩ := Finset.card_eq_two.mp hc
      have hu1m : u1 ∈ (freqOf a b k).erase v0 := by rw [hset]; simp
      have hu2m : u2 ∈ (freqOf a b k).erase v0 := by rw [hset]; simp
      rw [Finset.mem_erase] at hu1m hu2m
      refine ⟨u1, u2, hu1m.2, hu2m.2, hu1m.1, hu2m.1, hu12, ?_⟩
      rw [← Finset.insert_erase (hv0all k), hset]
    obtain ⟨uA1, uA2, huA1, huA2, huA1v0, huA2v0, huA12, hPA⟩ := hpair_other i0
    obtain ⟨uB1, uB2, huB1, huB2, huB1v0, huB2v0, huB12, hPB⟩ := hpair_other i2
    have huA1' : uA1 ∈ freqOf a b i1 := by rw [hPi1]; exact huA1
    have huA2' : uA2 ∈ freqOf a b i1 := by rw [hPi1]; exact huA2
    have huB1' : uB1 ∈ freqOf a b i3 := by rw [hPi3]; exact huB1
    have huB2' : uB2 ∈ freqOf a b i3 := by rw [hPi3]; exact huB2

    have hnotB_of_A : ∀ u ∈ ({uA1, uA2} : Finset (Vec 3)), u ∉ freqOf a b i2 := by
      intro u hu huB
      have huv0 : u ≠ v0 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      have huA : u ∈ freqOf a b i0 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      exact hPi2 ((plane_eq_of_two_mem (hvalid i2) (hv0all i2) huB huv0.symm).trans
        (plane_eq_of_two_mem (hvalid i0) (hv0all i0) huA huv0.symm).symm)
    have hnotA_of_B : ∀ u ∈ ({uB1, uB2} : Finset (Vec 3)), u ∉ freqOf a b i0 := by
      intro u hu huA
      have huv0 : u ≠ v0 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      have huB : u ∈ freqOf a b i2 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      exact hPi2 ((plane_eq_of_two_mem (hvalid i2) (hv0all i2) huB huv0.symm).trans
        (plane_eq_of_two_mem (hvalid i0) (hv0all i0) huA huv0.symm).symm)

    let T := (Finset.univ : Finset ((F × F) × (F × F))).filter (fun q =>
      rc (a i2) (b i2) q.2.1 q.2.2 v0 = - rc (a i0) (b i0) q.1.1 q.1.2 v0)
    have hTcard : T.card = 8 := by
      have h1 : T.card = ∑ q1 : F × F,
          ((Finset.univ : Finset (F × F)).filter (fun q2 =>
            rc (a i2) (b i2) q2.1 q2.2 v0 = - rc (a i0) (b i0) q1.1 q1.2 v0)).card := by
        rw [Finset.card_filter]
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun q1 _ => ?_
        rw [Finset.card_filter]
      rw [h1]
      have h2 : ∀ q1 : F × F,
          ((Finset.univ : Finset (F × F)).filter (fun q2 =>
            rc (a i2) (b i2) q2.1 q2.2 v0 = - rc (a i0) (b i0) q1.1 q1.2 v0)).card = 2 := by
        intro q1
        have hpm : rc (a i0) (b i0) q1.1 q1.2 v0 = 1 ∨ rc (a i0) (b i0) q1.1 q1.2 v0 = -1 := by
          have := rowCoeff_pm_one (a := a) (b := b) (α := fun _ => q1.1) (β := fun _ => q1.2)
            (i := i0) (hvalid i0) (hv0all i0)
          simpa [hrc_eq] using this
        have hneg : -rc (a i0) (b i0) q1.1 q1.2 v0 = 1 ∨ -rc (a i0) (b i0) q1.1 q1.2 v0 = -1 := by
          rcases hpm with h | h <;> simp [h]
        exact rc_card_single (hvalid i2) (hv0all i2) hneg
      simp [h2]

    have hbij : Til.card = T.card := by
      refine Finset.card_bij (fun p _ => ((p.1 i0, p.2 i0), (p.1 i2, p.2 i2))) ?_ ?_ ?_
      · intro p hp
        simp only [Til, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        have hsum4 : ∀ v : Vec 3, v ≠ 0 →
            rowCoeff a b p.1 p.2 i0 v + rowCoeff a b p.1 p.2 i1 v +
            rowCoeff a b p.1 p.2 i2 v + rowCoeff a b p.1 p.2 i3 v = 0 := by
          intro v hv
          have := hp v hv
          rw [huniv4] at this
          simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
            hi10.symm, hi20.symm, hi30.symm, hi21.symm, hi31.symm, hi32.symm,
            or_self, not_false_eq_true, Finset.sum_singleton] at this
          linarith
        have hA1 : rc (a i1) (b i1) (p.1 i1) (p.2 i1) uA1 = -rc (a i0) (b i0) (p.1 i0) (p.2 i0) uA1 := by
          have h := hsum4 uA1 (mem_freqOf_ne_zero (hvalid i0) huA1)
          have h2 : rowCoeff a b p.1 p.2 i2 uA1 = 0 :=
            rowCoeff_eq_zero_of_not_mem (hnotB_of_A uA1 (by simp))
          have h3 : rowCoeff a b p.1 p.2 i3 uA1 = 0 :=
            rowCoeff_eq_zero_of_not_mem (by rw [hPi3]; exact hnotB_of_A uA1 (by simp))
          simp only [hrc_eq] at h h2 h3; linarith
        have hA2 : rc (a i1) (b i1) (p.1 i1) (p.2 i1) uA2 = -rc (a i0) (b i0) (p.1 i0) (p.2 i0) uA2 := by
          have h := hsum4 uA2 (mem_freqOf_ne_zero (hvalid i0) huA2)
          have h2 : rowCoeff a b p.1 p.2 i2 uA2 = 0 :=
            rowCoeff_eq_zero_of_not_mem (hnotB_of_A uA2 (by simp))
          have h3 : rowCoeff a b p.1 p.2 i3 uA2 = 0 :=
            rowCoeff_eq_zero_of_not_mem (by rw [hPi3]; exact hnotB_of_A uA2 (by simp))
          simp only [hrc_eq] at h h2 h3; linarith
        have hB1 : rc (a i3) (b i3) (p.1 i3) (p.2 i3) uB1 = -rc (a i2) (b i2) (p.1 i2) (p.2 i2) uB1 := by
          have h := hsum4 uB1 (mem_freqOf_ne_zero (hvalid i2) huB1)
          have h0 : rowCoeff a b p.1 p.2 i0 uB1 = 0 :=
            rowCoeff_eq_zero_of_not_mem (hnotA_of_B uB1 (by simp))
          have h1 : rowCoeff a b p.1 p.2 i1 uB1 = 0 :=
            rowCoeff_eq_zero_of_not_mem (by rw [hPi1]; exact hnotA_of_B uB1 (by simp))
          simp only [hrc_eq] at h h0 h1; linarith
        have hB2 : rc (a i3) (b i3) (p.1 i3) (p.2 i3) uB2 = -rc (a i2) (b i2) (p.1 i2) (p.2 i2) uB2 := by
          have h := hsum4 uB2 (mem_freqOf_ne_zero (hvalid i2) huB2)
          have h0 : rowCoeff a b p.1 p.2 i0 uB2 = 0 :=
            rowCoeff_eq_zero_of_not_mem (hnotA_of_B uB2 (by simp))
          have h1 : rowCoeff a b p.1 p.2 i1 uB2 = 0 :=
            rowCoeff_eq_zero_of_not_mem (by rw [hPi1]; exact hnotA_of_B uB2 (by simp))
          simp only [hrc_eq] at h h0 h1; linarith
        have hv0A : rc (a i1) (b i1) (p.1 i1) (p.2 i1) v0 = rc (a i0) (b i0) (p.1 i0) (p.2 i0) v0 := by
          rw [rc_prod (hvalid i1) (p.1 i1) (p.2 i1) huA1' huA2'
            (hv0all i1) huA12 huA1v0 huA2v0]
          rw [rc_prod (hvalid i0) (p.1 i0) (p.2 i0) huA1 huA2 (hv0all i0) huA12 huA1v0 huA2v0]
          rw [hA1, hA2]; ring
        have hv0B : rc (a i3) (b i3) (p.1 i3) (p.2 i3) v0 = rc (a i2) (b i2) (p.1 i2) (p.2 i2) v0 := by
          rw [rc_prod (hvalid i3) (p.1 i3) (p.2 i3) huB1' huB2'
            (hv0all i3) huB12 huB1v0 huB2v0]
          rw [rc_prod (hvalid i2) (p.1 i2) (p.2 i2) huB1 huB2 (hv0all i2) huB12 huB1v0 huB2v0]
          rw [hB1, hB2]; ring
        have hv0sum := hsum4 v0 hv0ne
        simp only [hrc_eq] at hv0sum
        linarith
      ·
        intro p1 hp1 p2 hp2 heq
        simp only [Til, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
        have h0eq : (p1.1 i0, p1.2 i0) = (p2.1 i0, p2.2 i0) := congrArg Prod.fst heq
        have h2eq : (p1.1 i2, p1.2 i2) = (p2.1 i2, p2.2 i2) := congrArg Prod.snd heq
        have hget : ∀ p : (Fin 4 → F) × (Fin 4 → F), IsTiling a b p.1 p.2 Finset.univ →
            rc (a i1) (b i1) (p.1 i1) (p.2 i1) uA1 = -rc (a i0) (b i0) (p.1 i0) (p.2 i0) uA1 ∧
            rc (a i1) (b i1) (p.1 i1) (p.2 i1) uA2 = -rc (a i0) (b i0) (p.1 i0) (p.2 i0) uA2 ∧
            rc (a i3) (b i3) (p.1 i3) (p.2 i3) uB1 = -rc (a i2) (b i2) (p.1 i2) (p.2 i2) uB1 ∧
            rc (a i3) (b i3) (p.1 i3) (p.2 i3) uB2 = -rc (a i2) (b i2) (p.1 i2) (p.2 i2) uB2 := by
          intro p hp
          have hsum4 : ∀ v : Vec 3, v ≠ 0 →
              rowCoeff a b p.1 p.2 i0 v + rowCoeff a b p.1 p.2 i1 v +
              rowCoeff a b p.1 p.2 i2 v + rowCoeff a b p.1 p.2 i3 v = 0 := by
            intro v hv
            have := hp v hv
            rw [huniv4] at this
            simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
              hi10.symm, hi20.symm, hi30.symm, hi21.symm, hi31.symm, hi32.symm,
              or_self, not_false_eq_true, Finset.sum_singleton] at this
            linarith
          refine ⟨?_, ?_, ?_, ?_⟩
          · have h := hsum4 uA1 (mem_freqOf_ne_zero (hvalid i0) huA1)
            have h2 := rowCoeff_eq_zero_of_not_mem (α := p.1) (β := p.2) (hnotB_of_A uA1 (by simp))
            have h3 := rowCoeff_eq_zero_of_not_mem (α := p.1) (β := p.2) (i := i3) (by rw [hPi3]; exact hnotB_of_A uA1 (by simp))
            simp only [hrc_eq] at h h2 h3; linarith
          · have h := hsum4 uA2 (mem_freqOf_ne_zero (hvalid i0) huA2)
            have h2 := rowCoeff_eq_zero_of_not_mem (α := p.1) (β := p.2) (hnotB_of_A uA2 (by simp))
            have h3 := rowCoeff_eq_zero_of_not_mem (α := p.1) (β := p.2) (i := i3) (by rw [hPi3]; exact hnotB_of_A uA2 (by simp))
            simp only [hrc_eq] at h h2 h3; linarith
          · have h := hsum4 uB1 (mem_freqOf_ne_zero (hvalid i2) huB1)
            have h0 := rowCoeff_eq_zero_of_not_mem (α := p.1) (β := p.2) (hnotA_of_B uB1 (by simp))
            have h1 := rowCoeff_eq_zero_of_not_mem (α := p.1) (β := p.2) (i := i1) (by rw [hPi1]; exact hnotA_of_B uB1 (by simp))
            simp only [hrc_eq] at h h0 h1; linarith
          · have h := hsum4 uB2 (mem_freqOf_ne_zero (hvalid i2) huB2)
            have h0 := rowCoeff_eq_zero_of_not_mem (α := p.1) (β := p.2) (hnotA_of_B uB2 (by simp))
            have h1 := rowCoeff_eq_zero_of_not_mem (α := p.1) (β := p.2) (i := i1) (by rw [hPi1]; exact hnotA_of_B uB2 (by simp))
            simp only [hrc_eq] at h h0 h1; linarith
        obtain ⟨g1A1, g1A2, g1B1, g1B2⟩ := hget p1 hp1
        obtain ⟨g2A1, g2A2, g2B1, g2B2⟩ := hget p2 hp2
        have h0a : p1.1 i0 = p2.1 i0 := congrArg Prod.fst h0eq
        have h0b : p1.2 i0 = p2.2 i0 := congrArg Prod.snd h0eq
        have h2a : p1.1 i2 = p2.1 i2 := congrArg Prod.fst h2eq
        have h2b : p1.2 i2 = p2.2 i2 := congrArg Prod.snd h2eq
        have h1eq : (p1.1 i1, p1.2 i1) = (p2.1 i1, p2.2 i1) := by
          have hpm1 : -rc (a i0) (b i0) (p1.1 i0) (p1.2 i0) uA1 = 1 ∨
              -rc (a i0) (b i0) (p1.1 i0) (p1.2 i0) uA1 = -1 := by
            rcases rowCoeff_pm_one (a := a) (b := b) (α := p1.1) (β := p1.2) (hvalid i0) huA1 with h | h <;>
              simp [hrc_eq] at h ⊢ <;> simp [h]
          have hpm2 : -rc (a i0) (b i0) (p1.1 i0) (p1.2 i0) uA2 = 1 ∨
              -rc (a i0) (b i0) (p1.1 i0) (p1.2 i0) uA2 = -1 := by
            rcases rowCoeff_pm_one (a := a) (b := b) (α := p1.1) (β := p1.2) (hvalid i0) huA2 with h | h <;>
              simp [hrc_eq] at h ⊢ <;> simp [h]
          obtain ⟨_, _, huniq⟩ := rc_exists_unique_pair (hvalid i1)
            huA1' huA2' huA12 hpm1 hpm2
          have e1 := huniq (p1.1 i1, p1.2 i1) ⟨g1A1, g1A2⟩
          have e2 := huniq (p2.1 i1, p2.2 i1) ⟨by rw [g2A1, h0a, h0b], by rw [g2A2, h0a, h0b]⟩
          exact e1.trans e2.symm
        have h3eq : (p1.1 i3, p1.2 i3) = (p2.1 i3, p2.2 i3) := by
          have hpm1 : -rc (a i2) (b i2) (p1.1 i2) (p1.2 i2) uB1 = 1 ∨
              -rc (a i2) (b i2) (p1.1 i2) (p1.2 i2) uB1 = -1 := by
            rcases rowCoeff_pm_one (a := a) (b := b) (α := p1.1) (β := p1.2) (hvalid i2) huB1 with h | h <;>
              simp [hrc_eq] at h ⊢ <;> simp [h]
          have hpm2 : -rc (a i2) (b i2) (p1.1 i2) (p1.2 i2) uB2 = 1 ∨
              -rc (a i2) (b i2) (p1.1 i2) (p1.2 i2) uB2 = -1 := by
            rcases rowCoeff_pm_one (a := a) (b := b) (α := p1.1) (β := p1.2) (hvalid i2) huB2 with h | h <;>
              simp [hrc_eq] at h ⊢ <;> simp [h]
          obtain ⟨_, _, huniq⟩ := rc_exists_unique_pair (hvalid i3)
            huB1' huB2' huB12 hpm1 hpm2
          have e1 := huniq (p1.1 i3, p1.2 i3) ⟨g1B1, g1B2⟩
          have e2 := huniq (p2.1 i3, p2.2 i3) ⟨by rw [g2B1, h2a, h2b], by rw [g2B2, h2a, h2b]⟩
          exact e1.trans e2.symm
        have hforall : ∀ k : Fin 4, (p1.1 k, p1.2 k) = (p2.1 k, p2.2 k) := by
          intro k
          have hk : k ∈ ({i0, i1, i2, i3} : Finset (Fin 4)) := by rw [← huniv4]; exact Finset.mem_univ k
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl | rfl | rfl <;> assumption
        exact Prod.ext (funext fun k => congrArg Prod.fst (hforall k))
          (funext fun k => congrArg Prod.snd (hforall k))
      ·
        intro q hq
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        have hpmA1 : -rc (a i0) (b i0) q.1.1 q.1.2 uA1 = 1 ∨ -rc (a i0) (b i0) q.1.1 q.1.2 uA1 = -1 := by
          rcases rowCoeff_pm_one (a := a) (b := b) (α := fun _ => q.1.1) (β := fun _ => q.1.2)
            (hvalid i0) huA1 with h | h <;> simp [hrc_eq] at h ⊢ <;> simp [h]
        have hpmA2 : -rc (a i0) (b i0) q.1.1 q.1.2 uA2 = 1 ∨ -rc (a i0) (b i0) q.1.1 q.1.2 uA2 = -1 := by
          rcases rowCoeff_pm_one (a := a) (b := b) (α := fun _ => q.1.1) (β := fun _ => q.1.2)
            (hvalid i0) huA2 with h | h <;> simp [hrc_eq] at h ⊢ <;> simp [h]
        have hpmB1 : -rc (a i2) (b i2) q.2.1 q.2.2 uB1 = 1 ∨ -rc (a i2) (b i2) q.2.1 q.2.2 uB1 = -1 := by
          rcases rowCoeff_pm_one (a := a) (b := b) (α := fun _ => q.2.1) (β := fun _ => q.2.2)
            (hvalid i2) huB1 with h | h <;> simp [hrc_eq] at h ⊢ <;> simp [h]
        have hpmB2 : -rc (a i2) (b i2) q.2.1 q.2.2 uB2 = 1 ∨ -rc (a i2) (b i2) q.2.1 q.2.2 uB2 = -1 := by
          rcases rowCoeff_pm_one (a := a) (b := b) (α := fun _ => q.2.1) (β := fun _ => q.2.2)
            (hvalid i2) huB2 with h | h <;> simp [hrc_eq] at h ⊢ <;> simp [h]
        obtain ⟨q1, ⟨hq1A1, hq1A2⟩, _⟩ := rc_exists_unique_pair (hvalid i1)
          huA1' huA2' huA12 hpmA1 hpmA2
        obtain ⟨q3, ⟨hq3B1, hq3B2⟩, _⟩ := rc_exists_unique_pair (hvalid i3)
          huB1' huB2' huB12 hpmB1 hpmB2
        let α : Fin 4 → F := fun k =>
          if k = i0 then q.1.1 else if k = i1 then q1.1 else if k = i2 then q.2.1 else q3.1
        let β : Fin 4 → F := fun k =>
          if k = i0 then q.1.2 else if k = i1 then q1.2 else if k = i2 then q.2.2 else q3.2
        have hα0 : α i0 = q.1.1 := by simp [α]
        have hβ0 : β i0 = q.1.2 := by simp [β]
        have hα1 : α i1 = q1.1 := by simp [α, hi10]
        have hβ1 : β i1 = q1.2 := by simp [β, hi10]
        have hα2 : α i2 = q.2.1 := by simp [α, hi20, hi21]
        have hβ2 : β i2 = q.2.2 := by simp [β, hi20, hi21]
        have hα3 : α i3 = q3.1 := by simp [α, hi30, hi31, hi32]
        have hβ3 : β i3 = q3.2 := by simp [β, hi30, hi31, hi32]
        refine ⟨(α, β), ?_, by simp [hα0, hβ0, hα2, hβ2]⟩
        simp only [Til, Finset.mem_filter, Finset.mem_univ, true_and]
        intro v _hv
        rw [huniv4]
        simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
          hi10.symm, hi20.symm, hi30.symm, hi21.symm, hi31.symm, hi32.symm,
          or_self, not_false_eq_true, Finset.sum_singleton]
        by_cases hv0 : v = v0
        · rw [hv0]
          have hv0A : rc (a i1) (b i1) q1.1 q1.2 v0 = rc (a i0) (b i0) q.1.1 q.1.2 v0 := by
            rw [rc_prod (hvalid i1) q1.1 q1.2 huA1' huA2'
              (hv0all i1) huA12 huA1v0 huA2v0]
            rw [rc_prod (hvalid i0) q.1.1 q.1.2 huA1 huA2 (hv0all i0) huA12 huA1v0 huA2v0]
            rw [hq1A1, hq1A2]; ring
          have hv0B : rc (a i3) (b i3) q3.1 q3.2 v0 = rc (a i2) (b i2) q.2.1 q.2.2 v0 := by
            rw [rc_prod (hvalid i3) q3.1 q3.2 huB1' huB2'
              (hv0all i3) huB12 huB1v0 huB2v0]
            rw [rc_prod (hvalid i2) q.2.1 q.2.2 huB1 huB2 (hv0all i2) huB12 huB1v0 huB2v0]
            rw [hq3B1, hq3B2]; ring
          simp only [hrc_eq, hα0, hβ0, hα1, hβ1, hα2, hβ2, hα3, hβ3]
          linarith
        · by_cases hvA : v ∈ freqOf a b i0
          · have hcases : v = uA1 ∨ v = uA2 := by
              rw [hPA] at hvA
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvA
              rcases hvA with rfl | rfl | rfl
              · exact absurd rfl hv0
              · exact Or.inl rfl
              · exact Or.inr rfl
            have h20 : rowCoeff a b α β i2 v = 0 :=
              rowCoeff_eq_zero_of_not_mem (hnotB_of_A v (by rcases hcases with rfl | rfl <;> simp))
            have h30 : rowCoeff a b α β i3 v = 0 :=
              rowCoeff_eq_zero_of_not_mem (by rw [hPi3]; exact hnotB_of_A v (by rcases hcases with rfl | rfl <;> simp))
            rw [h20, h30]
            simp only [hrc_eq, hα0, hβ0, hα1, hβ1]
            rcases hcases with rfl | rfl <;> linarith
          · by_cases hvB : v ∈ freqOf a b i2
            · have hcases : v = uB1 ∨ v = uB2 := by
                rw [hPB] at hvB
                simp only [Finset.mem_insert, Finset.mem_singleton] at hvB
                rcases hvB with rfl | rfl | rfl
                · exact absurd rfl hv0
                · exact Or.inl rfl
                · exact Or.inr rfl
              have h00 : rowCoeff a b α β i0 v = 0 := rowCoeff_eq_zero_of_not_mem hvA
              have h10 : rowCoeff a b α β i1 v = 0 :=
                rowCoeff_eq_zero_of_not_mem (by rw [hPi1]; exact hvA)
              rw [h00, h10]
              simp only [hrc_eq, hα2, hβ2, hα3, hβ3]
              rcases hcases with rfl | rfl <;> linarith
            · have h00 : rowCoeff a b α β i0 v = 0 := rowCoeff_eq_zero_of_not_mem hvA
              have h10 : rowCoeff a b α β i1 v = 0 := rowCoeff_eq_zero_of_not_mem (by rw [hPi1]; exact hvA)
              have h20 : rowCoeff a b α β i2 v = 0 := rowCoeff_eq_zero_of_not_mem hvB
              have h30 : rowCoeff a b α β i3 v = 0 := rowCoeff_eq_zero_of_not_mem (by rw [hPi3]; exact hvB)
              rw [h00, h10, h20, h30]; ring
    exact hbij.trans hTcard
  ·
    push Not at hcommon
    have hdeg_le2 : ∀ v : Vec 3, v ≠ 0 → deg v ≤ 2 := by
      intro v hv
      have hev := hdeg_even v hv
      have hne4 := hcommon v hv
      have hle4 : deg v ≤ 4 := by
        calc deg v ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = 4 := by simp
      obtain ⟨m, hm⟩ := hev
      dsimp only [deg] at hne4 hle4 hm ⊢
      omega

    have hnot3 : ∀ (v : Vec 3) (i j k : Fin 4), i ≠ j → i ≠ k → j ≠ k →
        v ∈ freqOf a b i → v ∈ freqOf a b j → v ∈ freqOf a b k → False := by
      intro v i j k hij hik hjk hi hj hk
      have hvne : v ≠ 0 := mem_freqOf_ne_zero (hvalid i) hi
      have hsub : ({i, j, k} : Finset (Fin 4)) ⊆ Finset.univ.filter (fun t => v ∈ freqOf a b t) := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton] at ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases ht with rfl | rfl | rfl <;> assumption
      have h3 : 3 ≤ deg v := by
        have hc : ({i, j, k} : Finset (Fin 4)).card = 3 := by simp [hij, hik, hjk]
        rw [← hc]
        exact Finset.card_le_card hsub
      have h2 := hdeg_le2 v hvne
      omega

    have hex_inter : ∀ i j : Fin 4, i ≠ j →
        ∃ v : Vec 3, v ∈ freqOf a b i ∧ v ∈ freqOf a b j := fun i j _ =>
      planes_inter_nonempty (hvalid i) (hvalid j)
    obtain ⟨v01, hv01_0, hv01_1⟩ := hex_inter 0 1 (by decide)
    obtain ⟨v02, hv02_0, hv02_2⟩ := hex_inter 0 2 (by decide)
    obtain ⟨v03, hv03_0, hv03_3⟩ := hex_inter 0 3 (by decide)
    obtain ⟨v12, hv12_1, hv12_2⟩ := hex_inter 1 2 (by decide)
    obtain ⟨v13, hv13_1, hv13_3⟩ := hex_inter 1 3 (by decide)
    obtain ⟨v23, hv23_2, hv23_3⟩ := hex_inter 2 3 (by decide)

    have hv01_ne_02 : v01 ≠ v02 := fun h => hnot3 v01 0 1 2 (by decide) (by decide) (by decide) hv01_0 hv01_1 (h ▸ hv02_2)
    have hv01_ne_03 : v01 ≠ v03 := fun h => hnot3 v01 0 1 3 (by decide) (by decide) (by decide) hv01_0 hv01_1 (h ▸ hv03_3)
    have hv02_ne_03 : v02 ≠ v03 := fun h => hnot3 v02 0 2 3 (by decide) (by decide) (by decide) hv02_0 hv02_2 (h ▸ hv03_3)
    have hv01_ne_12 : v01 ≠ v12 := fun h => hnot3 v01 0 1 2 (by decide) (by decide) (by decide) hv01_0 hv01_1 (h ▸ hv12_2)
    have hv01_ne_13 : v01 ≠ v13 := fun h => hnot3 v01 0 1 3 (by decide) (by decide) (by decide) hv01_0 hv01_1 (h ▸ hv13_3)
    have hv12_ne_13 : v12 ≠ v13 := fun h => hnot3 v12 1 2 3 (by decide) (by decide) (by decide) hv12_1 hv12_2 (h ▸ hv13_3)
    have hv02_ne_12 : v02 ≠ v12 := fun h => hnot3 v02 0 1 2 (by decide) (by decide) (by decide) hv02_0 (h ▸ hv12_1) hv02_2
    have hv02_ne_23 : v02 ≠ v23 := fun h => hnot3 v02 0 2 3 (by decide) (by decide) (by decide) hv02_0 hv02_2 (h ▸ hv23_3)
    have hv12_ne_23 : v12 ≠ v23 := fun h => hnot3 v12 1 2 3 (by decide) (by decide) (by decide) hv12_1 hv12_2 (h ▸ hv23_3)
    have hv03_ne_13 : v03 ≠ v13 := fun h => hnot3 v03 0 1 3 (by decide) (by decide) (by decide) hv03_0 (h ▸ hv13_1) hv03_3
    have hv03_ne_23 : v03 ≠ v23 := fun h => hnot3 v03 0 2 3 (by decide) (by decide) (by decide) hv03_0 (h ▸ hv23_2) hv03_3
    have hv13_ne_23 : v13 ≠ v23 := fun h => hnot3 v13 1 2 3 (by decide) (by decide) (by decide) hv13_1 (h ▸ hv23_2) hv13_3

    have hP0 : freqOf a b 0 = {v01, v02, v03} := by
      symm; refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · rw [freqOf_card (hvalid 0)]; simp [hv01_ne_02, hv01_ne_03, hv02_ne_03]
    have hP1 : freqOf a b 1 = {v01, v12, v13} := by
      symm; refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · rw [freqOf_card (hvalid 1)]; simp [hv01_ne_12, hv01_ne_13, hv12_ne_13]
    have hP2 : freqOf a b 2 = {v02, v12, v23} := by
      symm; refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · rw [freqOf_card (hvalid 2)]; simp [hv02_ne_12, hv02_ne_23, hv12_ne_23]
    have hP3 : freqOf a b 3 = {v03, v13, v23} := by
      symm; refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
      · rw [freqOf_card (hvalid 3)]; simp [hv03_ne_13, hv03_ne_23, hv13_ne_23]

    have hv01_n2 : v01 ∉ freqOf a b 2 := fun h => hnot3 v01 0 1 2 (by decide) (by decide) (by decide) hv01_0 hv01_1 h
    have hv01_n3 : v01 ∉ freqOf a b 3 := fun h => hnot3 v01 0 1 3 (by decide) (by decide) (by decide) hv01_0 hv01_1 h
    have hv02_n1 : v02 ∉ freqOf a b 1 := fun h => hnot3 v02 0 1 2 (by decide) (by decide) (by decide) hv02_0 h hv02_2
    have hv02_n3 : v02 ∉ freqOf a b 3 := fun h => hnot3 v02 0 2 3 (by decide) (by decide) (by decide) hv02_0 hv02_2 h
    have hv03_n1 : v03 ∉ freqOf a b 1 := fun h => hnot3 v03 0 1 3 (by decide) (by decide) (by decide) hv03_0 h hv03_3
    have hv03_n2 : v03 ∉ freqOf a b 2 := fun h => hnot3 v03 0 2 3 (by decide) (by decide) (by decide) hv03_0 h hv03_3
    have hv12_n0 : v12 ∉ freqOf a b 0 := fun h => hnot3 v12 0 1 2 (by decide) (by decide) (by decide) h hv12_1 hv12_2
    have hv12_n3 : v12 ∉ freqOf a b 3 := fun h => hnot3 v12 1 2 3 (by decide) (by decide) (by decide) hv12_1 hv12_2 h
    have hv13_n0 : v13 ∉ freqOf a b 0 := fun h => hnot3 v13 0 1 3 (by decide) (by decide) (by decide) h hv13_1 hv13_3
    have hv13_n2 : v13 ∉ freqOf a b 2 := fun h => hnot3 v13 1 2 3 (by decide) (by decide) (by decide) hv13_1 h hv13_3
    have hv23_n0 : v23 ∉ freqOf a b 0 := fun h => hnot3 v23 0 2 3 (by decide) (by decide) (by decide) h hv23_2 hv23_3
    have hv23_n1 : v23 ∉ freqOf a b 1 := fun h => hnot3 v23 1 2 3 (by decide) (by decide) (by decide) h hv23_2 hv23_3

    have htil_edges : ∀ p : (Fin 4 → F) × (Fin 4 → F), IsTiling a b p.1 p.2 Finset.univ →
        rc (a 1) (b 1) (p.1 1) (p.2 1) v01 = -rc (a 0) (b 0) (p.1 0) (p.2 0) v01 ∧
        rc (a 2) (b 2) (p.1 2) (p.2 2) v02 = -rc (a 0) (b 0) (p.1 0) (p.2 0) v02 ∧
        rc (a 3) (b 3) (p.1 3) (p.2 3) v03 = -rc (a 0) (b 0) (p.1 0) (p.2 0) v03 ∧
        rc (a 2) (b 2) (p.1 2) (p.2 2) v12 = -rc (a 1) (b 1) (p.1 1) (p.2 1) v12 ∧
        rc (a 3) (b 3) (p.1 3) (p.2 3) v13 = -rc (a 1) (b 1) (p.1 1) (p.2 1) v13 ∧
        rc (a 3) (b 3) (p.1 3) (p.2 3) v23 = -rc (a 2) (b 2) (p.1 2) (p.2 2) v23 := by
      intro p hp
      have hsum : ∀ v : Vec 3, v ≠ 0 →
          rowCoeff a b p.1 p.2 0 v + rowCoeff a b p.1 p.2 1 v +
          rowCoeff a b p.1 p.2 2 v + rowCoeff a b p.1 p.2 3 v = 0 := by
        intro v hv
        have := hp v hv
        rw [Fin.sum_univ_four] at this
        linarith
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h := hsum v01 (mem_freqOf_ne_zero (hvalid 0) hv01_0)
        rw [rowCoeff_eq_zero_of_not_mem hv01_n2, rowCoeff_eq_zero_of_not_mem hv01_n3] at h
        simp only [hrc_eq] at h; linarith
      · have h := hsum v02 (mem_freqOf_ne_zero (hvalid 0) hv02_0)
        rw [rowCoeff_eq_zero_of_not_mem hv02_n1, rowCoeff_eq_zero_of_not_mem hv02_n3] at h
        simp only [hrc_eq] at h; linarith
      · have h := hsum v03 (mem_freqOf_ne_zero (hvalid 0) hv03_0)
        rw [rowCoeff_eq_zero_of_not_mem hv03_n1, rowCoeff_eq_zero_of_not_mem hv03_n2] at h
        simp only [hrc_eq] at h; linarith
      · have h := hsum v12 (mem_freqOf_ne_zero (hvalid 1) hv12_1)
        rw [rowCoeff_eq_zero_of_not_mem hv12_n0, rowCoeff_eq_zero_of_not_mem hv12_n3] at h
        simp only [hrc_eq] at h; linarith
      · have h := hsum v13 (mem_freqOf_ne_zero (hvalid 1) hv13_1)
        rw [rowCoeff_eq_zero_of_not_mem hv13_n0, rowCoeff_eq_zero_of_not_mem hv13_n2] at h
        simp only [hrc_eq] at h; linarith
      · have h := hsum v23 (mem_freqOf_ne_zero (hvalid 2) hv23_2)
        rw [rowCoeff_eq_zero_of_not_mem hv23_n0, rowCoeff_eq_zero_of_not_mem hv23_n1] at h
        simp only [hrc_eq] at h; linarith

    have hbij : Til.card = (Finset.univ : Finset ((F × F) × Bool)).card := by
      refine Finset.card_bij (fun p _ => ((p.1 0, p.2 0), decide (rc (a 1) (b 1) (p.1 1) (p.2 1) v12 = 1)))
        (fun _ _ => Finset.mem_univ _) ?_ ?_
      ·
        intro p1 hp1 p2 hp2 heq
        simp only [Til, Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
        have h0eq : (p1.1 0, p1.2 0) = (p2.1 0, p2.2 0) := congrArg Prod.fst heq
        have hbeq : decide (rc (a 1) (b 1) (p1.1 1) (p1.2 1) v12 = 1) =
            decide (rc (a 1) (b 1) (p2.1 1) (p2.2 1) v12 = 1) := congrArg Prod.snd heq
        have h12eq : rc (a 1) (b 1) (p1.1 1) (p1.2 1) v12 = rc (a 1) (b 1) (p2.1 1) (p2.2 1) v12 := by
          have hpm1 : rc (a 1) (b 1) (p1.1 1) (p1.2 1) v12 = 1 ∨ rc (a 1) (b 1) (p1.1 1) (p1.2 1) v12 = -1 := by
            simpa [hrc_eq] using rowCoeff_pm_one (a := a) (b := b) (α := p1.1) (β := p1.2) (hvalid 1) hv12_1
          have hpm2 : rc (a 1) (b 1) (p2.1 1) (p2.2 1) v12 = 1 ∨ rc (a 1) (b 1) (p2.1 1) (p2.2 1) v12 = -1 := by
            simpa [hrc_eq] using rowCoeff_pm_one (a := a) (b := b) (α := p2.1) (β := p2.2) (hvalid 1) hv12_1
          rcases hpm1 with h1 | h1 <;> rcases hpm2 with h2 | h2 <;> simp [h1, h2] at hbeq ⊢
        obtain ⟨e1_01, e1_02, e1_03, e1_12, e1_13, _⟩ := htil_edges p1 hp1
        obtain ⟨e2_01, e2_02, e2_03, e2_12, e2_13, _⟩ := htil_edges p2 hp2
        have hpm_rc : ∀ (k : Fin 4) (v : Vec 3), v ∈ freqOf a b k →
            rc (a k) (b k) (p1.1 k) (p1.2 k) v = 1 ∨ rc (a k) (b k) (p1.1 k) (p1.2 k) v = -1 := by
          intro k v hv
          simpa [hrc_eq] using rowCoeff_pm_one (a := a) (b := b) (α := p1.1) (β := p1.2) (hvalid k) hv
        have h0a : p1.1 0 = p2.1 0 := congrArg Prod.fst h0eq
        have h0b : p1.2 0 = p2.2 0 := congrArg Prod.snd h0eq
        have h1eq : (p1.1 1, p1.2 1) = (p2.1 1, p2.2 1) := by
          obtain ⟨_, _, hu⟩ := rc_exists_unique_pair (hvalid 1) hv01_1 hv12_1 hv01_ne_12
            (hpm_rc 1 v01 hv01_1) (hpm_rc 1 v12 hv12_1)
          have a1 := hu (p1.1 1, p1.2 1) ⟨rfl, rfl⟩
          have a2 := hu (p2.1 1, p2.2 1) ⟨by rw [e2_01, e1_01, h0a, h0b], h12eq.symm⟩
          exact a1.trans a2.symm
        have h1a : p1.1 1 = p2.1 1 := congrArg Prod.fst h1eq
        have h1b : p1.2 1 = p2.2 1 := congrArg Prod.snd h1eq
        have h2eq : (p1.1 2, p1.2 2) = (p2.1 2, p2.2 2) := by
          obtain ⟨_, _, hu⟩ := rc_exists_unique_pair (hvalid 2) hv02_2 hv12_2 hv02_ne_12
            (hpm_rc 2 v02 hv02_2) (hpm_rc 2 v12 hv12_2)
          have a1 := hu (p1.1 2, p1.2 2) ⟨rfl, rfl⟩
          have a2 := hu (p2.1 2, p2.2 2) ⟨by rw [e2_02, e1_02, h0a, h0b], by rw [e2_12, e1_12, h12eq]⟩
          exact a1.trans a2.symm
        have h3eq : (p1.1 3, p1.2 3) = (p2.1 3, p2.2 3) := by
          obtain ⟨_, _, hu⟩ := rc_exists_unique_pair (hvalid 3) hv03_3 hv13_3 hv03_ne_13
            (hpm_rc 3 v03 hv03_3) (hpm_rc 3 v13 hv13_3)
          have a1 := hu (p1.1 3, p1.2 3) ⟨rfl, rfl⟩
          have a2 := hu (p2.1 3, p2.2 3) ⟨by rw [e2_03, e1_03, h0a, h0b], by rw [e2_13, e1_13, h1a, h1b]⟩
          exact a1.trans a2.symm
        have hforall : ∀ k : Fin 4, (p1.1 k, p1.2 k) = (p2.1 k, p2.2 k) := by
          intro k; fin_cases k <;> assumption
        exact Prod.ext (funext fun k => congrArg Prod.fst (hforall k))
          (funext fun k => congrArg Prod.snd (hforall k))
      ·
        rintro ⟨⟨α0, β0⟩, b12⟩ _
        let s12 : ℤ := if b12 then 1 else -1
        have hs12 : s12 = 1 ∨ s12 = -1 := by cases b12 <;> simp [s12]
        have hneg_pm : ∀ (k : Fin 4) (αk βk : F) (v : Vec 3), v ∈ freqOf a b k →
            -rc (a k) (b k) αk βk v = 1 ∨ -rc (a k) (b k) αk βk v = -1 := by
          intro k αk βk v hv
          rcases rowCoeff_pm_one (a := a) (b := b) (α := fun _ => αk) (β := fun _ => βk)
            (hvalid k) hv with h | h <;> simp [hrc_eq] at h ⊢ <;> simp [h]
        obtain ⟨q1, ⟨hq1_01, hq1_12⟩, _⟩ := rc_exists_unique_pair (hvalid 1) hv01_1 hv12_1 hv01_ne_12
          (hneg_pm 0 α0 β0 v01 hv01_0) hs12
        obtain ⟨q2, ⟨hq2_02, hq2_12⟩, _⟩ := rc_exists_unique_pair (hvalid 2) hv02_2 hv12_2 hv02_ne_12
          (hneg_pm 0 α0 β0 v02 hv02_0) (hneg_pm 1 q1.1 q1.2 v12 hv12_1)
        obtain ⟨q3, ⟨hq3_03, hq3_13⟩, _⟩ := rc_exists_unique_pair (hvalid 3) hv03_3 hv13_3 hv03_ne_13
          (hneg_pm 0 α0 β0 v03 hv03_0) (hneg_pm 1 q1.1 q1.2 v13 hv13_1)

        have hq3_23 : rc (a 3) (b 3) q3.1 q3.2 v23 = -rc (a 2) (b 2) q2.1 q2.2 v23 := by
          have hp0 := rc_prod (hvalid 0) α0 β0 hv01_0 hv02_0 hv03_0 hv01_ne_02 hv01_ne_03 hv02_ne_03
          have hp1 := rc_prod (hvalid 1) q1.1 q1.2 hv01_1 hv12_1 hv13_1 hv01_ne_12 hv01_ne_13 hv12_ne_13
          have hp2 := rc_prod (hvalid 2) q2.1 q2.2 hv02_2 hv12_2 hv23_2 hv02_ne_12 hv02_ne_23 hv12_ne_23
          have hp3 := rc_prod (hvalid 3) q3.1 q3.2 hv03_3 hv13_3 hv23_3 hv03_ne_13 hv03_ne_23 hv13_ne_23
          have hsq01 : rc (a 0) (b 0) α0 β0 v01 * rc (a 0) (b 0) α0 β0 v01 = 1 := by
            rcases rowCoeff_pm_one (a := a) (b := b) (α := fun _ => α0) (β := fun _ => β0)
              (hvalid 0) hv01_0 with h | h <;> simp [hrc_eq] at h ⊢ <;> rw [h] <;> norm_num
          rw [hp3, hq3_03, hq3_13, hp0, hp1, hq1_01, hp2, hq2_02, hq2_12]
          calc -(rc (a 0) (b 0) α0 β0 v01 * rc (a 0) (b 0) α0 β0 v02) *
                -(-rc (a 0) (b 0) α0 β0 v01 * rc (a 1) (b 1) q1.1 q1.2 v12)
              = -(rc (a 0) (b 0) α0 β0 v01 * rc (a 0) (b 0) α0 β0 v01) *
                rc (a 0) (b 0) α0 β0 v02 * rc (a 1) (b 1) q1.1 q1.2 v12 := by ring
            _ = -(1 : ℤ) * rc (a 0) (b 0) α0 β0 v02 * rc (a 1) (b 1) q1.1 q1.2 v12 := by rw [hsq01]
            _ = -(-rc (a 0) (b 0) α0 β0 v02 * -rc (a 1) (b 1) q1.1 q1.2 v12) := by ring
        let α : Fin 4 → F := ![α0, q1.1, q2.1, q3.1]
        let β : Fin 4 → F := ![β0, q1.2, q2.2, q3.2]
        have hα0 : α 0 = α0 := rfl
        have hα1 : α 1 = q1.1 := rfl
        have hα2 : α 2 = q2.1 := rfl
        have hα3 : α 3 = q3.1 := rfl
        have hβ0 : β 0 = β0 := rfl
        have hβ1 : β 1 = q1.2 := rfl
        have hβ2 : β 2 = q2.2 := rfl
        have hβ3 : β 3 = q3.2 := rfl
        refine ⟨(α, β), ?_, ?_⟩
        · simp only [Til, Finset.mem_filter, Finset.mem_univ, true_and]
          intro v _hv
          rw [Fin.sum_univ_four]
          by_cases h01 : v = v01
          · rw [h01, rowCoeff_eq_zero_of_not_mem hv01_n2, rowCoeff_eq_zero_of_not_mem hv01_n3]
            simp only [hrc_eq, hα0, hβ0, hα1, hβ1]
            linarith
          by_cases h02 : v = v02
          · rw [h02, rowCoeff_eq_zero_of_not_mem hv02_n1, rowCoeff_eq_zero_of_not_mem hv02_n3]
            simp only [hrc_eq, hα0, hβ0, hα2, hβ2]
            linarith
          by_cases h03 : v = v03
          · rw [h03, rowCoeff_eq_zero_of_not_mem hv03_n1, rowCoeff_eq_zero_of_not_mem hv03_n2]
            simp only [hrc_eq, hα0, hβ0, hα3, hβ3]
            linarith
          by_cases h12 : v = v12
          · rw [h12, rowCoeff_eq_zero_of_not_mem hv12_n0, rowCoeff_eq_zero_of_not_mem hv12_n3]
            simp only [hrc_eq, hα1, hβ1, hα2, hβ2]
            linarith
          by_cases h13 : v = v13
          · rw [h13, rowCoeff_eq_zero_of_not_mem hv13_n0, rowCoeff_eq_zero_of_not_mem hv13_n2]
            simp only [hrc_eq, hα1, hβ1, hα3, hβ3]
            linarith
          by_cases h23 : v = v23
          · rw [h23, rowCoeff_eq_zero_of_not_mem hv23_n0, rowCoeff_eq_zero_of_not_mem hv23_n1]
            simp only [hrc_eq, hα2, hβ2, hα3, hβ3]
            linarith
          have hn0 : v ∉ freqOf a b 0 := by rw [hP0]; simp [h01, h02, h03]
          have hn1 : v ∉ freqOf a b 1 := by rw [hP1]; simp [h01, h12, h13]
          have hn2 : v ∉ freqOf a b 2 := by rw [hP2]; simp [h02, h12, h23]
          have hn3 : v ∉ freqOf a b 3 := by rw [hP3]; simp [h03, h13, h23]
          rw [rowCoeff_eq_zero_of_not_mem hn0, rowCoeff_eq_zero_of_not_mem hn1,
            rowCoeff_eq_zero_of_not_mem hn2, rowCoeff_eq_zero_of_not_mem hn3]
          ring
        · simp only [hα0, hβ0, hα1, hβ1]
          congr 1
          rw [hq1_12]
          cases b12 <;> decide
    simpa [Fintype.card_prod, ZMod.card] using hbij

theorem comp4_tiling_card {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → Vec n) (C : Finset I)
    (hvalid : ∀ i ∈ C, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i)
    (hcard : C.card = 4)
    (hrk : rkOf a b C = 3)
    (hex : ∃ α0 β0 : I → F, IsTiling a b α0 β0 C) :
    ((Finset.univ : Finset ((C → F) × (C → F))).filter
      (fun p => IsTiling (fun i : C => a i.1) (fun i : C => b i.1) p.1 p.2 Finset.univ)).card = 8 := by
  have hfin : Module.finrank F (spanOf a b C) = Module.finrank F (Vec 3) := by
    dsimp [rkOf] at hrk; rw [hrk]; simp [Vec]
  let e : spanOf a b C ≃ₗ[F] Vec 3 := LinearEquiv.ofFinrankEq (spanOf a b C) (Vec 3) hfin
  let σ : Fin 4 ≃ C := (C.equivFinOfCardEq hcard).symm
  let a' : Fin 4 → Vec 3 := fun k =>
    e ⟨a (σ k).1, mem_spanOf_of_mem_freqOf (σ k).2 (by simp [freqOf])⟩
  let b' : Fin 4 → Vec 3 := fun k =>
    e ⟨b (σ k).1, mem_spanOf_of_mem_freqOf (σ k).2 (by simp [freqOf])⟩
  have hvalid' : ∀ k : Fin 4, a' k ≠ 0 ∧ b' k ≠ 0 ∧ a' k ≠ b' k := by
    intro k
    obtain ⟨ha, hb, hab⟩ := hvalid (σ k).1 (σ k).2
    refine ⟨?_, ?_, ?_⟩
    · intro h; apply ha
      have := e.injective (h.trans (map_zero e).symm)
      exact congrArg Subtype.val this
    · intro h; apply hb
      have := e.injective (h.trans (map_zero e).symm)
      exact congrArg Subtype.val this
    · intro h; apply hab
      exact congrArg Subtype.val (e.injective h)
  have hnotall' : ∃ k1 k2 : Fin 4, freqOf a' b' k1 ≠ freqOf a' b' k2 := by
    by_contra hall
    push Not at hall
    have hsub : spanOf a b C ≤ Submodule.span F ({a (σ 0).1, b (σ 0).1} : Set (Vec n)) := by
      rw [spanOf, Submodule.span_le]
      intro v hv
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe] at hv
      have hmem0 : ∀ k : Fin 4, a' k ∈ freqOf a' b' 0 ∧ b' k ∈ freqOf a' b' 0 := by
        intro k
        rw [← hall k 0]
        exact ⟨by simp [freqOf], by simp [freqOf]⟩
      have hpull : ∀ w : Vec 3, w ∈ freqOf a' b' 0 →
          (e.symm w).1 ∈ Submodule.span F ({a (σ 0).1, b (σ 0).1} : Set (Vec n)) := by
        intro w hw
        simp only [freqOf, Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · simp [a']; exact Submodule.subset_span (by simp)
        · simp [b']; exact Submodule.subset_span (by simp)
        · have : (e.symm (a' 0 + b' 0)).1 = a (σ 0).1 + b (σ 0).1 := by
            rw [map_add]; simp [a', b']
          rw [this]
          exact Submodule.add_mem _ (Submodule.subset_span (by simp))
            (Submodule.subset_span (by simp))
      rcases hv with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩
      · let k := σ.symm ⟨i, hi⟩
        have hk : (σ k).1 = i := by simp [k]
        have heq : (e.symm (a' k)).1 = a i := by simp [a', hk]
        rw [← heq]
        exact hpull (a' k) (hmem0 k).1
      · let k := σ.symm ⟨i, hi⟩
        have hk : (σ k).1 = i := by simp [k]
        have heq : (e.symm (b' k)).1 = b i := by simp [b', hk]
        rw [← heq]
        exact hpull (b' k) (hmem0 k).2
    have hle2 : rkOf a b C ≤ 2 := by
      calc rkOf a b C = Module.finrank F (spanOf a b C) := rfl
        _ ≤ Module.finrank F (Submodule.span F ({a (σ 0).1, b (σ 0).1} : Set (Vec n))) :=
          Submodule.finrank_mono hsub
        _ ≤ ({a (σ 0).1, b (σ 0).1} : Finset (Vec n)).card := by
          simpa using finrank_span_le_card ({a (σ 0).1, b (σ 0).1} : Set (Vec n))
        _ ≤ 2 := Finset.card_le_two
    omega
  have htil_iff : ∀ (α β : C → F),
      IsTiling (fun i : C => a i.1) (fun i : C => b i.1) α β Finset.univ ↔
      IsTiling a' b' (α ∘ σ) (β ∘ σ) Finset.univ := by
    intro α β
    have hrow : ∀ (k : Fin 4) (v : spanOf a b C),
        rowCoeff (fun i : C => a i.1) (fun i : C => b i.1) α β (σ k) v.1 =
        rowCoeff a' b' (α ∘ σ) (β ∘ σ) k (e v) := by
      intro k v
      have ha : (a (σ k).1 = v.1) ↔ (a' k = e v) := by
        constructor
        · intro h; simp only [a']; congr 1; exact Subtype.ext h
        · intro h; exact congrArg Subtype.val (e.injective h)
      have hb : (b (σ k).1 = v.1) ↔ (b' k = e v) := by
        constructor
        · intro h; simp only [b']; congr 1; exact Subtype.ext h
        · intro h; exact congrArg Subtype.val (e.injective h)
      have hab : (a (σ k).1 + b (σ k).1 = v.1) ↔ (a' k + b' k = e v) := by
        constructor
        · intro h
          rw [← map_add]
          congr 1; exact Subtype.ext h
        · intro h
          rw [← map_add] at h
          exact congrArg Subtype.val (e.injective h)
      simp only [rowCoeff, Function.comp_apply, ha, hb, hab]
    constructor
    · intro h w hw
      let v : spanOf a b C := e.symm w
      have hvne : v.1 ≠ 0 := by
        intro h0
        apply hw
        have : v = 0 := Subtype.ext h0
        have := congrArg e this
        simpa [v] using this
      have h1 := h v.1 hvne
      have h2 : ∑ k : Fin 4, rowCoeff a' b' (α ∘ σ) (β ∘ σ) k w =
          ∑ i : C, rowCoeff (fun i : C => a i.1) (fun i : C => b i.1) α β i v.1 := by
        rw [← Equiv.sum_comp σ]
        refine Finset.sum_congr rfl fun k _ => ?_
        have := hrow k v
        simpa [v] using this.symm
      rw [h2, h1]
    · intro h v hv
      by_cases hvS : v ∈ spanOf a b C
      · let w : Vec 3 := e ⟨v, hvS⟩
        have hwne : w ≠ 0 := by
          intro h0
          apply hv
          have := e.injective (h0.trans (map_zero e).symm)
          exact congrArg Subtype.val this
        have h1 := h w hwne
        have h2 : ∑ i : C, rowCoeff (fun i : C => a i.1) (fun i : C => b i.1) α β i v =
            ∑ k : Fin 4, rowCoeff a' b' (α ∘ σ) (β ∘ σ) k w := by
          rw [← Equiv.sum_comp σ]
          refine Finset.sum_congr rfl fun k _ => hrow k ⟨v, hvS⟩
        rw [h2, h1]
      · refine Finset.sum_eq_zero fun i _ => ?_
        apply rowCoeff_eq_zero_of_not_mem
        intro hmem
        exact hvS (mem_spanOf_of_mem_freqOf i.2 hmem)
  have hex' : ∃ α0 β0 : Fin 4 → F, IsTiling a' b' α0 β0 Finset.univ := by
    obtain ⟨α0, β0, h0⟩ := hex
    refine ⟨(fun i : C => α0 i.1) ∘ σ, (fun i : C => β0 i.1) ∘ σ, ?_⟩
    rw [← htil_iff]
    intro v hv
    have := h0 v hv
    rw [← this]
    exact Finset.sum_coe_sort C (fun i => rowCoeff a b α0 β0 i v)
  have hbij :
      ((Finset.univ : Finset ((C → F) × (C → F))).filter
        (fun p => IsTiling (fun i : C => a i.1) (fun i : C => b i.1) p.1 p.2 Finset.univ)).card =
      ((Finset.univ : Finset ((Fin 4 → F) × (Fin 4 → F))).filter
        (fun p => IsTiling a' b' p.1 p.2 Finset.univ)).card := by
    refine Finset.card_bij (fun p _ => (p.1 ∘ σ, p.2 ∘ σ)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact (htil_iff p.1 p.2).mp hp
    · intro p1 _ p2 _ heq
      have h1 : p1.1 ∘ σ = p2.1 ∘ σ := congrArg Prod.fst heq
      have h2 : p1.2 ∘ σ = p2.2 ∘ σ := congrArg Prod.snd heq
      exact Prod.ext (σ.surjective.right_cancellable.mp h1) (σ.surjective.right_cancellable.mp h2)
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine ⟨(q.1 ∘ σ.symm, q.2 ∘ σ.symm), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [htil_iff]
        simpa [Function.comp_assoc] using hq
      · ext k <;> simp
  rw [hbij]
  exact vec3_tiling_card a' b' hvalid' hnotall' hex'

end
end sec4
end PEqualNP.Outside.L_lib_966

theorem PEqualNP.Outside.L_lib_966 : (let F := ZMod 2
let eligible := fun (n e : Nat) (a b : Fin (4*e) → (Fin n → F)) =>
  (∀ i, a i ≠ 0 ∧ b i ≠ 0 ∧ a i ≠ b i) ∧
  ∃ (P : Fin (4*e) → (Fin n → F)) (d : Fin (4*e) → F), ∀ x : Fin n → F,
    ((Finset.univ : Finset (Fin (4*e))).filter (fun i =>
      dotProduct (P i) x + d i ≠ dotProduct (a i) x * dotProduct (b i) x)).card ≤ e
let parts := fun (n e : Nat) (a b : Fin (4*e) → (Fin n → F)) =>
  let freq := fun i : Fin (4*e) => ({a i, b i, a i + b i} : Finset (Fin n → F))
  let adj := fun (i j : Fin (4*e)) => ∃ v ∈ freq i, v ∈ freq j
  (Finset.univ : Finset (Fin (4*e))).image (fun i => (Finset.univ : Finset (Fin (4*e))).filter
    (fun j => @decide (Relation.EqvGen adj i j) (Classical.propDecidable _) = true))
let rk := fun (n e : Nat) (a b : Fin (4*e) → (Fin n → F)) (S : Finset (Fin (4*e))) =>
  Module.finrank F (Submodule.span F (↑(S.image a ∪ S.image b) : Set (Fin n → F)))
∀ (n e : Nat) (a b : Fin (4*e) → (Fin n → F)),
  eligible n e a b → rk n e a b Finset.univ = 3*e →
  let W := Fin n → F
  let I := Fin (4*e)
  let H := List Bool
  let cs := parts n e a b
  let freq := fun i : I => ({a i, b i, a i+b i} : Finset W)
  let k := (cs.filter (fun C => ∃ v : W, ∀ i ∈ C, v ∈ freq i)).card
  let target := fun (x : W) (i : I) => dotProduct (a i) x * dotProduct (b i) x
  let good := (Finset.univ : Finset ((I → W) × (I → F))).filter (fun p =>
    ∀ x : W, ((Finset.univ : Finset I).filter (fun i =>
      target x i ≠ dotProduct (p.1 i) x + p.2 i)).card ≤ e)
  good.card = 8^e ∧ ∀ t L : Nat,
    let s := e-t
    let run := fun (T : Finset H) (ask : H → W) (bias : H → F) (x : W) =>
      (List.range T.card).foldl (fun (p : H) _ =>
        if p ∈ T then p ++ [decide (dotProduct (ask p) x+bias p ≠ 0)] else p) []
    (∃ (T : Finset H) (ask : H → W) (bias : H → F) (P : H → I → W) (d : H → I → F),
      T.card < L ∧ ∀ x : W,
        let p := run T ask bias x
        ((Finset.univ : Finset I).filter (fun i => target x i ≠ dotProduct (P p i) x+d p i)).card ≤ t) ↔
      2^(s+(s-k)) ≤ L) := by
  dsimp only
  intro n e a b helig hrk
  classical
  obtain ⟨hvalid, P0, d0, hP0⟩ := helig
  have hP0' : ∀ x : Fin n → ZMod 2,
      (Finset.univ.filter (fun i : Fin (4 * e) =>
        dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P0 i) x + d0 i)).card ≤ e := by
    intro x
    have h := hP0 x
    convert h using 2
    ext i
    simp [ne_comm]
  obtain ⟨α0, β0, hα0β0, ht0⟩ := (PEqualNP.Outside.L_lib_966.aux.good_iff_tiling hvalid P0 d0).mp hP0'
  have hrk' : PEqualNP.Outside.L_lib_966.aux.rkOf a b Finset.univ = 3 * e := hrk
  obtain ⟨hall43, hparts_card, hindep⟩ :=
    PEqualNP.Outside.L_lib_966.aux.rk_univ_3e_structure hvalid ht0 hrk'

  let cs := PEqualNP.Outside.L_lib_966.aux.partsOf a b
  have hcs_eq :
      (Finset.univ : Finset (Fin (4 * e))).image (fun i => (Finset.univ : Finset (Fin (4 * e))).filter
        (fun j => @decide (Relation.EqvGen (fun i j => ∃ v ∈ ({a i, b i, a i + b i} : Finset (Fin n → ZMod 2)),
          v ∈ ({a j, b j, a j + b j} : Finset (Fin n → ZMod 2))) i j) (Classical.propDecidable _) = true)) = cs := rfl
  let k := (cs.filter (fun C => ∃ v : Fin n → ZMod 2, ∀ i ∈ C, v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i)).card
  constructor
  ·
    let goodSet := (Finset.univ : Finset ((Fin (4 * e) → (Fin n → ZMod 2)) × (Fin (4 * e) → ZMod 2))).filter (fun p =>
      ∀ x : Fin n → ZMod 2, ((Finset.univ : Finset (Fin (4 * e))).filter (fun i =>
        dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (p.1 i) x + p.2 i)).card ≤ e)
    let Til (C : Finset (Fin (4 * e))) :=
      (Finset.univ : Finset ((C → ZMod 2) × (C → ZMod 2))).filter (fun p =>
        PEqualNP.Outside.L_lib_966.aux.IsTiling (fun i : C => a i.1) (fun i : C => b i.1) p.1 p.2 Finset.univ)
    have hTil_card : ∀ C ∈ cs, (Til C).card = 8 := by
      intro C hC
      have h43 := hall43 C hC
      have htC := PEqualNP.Outside.L_lib_966.aux.isTiling_restrict_part ht0 hC
      exact PEqualNP.Outside.L_lib_966.sec4.comp4_tiling_card a b C (fun i _ => hvalid i) h43.1 h43.2 ⟨α0, β0, htC⟩
    let prodTil : Finset (∀ C : cs, (C.1 → ZMod 2) × (C.1 → ZMod 2)) :=
      Fintype.piFinset (fun C : cs => Til C.1)
    have hprod_card : prodTil.card = 8 ^ e := by
      rw [Fintype.card_piFinset]
      have h1 : (∏ C : cs, (Til C.1).card) = ∏ _C : cs, 8 :=
        Finset.prod_congr rfl fun C _ => hTil_card C.1 C.2
      rw [h1, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hparts_card]
    rw [← hprod_card]

    symm
    refine Finset.card_bij
      (fun (f : ∀ C : cs, (C.1 → ZMod 2) × (C.1 → ZMod 2)) _ =>
        let α : Fin (4 * e) → ZMod 2 := fun i =>
          (f ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i,
              Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).1
            ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩
        let β : Fin (4 * e) → ZMod 2 := fun i =>
          (f ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i,
              Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).2
            ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩
        (fun i => PEqualNP.Outside.L_lib_966.aux.bestP (a i) (b i) (α i) (β i),
         fun i => PEqualNP.Outside.L_lib_966.aux.bestD (α i) (β i)))
      ?_ ?_ ?_
    · intro f hf
      simp only [prodTil, Fintype.mem_piFinset] at hf
      simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [PEqualNP.Outside.L_lib_966.aux.good_iff_tiling hvalid]
      let α : Fin (4 * e) → ZMod 2 := fun i =>
        (f ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i,
            Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).1
          ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩
      let β : Fin (4 * e) → ZMod 2 := fun i =>
        (f ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i,
            Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).2
          ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩
      refine ⟨α, β, fun i => ⟨rfl, rfl⟩, ?_⟩
      intro v hv
      have hdisj : (cs : Set (Finset (Fin (4 * e)))).PairwiseDisjoint id := fun C1 h1 C2 h2 hne =>
        PEqualNP.Outside.L_lib_966.aux.partsOf_disjoint a b h1 h2 hne
      rw [← PEqualNP.Outside.L_lib_966.aux.partsOf_biUnion a b, Finset.sum_biUnion hdisj]
      simp only [id_eq]
      refine Finset.sum_eq_zero fun C hC => ?_
      have hfC := (Finset.mem_filter.mp (hf ⟨C, hC⟩)).2 v hv
      rw [← hfC]
      rw [← Finset.sum_coe_sort C (fun i => PEqualNP.Outside.L_lib_966.aux.rowCoeff a b α β i v)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hcomp_eq : PEqualNP.Outside.L_lib_966.aux.compOf a b i.1 = C := by
        obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hC
        exact PEqualNP.Outside.L_lib_966.aux.compOf_eq_of_mem a b i.2
      have hsub : (⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i.1,
          Finset.mem_image.mpr ⟨i.1, Finset.mem_univ _, rfl⟩⟩ : cs) = ⟨C, hC⟩ := Subtype.ext hcomp_eq
      have hcast1 : ∀ (C1 C2 : cs) (h : C1 = C2) (x : C1.1) (y : C2.1), x.1 = y.1 → (f C1).1 x = (f C2).1 y := by
        rintro C1 _ rfl x y hxy; exact congrArg (f C1).1 (Subtype.ext hxy)
      have hcast2 : ∀ (C1 C2 : cs) (h : C1 = C2) (x : C1.1) (y : C2.1), x.1 = y.1 → (f C1).2 x = (f C2).2 y := by
        rintro C1 _ rfl x y hxy; exact congrArg (f C1).2 (Subtype.ext hxy)
      have hα_eq : α i.1 = (f ⟨C, hC⟩).1 i := hcast1 _ _ hsub _ _ rfl
      have hβ_eq : β i.1 = (f ⟨C, hC⟩).2 i := hcast2 _ _ hsub _ _ rfl
      simp only [PEqualNP.Outside.L_lib_966.aux.rowCoeff, hα_eq, hβ_eq]
    · intro f1 _ f2 _ heq
      have hcast1 : ∀ (g : ∀ C : cs, (C.1 → ZMod 2) × (C.1 → ZMod 2)) (C1 C2 : cs) (h : C1 = C2) (x : C1.1) (y : C2.1),
          x.1 = y.1 → (g C1).1 x = (g C2).1 y := by
        rintro g C1 _ rfl x y hxy; exact congrArg (g C1).1 (Subtype.ext hxy)
      have hcast2 : ∀ (g : ∀ C : cs, (C.1 → ZMod 2) × (C.1 → ZMod 2)) (C1 C2 : cs) (h : C1 = C2) (x : C1.1) (y : C2.1),
          x.1 = y.1 → (g C1).2 x = (g C2).2 y := by
        rintro g C1 _ rfl x y hxy; exact congrArg (g C1).2 (Subtype.ext hxy)
      funext ⟨C, hC⟩
      apply Prod.ext <;> funext ⟨i, hiC⟩
      · have hcomp_eq : PEqualNP.Outside.L_lib_966.aux.compOf a b i = C := by
          obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hC
          exact PEqualNP.Outside.L_lib_966.aux.compOf_eq_of_mem a b hiC
        have hsub : (⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i,
            Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ : cs) = ⟨C, hC⟩ := Subtype.ext hcomp_eq
        let ab1 : ZMod 2 × ZMod 2 :=
          ((f1 ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).1
            ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩,
           (f1 ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).2
            ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩)
        let ab2 : ZMod 2 × ZMod 2 :=
          ((f2 ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).1
            ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩,
           (f2 ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).2
            ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩)
        have hpair :
            (PEqualNP.Outside.L_lib_966.aux.bestP (a i) (b i) ab1.1 ab1.2,
             PEqualNP.Outside.L_lib_966.aux.bestD ab1.1 ab1.2) =
            (PEqualNP.Outside.L_lib_966.aux.bestP (a i) (b i) ab2.1 ab2.2,
             PEqualNP.Outside.L_lib_966.aux.bestD ab2.1 ab2.2) :=
          Prod.ext (congrFun (congrArg Prod.fst heq) i) (congrFun (congrArg Prod.snd heq) i)
        have hinj : ab1 = ab2 :=
          PEqualNP.Outside.L_lib_966.aux.best_injective (hvalid i).1 (hvalid i).2.1 (hvalid i).2.2 hpair
        have h1 : ab1.1 = ab2.1 := congrArg Prod.fst hinj
        have hc1 := hcast1 f1 _ ⟨C, hC⟩ hsub ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩ ⟨i, hiC⟩ rfl
        have hc2 := hcast1 f2 _ ⟨C, hC⟩ hsub ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩ ⟨i, hiC⟩ rfl
        exact hc1.symm.trans (h1.trans hc2)
      · have hcomp_eq : PEqualNP.Outside.L_lib_966.aux.compOf a b i = C := by
          obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hC
          exact PEqualNP.Outside.L_lib_966.aux.compOf_eq_of_mem a b hiC
        have hsub : (⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i,
            Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ : cs) = ⟨C, hC⟩ := Subtype.ext hcomp_eq
        let ab1 : ZMod 2 × ZMod 2 :=
          ((f1 ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).1
            ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩,
           (f1 ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).2
            ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩)
        let ab2 : ZMod 2 × ZMod 2 :=
          ((f2 ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).1
            ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩,
           (f2 ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩).2
            ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩)
        have hpair :
            (PEqualNP.Outside.L_lib_966.aux.bestP (a i) (b i) ab1.1 ab1.2,
             PEqualNP.Outside.L_lib_966.aux.bestD ab1.1 ab1.2) =
            (PEqualNP.Outside.L_lib_966.aux.bestP (a i) (b i) ab2.1 ab2.2,
             PEqualNP.Outside.L_lib_966.aux.bestD ab2.1 ab2.2) :=
          Prod.ext (congrFun (congrArg Prod.fst heq) i) (congrFun (congrArg Prod.snd heq) i)
        have hinj : ab1 = ab2 :=
          PEqualNP.Outside.L_lib_966.aux.best_injective (hvalid i).1 (hvalid i).2.1 (hvalid i).2.2 hpair
        have h2 : ab1.2 = ab2.2 := congrArg Prod.snd hinj
        have hc1 := hcast2 f1 _ ⟨C, hC⟩ hsub ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩ ⟨i, hiC⟩ rfl
        have hc2 := hcast2 f2 _ ⟨C, hC⟩ hsub ⟨i, PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i⟩ ⟨i, hiC⟩ rfl
        exact hc1.symm.trans (h2.trans hc2)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨α, β, hαβ, ht⟩ := (PEqualNP.Outside.L_lib_966.aux.good_iff_tiling hvalid p.1 p.2).mp hp
      refine ⟨fun C => (fun i => α i.1, fun i => β i.1), ?_, ?_⟩
      · simp only [prodTil, Fintype.mem_piFinset]
        intro ⟨C, hC⟩
        simp only [Til, Finset.mem_filter, Finset.mem_univ, true_and]
        intro v hv
        have htC := PEqualNP.Outside.L_lib_966.aux.isTiling_restrict_part ht hC v hv
        rw [← Finset.sum_coe_sort C (fun i => PEqualNP.Outside.L_lib_966.aux.rowCoeff a b α β i v)] at htC
        exact htC
      · apply Prod.ext <;> funext i
        · exact (hαβ i).1.symm
        · exact (hαβ i).2.symm
  ·
    intro t L
    constructor
    ·
      rintro ⟨T, ask, bias, P, d, hT, herr⟩
      refine PEqualNP.Outside.L_lib_966.aux.parity_tree_lower T ask bias e t k L hT ?_
      intro p hp
      obtain ⟨x0, _, hx0⟩ := Finset.mem_image.mp hp
      let H := PEqualNP.Outside.L_lib_966.aux.pathSpan ask p
      let V := PEqualNP.Outside.L_lib_966.aux.perpSub H
      let M : Finset (Fin (4 * e)) := Finset.univ.filter (fun i => ∃ v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i, v ∈ H)
      have hM_ge : 4 * (e - t) ≤ M.card := by
        have hV_pos : (0 : ℤ) < Fintype.card V := by
          have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨⟨0, V.zero_mem⟩⟩
          exact_mod_cast this
        have hsum_le : (∑ y : V, ((Finset.univ.filter (fun i : Fin (4 * e) =>
            dotProduct (a i) (x0 + y.1) * dotProduct (b i) (x0 + y.1) ≠
            dotProduct (P p i) (x0 + y.1) + d p i)).card : ℤ)) ≤ (t : ℤ) * (Fintype.card V : ℤ) := by
          calc (∑ y : V, ((Finset.univ.filter (fun i : Fin (4 * e) =>
                  dotProduct (a i) (x0 + y.1) * dotProduct (b i) (x0 + y.1) ≠
                  dotProduct (P p i) (x0 + y.1) + d p i)).card : ℤ))
              ≤ ∑ _y : V, (t : ℤ) := by
                refine Finset.sum_le_sum fun y _ => ?_
                have hrun : PEqualNP.Outside.L_lib_966.aux.run T ask bias (x0 + y.1) = p := by
                  rw [PEqualNP.Outside.L_lib_966.aux.run_eq_iff_add_mem_perpSub T ask bias hx0]
                  have : x0 + y.1 + x0 = y.1 := by
                    rw [add_comm x0 y.1, add_assoc, PEqualNP.Outside.L_lib_966.aux.vec_add_self, add_zero]
                  rw [this]; exact y.2
                have hy := herr (x0 + y.1)
                change (Finset.univ.filter (fun i : Fin (4 * e) =>
                  dotProduct (a i) (x0 + y.1) * dotProduct (b i) (x0 + y.1) ≠
                  dotProduct (P (PEqualNP.Outside.L_lib_966.aux.run T ask bias (x0 + y.1)) i) (x0 + y.1) +
                  d (PEqualNP.Outside.L_lib_966.aux.run T ask bias (x0 + y.1)) i)).card ≤ t at hy
                rw [hrun] at hy
                exact_mod_cast hy
            _ = (Fintype.card V : ℤ) * (t : ℤ) := by simp [Finset.sum_const]
            _ = (t : ℤ) * (Fintype.card V : ℤ) := mul_comm _ _
        have hswap : (∑ y : V, ((Finset.univ.filter (fun i : Fin (4 * e) =>
            dotProduct (a i) (x0 + y.1) * dotProduct (b i) (x0 + y.1) ≠
            dotProduct (P p i) (x0 + y.1) + d p i)).card : ℤ)) =
            ∑ i : Fin (4 * e), ((Finset.univ.filter (fun y : V =>
            dotProduct (a i) (x0 + y.1) * dotProduct (b i) (x0 + y.1) ≠
            dotProduct (P p i) (x0 + y.1) + d p i)).card : ℤ) := by
          simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
          exact Finset.sum_comm
        have hnonM_ge : ((Finset.univ \ M).card : ℤ) * (Fintype.card V : ℤ) ≤
            4 * (∑ i ∈ Finset.univ \ M, ((Finset.univ.filter (fun y : V =>
              dotProduct (a i) (x0 + y.1) * dotProduct (b i) (x0 + y.1) ≠
              dotProduct (P p i) (x0 + y.1) + d p i)).card : ℤ)) := by
          rw [Finset.mul_sum]
          calc ((Finset.univ \ M).card : ℤ) * (Fintype.card V : ℤ)
              = ∑ _i ∈ Finset.univ \ M, (Fintype.card V : ℤ) := by simp [Finset.sum_const]
            _ ≤ _ := by
                refine Finset.sum_le_sum fun i hi => ?_
                have hi_nM : i ∉ M := (Finset.mem_sdiff.mp hi).2
                simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and] at hi_nM
                exact PEqualNP.Outside.L_lib_966.aux.quad_coset_err_ge H x0 (a i) (b i) (P p i) (d p i)
                  (hi_nM (a i) (by simp [PEqualNP.Outside.L_lib_966.aux.freqOf]))
                  (hi_nM (b i) (by simp [PEqualNP.Outside.L_lib_966.aux.freqOf]))
                  (hi_nM (a i + b i) (by simp [PEqualNP.Outside.L_lib_966.aux.freqOf]))
        have hsub_le : (∑ i ∈ Finset.univ \ M, ((Finset.univ.filter (fun y : V =>
            dotProduct (a i) (x0 + y.1) * dotProduct (b i) (x0 + y.1) ≠
            dotProduct (P p i) (x0 + y.1) + d p i)).card : ℤ)) ≤
            ∑ i : Fin (4 * e), ((Finset.univ.filter (fun y : V =>
            dotProduct (a i) (x0 + y.1) * dotProduct (b i) (x0 + y.1) ≠
            dotProduct (P p i) (x0 + y.1) + d p i)).card : ℤ) :=
          Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.cast_nonneg _
        have hmul_le : ((Finset.univ \ M).card : ℤ) * (Fintype.card V : ℤ) ≤ (4 * t : ℤ) * (Fintype.card V : ℤ) := by
          linarith
        have hleZ : ((Finset.univ \ M).card : ℤ) ≤ (4 * t : ℤ) := le_of_mul_le_mul_right hmul_le hV_pos
        have hleN : (Finset.univ \ M).card ≤ 4 * t := by exact_mod_cast hleZ
        have hcard_sdiff : (Finset.univ \ M).card + M.card = 4 * e := by
          have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ M)
          simpa using this
        omega

      have hM_part : M.card = ∑ C ∈ cs, (C.filter (fun i => ∃ v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i, v ∈ H)).card := by
        have hdisj : (cs : Set (Finset (Fin (4 * e)))).PairwiseDisjoint
            (fun C => C.filter (fun i => ∃ v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i, v ∈ H)) := by
          intro C1 h1 C2 h2 hne
          exact (PEqualNP.Outside.L_lib_966.aux.partsOf_disjoint a b h1 h2 hne).mono
            (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        rw [← Finset.card_biUnion hdisj]
        congr 1
        ext i
        simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        constructor
        · intro h
          exact ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i,
            Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
            PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i, h⟩
        · rintro ⟨_, _, _, h⟩; exact h
      have hsum_inf : (∑ C ∈ cs, Module.finrank (ZMod 2) (H ⊓ PEqualNP.Outside.L_lib_966.aux.spanOf a b C : Submodule (ZMod 2) (Fin n → ZMod 2))) ≤
          Module.finrank (ZMod 2) H :=
        PEqualNP.Outside.L_lib_966.aux.sum_finrank_inf_le_of_finrank_sup_eq cs
          (PEqualNP.Outside.L_lib_966.aux.spanOf a b) hindep H
      have hbound1 : M.card ≤ 4 * Module.finrank (ZMod 2) H := by
        rw [hM_part]
        calc (∑ C ∈ cs, (C.filter (fun i => ∃ v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i, v ∈ H)).card)
            ≤ ∑ C ∈ cs, 4 * Module.finrank (ZMod 2) (H ⊓ PEqualNP.Outside.L_lib_966.aux.spanOf a b C : Submodule (ZMod 2) (Fin n → ZMod 2)) := by
              refine Finset.sum_le_sum fun C hC => ?_
              exact (PEqualNP.Outside.L_lib_966.sec4.comp4_affined_bounds a b C (fun i _ => hvalid i)
                (hall43 C hC).1 (hall43 C hC).2 ⟨α0, β0, PEqualNP.Outside.L_lib_966.aux.isTiling_restrict_part ht0 hC⟩ H).1
          _ = 4 * ∑ C ∈ cs, Module.finrank (ZMod 2) (H ⊓ PEqualNP.Outside.L_lib_966.aux.spanOf a b C : Submodule (ZMod 2) (Fin n → ZMod 2)) :=
              (Finset.mul_sum _ _ _).symm
          _ ≤ 4 * Module.finrank (ZMod 2) H := Nat.mul_le_mul_left 4 hsum_inf
      have hbound2 : M.card ≤ 2 * Module.finrank (ZMod 2) H + 2 * k := by
        rw [hM_part]
        calc (∑ C ∈ cs, (C.filter (fun i => ∃ v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i, v ∈ H)).card)
            ≤ ∑ C ∈ cs, (2 * Module.finrank (ZMod 2) (H ⊓ PEqualNP.Outside.L_lib_966.aux.spanOf a b C : Submodule (ZMod 2) (Fin n → ZMod 2)) +
                if (∃ v : Fin n → ZMod 2, ∀ i ∈ C, v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i) then 2 else 0) := by
              refine Finset.sum_le_sum fun C hC => ?_
              have hcb := (PEqualNP.Outside.L_lib_966.sec4.comp4_affined_bounds a b C (fun i _ => hvalid i)
                (hall43 C hC).1 (hall43 C hC).2 ⟨α0, β0, PEqualNP.Outside.L_lib_966.aux.isTiling_restrict_part ht0 hC⟩ H).2
              by_cases hex : ∃ v : Fin n → ZMod 2, ∀ i ∈ C, v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i
              · have hex' : ∃ v : PEqualNP.Outside.L_lib_966.sec4.Vec n, ∀ i ∈ C, v ∈ PEqualNP.Outside.L_lib_966.sec4.freqOf a b i := hex
                rw [if_pos hex'] at hcb; rw [if_pos hex]; exact hcb
              · have hex' : ¬ ∃ v : PEqualNP.Outside.L_lib_966.sec4.Vec n, ∀ i ∈ C, v ∈ PEqualNP.Outside.L_lib_966.sec4.freqOf a b i := hex
                rw [if_neg hex'] at hcb; rw [if_neg hex]; exact hcb
          _ = 2 * (∑ C ∈ cs, Module.finrank (ZMod 2) (H ⊓ PEqualNP.Outside.L_lib_966.aux.spanOf a b C : Submodule (ZMod 2) (Fin n → ZMod 2))) +
              ∑ C ∈ cs, (if (∃ v : Fin n → ZMod 2, ∀ i ∈ C, v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i) then 2 else 0) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          _ ≤ 2 * Module.finrank (ZMod 2) H + 2 * k := by
              have hk_sum : (∑ C ∈ cs, (if (∃ v : Fin n → ZMod 2, ∀ i ∈ C, v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i) then 2 else 0)) = 2 * k := by
                rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
              rw [hk_sum]
              omega
      dsimp only [H] at hbound1 hbound2
      change (e - t) + (e - t - k) ≤ Module.finrank (ZMod 2) (PEqualNP.Outside.L_lib_966.aux.pathSpan ask p)
      omega
    ·
      intro hL
      let s := e - t
      let q := s + (s - k)
      let cs1 := cs.filter (fun C => ∃ v : Fin n → ZMod 2, ∀ i ∈ C, v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i)
      let cs2 := cs \ cs1
      have hcs1_card : cs1.card = k := rfl
      have hcs2_card : cs2.card = e - k := by
        have h1 : cs2.card + cs1.card = cs.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ cs)
        rw [hparts_card, hcs1_card] at h1
        omega
      have hs_le_e : s ≤ e := Nat.sub_le e t
      obtain ⟨sel1, hsel1_sub, hsel1_card⟩ := Finset.exists_subset_card_eq (s := cs1) (n := min s k) (by rw [hcs1_card]; exact Nat.min_le_right s k)
      obtain ⟨sel2, hsel2_sub, hsel2_card⟩ := Finset.exists_subset_card_eq (s := cs2) (n := s - min s k) (by rw [hcs2_card]; omega)
      have hsel_disj : Disjoint sel1 sel2 :=
        Finset.disjoint_sdiff.mono hsel1_sub hsel2_sub
      have hsel_card : (sel1 ∪ sel2).card = s := by
        rw [Finset.card_union_of_disjoint hsel_disj, hsel1_card, hsel2_card]; omega

      have hkill1 : ∀ C ∈ sel1, ∃ w : Fin n → ZMod 2, ∀ i ∈ C, ∃ v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i,
          v ∈ Submodule.span (ZMod 2) ({w} : Set (Fin n → ZMod 2)) := by
        intro C hC
        have hC1 : C ∈ cs1 := hsel1_sub hC
        have hCcs : C ∈ cs := (Finset.mem_filter.mp hC1).1
        exact (PEqualNP.Outside.L_lib_966.sec4.comp4_kill_questions a b C (fun i _ => hvalid i)
          (hall43 C hCcs).1 (hall43 C hCcs).2 ⟨α0, β0, PEqualNP.Outside.L_lib_966.aux.isTiling_restrict_part ht0 hCcs⟩).1
          (Finset.mem_filter.mp hC1).2
      have hkill2 : ∀ C ∈ sel2, ∃ w1 w2 : Fin n → ZMod 2, ∀ i ∈ C, ∃ v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i,
          v ∈ Submodule.span (ZMod 2) ({w1, w2} : Set (Fin n → ZMod 2)) := by
        intro C hC
        have hCcs : C ∈ cs := (Finset.mem_sdiff.mp (hsel2_sub hC)).1
        exact (PEqualNP.Outside.L_lib_966.sec4.comp4_kill_questions a b C (fun i _ => hvalid i)
          (hall43 C hCcs).1 (hall43 C hCcs).2 ⟨α0, β0, PEqualNP.Outside.L_lib_966.aux.isTiling_restrict_part ht0 hCcs⟩).2
      let l1 : List (Fin n → ZMod 2) :=
        sel1.toList.map (fun C => if h : C ∈ sel1 then (hkill1 C h).choose else 0)
      let l2 : List (Fin n → ZMod 2) :=
        sel2.toList.flatMap (fun C => if h : C ∈ sel2 then [(hkill2 C h).choose, (hkill2 C h).choose_spec.choose] else [])
      let lall : List (Fin n → ZMod 2) := l1 ++ l2
      have hlall_len : lall.length = q := by
        have hl1 : l1.length = sel1.card := by simp [l1]
        have hl2 : l2.length = 2 * sel2.card := by
          have hmap : ∀ (xs : List (Finset (Fin (4 * e)))), (∀ C ∈ xs, C ∈ sel2) →
              (xs.flatMap (fun C => if h : C ∈ sel2 then [(hkill2 C h).choose, (hkill2 C h).choose_spec.choose] else [])).length =
              2 * xs.length := by
            intro xs hxs
            induction xs with
            | nil => simp
            | cons x xs ih =>
              simp only [List.flatMap_cons, List.length_append, List.length_cons]
              have hx : x ∈ sel2 := hxs x List.mem_cons_self
              simp only [hx, ↓reduceDIte, List.length_cons, List.length_nil]
              rw [ih (fun C hC => hxs C (List.mem_cons_of_mem x hC))]
              omega
          rw [hmap sel2.toList (fun C hC => Finset.mem_toList.mp hC), Finset.length_toList]
        simp only [lall, List.length_append, hl1, hl2, hsel1_card, hsel2_card, q]
        omega
      let w : Fin q → Fin n → ZMod 2 := fun j => lall.get (j.cast hlall_len.symm)
      have hmem_range_w : ∀ u ∈ lall, u ∈ Set.range w := by
        intro u hu
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hu
        refine ⟨⟨idx, by omega⟩, ?_⟩
        simp [w]
      have hkill_sel : ∀ C ∈ sel1 ∪ sel2, ∀ i ∈ C,
          ∃ v ∈ PEqualNP.Outside.L_lib_966.aux.freqOf a b i, v ∈ Submodule.span (ZMod 2) (Set.range w) := by
        intro C hC i hiC
        rcases Finset.mem_union.mp hC with hC1 | hC2
        · obtain ⟨v, hvi, hvspan⟩ := (hkill1 C hC1).choose_spec i hiC
          refine ⟨v, hvi, Submodule.span_mono ?_ hvspan⟩
          intro u hu
          rw [Set.mem_singleton_iff] at hu
          subst hu
          apply hmem_range_w
          apply List.mem_append_left
          refine List.mem_map.mpr ⟨C, Finset.mem_toList.mpr hC1, ?_⟩
          simp [hC1]
        · obtain ⟨v, hvi, hvspan⟩ := (hkill2 C hC2).choose_spec.choose_spec i hiC
          refine ⟨v, hvi, Submodule.span_mono ?_ hvspan⟩
          intro u hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
          apply hmem_range_w
          apply List.mem_append_right
          refine List.mem_flatMap.mpr ⟨C, Finset.mem_toList.mpr hC2, ?_⟩
          simp only [hC2, ↓reduceDIte, List.mem_cons, List.not_mem_nil, or_false]
          exact hu
      let T := PEqualNP.Outside.L_lib_966.aux.completeTree q
      let ask := PEqualNP.Outside.L_lib_966.aux.completeAsk w
      let bias : List Bool → ZMod 2 := fun _ => 0
      have hup := PEqualNP.Outside.L_lib_966.aux.parity_tree_upper hL w

      let P : List Bool → Fin (4 * e) → (Fin n → ZMod 2) := fun p i =>
        if h : PEqualNP.Outside.L_lib_966.aux.compOf a b i ∈ sel1 ∪ sel2 ∧
            ∃ x0 : Fin n → ZMod 2, PEqualNP.Outside.L_lib_966.aux.run T ask bias x0 = p then
          let hv := hkill_sel _ h.1 i (PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i)
          (PEqualNP.Outside.L_lib_966.aux.affine_of_mem_span w a b i hv.choose hv.choose_spec.2 hv.choose_spec.1 h.2.choose_spec).choose
        else P0 i
      let d : List Bool → Fin (4 * e) → ZMod 2 := fun p i =>
        if h : PEqualNP.Outside.L_lib_966.aux.compOf a b i ∈ sel1 ∪ sel2 ∧
            ∃ x0 : Fin n → ZMod 2, PEqualNP.Outside.L_lib_966.aux.run T ask bias x0 = p then
          let hv := hkill_sel _ h.1 i (PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i)
          (PEqualNP.Outside.L_lib_966.aux.affine_of_mem_span w a b i hv.choose hv.choose_spec.2 hv.choose_spec.1 h.2.choose_spec).choose_spec.choose
        else d0 i
      refine ⟨T, ask, bias, P, d, hup.1, ?_⟩
      intro x
      let p := PEqualNP.Outside.L_lib_966.aux.run T ask bias x

      have herr_zero_sel : ∀ i : Fin (4 * e), PEqualNP.Outside.L_lib_966.aux.compOf a b i ∈ sel1 ∪ sel2 →
          dotProduct (a i) x * dotProduct (b i) x = dotProduct (P p i) x + d p i := by
        intro i hi
        have hcond : PEqualNP.Outside.L_lib_966.aux.compOf a b i ∈ sel1 ∪ sel2 ∧
            ∃ x0 : Fin n → ZMod 2, PEqualNP.Outside.L_lib_966.aux.run T ask bias x0 = p :=
          ⟨hi, ⟨x, rfl⟩⟩
        simp only [P, d, hcond, ↓reduceDIte]
        let hv := hkill_sel _ hcond.1 i (PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i)
        exact (PEqualNP.Outside.L_lib_966.aux.affine_of_mem_span w a b i hv.choose hv.choose_spec.2 hv.choose_spec.1
          hcond.2.choose_spec).choose_spec.choose_spec x rfl

      have hrem_err : ∀ C ∈ cs \ (sel1 ∪ sel2),
          (C.filter (fun i => dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P p i) x + d p i)).card = 1 := by
        intro C hC
        have hCcs : C ∈ cs := (Finset.mem_sdiff.mp hC).1
        have hCnS : C ∉ sel1 ∪ sel2 := (Finset.mem_sdiff.mp hC).2
        have hfilt : C.filter (fun i => dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P p i) x + d p i) =
            C.filter (fun i => dotProduct (a i) x = α0 i ∧ dotProduct (b i) x = β0 i) := by
          ext i
          simp only [Finset.mem_filter, and_congr_right_iff]
          intro hiC
          have hcomp_eq : PEqualNP.Outside.L_lib_966.aux.compOf a b i = C := by
            obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hCcs
            exact PEqualNP.Outside.L_lib_966.aux.compOf_eq_of_mem a b hiC
          have hnot : ¬ (PEqualNP.Outside.L_lib_966.aux.compOf a b i ∈ sel1 ∪ sel2 ∧
              ∃ x0 : Fin n → ZMod 2, PEqualNP.Outside.L_lib_966.aux.run T ask bias x0 = p) :=
            fun h => hCnS (hcomp_eq ▸ h.1)
          simp only [P, d, hnot, ↓reduceDIte]
          rw [(hα0β0 i).1, (hα0β0 i).2, ne_comm]
          exact PEqualNP.Outside.L_lib_966.aux.best_err_iff (a i) (b i) x (α0 i) (β0 i)
        rw [hfilt]
        have htC := PEqualNP.Outside.L_lib_966.aux.isTiling_restrict_part ht0 hCcs
        have hconst := (PEqualNP.Outside.L_lib_966.aux.isTiling_iff_const_count a b α0 β0 C (fun i _ => hvalid i)).mp htC x
        rw [(hall43 C hCcs).1] at hconst
        have hnat : 4 * (C.filter (fun i => dotProduct (a i) x = α0 i ∧ dotProduct (b i) x = β0 i)).card = 4 := by
          exact_mod_cast hconst
        omega

      have hsub : (Finset.univ.filter (fun i : Fin (4 * e) =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P p i) x + d p i)) ⊆
          (cs \ (sel1 ∪ sel2)).biUnion
            (fun C => C.filter (fun i => dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P p i) x + d p i)) := by
        intro i hi
        have hne := (Finset.mem_filter.mp hi).2
        have hnot_sel : PEqualNP.Outside.L_lib_966.aux.compOf a b i ∉ sel1 ∪ sel2 :=
          fun h => hne (herr_zero_sel i h)
        refine Finset.mem_biUnion.mpr ⟨PEqualNP.Outside.L_lib_966.aux.compOf a b i,
          Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hnot_sel⟩,
          Finset.mem_filter.mpr ⟨PEqualNP.Outside.L_lib_966.aux.compOf_mem_self a b i, hne⟩⟩
      have hcard_le : (Finset.univ.filter (fun i : Fin (4 * e) =>
          dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P p i) x + d p i)).card ≤ (cs \ (sel1 ∪ sel2)).card := by
        calc (Finset.univ.filter (fun i : Fin (4 * e) =>
                dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P p i) x + d p i)).card
            ≤ ((cs \ (sel1 ∪ sel2)).biUnion
                (fun C => C.filter (fun i => dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P p i) x + d p i))).card :=
              Finset.card_le_card hsub
          _ ≤ ∑ C ∈ cs \ (sel1 ∪ sel2),
                (C.filter (fun i => dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P p i) x + d p i)).card :=
              Finset.card_biUnion_le
          _ = ∑ _C ∈ cs \ (sel1 ∪ sel2), 1 := Finset.sum_congr rfl hrem_err
          _ = (cs \ (sel1 ∪ sel2)).card := by simp
      have hsel_sub_cs : sel1 ∪ sel2 ⊆ cs :=
        Finset.union_subset (hsel1_sub.trans (Finset.filter_subset _ cs)) (hsel2_sub.trans Finset.sdiff_subset)
      have hrem_card : (cs \ (sel1 ∪ sel2)).card = e - s := by
        have h1 : (cs \ (sel1 ∪ sel2)).card + (sel1 ∪ sel2).card = cs.card :=
          Finset.card_sdiff_add_card_eq_card hsel_sub_cs
        rw [hsel_card, hparts_card] at h1
        omega
      change (Finset.univ.filter (fun i : Fin (4 * e) =>
        dotProduct (a i) x * dotProduct (b i) x ≠ dotProduct (P p i) x + d p i)).card ≤ t
      omega
