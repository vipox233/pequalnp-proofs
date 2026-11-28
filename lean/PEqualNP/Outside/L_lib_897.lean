import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_897
open scoped BigOperators

abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
abbrev W (l r : ℕ) := V l × V r

variable {l r m : ℕ}

def ev (Y : Submodule F (V l)) (i : Fin l) (y : Y) : F := y.val i

noncomputable def neigh (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l)) (j : Fin r) : Finset (Fin l) := by
  classical
  exact Finset.univ.filter (fun i => edge i j ∧ ev Y i ≠ 0)

noncomputable def free (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l)) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun j => (neigh edge Y j).card = 0)

noncomputable def tied (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l)) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun j => ((neigh edge Y j).image (ev Y)).card = 1)

noncomputable def tether (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l)) (j : Fin r) (y : Y) : F := by
  classical
  exact ∑ g ∈ (neigh edge Y j).image (ev Y), g y

def projects (Y : Submodule F (V l)) (U : Submodule F (W l r)) : Prop :=
  ∀ x : V l, x ∈ Y ↔ ∃ z : V r, (x,z) ∈ U

def iso (edge : Fin l → Fin r → Prop) (U : Submodule F (W l r)) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ i j, edge i j → x.1 i * y.2 j = y.1 i * x.2 j

def synd (p : Fin l → V m) (h : Fin r → V m) (U : Submodule F (W l r)) : Prop :=
  ∀ x ∈ U, ∀ b : Fin m, (∑ i, p i b * x.1 i) + (∑ j, h j b * x.2 j) = 0

noncomputable def fixedPart (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    (b : ↥(tied edge Y) → F) (y : Y) (j : Fin r) : F := by
  classical
  exact if hj : j ∈ tied edge Y then b ⟨j,hj⟩ * tether edge Y j y else 0

def fits (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    (b : ↥(tied edge Y) → F) (U : Submodule F (W l r)) : Prop :=
  ∀ (y : Y) (z : V r), (y.val,z) ∈ U → ∀ j, j ∉ free edge Y → z j = fixedPart edge Y b y j

noncomputable def D (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l)) (h : Fin r → V m) : Submodule F (V m) := by
  classical
  exact Submodule.span F (↑((free edge Y).image h) : Set (V m))

noncomputable def col (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l)) (h : Fin r → V m)
    (j : Fin r) (y : Y) : V m ⧸ D edge Y h :=
  (tether edge Y j y) • (D edge Y h).mkQ (h j)

noncomputable def T (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l)) (h : Fin r → V m) :
    Submodule F (Y → V m ⧸ D edge Y h) := by
  classical
  exact Submodule.span F (↑((tied edge Y).image (col edge Y h)) : Set (Y → V m ⧸ D edge Y h))

noncomputable def offset (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    (p : Fin l → V m) (h : Fin r → V m) (y : Y) : V m ⧸ D edge Y h :=
  (D edge Y h).mkQ (∑ i, ev Y i y • p i)

noncomputable def betaMap (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l)) (h : Fin r → V m) :
    (↥(tied edge Y) → F) →ₗ[F] (Y → V m ⧸ D edge Y h) :=
  Fintype.linearCombination F (fun j : ↥(tied edge Y) => col edge Y h j.val)

noncomputable def freeMap (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l)) (h : Fin r → V m) :
    (↥(free edge Y) → F) →ₗ[F] V m :=
  Fintype.linearCombination F (fun j : ↥(free edge Y) => h j.val)

end PEqualNP.Outside.L_lib_897

namespace PEqualNP.Outside.L_lib_897
open scoped BigOperators

variable {l r m : ℕ} (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
variable (p : Fin l → V m) (h : Fin r → V m)

abbrev Free := ↥(free edge Y) → F
abbrev Bits := ↥(tied edge Y) → F

def evalL (i : Fin l) : Y →ₗ[F] F := (LinearMap.proj i).comp Y.subtype

noncomputable def leftS : Y →ₗ[F] V m :=
  (Fintype.linearCombination F p).comp Y.subtype

noncomputable def tetherL (j : Fin r) : Y →ₗ[F] F where
  toFun := tether edge Y j
  map_add' x y := by
    classical
    unfold tether
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g hg
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hg
    rfl
  map_smul' c x := by
    classical
    unfold tether
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hg
    rfl

noncomputable def fixedL (b : Bits edge Y) : Y →ₗ[F] V r := by
  classical
  exact LinearMap.pi fun j => if hj : j ∈ tied edge Y then b ⟨j,hj⟩ • tetherL edge Y j else 0

theorem fixedL_apply (b : Bits edge Y) (y : Y) (j : Fin r) :
    fixedL edge Y b y j = fixedPart edge Y b y j := by
  classical
  by_cases hj : j ∈ tied edge Y <;> simp [fixedL, fixedPart, hj, tetherL, smul_eq_mul]

noncomputable def fill : Free edge Y →ₗ[F] V r := by
  classical
  exact LinearMap.pi fun j => if hj : j ∈ free edge Y then LinearMap.proj ⟨j,hj⟩ else 0

def takeFree (z : V r) : Free edge Y := fun j => z j.val

theorem fill_on (c : Free edge Y) (j : ↥(free edge Y)) : fill edge Y c j.val = c j := by
  simp [fill, j.property]

theorem fill_off (c : Free edge Y) (j : Fin r) (hj : j ∉ free edge Y) : fill edge Y c j = 0 := by
  simp [fill, hj]

theorem fixed_on_free (b : Bits edge Y) (y : Y) (j : ↥(free edge Y)) :
    fixedL edge Y b y j.val = 0 := by
  classical
  have hcard : (neigh edge Y j.val).card = 0 := (Finset.mem_filter.mp j.property).2
  have hempty : neigh edge Y j.val = ∅ := Finset.card_eq_zero.mp hcard
  have hn : j.val ∉ tied edge Y := by simp [tied, hempty]
  rw [fixedL_apply]
  simp [fixedPart, hn]

noncomputable def encode (b : Bits edge Y) : (Y × Free edge Y) →ₗ[F] W l r :=
  (Y.subtype.comp (LinearMap.fst _ _ _)).prod
    ((fixedL edge Y b).coprod (fill edge Y))

theorem encode_apply (b : Bits edge Y) (y : Y) (c : Free edge Y) :
    encode edge Y b (y,c) = (y.val, fixedL edge Y b y + fill edge Y c) := rfl

theorem encode_inj (b : Bits edge Y) : Function.Injective (encode edge Y b) := by
  rintro ⟨x,c⟩ ⟨y,d⟩ eq
  have he : x = y := Subtype.ext (congrArg Prod.fst eq)
  subst y
  have hcd := congrArg Prod.snd eq
  refine Prod.ext (show x = x from rfl) ?_
  funext j
  have hh := congrFun hcd j.val
  change fixedL edge Y b x j.val + fill edge Y c j.val =
    fixedL edge Y b x j.val + fill edge Y d j.val at hh
  simpa only [fill_on, add_left_cancel_iff] using hh

theorem encode_exists (b : Bits edge Y) (y : Y) (z : V r)
    (hf : ∀ j, j ∉ free edge Y → z j = fixedPart edge Y b y j) :
    encode edge Y b (y, takeFree edge Y z) = (y.val,z) := by
  rw [encode_apply]
  refine Prod.ext rfl ?_
  funext j
  change fixedL edge Y b y j + fill edge Y (takeFree edge Y z) j = z j
  by_cases hj : j ∈ free edge Y
  · rw [fixed_on_free edge Y b y ⟨j,hj⟩, fill_on edge Y _ ⟨j,hj⟩, zero_add]
    rfl
  · rw [fill_off edge Y _ j hj, add_zero, fixedL_apply, hf j hj]

noncomputable def rightS : V r →ₗ[F] V m := Fintype.linearCombination F h

noncomputable def patternS (b : Bits edge Y) : Y →ₗ[F] V m :=
  leftS Y p + (rightS h).comp (fixedL edge Y b)

theorem rightS_fill (c : Free edge Y) : rightS h (fill edge Y c) = freeMap edge Y h c := by
  classical
  change (∑ j, fill edge Y c j • h j) = ∑ j : ↥(free edge Y), c j • h j.val
  calc
    _ = ∑ j ∈ free edge Y, fill edge Y c j • h j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      rw [fill_off edge Y _ j hj, zero_smul]
    _ = _ := by
      rw [← Finset.sum_coe_sort]
      exact Finset.sum_congr rfl (fun j _ => by rw [fill_on])

theorem synd_sum (x : W l r) (a : Fin m) :
    ((Fintype.linearCombination F p) x.1 + rightS h x.2) a =
      (∑ i, p i a * x.1 i) + (∑ j, h j a * x.2 j) := by
  simp only [rightS, Pi.add_apply, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1 <;> exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem proj_synd (b : Bits edge Y) (y : Y) (c : Free edge Y) :
    (Fintype.linearCombination F p) (encode edge Y b (y,c)).1 + rightS h (encode edge Y b (y,c)).2 =
      patternS edge Y p h b y + freeMap edge Y h c := by
  rw [encode_apply]
  simp only [map_add, rightS_fill, patternS, LinearMap.add_apply, LinearMap.comp_apply, leftS,
    Submodule.subtype_apply, add_assoc]

theorem pattern_quot (b : Bits edge Y) (y : Y) :
    (D edge Y h).mkQ (patternS edge Y p h b y) = offset edge Y p h y + betaMap edge Y h b y := by
  classical
  simp only [patternS, LinearMap.add_apply, map_add, leftS, offset, betaMap,
    LinearMap.comp_apply, Submodule.subtype_apply, Fintype.linearCombination_apply]
  congr 1
  simp only [rightS, Fintype.linearCombination_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, col]
  calc
    _ = ∑ j ∈ tied edge Y, fixedL edge Y b y j • (D edge Y h).mkQ (h j) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp [fixedL_apply, fixedPart, hj]
    _ = _ := by
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro j _
      simp [fixedL_apply, fixedPart, j.property, mul_smul]

end PEqualNP.Outside.L_lib_897

namespace PEqualNP.Outside.L_lib_897

variable {l r m : ℕ} (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
variable (p : Fin l → V m) (h : Fin r → V m)

theorem range_betaMap : LinearMap.range (betaMap edge Y h) = T edge Y h := by
  classical
  rw [betaMap, Fintype.range_linearCombination, T, Finset.coe_image]
  exact congrArg (Submodule.span F)
    (Set.image_eq_range (col edge Y h) (↑(tied edge Y) : Set (Fin r))).symm

theorem range_freeMap : LinearMap.range (freeMap edge Y h) = D edge Y h := by
  classical
  rw [freeMap, Fintype.range_linearCombination, D, Finset.coe_image]
  exact congrArg (Submodule.span F)
    (Set.image_eq_range h (↑(free edge Y) : Set (Fin r))).symm

theorem rank_freeKer : Module.finrank F (LinearMap.ker (freeMap edge Y h)) =
    (free edge Y).card - Module.finrank F (D edge Y h) := by
  have hr := (freeMap edge Y h).finrank_range_add_finrank_ker
  rw [range_freeMap, Module.finrank_pi, Fintype.card_coe] at hr
  omega

noncomputable def offsetLinear : Y →ₗ[F] V m ⧸ D edge Y h :=
  (D edge Y h).mkQ.comp ((Fintype.linearCombination F p).comp Y.subtype)

@[simp] theorem coe_offsetLinear :
    (offsetLinear edge Y p h : Y → V m ⧸ D edge Y h) = offset edge Y p h := rfl

open scoped Classical in
theorem count_beta :
    Nat.card {b // betaMap edge Y h b = offset edge Y p h} =
      if offset edge Y p h ∈ T edge Y h then
        2 ^ ((tied edge Y).card - Module.finrank F (T edge Y h))
      else 0 := by
  by_cases hT : offset edge Y p h ∈ T edge Y h
  · rw [if_pos hT]
    rw [← range_betaMap] at hT
    obtain ⟨b₀, hb₀⟩ := LinearMap.mem_range.mp hT

    let e : {b // betaMap edge Y h b = offset edge Y p h} ≃
        LinearMap.ker (betaMap edge Y h) :=
      { toFun := fun b => ⟨b.val - b₀, by
          rw [LinearMap.mem_ker, map_sub, b.property, hb₀, sub_self]⟩
        invFun := fun k => ⟨k.val + b₀, by
          have hk : betaMap edge Y h k.val = 0 := LinearMap.mem_ker.mp k.property
          rw [map_add, hk, hb₀, zero_add]⟩
        left_inv := fun b => Subtype.ext (sub_add_cancel b.val b₀)
        right_inv := fun k => Subtype.ext (add_sub_cancel_right k.val b₀) }
    have hr := (betaMap edge Y h).finrank_range_add_finrank_ker
    rw [range_betaMap, Module.finrank_pi, Fintype.card_coe] at hr
    have hk : Module.finrank F (LinearMap.ker (betaMap edge Y h)) =
        (tied edge Y).card - Module.finrank F (T edge Y h) := by omega
    rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := F), Nat.card_zmod, hk]
  · rw [if_neg hT]
    letI : IsEmpty {b // betaMap edge Y h b = offset edge Y p h} := ⟨fun b => hT (by
      rw [← range_betaMap]
      exact LinearMap.mem_range.mpr ⟨b.val, b.property⟩)⟩
    exact Nat.card_of_isEmpty

end PEqualNP.Outside.L_lib_897

namespace PEqualNP.Outside.L_lib_897
open scoped BigOperators

variable {l r : ℕ}

private theorem f2_eq_one_of_ne_zero {a : F} (ha : a ≠ 0) : a = 1 := by
  have h : ∀ x : F, x = 0 ∨ x = 1 := by decide
  exact (h a).resolve_left ha

open scoped Classical

private theorem mem_iso_neigh (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    {i : Fin l} {j : Fin r} : i ∈ neigh edge Y j ↔ edge i j ∧ ev Y i ≠ 0 := by
  simp only [neigh, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem mem_iso_free (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    {j : Fin r} : j ∈ free edge Y ↔ neigh edge Y j = ∅ := by
  simp only [free, Finset.mem_filter, Finset.mem_univ, true_and, Finset.card_eq_zero]

private theorem mem_iso_tied (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    {j : Fin r} : j ∈ tied edge Y ↔ ((neigh edge Y j).image (ev Y)).card = 1 := by
  simp only [tied, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem tied_iff_image_eq (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    {i : Fin l} {j : Fin r} (hi : i ∈ neigh edge Y j) :
    j ∈ tied edge Y ↔ (neigh edge Y j).image (ev Y) = {ev Y i} := by
  rw [mem_iso_tied edge Y]
  constructor
  · intro hj
    obtain ⟨g, hg⟩ := Finset.card_eq_one.mp hj
    have hi' : ev Y i ∈ ({g} : Finset (Y → F)) :=
      hg ▸ Finset.mem_image_of_mem (ev Y) hi
    simpa only [Finset.mem_singleton.mp hi'] using hg
  · intro h
    exact Finset.card_eq_one.mpr ⟨ev Y i, h⟩

theorem free_not_tied (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    {j : Fin r} (hj : j ∈ free edge Y) : j ∉ tied edge Y := by
  intro ht
  have hn := (mem_iso_free edge Y).mp hj
  have hc := (mem_iso_tied edge Y).mp ht
  simpa [hn] using hc

theorem tether_eq_ev (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    {i : Fin l} {j : Fin r} (hj : j ∈ tied edge Y) (hi : i ∈ neigh edge Y j) :
    tether edge Y j = ev Y i := by
  funext y
  simp only [tether, (tied_iff_image_eq edge Y hi).mp hj, Finset.sum_singleton]

noncomputable def tether_linear (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    (j : Fin r) : Y →ₗ[F] F where
  toFun := tether edge Y j
  map_add' x y := by
    simp only [tether, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g hg
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    rfl
  map_smul' a x := by
    simp only [RingHom.id_apply, tether, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    rfl

@[simp] theorem tether_linear_apply (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    (j : Fin r) (y : Y) : tether_linear edge Y j y = tether edge Y j y := rfl

private theorem exists_ev_eq_one (Y : Submodule F (V l)) {i : Fin l}
    (hi : ev Y i ≠ 0) : ∃ y : Y, ev Y i y = 1 := by
  by_contra h
  apply hi
  funext y
  change ev Y i y = 0
  by_contra hy
  exact h ⟨y, f2_eq_one_of_ne_zero hy⟩

theorem iso_iff_unique_fits (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
    (U : Submodule F (W l r)) (hproj : projects Y U) :
    iso edge U ↔ ∃! b : ↥(tied edge Y) → F, fits edge Y b U := by
  constructor
  · intro hIso

    have hmul : ∀ j i, i ∈ neigh edge Y j →
        ∃ a : F, ∀ (y : Y) (z : V r), (y.val, z) ∈ U → z j = a * ev Y i y := by
      intro j i hi
      obtain ⟨hij, hne⟩ := (mem_iso_neigh edge Y).mp hi
      obtain ⟨y₀, hy₀⟩ := exists_ev_eq_one Y hne
      obtain ⟨z₀, hz₀⟩ := (hproj y₀.val).mp y₀.property
      refine ⟨z₀ j, ?_⟩
      intro y z hz
      have h := hIso (y₀.val, z₀) hz₀ (y.val, z) hz i j hij
      change ev Y i y₀ * z j = ev Y i y * z₀ j at h
      simpa only [hy₀, one_mul, mul_comm (ev Y i y) (z₀ j)] using h
    have hnonempty : ∀ j, j ∉ free edge Y → (neigh edge Y j).Nonempty := by
      intro j hj
      exact Finset.nonempty_iff_ne_empty.mpr (fun h => hj ((mem_iso_free edge Y).mpr h))
    have hzero : ∀ j, j ∉ free edge Y → j ∉ tied edge Y →
        ∀ (y : Y) (z : V r), (y.val, z) ∈ U → z j = 0 := by
      intro j hjf hjt
      obtain ⟨i, hi⟩ := hnonempty j hjf
      have hk : ∃ k ∈ neigh edge Y j, ev Y k ≠ ev Y i := by
        by_contra h
        apply hjt
        apply (tied_iff_image_eq edge Y hi).mpr
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_image_of_mem _ hi, ?_⟩
        intro g hg
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hg
        by_contra hne
        exact h ⟨k, hk, hne⟩
      obtain ⟨k, hk, hdiff⟩ := hk
      obtain ⟨a, ha⟩ := hmul j i hi
      obtain ⟨c, hc⟩ := hmul j k hk
      intro y z hz
      by_contra hne

      have ha₁ : a = 1 := f2_eq_one_of_ne_zero fun ha₀ =>
        hne (by simpa only [ha₀, zero_mul] using ha y z hz)
      have hc₁ : c = 1 := f2_eq_one_of_ne_zero fun hc₀ =>
        hne (by simpa only [hc₀, zero_mul] using hc y z hz)
      apply hdiff
      funext x
      obtain ⟨w, hw⟩ := (hproj x.val).mp x.property
      calc
        ev Y k x = w j := by simpa only [hc₁, one_mul] using (hc x w hw).symm
        _ = ev Y i x := by simpa only [ha₁, one_mul] using ha x w hw
    have hcoeff : ∀ j : ↥(tied edge Y),
        ∃ a : F, ∀ (y : Y) (z : V r), (y.val, z) ∈ U →
          z j.val = a * tether edge Y j.val y := by
      intro j
      obtain ⟨i, hi⟩ := hnonempty j.val (fun hf => free_not_tied edge Y hf j.property)
      obtain ⟨a, ha⟩ := hmul j.val i hi
      refine ⟨a, ?_⟩
      rw [tether_eq_ev edge Y j.property hi]
      exact ha
    let b : ↥(tied edge Y) → F := fun j => Classical.choose (hcoeff j)
    refine ⟨b, ?_, ?_⟩
    · intro y z hz j hj
      by_cases ht : j ∈ tied edge Y
      · simpa only [fixedPart, dif_pos ht, b] using
          Classical.choose_spec (hcoeff ⟨j, ht⟩) y z hz
      · simpa only [fixedPart, dif_neg ht] using hzero j hj ht y z hz
    · intro c hc
      funext j
      have hjf : j.val ∉ free edge Y := fun hf => free_not_tied edge Y hf j.property
      obtain ⟨i, hi⟩ := hnonempty j.val hjf
      obtain ⟨y, hy⟩ := exists_ev_eq_one Y ((mem_iso_neigh edge Y).mp hi).2
      obtain ⟨z, hz⟩ := (hproj y.val).mp y.property
      have hty : tether edge Y j.val y = 1 :=
        (congrFun (tether_eq_ev edge Y j.property hi) y).trans hy
      have hc' : z j.val = c j := by
        simpa only [fixedPart, dif_pos j.property, hty, mul_one] using hc y z hz j.val hjf
      have hb' : z j.val = b j := by
        simpa only [hty, mul_one, b] using Classical.choose_spec (hcoeff j) y z hz
      exact hc'.symm.trans hb'
  · rintro ⟨b, hb, _⟩ ⟨x, z⟩ hx ⟨y, w⟩ hy i j hij
    let xY : Y := ⟨x, (hproj x).mpr ⟨z, hx⟩⟩
    let yY : Y := ⟨y, (hproj y).mpr ⟨w, hy⟩⟩
    change ev Y i xY * w j = ev Y i yY * z j
    by_cases hev : ev Y i = 0
    · simp only [hev, Pi.zero_apply, zero_mul]
    · have hi : i ∈ neigh edge Y j := (mem_iso_neigh edge Y).mpr ⟨hij, hev⟩
      have hj : j ∉ free edge Y := fun hf =>
        Finset.ne_empty_of_mem hi ((mem_iso_free edge Y).mp hf)
      rw [hb xY z hx j hj, hb yY w hy j hj]
      by_cases ht : j ∈ tied edge Y
      · simp only [fixedPart, dif_pos ht, tether_eq_ev edge Y ht hi]
        ac_rfl
      · simp only [fixedPart, dif_neg ht, mul_zero]

end PEqualNP.Outside.L_lib_897

namespace PEqualNP.Outside.L_lib_897
open scoped BigOperators

variable {l r m : ℕ} (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
variable (p : Fin l → V m) (h : Fin r → V m)

noncomputable abbrev KerFree := LinearMap.ker (freeMap edge Y h)

theorem add_self_fzero {M : Type*} [AddCommGroup M] [Module F M] (x : M) : x+x=0 := by
  rw [← two_smul F, show (2 : F) = 0 by decide, zero_smul]

theorem pattern_feasible (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h) (y : Y) :
    patternS edge Y p h b y ∈ D edge Y h := by
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change (D edge Y h).mkQ (patternS edge Y p h b y) = 0
  rw [pattern_quot, hb, add_self_fzero]

theorem fits_feasible (b : Bits edge Y) (U : Submodule F (W l r)) (hp : projects Y U)
    (hs : synd p h U) (hf : fits edge Y b U) : betaMap edge Y h b = offset edge Y p h := by
  funext y
  obtain ⟨z,hz⟩ := (hp y.val).mp y.property
  have he := encode_exists edge Y b y z (hf y z hz)
  have ho : patternS edge Y p h b y + freeMap edge Y h (takeFree edge Y z) = 0 := by
    rw [← proj_synd, he]
    ext a
    rw [synd_sum p h (y.val,z), Pi.zero_apply]
    exact hs (y.val,z) hz a
  have hv : freeMap edge Y h (takeFree edge Y z) ∈ D edge Y h := by
    rw [← range_freeMap]
    exact LinearMap.mem_range_self _ _
  have hzero := congrArg (D edge Y h).mkQ ho
  have hq : (D edge Y h).mkQ (freeMap edge Y h (takeFree edge Y z)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hv
  rw [map_add, map_zero, hq, add_zero, pattern_quot] at hzero
  have hsum := add_self_fzero (offset edge Y p h y)
  exact add_left_cancel (hzero.trans hsum.symm)

noncomputable def getSection (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h) :
    Y →ₗ[F] Free edge Y := by
  classical
  let B := Module.finBasis F Y
  have hs (i : Fin (Module.finrank F Y)) : -patternS edge Y p h b (B i) ∈ LinearMap.range (freeMap edge Y h) := by
    rw [range_freeMap]
    exact Submodule.neg_mem _ (pattern_feasible edge Y p h b hb (B i))
  exact B.constr F (fun i => Classical.choose (LinearMap.mem_range.mp (hs i)))

theorem getSection_spec (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h) :
    (freeMap edge Y h).comp (getSection edge Y p h b hb) = -patternS edge Y p h b := by
  classical
  let B := Module.finBasis F Y
  apply B.ext
  intro i
  simp only [getSection, B, LinearMap.comp_apply, Module.Basis.constr_basis, LinearMap.neg_apply]
  exact Classical.choose_spec (LinearMap.mem_range.mp (show
    -patternS edge Y p h b (Module.finBasis F Y i) ∈ LinearMap.range (freeMap edge Y h) by
    rw [range_freeMap]
    exact Submodule.neg_mem _ (pattern_feasible edge Y p h b hb _)))

noncomputable def encodeClosed (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h) :
    (Y × KerFree edge Y h) →ₗ[F] W l r :=
  (encode edge Y b).comp ((LinearMap.fst F Y (KerFree edge Y h)).prod
    ((getSection edge Y p h b hb).coprod (KerFree edge Y h).subtype))

theorem encodeClosed_apply (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h)
    (y : Y) (c : KerFree edge Y h) :
    encodeClosed edge Y p h b hb (y,c) = encode edge Y b (y, getSection edge Y p h b hb y + c.val) := rfl

theorem encodeClosed_inj (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h) :
    Function.Injective (encodeClosed edge Y p h b hb) := by
  rintro ⟨a,c⟩ ⟨b',d⟩ eq
  have he := encode_inj edge Y b eq
  have hfst : a = b' := congrArg Prod.fst he
  subst b'
  have hs : getSection edge Y p h b hb a + c.val = getSection edge Y p h b hb a + d.val := congrArg Prod.snd he
  exact Prod.ext (show a = a from rfl) (Subtype.ext (add_left_cancel hs))

theorem encodeClosed_synd (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h)
    (y : Y) (c : KerFree edge Y h) (a : Fin m) :
    (∑ i, p i a * (encodeClosed edge Y p h b hb (y,c)).1 i) +
      (∑ j, h j a * (encodeClosed edge Y p h b hb (y,c)).2 j) = 0 := by
  rw [← synd_sum p h, encodeClosed_apply, proj_synd, map_add]
  have he := LinearMap.congr_fun (getSection_spec edge Y p h b hb) y
  change freeMap edge Y h (getSection edge Y p h b hb y) = -patternS edge Y p h b y at he
  rw [he, LinearMap.mem_ker.mp c.property, add_zero, add_neg_cancel]
  rfl

theorem member_closed_range (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h)
    (U : Submodule F (W l r)) (hp : projects Y U) (hs : synd p h U) (hf : fits edge Y b U) :
    U ≤ LinearMap.range (encodeClosed edge Y p h b hb) := by
  rintro ⟨x,z⟩ hx
  have hx' : x ∈ Y := (hp x).mpr ⟨z,hx⟩
  let y : Y := ⟨x,hx'⟩
  let c := takeFree edge Y z
  have he : encode edge Y b (y,c) = (x,z) := encode_exists edge Y b y z (hf y z hx)
  have hk : patternS edge Y p h b y + freeMap edge Y h c = 0 := by
    rw [← proj_synd, he]
    ext a
    rw [synd_sum p h (x,z), Pi.zero_apply]
    exact hs (x,z) hx a
  have hh : freeMap edge Y h (getSection edge Y p h b hb y) = -patternS edge Y p h b y :=
    LinearMap.congr_fun (getSection_spec edge Y p h b hb) y
  let c' : KerFree edge Y h := ⟨c - getSection edge Y p h b hb y, by
    rw [LinearMap.mem_ker, map_sub, hh, add_eq_zero_iff_eq_neg'.mp hk, sub_self]⟩
  refine LinearMap.mem_range.mpr ⟨(y,c'), ?_⟩
  rw [encodeClosed_apply]
  change encode edge Y b (y, getSection edge Y p h b hb y + (c-getSection edge Y p h b hb y)) = _
  rw [add_sub_cancel, he]

end PEqualNP.Outside.L_lib_897

namespace PEqualNP.Outside.L_lib_897

section ProductCount

open Module (finrank)
open scoped BigOperators

variable {X Z : Type*} [AddCommGroup X] [Module F X] [AddCommGroup Z] [Module F Z]

def ontoFst (S : Submodule F (X × Z)) : Prop :=
  ∀ x, ∃ z, (x, z) ∈ S

def vertical (S : Submodule F (X × Z)) : Submodule F Z :=
  S.comap (LinearMap.inr F X Z)

@[simp] theorem mem_vertical (S : Submodule F (X × Z)) (z : Z) :
    z ∈ vertical S ↔ ((0 : X), z) ∈ S :=
  Iff.rfl

private def quotientSnd (K : Submodule F Z) : X × Z →ₗ[F] X × (Z ⧸ K) :=
  (LinearMap.id : X →ₗ[F] X).prodMap K.mkQ

private def pullbackGraph (K : Submodule F Z) (f : X →ₗ[F] (Z ⧸ K)) :
    Submodule F (X × Z) :=
  f.graph.comap (quotientSnd K)

private theorem mem_pullbackGraph (K : Submodule F Z) (f : X →ₗ[F] (Z ⧸ K))
    (x : X) (z : Z) : (x, z) ∈ pullbackGraph K f ↔ K.mkQ z = f x :=
  Iff.rfl

private theorem ontoFst_pullbackGraph (K : Submodule F Z) (f : X →ₗ[F] (Z ⧸ K)) :
    ontoFst (pullbackGraph K f) := by
  intro x
  obtain ⟨z, hz⟩ := K.mkQ_surjective (f x)
  exact ⟨z, (mem_pullbackGraph K f x z).mpr hz⟩

private theorem vertical_pullbackGraph (K : Submodule F Z) (f : X →ₗ[F] (Z ⧸ K)) :
    vertical (pullbackGraph K f) = K := by
  ext z
  change K.mkQ z = f 0 ↔ z ∈ K
  rw [map_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

private theorem exists_eq_pullbackGraph (S : Submodule F (X × Z)) (hS : ontoFst S) :
    ∃ f : X →ₗ[F] (Z ⧸ vertical S), S = pullbackGraph (vertical S) f := by
  let K := vertical S
  let q : X × Z →ₗ[F] X × (Z ⧸ K) := quotientSnd K
  let g := q.domRestrict S
  have hfst : Function.Surjective (Prod.fst ∘ g) := by
    intro x
    obtain ⟨z, hz⟩ := hS x
    exact ⟨⟨(x, z), hz⟩, rfl⟩

  have hline (a b : S) (h : (g a).1 = (g b).1) : (g a).2 = (g b).2 := by
    change a.val.1 = b.val.1 at h
    change K.mkQ a.val.2 = K.mkQ b.val.2
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq]
    change ((0 : X), a.val.2 - b.val.2) ∈ S
    have hab : (a.val.1 - b.val.1, a.val.2 - b.val.2) ∈ S := S.sub_mem a.property b.property
    simpa only [h, sub_self] using hab
  obtain ⟨f, hf⟩ := LinearMap.exists_range_eq_graph hfst hline
  have hmap : S.map q = f.graph := by
    simpa only [g, LinearMap.range_domRestrict] using hf

  have hker : LinearMap.ker q ≤ S := by
    rintro ⟨x, z⟩ hz
    have hq : (x, K.mkQ z) = (0 : X × (Z ⧸ K)) := LinearMap.mem_ker.mp hz
    have hx : x = 0 := congrArg Prod.fst hq
    have hz' : K.mkQ z = 0 := congrArg Prod.snd hq
    subst x
    change z ∈ K
    exact (Submodule.Quotient.mk_eq_zero K).mp hz'
  refine ⟨f, ?_⟩
  change S = f.graph.comap q
  rw [← hmap, Submodule.comap_map_eq, sup_eq_left.mpr hker]

variable [FiniteDimensional F X] [FiniteDimensional F Z]

theorem finrank_eq_add_finrank_vertical (S : Submodule F (X × Z)) (hS : ontoFst S) :
    finrank F S = finrank F X + finrank F (vertical S) := by
  let p : S →ₗ[F] X := (LinearMap.fst F X Z).domRestrict S
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨z, hz⟩ := hS x
    exact ⟨⟨(x, z), hz⟩, rfl⟩
  let i : vertical S ≃ₗ[F] LinearMap.ker p :=
    { toFun := fun z => ⟨⟨(0, (z : Z)), z.property⟩, LinearMap.mem_ker.mpr rfl⟩
      invFun := fun u => ⟨u.val.val.2, by
        change ((0 : X), u.val.val.2) ∈ S
        have hu : u.val.val.1 = 0 := LinearMap.mem_ker.mp u.property
        have hpair : ((0 : X), u.val.val.2) = u.val.val := Prod.ext hu.symm rfl
        rw [hpair]
        exact u.val.property⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := by
        intro u
        apply Subtype.ext
        apply Subtype.ext
        have hu : u.val.val.1 = 0 := LinearMap.mem_ker.mp u.property
        exact Prod.ext hu.symm rfl
      map_add' := by
        intro u v
        apply Subtype.ext
        apply Subtype.ext
        change ((0 : X), (u : Z) + (v : Z)) = (0 + 0, (u : Z) + (v : Z))
        rw [zero_add]
      map_smul' := by
        intro c z
        apply Subtype.ext
        apply Subtype.ext
        change ((0 : X), c • (z : Z)) = (c • (0 : X), c • (z : Z))
        rw [smul_zero] }
  have h := p.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, ← i.finrank_eq] at h
  exact h.symm

noncomputable def ontoFstEquiv (d : ℕ) (hd : finrank F X ≤ d) :
    {S : Submodule F (X × Z) // finrank F S = d ∧ ontoFst S} ≃
      (Σ K : {K : Submodule F Z // finrank F K = d - finrank F X},
        X →ₗ[F] (Z ⧸ K.val)) := by
  let mk : (Σ K : {K : Submodule F Z // finrank F K = d - finrank F X},
      X →ₗ[F] (Z ⧸ K.val)) → {S : Submodule F (X × Z) // finrank F S = d ∧ ontoFst S} :=
    fun ⟨K, f⟩ => ⟨pullbackGraph K.val f, ⟨by
      rw [finrank_eq_add_finrank_vertical _ (ontoFst_pullbackGraph K.val f),
        vertical_pullbackGraph, K.property]
      omega, ontoFst_pullbackGraph K.val f⟩⟩
  refine (Equiv.ofBijective mk ⟨?_, ?_⟩).symm
  · rintro ⟨K, f⟩ ⟨J, g⟩ h
    have hS := congrArg Subtype.val h
    change pullbackGraph K.val f = pullbackGraph J.val g at hS
    have hK : K = J := by
      apply Subtype.ext
      rw [← vertical_pullbackGraph K.val f, hS, vertical_pullbackGraph]
    subst J
    have hfg : f = g := by
      apply LinearMap.ext
      intro x
      obtain ⟨z, hz⟩ := K.val.mkQ_surjective (f x)
      have hmem : (x, z) ∈ pullbackGraph K.val f := (mem_pullbackGraph K.val f x z).mpr hz
      rw [hS] at hmem
      exact hz.symm.trans ((mem_pullbackGraph K.val g x z).mp hmem)
    subst g
    rfl
  · intro S
    have hK : finrank F (vertical S.val) = d - finrank F X := by
      have h := finrank_eq_add_finrank_vertical S.val S.property.2
      rw [S.property.1] at h
      omega
    obtain ⟨f, hf⟩ := exists_eq_pullbackGraph S.val S.property.2
    exact ⟨⟨⟨vertical S.val, hK⟩, f⟩, Subtype.ext hf.symm⟩

private theorem card_rank_submodules (n : ℕ) :
    Nat.card {K : Submodule F Z // finrank F K = n} =
      Nat.card {K : Submodule F (Fin (finrank F Z) → F) // finrank F K = n} := by
  let i : Z ≃ₗ[F] (Fin (finrank F Z) → F) :=
    LinearEquiv.ofFinrankEq _ _ (Module.finrank_fin_fun F).symm
  let b := (Submodule.orderIsoMapComap i).toEquiv
  apply Nat.card_congr (b.subtypeEquiv ?_)
  intro K
  change finrank F K = n ↔ finrank F (K.map i.toLinearMap) = n
  rw [i.finrank_map_eq K]

theorem card_ontoFst (d : ℕ) :
    let e := finrank F X
    let k := finrank F Z
    Nat.card {S : Submodule F (X × Z) // finrank F S = d ∧ ontoFst S} =
      if e ≤ d ∧ d ≤ e + k then
        Nat.card {K : Submodule F (Fin k → F) // finrank F K = d - e} *
          2 ^ (e * (k - (d - e)))
      else 0 := by
  classical
  dsimp only
  by_cases hd : finrank F X ≤ d ∧ d ≤ finrank F X + finrank F Z
  · rw [if_pos hd, Nat.card_congr (ontoFstEquiv d hd.1)]
    let A := {K : Submodule F Z // finrank F K = d - finrank F X}
    letI : Finite Z := Module.finite_of_finite F
    letI : Fintype A := Fintype.ofFinite A
    letI : ∀ K : A, Finite (X →ₗ[F] (Z ⧸ K.val)) := fun _ => Module.finite_of_finite F
    have hfiber (K : A) : Nat.card (X →ₗ[F] (Z ⧸ K.val)) =
        2 ^ (finrank F X * (finrank F Z - (d - finrank F X))) := by
      have hsum := K.val.finrank_quotient_add_finrank
      have hK := K.property
      have hq : finrank F (Z ⧸ K.val) = finrank F Z - (d - finrank F X) := by omega
      rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_zmod, Module.finrank_linearMap, hq]
    change Nat.card (Σ K : A, X →ₗ[F] (Z ⧸ K.val)) = _
    rw [Nat.card_sigma]
    simp only [hfiber, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card, card_rank_submodules (Z := Z)]
  · rw [if_neg hd]
    letI : IsEmpty {S : Submodule F (X × Z) // finrank F S = d ∧ ontoFst S} := ⟨fun S => by
      have h := finrank_eq_add_finrank_vertical S.val S.property.2
      have hK := (vertical S.val).finrank_le
      rw [S.property.1] at h
      exact hd ⟨by omega, by omega⟩⟩
    exact Nat.card_of_isEmpty

end ProductCount

end PEqualNP.Outside.L_lib_897

namespace PEqualNP.Outside.L_lib_897
open scoped BigOperators

variable {l r m : ℕ} (edge : Fin l → Fin r → Prop) (Y : Submodule F (V l))
variable (p : Fin l → V m) (h : Fin r → V m)

private theorem fits_iso (b : Bits edge Y) {U : Submodule F (W l r)} (hp : projects Y U)
    (hf : fits edge Y b U) : iso edge U := by
  rintro ⟨x,z⟩ hx ⟨y,w⟩ hy i j hij
  let xY : Y := ⟨x, (hp x).mpr ⟨z,hx⟩⟩
  let yY : Y := ⟨y, (hp y).mpr ⟨w,hy⟩⟩
  change ev Y i xY * w j = ev Y i yY * z j
  by_cases he : ev Y i = 0
  · simp [he]
  · have hi : i ∈ neigh edge Y j := (mem_iso_neigh edge Y).mpr ⟨hij,he⟩
    have hj : j ∉ free edge Y := fun hh =>
      Finset.ne_empty_of_mem hi ((mem_iso_free edge Y).mp hh)
    rw [hf xY z hx j hj, hf yY w hy j hj]
    by_cases ht : j ∈ tied edge Y
    · simp only [fixedPart, dite_eq_left ht, tether_eq_ev edge Y ht hi]
      ac_rfl
    · simp only [fixedPart, dite_eq_right ht, mul_zero]

private theorem encodeClosed_fst (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h)
    (x : Y × KerFree edge Y h) : (encodeClosed edge Y p h b hb x).1 = x.1.val := rfl

private theorem mapped_projects (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h)
    (S : Submodule F (Y × KerFree edge Y h)) (hs : ontoFst S) :
    projects Y (S.map (encodeClosed edge Y p h b hb)) := by
  intro x
  constructor
  · intro hx
    obtain ⟨c,hc⟩ := hs ⟨x,hx⟩
    let v := encodeClosed edge Y p h b hb (⟨x,hx⟩,c)
    refine ⟨v.2, Submodule.mem_map.mpr ⟨_,hc,?_⟩⟩
    exact Prod.ext (encodeClosed_fst edge Y p h b hb _) rfl
  · rintro ⟨z,hz⟩
    obtain ⟨a,_,ha⟩ := Submodule.mem_map.mp hz
    have eq : a.1.val = x := congrArg Prod.fst ha
    exact eq ▸ a.1.property

private theorem mapped_fits (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h)
    (S : Submodule F (Y × KerFree edge Y h)) : fits edge Y b (S.map (encodeClosed edge Y p h b hb)) := by
  intro y z hz j hj
  obtain ⟨⟨a,c⟩,_,hc⟩ := Submodule.mem_map.mp hz
  have he : a = y := Subtype.ext (congrArg Prod.fst hc)
  subst a
  have eq := congrArg Prod.snd hc
  rw [encodeClosed_apply, encode_apply] at eq
  change fixedL edge Y b y + fill edge Y (getSection edge Y p h b hb y + c.val) = z at eq
  change z j = fixedPart edge Y b y j
  rw [← eq, Pi.add_apply, fill_off edge Y _ j hj, add_zero, fixedL_apply]

private theorem mapped_synd (b : Bits edge Y) (hb : betaMap edge Y h b = offset edge Y p h)
    (S : Submodule F (Y × KerFree edge Y h)) : synd p h (S.map (encodeClosed edge Y p h b hb)) := by
  intro y hy a
  obtain ⟨⟨x,c⟩,_,rfl⟩ := Submodule.mem_map.mp hy
  exact encodeClosed_synd edge Y p h b hb x c a

def Good (d : ℕ) (U : Submodule F (W l r)) : Prop :=
  Module.finrank F U = d ∧ projects Y U ∧ synd p h U ∧ iso edge U

private noncomputable def assembleEquiv (d : ℕ) :
    ({b : Bits edge Y // betaMap edge Y h b = offset edge Y p h} ×
      {S : Submodule F (Y × KerFree edge Y h) // Module.finrank F S = d ∧ ontoFst S}) ≃
    {U : Submodule F (W l r) // Good edge Y p h d U} := by
  classical
  let A := {b : Bits edge Y // betaMap edge Y h b = offset edge Y p h}
  let B := {S : Submodule F (Y × KerFree edge Y h) // Module.finrank F S = d ∧ ontoFst S}
  let embedSub (x : A × B) : {U : Submodule F (W l r) // Good edge Y p h d U} := by
    let f := encodeClosed edge Y p h x.1.val x.1.property
    let U := x.2.val.map f
    have hp : projects Y U := mapped_projects edge Y p h _ _ _ x.2.property.2
    have hf : fits edge Y x.1.val U := mapped_fits edge Y p h _ _ _
    have hs : synd p h U := mapped_synd edge Y p h _ _ _
    have hd : Module.finrank F U = d := ((Submodule.equivMapOfInjective f
      (encodeClosed_inj edge Y p h _ _) x.2.val).finrank_eq.symm).trans x.2.property.1
    exact ⟨U,hd,hp,hs,fits_iso edge Y _ hp hf⟩
  refine Equiv.ofBijective embedSub ⟨?_,?_⟩
  · rintro ⟨b,S⟩ ⟨c,R⟩ eq
    let f := encodeClosed edge Y p h b.val b.property
    let g := encodeClosed edge Y p h c.val c.property
    have hEq : S.val.map f = R.val.map g := congrArg Subtype.val eq
    have hb : fits edge Y b.val (S.val.map f) := mapped_fits edge Y p h _ _ _
    have hc : fits edge Y c.val (S.val.map f) := hEq.symm ▸ mapped_fits edge Y p h c.val c.property R.val
    have hp := mapped_projects edge Y p h b.val b.property S.val S.property.2
    obtain ⟨b',_,hun⟩ := (iso_iff_unique_fits edge Y (S.val.map f) hp).mp
      (fits_iso edge Y _ hp hb)
    have hbc : b = c := Subtype.ext ((hun b.val hb).trans (hun c.val hc).symm)
    subst c
    change S.val.map f = R.val.map f at hEq
    have hSR : (S.val.map f).comap f = (R.val.map f).comap f :=
      congrArg (Submodule.comap f) hEq
    have hinj : Function.Injective f := encodeClosed_inj edge Y p h b.val b.property
    rw [Submodule.comap_map_eq_of_injective hinj, Submodule.comap_map_eq_of_injective hinj] at hSR
    exact Prod.ext (show b = b from rfl) (Subtype.ext hSR)
  · intro U
    obtain ⟨hd,hp,hs,hi⟩ := U.property
    obtain ⟨b,hf,_⟩ := (iso_iff_unique_fits edge Y U.val hp).mp hi
    let hb := fits_feasible edge Y p h b U.val hp hs hf
    let f := encodeClosed edge Y p h b hb
    let S := U.val.comap f
    have hRange := member_closed_range edge Y p h b hb U.val hp hs hf
    have hMap : S.map f = U.val := by
      ext x
      rw [Submodule.mem_map]
      exact ⟨by rintro ⟨y,hy,rfl⟩; exact hy, by
        intro hx
        obtain ⟨y,hy⟩ := LinearMap.mem_range.mp (hRange hx)
        exact ⟨y, by change f y ∈ U.val; rwa [hy], hy⟩⟩
    have hOnto : ontoFst S := by
      intro y
      obtain ⟨z,hz⟩ := (hp y.val).mp y.property
      obtain ⟨⟨x,c⟩,he⟩ := LinearMap.mem_range.mp (hRange hz)
      have hh : x = y := Subtype.ext (congrArg Prod.fst he)
      subst x
      exact ⟨c, by change f (y,c) ∈ U.val; rwa [he]⟩
    have hdim : Module.finrank F S = d := by
      rw [(Submodule.equivMapOfInjective f (encodeClosed_inj edge Y p h b hb) S).finrank_eq, hMap]
      exact hd
    exact ⟨(⟨b,hb⟩,⟨S,hdim,hOnto⟩), Subtype.ext hMap⟩

open scoped Classical in
theorem card_good (d : ℕ) :
    let e := Module.finrank F Y
    let k := (free edge Y).card - Module.finrank F (D edge Y h)
    Nat.card {U : Submodule F (W l r) // Good edge Y p h d U} =
      if e ≤ d ∧ d ≤ e+k ∧ offset edge Y p h ∈ T edge Y h then
        2^((tied edge Y).card - Module.finrank F (T edge Y h)) *
          Nat.card {K : Submodule F (Fin k → F) // Module.finrank F K = d-e} *
          2^(e*(k-(d-e)))
      else 0 := by
  classical
  dsimp only
  rw [← Nat.card_congr (assembleEquiv edge Y p h d), Nat.card_prod,
    count_beta edge Y p h, card_ontoFst, rank_freeKer]
  by_cases hT : offset edge Y p h ∈ T edge Y h <;>
    by_cases hl : Module.finrank F Y ≤ d <;>
      by_cases hh : d ≤ Module.finrank F Y + ((free edge Y).card - Module.finrank F (D edge Y h)) <;>
        simp [hl,hh,hT, Nat.mul_assoc]

theorem filterClassical {α : Type*} (s : Finset α) (p : α → Prop) [a : DecidablePred p] :
    s.filter p = @Finset.filter α p (fun x => Classical.propDecidable (p x)) s := by
  have e : a = (fun x => Classical.propDecidable (p x)) := Subsingleton.elim _ _
  cases e
  rfl

theorem imageClassical {α β : Type*} (s : Finset α) (f : α → β) [a : DecidableEq β] :
    s.image f = @Finset.image α β (fun x y => Classical.propDecidable (x = y)) f s := by
  have e : a = (fun x y => Classical.propDecidable (x = y)) := Subsingleton.elim _ _
  cases e
  rfl

theorem iteClassical {α : Type*} (p : Prop) (x y : α) [a : Decidable p] :
    (if p then x else y) = @ite α p (Classical.propDecidable p) x y := by
  have e : a = Classical.propDecidable p := Subsingleton.elim _ _
  cases e
  rfl

end PEqualNP.Outside.L_lib_897

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.L_lib_897 : (∀ (l r m d : ℕ) (edge : Fin l → Fin r → Prop)
  (p : Fin l → Fin m → ZMod 2) (h : Fin r → Fin m → ZMod 2)
  (Y : Submodule (ZMod 2) (Fin l → ZMod 2)),
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  let W := (Fin l → F) × (Fin r → F)
  letI : Fintype (Submodule F W) := Fintype.ofFinite _
  let ev := fun (i : Fin l) (y : Y) => y.val i
  let neigh := fun j : Fin r =>
    Finset.univ.filter (fun i : Fin l => edge i j ∧ ev i ≠ 0)
  let free := Finset.univ.filter (fun j : Fin r => (neigh j).card = 0)
  let tied := Finset.univ.filter (fun j : Fin r => ((neigh j).image ev).card = 1)
  let D := Submodule.span F (↑(free.image h) : Set A)
  let v := fun (j : Fin r) (y : Y) =>
    (∑ g ∈ (neigh j).image ev, g y) • D.mkQ (h j)
  let T := Submodule.span F (↑(tied.image v) : Set (Y → (A ⧸ D)))
  let offset := fun y : Y => D.mkQ (∑ i, ev i y • p i)
  let e := Module.finrank F Y
  let k := free.card - Module.finrank F D
  let good := fun U : Submodule F W =>
    Module.finrank F U = d ∧
    (∀ x : Fin l → F, x ∈ Y ↔ ∃ z : Fin r → F, (x,z) ∈ U) ∧
    (∀ x ∈ U, ∀ b : Fin m, (∑ i, p i b * x.1 i) + (∑ j, h j b * x.2 j) = 0) ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ i j, edge i j → x.1 i * y.2 j = y.1 i * x.2 j)
  (Finset.univ.filter good).card =
    if e ≤ d ∧ d ≤ e+k ∧ offset ∈ T then
      2^(tied.card - Module.finrank F T) *
        Nat.card {K : Submodule F (Fin k → F) // Module.finrank F K = d-e} *
        2^(e*(k-(d-e)))
    else 0) := by
  intro l r m d edge p h Y FF AA WW eV N Fr Ti DD vv TT Off ee kk gd
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  letI : Fintype (Submodule FF WW) := Fintype.ofFinite _
  change (Finset.univ.filter (L_lib_897.Good edge Y p h d)).card = _
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  let a (j : Fin r) (y : Y) : FF := ∑ g ∈ (N j).image eV, g y
  let result (nf : ℕ) (ts : Finset (Fin r)) (b : Fin r → Y → FF)
      (Q : Submodule FF AA) : ℕ :=
    let S := Submodule.span FF (↑(ts.image (fun j (y : Y) => b j y • Q.mkQ (h j))) : Set (Y → AA ⧸ Q))
    let o := fun y : Y => Q.mkQ (∑ i, eV i y • p i)
    let k := nf - Module.finrank FF Q
    if ee ≤ d ∧ d ≤ ee+k ∧ o ∈ S then
      2^(ts.card - Module.finrank FF S) *
        Nat.card {K : Submodule FF (Fin k → FF) // Module.finrank FF K = d-ee} *
        2^(ee*(k-(d-ee)))
    else 0
  change _ = result Fr.card Ti a DD
  have hn : N = L_lib_897.neigh edge Y := by
    funext j
    ext i
    simp only [N, L_lib_897.neigh, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hf : Fr = L_lib_897.free edge Y := by
    ext j
    simp [Fr, hn, L_lib_897.free]
  have ha : a = L_lib_897.tether edge Y := by
    funext j y
    unfold a L_lib_897.tether
    simp only [hn, L_lib_897.imageClassical]
    rfl
  have ht : Ti = L_lib_897.tied edge Y := by
    ext j
    simp only [Ti, L_lib_897.tied, Finset.mem_filter, Finset.mem_univ, true_and, hn,
      L_lib_897.imageClassical]
    rfl
  have hD : DD = L_lib_897.D edge Y h := by
    simp only [DD, L_lib_897.D, hf, L_lib_897.imageClassical]
    rfl
  rw [hf, ht, ha, hD]
  have hc := L_lib_897.card_good edge Y p h d
  dsimp only at hc
  let Q := L_lib_897.D edge Y h
  let S' : Submodule FF (Y → AA ⧸ Q) :=
    Submodule.span FF (↑((L_lib_897.tied edge Y).image
      (fun j (y : Y) => L_lib_897.tether edge Y j y • Q.mkQ (h j))) : Set (Y → AA ⧸ Q))
  let o' : Y → AA ⧸ Q := fun y => Q.mkQ (∑ i, eV i y • p i)
  have heq : S' = L_lib_897.T edge Y h := by
    unfold S' L_lib_897.T
    simp only [L_lib_897.imageClassical]
    rfl
  have hoff : o' = L_lib_897.offset edge Y p h := rfl
  let k₀ := (L_lib_897.free edge Y).card - Module.finrank FF Q
  change _ = if ee ≤ d ∧ d ≤ ee + k₀ ∧ o' ∈ S' then
      2 ^ ((L_lib_897.tied edge Y).card - Module.finrank FF S') *
        Nat.card {K : Submodule FF (Fin k₀ → FF) // Module.finrank FF K = d-ee} *
        2^(ee*(k₀-(d-ee)))
    else 0
  rw [hoff, heq]
  by_cases hp : ee ≤ d ∧ d ≤ ee + k₀ ∧ L_lib_897.offset edge Y p h ∈ L_lib_897.T edge Y h
  · rw [ite_eq_left hp] at hc ⊢
    exact hc
  · rw [ite_eq_right hp] at hc ⊢
    exact hc
