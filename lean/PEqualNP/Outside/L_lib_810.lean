import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_810

abbrev F := ZMod 2
abbrev W (k : ℕ) := Fin k → F
abbrev A (k : ℕ) := W k × F

def lift {k : ℕ} (x : W k) : A k := (x, 1)

def hull {k : ℕ} (D : Finset (W k)) : Submodule F (A k) :=
  Submodule.span F (lift '' (D : Set (W k)))

lemma small {k : ℕ} (D : Finset (W k)) :
    ∃ E : Finset (W k), E ⊆ D ∧ E.card ≤ k + 1 ∧ hull E = hull D := by
  classical
  obtain ⟨t, ht, hcard, hspan, hind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn F (lift '' (D : Set (W k)))
  let E := t.image Prod.fst
  have htform : ∀ z ∈ t, z = lift z.1 := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := ht hz
    subst z
    rfl
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y, hy, hzy⟩ := ht hz
    subst z
    exact hy
  · calc
      E.card ≤ t.card := Finset.card_image_le
      _ = Module.finrank F (hull D) := hcard
      _ ≤ Module.finrank F (A k) := Submodule.finrank_le _
      _ = k + 1 := by simp [A, W, F, Module.finrank_prod, Module.finrank_pi]
  · unfold hull
    rw [← hspan]
    congr 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (htform y hy).symm ▸ hy
    · intro hz
      exact ⟨z.1, Finset.mem_image.mpr ⟨z, hz, rfl⟩, (htform z hz).symm⟩

def pol {k : ℕ} (Q : W k → W k) (x y : W k) := Q (x+y) + Q x + Q y + Q 0

lemma pol_symm {k : ℕ} (Q : W k → W k) (x y : W k) :
    pol Q x y = pol Q y x := by
  simp only [pol, add_comm x y]
  abel

lemma pol_zero {k : ℕ} (Q : W k → W k) (x : W k) : pol Q 0 x = 0 := by
  simp only [pol, zero_add]
  rw [show Q x + Q 0 + Q x + Q 0 = (Q x + Q x) + (Q 0 + Q 0) by abel]
  ext i
  simp [CharTwo.add_self_eq_zero]

lemma pol_add_right {k : ℕ} (Q : W k → W k)
    (h : ∀ u v w, pol Q (u+v) w = pol Q u w + pol Q v w) (x y z : W k) :
    pol Q x (y+z) = pol Q x y + pol Q x z := by
  rw [pol_symm Q x, h, pol_symm Q y, pol_symm Q z]

lemma sum_units {k : ℕ} (x : W k) :
    ∑ i : Fin k, x i • (fun j : Fin k => if j=i then (1 : F) else 0) = x := by
  ext j
  simp

lemma pol_mem {k : ℕ} (Q : W k → W k)
    (h : ∀ u v w, pol Q (u+v) w = pol Q u w + pol Q v w)
    (H : Submodule F (A k)) (d : W k)
    (hu : ∀ i : Fin k, (pol Q (fun j => if j=i then 1 else 0) d, 0) ∈ H) :
    ∀ x, (pol Q x d, 0) ∈ H := by
  intro x
  let f : W k →ₗ[F] A k := {
    toFun := fun x => (pol Q x d, 0)
    map_add' := by intro x y; ext <;> simp [h]
    map_smul' := by
      intro c x
      fin_cases c
      · change (pol Q ((0 : F) • x) d, 0) = (0 : F) • (pol Q x d, 0)
        simp only [zero_smul, pol_zero]
        rfl
      · change (pol Q ((1 : F) • x) d, 0) = (1 : F) • (pol Q x d, 0)
        simp only [one_smul] }
  rw [← sum_units x]
  change f _ ∈ H
  rw [map_sum]
  exact H.sum_mem fun i _ => by
    rw [map_smul]
    exact H.smul_mem _ (hu i)

def step {k : ℕ} (Q : W k → W k) (c : W k) (D X : Finset (W k)) :=
  (D.product X).image (fun p => Q (p.2+p.1) + Q p.2 + c)

def base (k : ℕ) : Finset (W k) :=
  insert 0 (Finset.univ.image (fun i : Fin k => fun j : Fin k => if j=i then 1 else 0))

lemma transition {k : ℕ} (Q : W k → W k) (c : W k)
    (h : ∀ u v w, pol Q (u+v) w = pol Q u w + pol Q v w)
    (D E : Finset (W k))
    (he : ∀ d ∈ E, lift d ∈ hull D) :
    hull (step Q c E Finset.univ) ≤ hull (step Q c D (base k)) := by
  classical
  let H := hull (step Q c D (base k))
  have h2 : (2 : F) = 0 := by decide
  have h3 : (3 : F) = 1 := by decide
  have hs : ∀ d ∈ D, ∀ x ∈ base k, lift (Q (x+d)+Q x+c) ∈ H := by
    intro d hd x hx
    apply Submodule.subset_span
    exact ⟨_, Finset.mem_image.mpr ⟨(d,x), Finset.mem_product.mpr ⟨hd,hx⟩, rfl⟩, rfl⟩
  have hz : ∀ d ∈ D, lift (Q d+Q 0+c) ∈ H := by
    intro d hd
    simpa using hs d hd 0 (Finset.mem_insert_self _ _)
  have hp : ∀ d ∈ D, ∀ x, (pol Q x d, 0) ∈ H := by
    intro d hd
    apply pol_mem Q h H d
    intro i
    have hi := hs d hd (fun j => if j=i then 1 else 0)
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    have hh := H.add_mem hi (hz d hd)
    convert hh using 1 <;> ext j <;> simp [lift, pol, Pi.add_apply] <;> ring_nf <;> simp only [h2, h3, mul_zero, mul_one, add_zero]
  have hzero : (Q 0 + Q 0 : W k) = 0 := by
    ext i
    exact CharTwo.add_self_eq_zero _
  have hall : ∀ z ∈ hull D,
      (∀ x, (pol Q x z.1, 0) ∈ H) ∧
      (Q z.1 + Q 0 + z.2 • c, z.2) ∈ H := by
    intro z hzmem
    induction hzmem using Submodule.span_induction with
    | mem z hzmem =>
      obtain ⟨d, hd, rfl⟩ := hzmem
      exact ⟨hp d hd, by simpa [lift] using hz d hd⟩
    | zero =>
      constructor
      · intro x
        simp only [Prod.fst_zero, pol_symm Q x 0, pol_zero]
        exact H.zero_mem
      · simp only [Prod.fst_zero, Prod.snd_zero, zero_smul, add_zero, hzero]
        exact H.zero_mem
    | add u v hu hv ihu ihv =>
      constructor
      · intro x
        simpa [pol_add_right Q h, Prod.mk_add_mk] using H.add_mem (ihu.1 x) (ihv.1 x)
      · have hh := H.add_mem (H.add_mem ihu.2 ihv.2) (ihv.1 u.1)
        convert hh using 1 <;> ext i <;>
          simp [pol, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul] <;> ring_nf <;> simp only [h2, h3, mul_zero, mul_one, add_zero]
    | smul a z hzmem ih =>
      fin_cases a
      · change (∀ x, (pol Q x ((0 : F) • z).1, 0) ∈ H) ∧
          (Q ((0 : F) • z).1 + Q 0 + ((0 : F) • z).2 • c, ((0 : F) • z).2) ∈ H
        simp only [zero_smul, Prod.fst_zero, Prod.snd_zero, add_zero, hzero]
        constructor
        · intro x
          simp only [pol_symm Q x 0, pol_zero]
          exact H.zero_mem
        · exact H.zero_mem
      · change (∀ x, (pol Q x ((1 : F) • z).1, 0) ∈ H) ∧
          (Q ((1 : F) • z).1 + Q 0 + ((1 : F) • z).2 • c, ((1 : F) • z).2) ∈ H
        simpa only [one_smul] using ih
  apply Submodule.span_le.mpr
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨⟨d,x⟩, hdx, rfl⟩ := Finset.mem_image.mp hy
  have hd := (Finset.mem_product.mp hdx).1
  obtain ⟨hpol, hquad⟩ := hall (lift d) (he d hd)
  have hh := H.add_mem hquad (hpol x)
  change lift (Q (x+d)+Q x+c) ∈ H
  convert hh using 1 <;> ext i <;> simp [lift, pol, Pi.add_apply] <;> ring_nf <;> simp only [h2, h3, mul_zero, mul_one, add_zero]

noncomputable def shrink {k : ℕ} (D : Finset (W k)) : Finset (W k) :=
  Classical.choose (small D)

lemma shrink_spec {k : ℕ} (D : Finset (W k)) :
    shrink D ⊆ D ∧ (shrink D).card ≤ k+1 ∧ hull (shrink D) = hull D :=
  Classical.choose_spec (small D)

lemma step_mono {k : ℕ} (Q : W k → W k) (c : W k)
    {D E X Y : Finset (W k)} (h : D ⊆ E) (hx : X ⊆ Y) :
    step Q c D X ⊆ step Q c E Y :=
  Finset.image_subset_image (Finset.product_subset_product h hx)

lemma walk {k : ℕ} {J : Type} (Q : J → W k → W k) (c : J → W k)
    (h : ∀ j u v w, pol (Q j) (u+v) w = pol (Q j) u w + pol (Q j) v w)
    (initial : W k) (l : List J) :
    let D := l.foldl (fun D j => shrink (step (Q j) (c j) D (base k))) {initial}
    let E := l.foldl (fun E j => step (Q j) (c j) E Finset.univ) {initial}
    D.card ≤ k+1 ∧ D ⊆ E ∧ hull E ≤ hull D := by
  classical
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l j ih =>
    dsimp only at ih ⊢
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hcard, hsub, hspan⟩ := ih
    obtain ⟨hs, hc, hh⟩ := shrink_spec
      (step (Q j) (c j) (l.foldl (fun D j => shrink (step (Q j) (c j) D (base k))) {initial}) (base k))
    refine ⟨hc, hs.trans (step_mono _ _ hsub (Finset.subset_univ _)), ?_⟩
    rw [hh]
    apply transition _ _ (h j)
    intro d hd
    exact hspan (Submodule.subset_span ⟨d, hd, rfl⟩)

lemma equations {k : ℕ} (D E : Finset (W k)) (hsub : D ⊆ E)
    (hspan : hull E ≤ hull D) (a : W k) (b : F) :
    (∀ x ∈ D, (∑ i, a i*x i) = b) ↔ (∀ x ∈ E, (∑ i, a i*x i) = b) := by
  classical
  constructor
  · intro hd
    let f : A k →ₗ[F] F := {
      toFun := fun z => (∑ i, a i * z.1 i) - b * z.2
      map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]; ring
      map_smul' := by
        intro t x
        simp [smul_eq_mul, Finset.mul_sum, mul_sub, mul_assoc, mul_left_comm] }
    have hker : hull D ≤ LinearMap.ker f := by
      apply Submodule.span_le.mpr
      rintro z ⟨x, hx, rfl⟩
      change (∑ i, a i*x i) - b*1 = 0
      rw [hd x hx]
      ring
    intro x hx
    have hm := hker (hspan (Submodule.subset_span ⟨x,hx,rfl⟩))
    change (∑ i, a i*x i) - b*1 = 0 at hm
    simpa only [mul_one, sub_eq_zero] using hm
  · intro he x hx
    exact he x (hsub hx)

end PEqualNP.Outside.L_lib_810

theorem PEqualNP.Outside.L_lib_810 : (∀ (k r : ℕ),
  let W := Fin k → ZMod 2
  ∀ (Q : Fin r → W → W) (kick : Fin r → W) (initial : W),
    let polar := fun (j : Fin r) (u v : W) => Q j (u+v) + Q j u + Q j v + Q j 0
    (∀ (j : Fin r) (u v w : W), polar j (u+v) w = polar j u w + polar j v w) →
    let unit := fun (pivot i : Fin k) => if i=pivot then (1 : ZMod 2) else 0
    let base : Finset W := insert (0 : W) (Finset.univ.image unit)
    let step := fun (j : Fin r) (D X : Finset W) => (D.product X).image
      (fun p => Q j (p.2+p.1) + Q j p.2 + kick j)
    let reached := fun n : ℕ => ((List.finRange r).take n).foldl
      (fun S j => step j S Finset.univ) {initial}
    let dot := fun (a x : W) => ∑ i : Fin k, a i * x i
    ∃ keep : ℕ → Finset W, keep 0 = {initial} ∧
      (∀ j : Fin r, keep (j.val+1) ⊆ step j (keep j.val) base) ∧
      ∀ n ≤ r, (keep n).card ≤ k+1 ∧ keep n ⊆ reached n ∧
        ∀ (a : W) (b : ZMod 2),
          (∀ x ∈ keep n, dot a x = b) ↔ (∀ x ∈ reached n, dot a x = b)) := by
  classical
  dsimp only
  intro k r Q kick initial h
  change ∀ j u v w,
    PEqualNP.Outside.L_lib_810.pol (Q j) (u+v) w =
    PEqualNP.Outside.L_lib_810.pol (Q j) u w +
    PEqualNP.Outside.L_lib_810.pol (Q j) v w at h
  let K := fun l : List (Fin r) => l.foldl
    (fun D j => PEqualNP.Outside.L_lib_810.shrink
      (PEqualNP.Outside.L_lib_810.step (Q j) (kick j) D
        (PEqualNP.Outside.L_lib_810.base k))) {initial}
  refine ⟨fun n => K ((List.finRange r).take n), ?_, ?_, ?_⟩
  · rfl
  · intro j
    change K ((List.finRange r).take (j.val+1)) ⊆
      PEqualNP.Outside.L_lib_810.step (Q j) (kick j)
        (K ((List.finRange r).take j.val)) (PEqualNP.Outside.L_lib_810.base k)
    rw [← List.take_concat_get' (List.finRange r) j.val (by simpa using j.isLt)]
    simpa [K] using (PEqualNP.Outside.L_lib_810.shrink_spec
      (PEqualNP.Outside.L_lib_810.step (Q j) (kick j)
        (K ((List.finRange r).take j.val)) (PEqualNP.Outside.L_lib_810.base k))).1
  · intro n hn
    obtain ⟨hc, hs, hh⟩ := PEqualNP.Outside.L_lib_810.walk Q kick h initial
      ((List.finRange r).take n)
    exact ⟨hc, hs, fun a b => PEqualNP.Outside.L_lib_810.equations _ _ hs hh a b⟩
