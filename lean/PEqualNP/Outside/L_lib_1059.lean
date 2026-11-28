import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_1059

namespace Systematic1059

open scoped Classical

abbrev F := ZMod 2
abbrev W (n : ℕ) := Fin n → F

def join {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n) (a : W j) (b : W r) : W n :=
  fun i => Sum.elim a b (p.symm i)

@[simp] theorem join_left {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n) (a : W j) (b : W r)
    (i : Fin j) : join p a b (p (.inl i)) = a i := by simp [join]

@[simp] theorem join_right {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n) (a : W j) (b : W r)
    (i : Fin r) : join p a b (p (.inr i)) = b i := by simp [join]

private theorem coord_basis {n : ℕ} (C : Submodule F (W n)) :
    ∃ e : Fin (Module.finrank F C) ↪ Fin n,
      Function.Injective (fun (x : C) (i : Fin (Module.finrank F C)) => x.val (e i)) := by
  classical
  let f (i : Fin n) : Module.Dual F C := (LinearMap.proj i).comp C.subtype
  obtain ⟨I,idx,hi,hspan,hind⟩ := exists_linearIndependent' (K := F) f
  let _ : Fintype I := Fintype.ofInjective idx hi
  let P : C →ₗ[F] (I → F) :=
    { toFun := fun x i => f (idx i) x
      map_add' := by intro x y; funext i; exact map_add (f (idx i)) x y
      map_smul' := by intro a x; funext i; exact map_smul (f (idx i)) a x }
  have hinj : Function.Injective P := by
    intro x y hxy
    apply Subtype.ext
    funext k
    have hk : f k ∈ Submodule.span F (Set.range (f ∘ idx)) :=
      hspan.symm ▸ Submodule.subset_span ⟨k,rfl⟩
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hk
    have value (z : C) : f k z = ∑ i, c i * f (idx i) z := by
      have hz := congrArg (fun v : Module.Dual F C => v z) hc.symm
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Function.comp_apply]
        using hz
    change f k x = f k y
    rw [value x, value y]
    exact Finset.sum_congr rfl (fun i _ => congrArg (c i * ·) (congrFun hxy i))
  have hl : Module.finrank F C ≤ Fintype.card I := by
    simpa only [Module.finrank_pi] using LinearMap.finrank_le_finrank_of_injective hinj
  have hr : Fintype.card I ≤ Module.finrank F C := by
    simpa only [Subspace.dual_finrank_eq] using hind.fintype_card_le_finrank
  let e : Fin (Module.finrank F C) ≃ I :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin]; omega)
  refine ⟨⟨idx ∘ e,hi.comp e.injective⟩,?_⟩
  intro x y hxy
  apply hinj
  funext i
  have h := congrFun hxy (e.symm i)
  change x.val (idx (e (e.symm i))) = y.val (idx (e (e.symm i))) at h
  rw [e.apply_symm_apply] at h
  exact h

theorem systematic {n : ℕ} (C : Submodule F (W n)) :
    ∃ (r : ℕ) (perm : Fin (Module.finrank F C) ⊕ Fin r ≃ Fin n)
      (L : W (Module.finrank F C) →ₗ[F] W r),
      ∀ x, x ∈ C ↔ ∀ k, x (perm (.inr k)) = L (fun i => x (perm (.inl i))) k := by
  classical
  let j := Module.finrank F C
  obtain ⟨e,he⟩ := coord_basis C
  let r := Fintype.card {i : Fin n // i ∉ Set.range e}
  let R : Fin r ≃ {i : Fin n // i ∉ Set.range e} := (Fintype.equivFin _).symm
  let perm : Fin j ⊕ Fin r ≃ Fin n :=
    (Equiv.sumCongr (Equiv.ofInjective e e.injective) R).trans (Equiv.sumCompl (· ∈ Set.range e))
  have hleft (i : Fin j) : perm (.inl i) = e i := rfl
  let P : C →ₗ[F] W j :=
    { toFun := fun x i => x.val (perm (.inl i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective P := by
    simpa only [P, LinearMap.coe_mk, AddHom.coe_mk, hleft] using he
  let E : C ≃ₗ[F] W j :=
    LinearEquiv.ofInjectiveOfFinrankEq P hinj (by simp [j])
  let Q : C →ₗ[F] W r :=
    { toFun := fun x i => x.val (perm (.inr i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L := Q.comp E.symm.toLinearMap
  refine ⟨r,perm,L,?_⟩
  intro x
  constructor
  · intro hx k
    change x (perm (.inr k)) = Q (E.symm (P ⟨x,hx⟩)) k
    change x (perm (.inr k)) = Q (E.symm (E ⟨x,hx⟩)) k
    rw [LinearEquiv.symm_apply_apply]
    rfl
  · intro hx
    let y := E.symm (fun i => x (perm (.inl i)))
    have ey : E y = fun i => x (perm (.inl i)) := E.apply_symm_apply _
    have eq : y.val = x := by
      funext i
      obtain ⟨q,rfl⟩ := perm.surjective i
      cases q with
      | inl i => exact congrFun ey i
      | inr i => exact (hx i).symm
    exact eq ▸ y.property

theorem split_sum {A : Type*} [AddCommMonoid A] {j r n : ℕ}
    (perm : Fin j ⊕ Fin r ≃ Fin n) (f : Fin n → A) :
    (∑ i, f i) = (∑ i : Fin j, f (perm (.inl i))) + ∑ k : Fin r, f (perm (.inr k)) := by
  rw [← Equiv.sum_comp perm f]
  exact Fintype.sum_sum_type _

def wt {n : ℕ} (x : W n) : ℕ := (Finset.univ.filter (fun i => x i ≠ 0)).card

theorem wt_split {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n) (a : W j) (b : W r) :
    wt (join p a b) = wt a + wt b := by
  have form {l : ℕ} (x : W l) : wt x = ∑ i, if x i ≠ 0 then (1 : ℕ) else 0 := by
    rw [← Finset.sum_filter]
    simp [wt]
  simp only [form, split_sum p (fun i => if join p a b i ≠ 0 then (1 : ℕ) else 0),
    join_left, join_right]

theorem graph_join {j r n : ℕ} {C : Submodule F (W n)}
    {p : Fin j ⊕ Fin r ≃ Fin n} {L : W j →ₗ[F] W r}
    (h : ∀ x, x ∈ C ↔ ∀ k, x (p (.inr k)) = L (fun i => x (p (.inl i))) k)
    (a : W j) : join p a (L a) ∈ C := by
  apply (h _).mpr
  intro k
  simp

private theorem single_wt {j : ℕ} (i : Fin j) : wt (Pi.single i (1 : F)) = 1 := by
  have he : (Finset.univ.filter (fun k => (Pi.single i (1 : F) : W j) k ≠ 0)) = {i} := by
    ext k
    by_cases h : i = k <;> simp [Pi.single_apply, h, Ne.symm]
  rw [wt, he, Finset.card_singleton]

theorem rows_nonzero {j r n : ℕ} {C : Submodule F (W n)}
    {p : Fin j ⊕ Fin r ≃ Fin n} {L : W j →ₗ[F] W r}
    (h : ∀ x, x ∈ C ↔ ∀ k, x (p (.inr k)) = L (fun i => x (p (.inl i))) k)
    (hwt : ∀ x ∈ C, x ≠ 0 → 2 ≤ wt x) :
    ∀ i, L (Pi.single i (1 : F)) ≠ 0 := by
  intro i he
  let z := join p (Pi.single i (1 : F)) (L (Pi.single i (1 : F)))
  have hz : z ≠ 0 := by
    intro hz
    have eq := congrFun hz (p (.inl i))
    simp [z] at eq
  have lb := hwt z (graph_join h _) hz
  rw [wt_split, he, single_wt] at lb
  simp [wt] at lb

theorem sum_graph {A : Type*} [AddCommMonoid A] {j r n : ℕ} {C : Submodule F (W n)}
    {p : Fin j ⊕ Fin r ≃ Fin n} {L : W j →ₗ[F] W r}
    (h : ∀ x, x ∈ C ↔ ∀ k, x (p (.inr k)) = L (fun i => x (p (.inl i))) k)
    (f : W n → A) :
    (∑ x ∈ Finset.univ.filter (fun x => x ∈ C), f x) = ∑ a, f (join p a (L a)) := by
  classical
  let _ : Fintype C := Fintype.ofFinite C
  let e : W j ≃ C :=
    { toFun := fun a => ⟨join p a (L a), graph_join h a⟩
      invFun := fun x i => x.val (p (.inl i))
      left_inv := fun a => by funext i; simp
      right_inv := by
        intro x
        apply Subtype.ext
        funext i
        obtain ⟨k,rfl⟩ := p.surjective i
        cases k with
        | inl i => simp
        | inr i => simpa using ((h x.val).mp x.property i).symm }
  rw [Finset.sum_subtype (p := fun x : W n => x ∈ C) _ (by intro x; simp) f]
  exact (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm

def info {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n) : Finset (Fin n) :=
  Finset.univ.map ⟨fun i => p (.inl i), p.injective.comp Sum.inl_injective⟩

theorem mem_info {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n) (x : Fin n) :
    x ∈ info p ↔ ∃ i : Fin j, p (.inl i) = x := by
  simp [info]

@[simp] theorem info_card {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n) :
    (info p).card = j := by simp [info]

@[simp] theorem info_left {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n) (i : Fin j) :
    p (.inl i) ∈ info p := (mem_info _ _).mpr ⟨i,rfl⟩

@[simp] theorem info_right {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n) (i : Fin r) :
    p (.inr i) ∉ info p := by
  rw [mem_info]
  rintro ⟨l,h⟩
  have he := p.injective h
  cases he

private theorem parity_set {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n)
    (T : Finset (Fin n)) (hi : info p ⊆ T) (hc : T.card = j+1) :
    ∃ k : Fin r, T = insert (p (.inr k)) (info p) := by
  have hc' : (T \ info p).card = 1 := by rw [Finset.card_sdiff_of_subset hi, hc, info_card]; omega
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hc'
  have hm : b ∈ T \ info p := by rw [hb]; simp
  obtain ⟨q,rfl⟩ := p.surjective b
  cases q with
  | inl a => exact ((Finset.mem_sdiff.mp hm).2 (info_left p a)).elim
  | inr k =>
    refine ⟨k,?_⟩
    ext i
    rw [Finset.mem_insert]
    constructor
    · intro h
      by_cases his : i ∈ info p
      · exact Or.inr his
      · have cit := Finset.mem_sdiff.mpr ⟨h,his⟩
        rw [hb, Finset.mem_singleton] at cit
        exact Or.inl cit
    · rintro (rfl | h)
      · exact (Finset.mem_sdiff.mp hm).1
      · exact hi h

private theorem parity_iff_right {j r n : ℕ} (p : Fin j ⊕ Fin r ≃ Fin n) (k : Fin r)
    (x : W n) : ((∀ i, i ∉ insert (p (.inr k)) (info p) → x i = 0) ∧ (∑ i, x i) = 0) ↔
      ∀ q, x (p (.inr q)) = (Pi.single k (∑ i : Fin j, x (p (.inl i))) : W r) q := by
  let s : F := ∑ i : Fin j, x (p (.inl i))
  let b : W r := fun q => x (p (.inr q))
  have off : (∀ i, i ∉ insert (p (.inr k)) (info p) → x i = 0) ↔
      ∀ q, q ≠ k → b q = 0 := by
    constructor
    · intro ho q hq
      apply ho
      simp [hq, p.injective.eq_iff]
    · intro ho i hi
      obtain ⟨q,rfl⟩ := p.surjective i
      cases q with
      | inl i => exact (hi (Finset.mem_insert_of_mem (info_left p i))).elim
      | inr q => exact ho q (fun he => hi (he.symm ▸ Finset.mem_insert_self _ _))
  have onlyK (hb : ∀ q, q ≠ k → b q = 0) : (∑ q, b q) = b k := by
    apply Finset.sum_eq_single k (fun q _ hq => hb q hq)
    simp
  have htwo : ∀ a b : F, a+b=0 ↔ b=a := by decide +kernel
  rw [off, split_sum p x]
  change ((∀ q, q ≠ k → b q=0) ∧ s + (∑ q, b q)=0) ↔
    ∀ q, b q = (Pi.single k s : W r) q
  constructor
  · rintro ⟨hb,hz⟩ q
    by_cases hq : q=k
    · subst q
      rw [onlyK hb, htwo] at hz
      simpa using hz
    · rw [hb q hq]
      simp [Ne.symm hq]
  · intro hb
    have hb0 (q : Fin r) (hq : q ≠ k) : b q = 0 := by
      simpa [Pi.single_apply, Ne.symm hq] using hb q
    refine ⟨hb0,?_⟩
    rw [onlyK hb0, htwo]
    simpa using hb k

private theorem single_expansion {j : ℕ} (a : W j) :
    (∑ i, a i • (Pi.single i (1 : F) : W j)) = a := by
  classical
  funext k
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]

private theorem rows_expand {j r : ℕ} (L : W j →ₗ[F] W r) (k : Fin r)
    (hL : ∀ i, L (Pi.single i (1 : F)) = Pi.single k (1 : F)) (a : W j) :
    L a = Pi.single k (∑ i, a i) := by
  have he := congrArg L (single_expansion a)
  rw [map_sum] at he
  simp only [map_smul, hL] at he
  rw [← he]
  funext q
  by_cases hq : k=q <;> simp [Finset.sum_apply, Pi.smul_apply, hq]

theorem parity_iff_rows {j r n : ℕ} {C : Submodule F (W n)}
    {p : Fin j ⊕ Fin r ≃ Fin n} {L : W j →ₗ[F] W r}
    (h : ∀ x, x ∈ C ↔ ∀ k, x (p (.inr k)) = L (fun i => x (p (.inl i))) k) :
    (∃ T : Finset (Fin n), T.card = j+1 ∧ ∀ x : W n,
      x ∈ C ↔ (∀ i, i ∉ T → x i = 0) ∧ (∑ i, x i) = 0) ↔
    ∃ k : Fin r, ∀ i, L (Pi.single i (1 : F)) = Pi.single k (1 : F) := by
  constructor
  · rintro ⟨T,hcard,hT⟩
    have hsubset : info p ⊆ T := by
      intro i hi
      obtain ⟨a,rfl⟩ := (mem_info _ _).mp hi
      by_contra hnot
      let u : W j := Pi.single a (1 : F)
      have he := ((hT _).mp (graph_join h u)).1 _ hnot
      simp [u] at he
    obtain ⟨k,rfl⟩ := parity_set p T hsubset hcard
    refine ⟨k,fun i => ?_⟩
    let a : W j := Pi.single i (1 : F)
    have ha := (parity_iff_right p k (join p a (L a))).mp ((hT _).mp (graph_join h a))
    funext q
    simpa [a, Pi.single_apply] using ha q
  · rintro ⟨k,hk⟩
    refine ⟨insert (p (.inr k)) (info p), by simp, fun x => ?_⟩
    rw [parity_iff_right p k x, h x, rows_expand L k hk]
end Systematic1059

namespace Fourier1059

abbrev F := ZMod 2

def wt {I : Type} [Fintype I] (x : I → F) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

def dot {I : Type} [Fintype I] (u v : I → F) : F := dotProduct u v

noncomputable def bias (z : ℝ) (b : F) : ℝ := if b = 0 then (1+z)/2 else (1-z)/2

noncomputable def law {I : Type} [Fintype I] (z : ℝ) (u : I → F) : ℝ := ∏ i, bias z (u i)

def sign (b : F) : ℝ := if b = 0 then 1 else -1

private theorem binary : ∀ b : F, b = 0 ∨ b = 1 := by decide +kernel

private theorem nonzero_one : (1 : F) ≠ 0 := by decide +kernel

private theorem one_add_one : (1 : F)+1 = 0 := by decide +kernel

private theorem sign_add (a b : F) : sign (a+b) = sign a * sign b := by
  rcases binary a with rfl | rfl <;> rcases binary b with rfl | rfl <;> simp [sign, one_add_one]

private theorem sign_sum {I : Type} (S : Finset I) (a : I → F) :
    sign (∑ i ∈ S, a i) = ∏ i ∈ S, sign (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sign]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, sign_add, ih]

private theorem single_moment (z : ℝ) (v : F) :
    (∑ b : F, bias z b * sign (b*v)) = if v = 0 then 1 else z := by
  have hU : (Finset.univ : Finset F) = {0,1} := by decide +kernel
  rw [hU, Finset.sum_insert (by simp [nonzero_one.symm]), Finset.sum_singleton]
  rcases binary v with rfl | rfl <;> simp [bias, sign] <;> ring

private theorem prod_weight {I : Type} [Fintype I] (z : ℝ) (v : I → F) :
    (∏ i, if v i = 0 then 1 else z) = z^(wt v) := by
  classical
  simp [Finset.prod_ite, wt]

theorem moment {I : Type} [Fintype I] [DecidableEq I] (z : ℝ) (v : I → F) :
    (∑ u : I → F, law z u * sign (dot u v)) = z^(wt v) := by
  calc
    _ = ∑ u : I → F, ∏ i, bias z (u i) * sign (u i*v i) := by
      simp [law, dot, dotProduct, sign_sum, Finset.prod_mul_distrib]
    _ = ∏ i : I, ∑ b : F, bias z b * sign (b*v i) :=
      (Fintype.prod_sum fun i b => bias z b * sign (b*v i)).symm
    _ = _ := by simp_rw [single_moment]; exact prod_weight z v

theorem mass {I : Type} [Fintype I] [DecidableEq I] (z : ℝ) :
    (∑ u : I → F, law z u) = 1 := by
  simpa [dot, wt, sign] using moment z (0 : I → F)

theorem law_nonneg {I : Type} [Fintype I] {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (u : I → F) : 0 ≤ law z u := by
  exact Finset.prod_nonneg fun i _ => by unfold bias; split <;> linarith

private theorem bit_indicator (b : F) : (if b = 0 then (0 : ℝ) else 1) = (1-sign b)/2 := by
  split <;> simp [sign, *]

theorem prob_nonzero {I : Type} [Fintype I] [DecidableEq I] (z : ℝ) (v : I → F) :
    (∑ u : I → F, law z u * (if dot u v = 0 then 0 else 1)) = (1-z^wt v)/2 := by
  simp_rw [bit_indicator, ← mul_div_assoc, mul_sub, mul_one, div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, mass z, moment]

private theorem add_zero_iff_equal : ∀ a b : F, a+b = 0 ↔ a=b := by decide +kernel

theorem prob_mismatch {I : Type} [Fintype I] [DecidableEq I] (z : ℝ) (v w : I → F) :
    (∑ u ∈ (Finset.univ.filter fun u => dot u v ≠ dot u w), law z u) = (1-z^wt (v+w))/2 := by
  rw [Finset.sum_filter]
  have h (u : I → F) : dot u (v+w) = 0 ↔ dot u v = dot u w := by
    rw [dot, dotProduct_add, add_zero_iff_equal]
    rfl
  calc
    _ = ∑ u : I → F, law z u * (if dot u (v+w) = 0 then 0 else 1) := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : dot u v = dot u w
      · simp [hu, (h u).2 hu]
      · have hn : dot u (v+w) ≠ 0 := fun e => hu ((h u).1 e)
        simp [hu, hn]
    _ = _ := prob_nonzero z (v+w)

def adjoint {I J : Type} [DecidableEq I] [Fintype J]
    (L : (I → F) →ₗ[F] (J → F)) (u : J → F) : I → F :=
  fun i => dot u (L (Pi.single i 1))

private def dotLinear {J : Type} [Fintype J] (u : J → F) : (J → F) →ₗ[F] F where
  toFun := dot u
  map_add' v w := by simp [dot, dotProduct_add]
  map_smul' c v := by
    simp only [dot, dotProduct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem dot_adjoint {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (L : (I → F) →ₗ[F] (J → F)) (u : J → F) (x : I → F) :
    dot u (L x) = dot x (adjoint L u) := by
  have hx : (∑ i : I, x i • Pi.single i (1 : F)) = x := by
    calc
      _ = ∑ i : I, Pi.single i (x i) := by
        apply Finset.sum_congr rfl
        intro i _
        funext j
        by_cases h : j = i <;> simp [h]
      _ = x := LinearMap.sum_single_apply (fun _ : I => F) x
  calc
    _ = ((dotLinear u).comp L) (∑ i : I, x i • Pi.single i (1 : F)) := by rw [hx]; rfl
    _ = ∑ i : I, x i * dot u (L (Pi.single i (1 : F))) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, LinearMap.comp_apply]
      rfl
    _ = _ := rfl

theorem expected_weight {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (L : (I → F) →ₗ[F] (J → F)) (z : ℝ) :
    (∑ u : J → F, law z u * (wt (adjoint L u) : ℝ)) =
      ∑ i : I, (1-z^wt (L (Pi.single i 1)))/2 := by
  have h (u : J → F) : (wt (adjoint L u) : ℝ) =
      ∑ i : I, if dot u (L (Pi.single i (1 : F))) = 0 then 0 else 1 := by
    unfold wt
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : dot u (L (Pi.single i (1 : F))) = 0 <;> simp [adjoint, hi]
  simp_rw [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [prob_nonzero]

private theorem normalized_weight {I : Type} [Fintype I] (z : ℝ) (hz : 1+z ≠ 0)
    (x : I → F) : z ^ wt x = (1+z) ^ Fintype.card I * law ((1-z)/(1+z)) x := by
  have h (b : F) : (if b = 0 then 1 else z) = (1+z) * bias ((1-z)/(1+z)) b := by
    by_cases hb : b = 0 <;> simp [bias, hb] <;> field_simp [hz] <;> ring
  rw [← prod_weight]
  simp_rw [h, Finset.prod_mul_distrib]
  simp [law]

theorem transform {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (L : (I → F) →ₗ[F] (J → F)) (z : ℝ) (hz : 1+z ≠ 0) :
    (∑ x : I → F, z^(wt x+wt (L x))) =
      (1+z)^Fintype.card I * ∑ u : J → F, law z u * ((1-z)/(1+z))^wt (adjoint L u) := by
  let t := (1-z)/(1+z)
  have hx (x : I → F) : z^(wt x+wt (L x)) =
      (1+z)^Fintype.card I * ∑ u : J → F, law z u * (law t x * sign (dot x (adjoint L u))) := by
    calc
      _ = ((1+z)^Fintype.card I * law t x) * ∑ u : J → F, law z u * sign (dot u (L x)) := by
        rw [pow_add, normalized_weight z hz x, moment z (L x)]
      _ = _ := by
        rw [mul_assoc, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro u _
        rw [dot_adjoint]
        ring
  simp_rw [hx, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, moment]
  rfl

end Fourier1059

namespace Moments1059

abbrev F := ZMod 2
abbrev W (n : ℕ) := Fin n → F

def support {n : ℕ} (x : W n) : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)

def wt {n : ℕ} (x : W n) : ℕ := (support x).card

theorem bit_cases : ∀ a : F, a = 0 ∨ a = 1 := by decide +kernel

theorem mem_support {n : ℕ} (x : W n) (i : Fin n) : i ∈ support x ↔ x i ≠ 0 := by
  simp [support]

theorem wt_le {n : ℕ} (x : W n) : wt x ≤ n := by
  unfold wt
  simpa using Finset.card_le_card (Finset.subset_univ (support x))

theorem wt_pos {n : ℕ} {x : W n} (hx : x ≠ 0) : 0 < wt x := by
  by_contra! h
  apply hx
  funext i
  by_contra hi
  have hmem : i ∈ support x := (mem_support x i).mpr hi
  have hpos : 0 < wt x := Finset.card_pos.mpr ⟨i, hmem⟩
  omega

private theorem wt_lt_of_coordinate {n : ℕ} {x : W n} {i : Fin n} (hi : x i = 0) :
    wt x < n := by
  have hs : support x ⊂ Finset.univ := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro he
    have hm : i ∈ support x := he ▸ Finset.mem_univ i
    exact (mem_support x i).mp hm hi
  unfold wt
  simpa using Finset.card_lt_card hs

theorem mismatch_interior {n : ℕ} (x : W n) (i k : Fin n) (h : x i ≠ x k) :
    0 < wt x ∧ wt x < n := by
  have hx : x ≠ 0 := by
    intro he
    apply h
    rw [he]
    rfl
  refine ⟨wt_pos hx, ?_⟩
  rcases bit_cases (x i) with hi | hi
  · exact wt_lt_of_coordinate hi
  · rcases bit_cases (x k) with hk | hk
    · exact wt_lt_of_coordinate hk
    · exact (h (hi.trans hk.symm)).elim

theorem single_of_weight {n : ℕ} (x : W n) (h : wt x = 1) :
    ∃ i : Fin n, x = Pi.single i 1 := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  refine ⟨i, ?_⟩
  funext k
  by_cases hk : k = i
  · subst k
    have hm : i ∈ support x := hi ▸ Finset.mem_singleton_self i
    have hn : x i ≠ 0 := (mem_support x i).mp hm
    simpa using (bit_cases (x i)).resolve_left hn
  · have hn : x k = 0 := by
      by_contra hne
      exact hk (Finset.mem_singleton.mp (hi ▸ (mem_support x k).mpr hne))
    simpa [Pi.single_apply, hk, Ne.symm hk] using hn

theorem weight_two_singles {n : ℕ} (i k : Fin n) (h : i ≠ k) :
    wt (Pi.single i 1 + Pi.single k 1 : W n) = 2 := by
  have hs : support (Pi.single i 1 + Pi.single k 1 : W n) = {i,k} := by
    ext a
    rw [mem_support]
    by_cases hai : a = i
    · subst a
      simp [h]
    · by_cases hak : a = k
      · subst a
        simp [Ne.symm h]
      · simp [hai, hak]
  rw [wt, hs, Finset.card_insert_of_notMem (by simpa using h), Finset.card_singleton]

theorem sum_floor {n : ℕ} (p : Fin n → ℝ) (v : ℝ) (h : ∀ i, v ≤ p i) :
    (n : ℝ)*v ≤ ∑ i, p i := by
  calc
    (n : ℝ)*v = ∑ _ : Fin n, v := by simp [nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun i _ => h i

theorem sum_floor_strong {n : ℕ} (p : Fin n → ℝ) (v δ : ℝ) (i₀ : Fin n)
    (h : ∀ i, v ≤ p i) (hδ : v+δ ≤ p i₀) :
    (n : ℝ)*v + δ ≤ ∑ i, p i := by
  calc
    (n : ℝ)*v + δ = ∑ i : Fin n, (v + if i = i₀ then δ else 0) := by
      simp [Finset.sum_add_distrib, nsmul_eq_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with he
      · rwa [he]
      · simpa using h i

theorem gap_of_weight {k : ℕ} (z : ℝ) (hz : 0 < z) (hz1 : z < 1) (hk : 1 ≤ k) :
    (1-z)/2 ≤ (1-z^k)/2 := by
  have hp := pow_le_pow_of_le_one hz.le hz1.le hk
  rw [pow_one] at hp
  linarith

theorem gap_of_heavy {k : ℕ} (z : ℝ) (hz : 0 < z) (hz1 : z < 1) (hk : 2 ≤ k) :
    (1-z)/2 + (z-z^2)/2 ≤ (1-z^k)/2 := by
  have hp := pow_le_pow_of_le_one hz.le hz1.le hk
  linarith

theorem compare_mass {α : Type} [Fintype α] (μ : α → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (S T : Finset α) (h : S ⊆ T) : (∑ a ∈ S, μ a) ≤ ∑ a ∈ T, μ a :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun a _ _ => hμ a)

end Moments1059

namespace Chord1059

open scoped BigOperators

private theorem geom (t : ℝ) (n : ℕ) :
    (1-t) * (∑ j ∈ Finset.range n, t^j) = 1-t^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring

private theorem pow_decrease (t : ℝ) (h₀ : 0 ≤ t) (h₁ : t ≤ 1) {i j : ℕ} (h : i ≤ j) :
    t^j ≤ t^i := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le h
  have hpow : ∀ w : ℕ, t^w ≤ 1 := by
    intro w
    induction w with
    | zero => simp
    | succ w ih => rw [pow_succ]; exact (mul_le_mul_of_nonneg_right ih h₀).trans (by simpa using h₁)
  rw [pow_add]
  exact (mul_le_mul_of_nonneg_left (hpow v) (pow_nonneg h₀ _)).trans_eq (mul_one _)

private theorem difference (t : ℝ) (w v : ℕ) :
    (1-t) * (∑ a ∈ Finset.range w, ∑ b ∈ Finset.range v, (t^a-t^(w+b))) =
      (v : ℝ) + (w : ℝ)*t^(w+v) - (w+v : ℝ)*t^w := by
  have hs : (∑ a ∈ Finset.range w, ∑ b ∈ Finset.range v, (t^a-t^(w+b))) =
      (v : ℝ)*(∑ a ∈ Finset.range w, t^a) -
        (w : ℝ)*(t^w*(∑ b ∈ Finset.range v, t^b)) := by
    simp_rw [Finset.sum_sub_distrib, pow_add, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    rw [← Finset.mul_sum]
    ring
  rw [hs]
  calc
    _ = (v : ℝ)*((1-t)*(∑ a ∈ Finset.range w, t^a)) -
      (w : ℝ)*t^w*((1-t)*(∑ b ∈ Finset.range v, t^b)) := by ring
    _ = _ := by rw [geom, geom, pow_add]; ring

theorem chord_scaled (t : ℝ) (h₀ : 0 ≤ t) (h₁ : t ≤ 1) (j w : ℕ) (hw : w ≤ j) :
    (j : ℝ)*t^w ≤ (j : ℝ) - (w : ℝ)*(1-t^j) := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hw
  have hp : (0 : ℝ) ≤ ∑ a ∈ Finset.range w, ∑ b ∈ Finset.range v, (t^a-t^(w+b)) := by
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b _
    exact sub_nonneg.mpr (pow_decrease t h₀ h₁ ((Finset.mem_range.mp ha).le.trans (Nat.le_add_right _ _)))
  have hg := mul_nonneg (sub_nonneg.mpr h₁) hp
  rw [difference] at hg
  push_cast
  linarith

theorem chord_gap_scaled (t : ℝ) (h₀ : 0 ≤ t) (h₁ : t ≤ 1) (j w : ℕ)
    (hw₀ : 0 < w) (hw₁ : w < j) :
    (j : ℝ)*t^w + (1-t)^2 ≤ (j : ℝ) - (w : ℝ)*(1-t^j) := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hw₁.le
  have hv : 0 < v := by omega
  have hpos (a b : ℕ) (ha : a ∈ Finset.range w) : 0 ≤ t^a-t^(w+b) :=
    sub_nonneg.mpr (pow_decrease t h₀ h₁ ((Finset.mem_range.mp ha).le.trans (Nat.le_add_right _ _)))
  have hm : 1-t ≤ ∑ a ∈ Finset.range w, ∑ b ∈ Finset.range v, (t^a-t^(w+b)) := by
    calc
      _ ≤ t^0-t^(w+0) := by simpa using sub_le_sub_left (pow_decrease t h₀ h₁ hw₀) 1
      _ ≤ ∑ b ∈ Finset.range v, (t^0-t^(w+b)) :=
        Finset.single_le_sum (fun b _ => hpos 0 b (Finset.mem_range.mpr hw₀)) (Finset.mem_range.mpr hv)
      _ ≤ _ := Finset.single_le_sum (fun a ha => Finset.sum_nonneg fun b _ => hpos a b ha)
        (Finset.mem_range.mpr hw₀)
  have hg := mul_le_mul_of_nonneg_left hm (sub_nonneg.mpr h₁)
  rw [difference] at hg
  push_cast
  rw [pow_two]
  linarith

theorem weighted_chord {Ω : Type*} [Fintype Ω] (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (j : ℕ) (μ : Ω → ℝ) (hμ : ∀ u, 0 ≤ μ u) (hmass : ∑ u, μ u = 1)
    (w : Ω → ℕ) (hw : ∀ u, w u ≤ j) (S : Finset Ω) (hS : ∀ u ∈ S, 0 < w u ∧ w u < j) :
    (j : ℝ)*(∑ u, μ u*t^(w u)) + (∑ u ∈ S, μ u)*(1-t)^2 ≤
      (j : ℝ) - (∑ u, μ u*(w u : ℝ))*(1-t^j) := by
  classical
  let g (u : Ω) := if u ∈ S then (1-t)^2 else 0
  have hg : ∑ u, μ u*g u = (∑ u ∈ S, μ u)*(1-t)^2 := by
    calc
      _ = ∑ u, if u ∈ S then μ u*(1-t)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases hu : u ∈ S <;> simp [g, hu]
      _ = _ := by rw [← Finset.sum_filter]; simp [Finset.sum_mul]
  have hscale : (j : ℝ)*(∑ u, μ u*t^(w u)) =
      ∑ u, μ u*((j : ℝ)*t^(w u)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  calc
    _ = ∑ u, μ u*((j : ℝ)*t^(w u)+g u) := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← hscale, hg]
    _ ≤ ∑ u, μ u*((j : ℝ)-(w u : ℝ)*(1-t^j)) := by
      apply Finset.sum_le_sum
      intro u _
      apply mul_le_mul_of_nonneg_left _ (hμ u)
      by_cases hu : u ∈ S
      · simpa only [g, ite_eq_left hu] using chord_gap_scaled t ht₀ ht₁ j (w u) (hS u hu).1 (hS u hu).2
      · simpa only [g, ite_eq_right hu, add_zero] using chord_scaled t ht₀ ht₁ j (w u) (hw u)
    _ = _ := by simp_rw [mul_sub, ← mul_assoc, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]

noncomputable def ratio (z : ℝ) : ℝ := (1-z)/(1+z)

noncomputable def target (j : ℕ) (z : ℝ) : ℝ := ((1+z)^(j+1)+(1-z)^(j+1))/2

theorem ratio_nonneg {z : ℝ} (hz : 0 ≤ z) (hz₁ : z ≤ 1) : 0 ≤ ratio z :=
  div_nonneg (sub_nonneg.mpr hz₁) (by linarith)

theorem ratio_lt_one {z : ℝ} (hz : 0 < z) : ratio z < 1 := by
  unfold ratio
  exact (div_lt_iff₀ (by linarith)).mpr (by linarith)

private theorem target_eq {z : ℝ} (hz : 0 ≤ z) (j : ℕ) :
    target j z = (1+z)^j*(1-((1-z)/2)*(1-ratio z^j)) := by
  unfold target ratio
  rw [div_pow, pow_succ (1+z), pow_succ (1-z)]
  have h : (1+z)^j ≠ 0 := pow_ne_zero _ (by linarith)
  field_simp
  ring

theorem estimate {j : ℕ} (hj : 0 < j) {z E P W δ η : ℝ} (hz : 0 < z) (hz₁ : z < 1)
    (hmoment : (j : ℝ)*((1-z)/2)+δ ≤ W) (hinterior : η ≤ P)
    (hchord : (j : ℝ)*E + P*(1-ratio z)^2 ≤ (j : ℝ)-W*(1-ratio z^j)) :
    (1+z)^j*E + (1+z)^j*(δ*(1-ratio z^j)+η*(1-ratio z)^2)/(j : ℝ) ≤ target j z := by
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hZ : (0 : ℝ) ≤ 1+z := by linarith
  have ht := ratio_nonneg hz.le hz₁.le
  have ht' := ratio_lt_one hz
  have hd : 0 ≤ 1-ratio z^j := by
    have hpow := pow_decrease _ ht ht'.le (show 0 ≤ j by omega)
    simpa using sub_nonneg.mpr (hpow.trans_eq (pow_zero _))
  have h1 := mul_le_mul_of_nonneg_right hmoment hd
  have h2 := mul_le_mul_of_nonneg_right hinterior (sq_nonneg (1-ratio z))
  have hb : (j : ℝ)*(E+(δ*(1-ratio z^j)+η*(1-ratio z)^2)/(j : ℝ)) ≤
      (j : ℝ)*(1-((1-z)/2)*(1-ratio z^j)) := by
    rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hj')]
    linarith only [h1, h2, hchord]
  have he : E+(δ*(1-ratio z^j)+η*(1-ratio z)^2)/(j : ℝ) ≤
      1-((1-z)/2)*(1-ratio z^j) := by
    by_contra! hn
    exact (not_lt_of_ge hb) (mul_lt_mul_of_pos_left hn hj')
  have he' := mul_le_mul_of_nonneg_left he (pow_nonneg hZ j)
  rwa [target_eq hz.le, mul_div_assoc, ← mul_add]

theorem positive_bonus {j : ℕ} (hj : 0 < j) {z δ η : ℝ} (hz : 0 < z) (hz₁ : z < 1)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hpos : 0 < δ ∨ 0 < η) :
    0 < (1+z)^j*(δ*(1-ratio z^j)+η*(1-ratio z)^2)/(j : ℝ) := by
  have ht := ratio_nonneg hz.le hz₁.le
  have ht' := ratio_lt_one hz
  have hpow : ratio z^j ≤ ratio z := by simpa using pow_decrease _ ht ht'.le hj
  have hα : 0 < 1-ratio z^j := sub_pos.mpr (hpow.trans_lt ht')
  have hβ : 0 < (1-ratio z)^2 := pow_pos (sub_pos.mpr ht') _
  have h : 0 < δ*(1-ratio z^j)+η*(1-ratio z)^2 := by
    rcases hpos with hp | hp
    · exact add_pos_of_pos_of_nonneg (mul_pos hp hα) (mul_nonneg hη hβ.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hδ hα.le) (mul_pos hp hβ)
  have hZ : (0 : ℝ) < 1+z := by linarith
  exact div_pos (mul_pos (pow_pos hZ _) h) (by exact_mod_cast hj)

theorem exact_of_endpoints {Ω : Type*} [Fintype Ω] {j : ℕ} (hj : 0 < j) {z : ℝ}
    (hz : 0 ≤ z) (μ : Ω → ℝ) (hmass : ∑ u, μ u = 1)
    (w : Ω → ℕ) (hw : ∀ u, w u = 0 ∨ w u = j)
    (hmoment : ∑ u, μ u*(w u : ℝ) = (j : ℝ)*((1-z)/2)) :
    (1+z)^j*(∑ u, μ u*ratio z^(w u)) = target j z := by
  have hscale : (j : ℝ)*(∑ u, μ u*ratio z^(w u)) =
      ∑ u, μ u*((j : ℝ)*ratio z^(w u)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hpoint (u : Ω) : (j : ℝ)*ratio z^(w u) =
      (j : ℝ)-(w u : ℝ)*(1-ratio z^j) := by
    rcases hw u with hu | hu
    · rw [hu]; simp
    · rw [hu]; ring
  have he : (j : ℝ)*(∑ u, μ u*ratio z^(w u)) =
      (j : ℝ)*(1-((1-z)/2)*(1-ratio z^j)) := by
    rw [hscale]
    simp_rw [hpoint, mul_sub, ← mul_assoc, Finset.sum_sub_distrib, ← Finset.sum_mul,
      hmass, hmoment, one_mul]
    ring
  rw [target_eq hz]
  congr 1
  exact mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hj)) he

theorem quarter_gap {j : ℕ} (hj : 0 < j) {v δ η : ℝ}
    (hcase : (δ = 3/32 ∧ η = 0) ∨ (δ = 0 ∧ η = 15/64))
    (h : v + (1+(1/4:ℝ))^j*(δ*(1-ratio (1/4)^j)+η*(1-ratio (1/4))^2)/(j : ℝ) ≤
      target j (1/4)) :
    3*(5/4 : ℝ)^j ≤ 80*(j : ℝ)*(target j (1/4)-v) := by
  have hq : ratio (1/4) = (3/5 : ℝ) := by norm_num [ratio]
  have hpow : (3/5 : ℝ)^j ≤ 3/5 := by
    simpa using pow_decrease (3/5) (by norm_num) (by norm_num) hj
  have hdef : (3/80 : ℝ) ≤ δ*(1-ratio (1/4)^j)+η*(1-ratio (1/4))^2 := by
    rcases hcase with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [hq]
      linarith
    · norm_num [hq]
  have hj' : (0 : ℝ) < j := by exact_mod_cast hj
  have hh : (1+(1/4:ℝ))^j*(δ*(1-ratio (1/4)^j)+η*(1-ratio (1/4))^2)/(j : ℝ) ≤
      target j (1/4) - v := by linarith
  have h1 := (div_le_iff₀ hj').mp hh
  have hZ : (1+(1/4:ℝ))^j=(5/4:ℝ)^j := by norm_num
  rw [hZ] at h1
  have h2 := (mul_le_mul_of_nonneg_left hdef (by positivity : 0 ≤ (5/4:ℝ)^j)).trans h1
  nlinarith only [h2]

end Chord1059

namespace Bound1059

open Fourier1059
abbrev F := ZMod 2
abbrev W (n : ℕ) := Fin n → F

noncomputable def value {j r : ℕ} (L : W j →ₗ[F] W r) (z : ℝ) : ℝ :=
  ∑ x : W j, z^(wt x + wt (L x))

def row {j r : ℕ} (L : W j →ₗ[F] W r) (i : Fin j) : W r := L (Pi.single i 1)

def uniform {j r : ℕ} (L : W j →ₗ[F] W r) : Prop :=
  ∃ k : Fin r, ∀ i : Fin j, row L i = Pi.single k 1

noncomputable def expectation {j r : ℕ} (L : W j →ₗ[F] W r) (z : ℝ) : ℝ :=
  ∑ u : W r, law z u * (wt (adjoint L u) : ℝ)

def interior {j r : ℕ} (L : W j →ₗ[F] W r) : Finset (W r) :=
  Finset.univ.filter (fun u => 0 < wt (adjoint L u) ∧ wt (adjoint L u) < j)

noncomputable def interiorMass {j r : ℕ} (L : W j →ₗ[F] W r) (z : ℝ) : ℝ :=
  ∑ u ∈ interior L, law z u

theorem base_expectation {j r : ℕ} (L : W j →ₗ[F] W r)
    (hn : ∀ i, row L i ≠ 0) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    (j : ℝ)*((1-z)/2) ≤ expectation L z := by
  unfold expectation
  rw [expected_weight]
  apply Moments1059.sum_floor
  intro i
  exact Moments1059.gap_of_weight z hz hz1 (Moments1059.wt_pos (hn i))

theorem heavy_expectation {j r : ℕ} (L : W j →ₗ[F] W r)
    (hn : ∀ i, row L i ≠ 0) (i₀ : Fin j) (hheavy : 2 ≤ wt (row L i₀))
    {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    (j : ℝ)*((1-z)/2)+(z-z^2)/2 ≤ expectation L z := by
  unfold expectation
  rw [expected_weight]
  apply Moments1059.sum_floor_strong _ _ _ i₀
  · intro i
    exact Moments1059.gap_of_weight z hz hz1 (Moments1059.wt_pos (hn i))
  · exact Moments1059.gap_of_heavy z hz hz1 hheavy

theorem mismatch_mass {j r : ℕ} (L : W j →ₗ[F] W r)
    (i i' : Fin j) (k k' : Fin r) (hk : k ≠ k')
    (h : row L i = Pi.single k 1) (h' : row L i' = Pi.single k' 1)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (1-z^2)/2 ≤ interiorMass L z := by
  let A : Finset (W r) := Finset.univ.filter (fun u => dot u (row L i) ≠ dot u (row L i'))
  have hsub : A ⊆ interior L := by
    intro u hu
    have hm := (Finset.mem_filter.mp hu).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Moments1059.mismatch_interior (adjoint L u) i i' hm⟩
  have ha := Moments1059.compare_mass (law z) (law_nonneg hz hz1) A (interior L) hsub
  have hA : ∑ u ∈ A, law z u = (1-z^2)/2 := by
    unfold A
    have hwt : wt (Pi.single k 1 + Pi.single k' 1 : W r) = 2 :=
      Moments1059.weight_two_singles k k' hk
    rw [prob_mismatch, h, h', hwt]
  rwa [← hA]

theorem dichotomy {j r : ℕ} (L : W j →ₗ[F] W r) (hj : 0 < j)
    (hn : ∀ i, row L i ≠ 0) (hu : ¬ uniform L) :
    (∃ i, 2 ≤ wt (row L i)) ∨
      ∃ (i i' : Fin j) (k k' : Fin r), k ≠ k' ∧
        row L i = Pi.single k 1 ∧ row L i' = Pi.single k' 1 := by
  classical
  by_cases h : ∃ i, 2 ≤ wt (row L i)
  · exact Or.inl h
  · right
    have each (i : Fin j) : ∃ k : Fin r, row L i = Pi.single k 1 := by
      apply Moments1059.single_of_weight
      change wt (row L i) = 1
      have hlo : 0 < wt (row L i) := Moments1059.wt_pos (hn i)
      have hhi : ¬ 2 ≤ wt (row L i) := fun hi => h ⟨i, hi⟩
      omega
    choose k hk using each
    let i₀ : Fin j := ⟨0, hj⟩
    have hdiff : ∃ i, k i ≠ k i₀ := by
      by_contra! he
      exact hu ⟨k i₀, fun i => (hk i).trans (congrArg (fun a => Pi.single a 1) (he i))⟩
    obtain ⟨i, hi⟩ := hdiff
    exact ⟨i, i₀, k i, k i₀, hi, hk i, hk i₀⟩

theorem estimate {j r : ℕ} (L : W j →ₗ[F] W r) (hj : 0 < j) {z δ η : ℝ}
    (hz : 0 < z) (hz1 : z < 1)
    (hd : (j : ℝ)*((1-z)/2)+δ ≤ expectation L z)
    (he : η ≤ interiorMass L z) :
    value L z + (1+z)^j*(δ*(1-Chord1059.ratio z^j)+η*(1-Chord1059.ratio z)^2)/(j : ℝ)
      ≤ Chord1059.target j z := by
  have hc := Chord1059.weighted_chord (Chord1059.ratio z)
    (Chord1059.ratio_nonneg hz.le hz1.le) (Chord1059.ratio_lt_one hz).le j
    (law z : W r → ℝ) (law_nonneg hz.le hz1.le) (mass z)
    (fun u => wt (adjoint L u)) (fun u => Moments1059.wt_le (adjoint L u)) (interior L)
    (fun u hu => (Finset.mem_filter.mp hu).2)
  unfold value
  rw [transform L z (by linarith), Fintype.card_fin]
  exact Chord1059.estimate hj hz hz1 hd he hc

theorem interior_nonneg {j r : ℕ} (L : W j →ₗ[F] W r) {z : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ interiorMass L z :=
  Finset.sum_nonneg fun _ _ => law_nonneg hz hz1 _

private theorem wt_single {r : ℕ} (k : Fin r) : wt (Pi.single k 1 : W r) = 1 := by
  have he : Moments1059.support (Pi.single k 1 : W r) = {k} := by
    ext i
    rw [Moments1059.mem_support]
    by_cases h : i = k
    · subst i
      simp
    · simp [h]
  change (Moments1059.support _).card = 1
  rw [he, Finset.card_singleton]

theorem exact_uniform {j r : ℕ} (L : W j →ₗ[F] W r) (hj : 0 < j) (h : uniform L)
    {z : ℝ} (hz : 0 ≤ z) : value L z = Chord1059.target j z := by
  obtain ⟨k, hk⟩ := h
  have hwt (u : W r) : wt (adjoint L u) = 0 ∨ wt (adjoint L u) = j := by
    have ha : adjoint L u = fun _ => dot u (Pi.single k 1) := by
      funext i
      change dot u (row L i) = _
      rw [hk]
    rw [ha]
    by_cases hb : dot u (Pi.single k 1) = 0
    · left
      simp [wt, hb]
    · right
      simp [wt, hb]
  have he : expectation L z = (j : ℝ)*((1-z)/2) := by
    unfold expectation
    rw [expected_weight]
    change (∑ i : Fin j, (1-z^wt (row L i))/2) = _
    simp_rw [hk, wt_single, pow_one]
    simp [nsmul_eq_mul]
  unfold value
  rw [transform L z (by linarith), Fintype.card_fin]
  exact Chord1059.exact_of_endpoints hj hz (law z) (mass z)
    (fun u => wt (adjoint L u)) hwt he

theorem bounds {j r : ℕ} (L : W j →ₗ[F] W r) (hj : 0 < j) (hn : ∀ i, row L i ≠ 0) :
    (∀ z : ℝ, 0 < z → z < 1 → value L z ≤ Chord1059.target j z ∧
      (value L z = Chord1059.target j z ↔ uniform L)) ∧
    (¬ uniform L →
      3*(5/4 : ℝ)^j ≤ 80*(j : ℝ)*(Chord1059.target j (1/4) - value L (1/4))) := by
  have strict {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (hu : ¬ uniform L) :
      value L z < Chord1059.target j z := by
    rcases dichotomy L hj hn hu with ⟨i, hi⟩ | ⟨i, i', k, k', hk, he, he'⟩
    · have hd : 0 < (z-z^2)/2 := by nlinarith [mul_pos hz (sub_pos.mpr hz1)]
      have hm := estimate L hj hz hz1 (heavy_expectation L hn i hi hz hz1)
        (interior_nonneg L hz.le hz1.le)
      have hp := Chord1059.positive_bonus hj hz hz1 hd.le (le_refl 0) (Or.inl hd)
      linarith only [hm, hp]
    · have hd : 0 < (1-z^2)/2 := by nlinarith [mul_pos (sub_pos.mpr hz1) (show 0 < 1+z by linarith)]
      have hm := estimate L hj hz hz1
        (show (j : ℝ)*((1-z)/2)+0 ≤ expectation L z by simpa using base_expectation L hn hz hz1)
        (mismatch_mass L i i' k k' hk he he' hz.le hz1.le)
      have hp := Chord1059.positive_bonus hj hz hz1 (le_refl 0) hd.le (Or.inr hd)
      linarith only [hm, hp]
  constructor
  · intro z hz hz1
    by_cases h : uniform L
    · exact ⟨(exact_uniform L hj h hz.le).le, iff_of_true (exact_uniform L hj h hz.le) h⟩
    · exact ⟨(strict hz hz1 h).le, iff_of_false (ne_of_lt (strict hz hz1 h)) h⟩
  · intro hu
    have hq : (0 : ℝ) < 1/4 := by norm_num
    have hq1 : (1/4 : ℝ) < 1 := by norm_num
    rcases dichotomy L hj hn hu with ⟨i, hi⟩ | ⟨i, i', k, k', hk, he, he'⟩
    · apply Chord1059.quarter_gap hj (δ := 3/32) (η := 0) (Or.inl ⟨rfl, rfl⟩)
      apply estimate L hj hq hq1 _ (interior_nonneg L hq.le hq1.le)
      have hm := heavy_expectation L hn i hi hq hq1
      norm_num at hm ⊢
      linarith only [hm]
    · apply Chord1059.quarter_gap hj (δ := 0) (η := 15/64) (Or.inr ⟨rfl, rfl⟩)
      apply estimate L hj hq hq1 _ _
      · simpa using base_expectation L hn hq hq1
      · have hm := mismatch_mass L i i' k k' hk he he' hq.le hq1.le
        norm_num at hm ⊢
        linarith only [hm]

end Bound1059

end PEqualNP.Outside.L_lib_1059

open PEqualNP.Outside.L_lib_1059

set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.L_lib_1059 :
    ∀ n : ℕ,
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let F := ZMod 2
      let W := Fin n → F
      ∀ C : Submodule F W,
        let j := Module.finrank F C
        let wt := fun (x : W) => (Finset.univ.filter (fun i => x i ≠ 0)).card
        let value := fun (z : ℝ) => ∑ x ∈ (Finset.univ : Finset W).filter (fun x => x ∈ C), z^(wt x)
        let bound := fun (z : ℝ) => ((1+z)^(j+1)+(1-z)^(j+1))/2
        let parity := ∃ T : Finset (Fin n), T.card = j+1 ∧ ∀ x : W,
          x ∈ C ↔ (∀ i, i ∉ T → x i = 0) ∧ (∑ i, x i) = 0
        0 < j → (∀ x ∈ C, x ≠ 0 → 2 ≤ wt x) →
          (∀ z : ℝ, 0 < z → z < 1 → value z ≤ bound z ∧ (value z = bound z ↔ parity)) ∧
          (¬ parity → 3*(5/4 : ℝ)^j ≤ 80*(j : ℝ)*(bound (1/4) - value (1/4))) := by
  classical
  intro n
  dsimp only
  intro C hj hn
  obtain ⟨r, p, L, h⟩ := Systematic1059.systematic C
  let j := Module.finrank (ZMod 2) C
  let cw (x : Systematic1059.W n) :=
    (@Finset.filter (Fin n) (fun i => x i ≠ 0)
      (fun _ => Classical.propDecidable _) Finset.univ).card
  let cv (z : ℝ) :=
    ∑ x ∈ @Finset.filter (Systematic1059.W n) (fun x => x ∈ C)
      (fun _ => Classical.propDecidable _) Finset.univ, z^(cw x)
  have hw (x : Systematic1059.W n) : cw x = Systematic1059.wt x := by
    unfold cw Systematic1059.wt
    rw [Finset.filter_congr_decidable]
  have hrow : ∀ i, Bound1059.row L i ≠ 0 := by
    apply Systematic1059.rows_nonzero h
    intro x hx hzero
    rw [← hw]
    exact hn x hx hzero
  have hvalue (z : ℝ) : cv z = Bound1059.value L z := by
    unfold cv
    simp only [hw]
    rw [Finset.filter_congr_decidable]
    rw [Systematic1059.sum_graph h (fun x => z^(Systematic1059.wt x))]
    unfold Bound1059.value
    simp only [Systematic1059.wt_split]
    rfl
  let parity : Prop :=
    ∃ T : Finset (Fin n), T.card = j+1 ∧ ∀ x : Systematic1059.W n,
      x ∈ C ↔ (∀ i, i ∉ T → x i = 0) ∧ (∑ i, x i) = 0
  have hp : parity ↔ Bound1059.uniform L := Systematic1059.parity_iff_rows h
  have hh := Bound1059.bounds L hj hrow
  have finish {g : ℝ → ℝ} (hg : ∀ z, g z = Bound1059.value L z) :
      (∀ z : ℝ, 0 < z → z < 1 → g z ≤ Chord1059.target j z ∧
        (g z = Chord1059.target j z ↔ parity)) ∧
      (¬ parity → 3*(5/4 : ℝ)^j ≤ 80*(j : ℝ)*(Chord1059.target j (1/4) - g (1/4))) := by
    simpa only [← hg, ← hp] using hh
  apply finish
  intro z
  refine Eq.trans ?_ (hvalue z)
  unfold cv
  apply Finset.sum_congr
  · ext x
    simp
  · intro x _
    congr 1
