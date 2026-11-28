import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Pigeonhole

namespace PEqualNP.Outside.L_lib_878

abbrev Bin := ZMod 2
abbrev Vec (k : Nat) := Fin k → Bin

noncomputable def count {D : Type} (p : D → Prop) := Nat.card {z // p z}

noncomputable def best {k e : Nat} (q : Vec k → Vec e) (s : Nat) :=
  sSup {n : Nat | ∃ (P : (Vec k × Vec e) →ₗ[Bin] Vec s) (v : Vec s),
    Function.Surjective P ∧ n = ((Finset.univ : Finset (Vec k)).filter
      (fun x => P (x,q x) = v)).card}

theorem best_le {k e s : Nat} {q : Vec k → Vec e} {n : Nat}
    (h : ∀ (P : (Vec k × Vec e) →ₗ[Bin] Vec s) (v : Vec s), Function.Surjective P →
      ((Finset.univ : Finset (Vec k)).filter (fun x => P (x,q x) = v)).card ≤ n) :
    best q s ≤ n := by
  apply csSup_le'
  rintro _ ⟨P, v, hp, rfl⟩
  exact h P v hp

theorem best_total {k e s : Nat} (q : Vec k → Vec e) : best q s ≤ 2^k := by
  apply best_le
  intro P v hp
  simpa [Fintype.card_pi, ZMod.card] using
    (Finset.card_filter_le (Finset.univ : Finset (Vec k)) (fun x => P (x,q x) = v))

theorem le_best {k e s : Nat} (q : Vec k → Vec e)
    (P : (Vec k × Vec e) →ₗ[Bin] Vec s) (v : Vec s) (hp : Function.Surjective P) :
    ((Finset.univ : Finset (Vec k)).filter (fun x => P (x,q x) = v)).card ≤ best q s := by
  unfold best
  apply le_csSup
  swap
  · exact ⟨P, v, hp, rfl⟩
  refine ⟨Fintype.card (Vec k), ?_⟩
  rintro _ ⟨P, v, hp, rfl⟩
  exact Finset.card_le_univ _

theorem slice_eq {k e s : Nat} {D : Type} [AddCommGroup D] [Module Bin D]
    (q : Vec k → Vec e) (E : D →ₗ[Bin] (Vec k × Vec e)) (hin : Function.Injective E)
    (c : Vec k × Vec e) (P : (Vec k × Vec e) →ₗ[Bin] Vec s)
    (hker : LinearMap.ker P = LinearMap.range E) :
    count (fun z => (E z + c).2 = q (E z + c).1) =
    ((Finset.univ : Finset (Vec k)).filter (fun x => P (x,q x) = P c)).card := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  let f : {z : D // (E z + c).2 = q (E z + c).1} → {x : Vec k // P (x,q x) = P c} :=
    fun z => ⟨(E z.1 + c).1, by
      rw [← z.property]
      change P (E z.1 + c) = P c
      rw [map_add]
      have hz : E z.1 ∈ LinearMap.ker P := hker.symm ▸ LinearMap.mem_range_self E _
      rw [LinearMap.mem_ker.mp hz, zero_add]⟩
  apply Nat.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro x y h
    have hf : (E x.1 + c).1 = (E y.1 + c).1 := congrArg Subtype.val h
    apply Subtype.ext
    apply hin
    exact add_right_cancel (show E x.1 + c = E y.1 + c from
      Prod.ext hf (x.property.trans ((congrArg q hf).trans y.property.symm)))
  · rintro ⟨x,hx⟩
    have hm : (x,q x) - c ∈ LinearMap.ker P := by simp [LinearMap.mem_ker, hx]
    rw [hker] at hm
    obtain ⟨z,hz⟩ := hm
    have heq : E z + c = (x,q x) := by rw [hz, sub_add_cancel]
    refine ⟨⟨z, by rw [heq]⟩, Subtype.ext ?_⟩
    exact congrArg Prod.fst heq

theorem slice_le {k e s : Nat} {D : Type} [AddCommGroup D] [Module Bin D] [Module.Finite Bin D]
    (q : Vec k → Vec e) (E : D →ₗ[Bin] (Vec k × Vec e)) (hin : Function.Injective E)
    (c : Vec k × Vec e) (hd : Module.finrank Bin D + s = k + e) :
    count (fun z => (E z + c).2 = q (E z + c).1) ≤ best q s := by
  let R := LinearMap.range E
  have hdim := R.finrank_quotient_add_finrank
  have hr : Module.finrank Bin R = Module.finrank Bin D := LinearMap.finrank_range_of_inj hin
  rw [hr, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun] at hdim
  let iso := LinearEquiv.ofFinrankEq ((Vec k × Vec e) ⧸ R) (Vec s)
    (R := Bin) (by rw [Module.finrank_fin_fun]; omega)
  let P := iso.toLinearMap ∘ₗ R.mkQ
  rw [slice_eq q E hin c P (by simp [P, R, LinearMap.ker_comp])]
  exact le_best q P (P c) (iso.surjective.comp R.mkQ_surjective)

theorem best_le_slices {k e s n : Nat} (q : Vec k → Vec e)
    (h : ∀ (R : Submodule Bin (Vec k × Vec e)) (c : Vec k × Vec e),
      Module.finrank Bin R + s = k+e → count (fun z : R => (z.val + c).2 = q (z.val + c).1) ≤ n) :
    best q s ≤ n := by
  apply best_le
  intro P v hp
  obtain ⟨c, rfl⟩ := hp v
  rw [← slice_eq q (LinearMap.ker P).subtype Subtype.val_injective c P (by simp)]
  apply h
  have hr := P.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, Module.finrank_fin_fun, Module.finrank_prod,
    Module.finrank_fin_fun, Module.finrank_fin_fun] at hr
  omega

theorem max_slice {D C S : Type} [Finite C] [Finite S] [Nonempty C]
    (split : C × S ≃ D) (p : D → Prop) :
    ∃ c : C, count p ≤ Nat.card C * count (fun z : S => p (split (c,z))) := by
  classical
  letI := Fintype.ofFinite C
  let scores := fun c : C => count (fun z : S => p (split (c,z)))
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image Finset.univ scores Finset.univ_nonempty
  refine ⟨c, ?_⟩
  have he := split.subtypeEquiv (p := fun t => p (split t)) (q := p) (fun _ => Iff.rfl)
  calc count p = Nat.card (Σ c : C, {z : S // p (split (c,z))}) :=
        Nat.card_congr (he.symm.trans (Equiv.subtypeProdEquivSigmaSubtype (fun c z => p (split (c,z)))))
    _ = ∑ c : C, scores c := Nat.card_sigma
    _ ≤ ∑ _ : C, scores c := Finset.sum_le_sum (fun u hu => hc u hu)
    _ = _ := by simp [Nat.card_eq_fintype_card, scores]

theorem small_slice {D : Type} [AddCommGroup D] [Module Bin D] [Module.Finite Bin D]
    {W : Type} [AddCommGroup W] [Module Bin W] [Module.Finite Bin W]
    (G : D →ₗ[Bin] W) (n : Nat) (hn : n ≤ Module.finrank Bin (LinearMap.range G)) :
    ∃ S : Submodule Bin D, Module.finrank Bin S = n ∧ Function.Injective (G ∘ₗ S.subtype) := by
  obtain ⟨E, hin⟩ : ∃ E : Vec n →ₗ[Bin] LinearMap.range G, Function.Injective E :=
    finrank_le_iff_exists_linearMap.mp (by rwa [Module.finrank_fin_fun])
  obtain ⟨lift, h⟩ := G.rangeRestrict.exists_rightInverse_of_surjective G.range_rangeRestrict
  have hleft : Function.LeftInverse G.rangeRestrict lift := fun z => LinearMap.congr_fun h z
  let A := lift ∘ₗ E
  refine ⟨LinearMap.range A, (LinearMap.finrank_range_of_inj (f := A) (hleft.injective.comp hin)).trans
    (Module.finrank_fin_fun Bin), ?_⟩
  rintro ⟨_,x,rfl⟩ ⟨_,y,rfl⟩ hxy
  apply Subtype.ext
  apply congrArg lift
  have hx := hleft (E x)
  have hy := hleft (E y)
  exact hx.symm.trans ((Subtype.ext hxy).trans hy)

theorem split_dim {D : Type} [AddCommGroup D] [Module Bin D] [Module.Finite Bin D]
    {S C : Submodule Bin D} (h : IsCompl C S) :
    Module.finrank Bin C + Module.finrank Bin S = Module.finrank Bin D := by
  simpa only [Module.finrank_prod] using (C.prodEquivOfIsCompl S h).finrank_eq

theorem card_bin {D : Type} [AddCommGroup D] [Module Bin D] [Module.Finite Bin D] :
    Nat.card D = 2 ^ Module.finrank Bin D := by
  simpa [Nat.card_eq_fintype_card (α := Bin), ZMod.card] using
    (Module.natCard_eq_pow_finrank (K := Bin) (V := D))

theorem graph_transport {k e : Nat} (q : Vec k → Vec e) (M : Vec k →ₗ[Bin] Vec k)
    (a : Vec k) (L : Vec k →ₗ[Bin] Vec e) (b : Vec e) (z u c : Vec k × Vec e) :
    ((u+z)+c).2 = q (M ((u+z)+c).1 + a) + L ((u+z)+c).1 + b ↔
    (z.2 - L z.1) + (((u+c).2 - L (u+c).1) + -b) = q (M z.1 + (M (u+c).1+a)) := by
  rw [add_comm u z, add_assoc]
  simp only [Prod.fst_add, Prod.snd_add, map_add]
  rw [add_assoc (M z.1) (M u.1 + M c.1) a]
  constructor <;> intro he <;> apply sub_eq_zero.mp
  all_goals have hzero := sub_eq_zero.mpr he
  all_goals convert hzero using 1 <;> abel

set_option maxHeartbeats 1000000 in
theorem upper {k e s : Nat} (q : Vec k → Vec e) (M : Vec k →ₗ[Bin] Vec k)
    (a : Vec k) (L : Vec k →ₗ[Bin] Vec e) (b : Vec e) :
    let j := min (Module.finrank Bin (LinearMap.ker M)) (k+e-s)
    best (fun x => q (M x+a) + L x + b) s ≤ 2^j * best q (s+j) := by
  classical
  intro j
  apply best_le_slices
  intro R c hdim
  let X := LinearMap.fst Bin (Vec k) (Vec e)
  let Y := LinearMap.snd Bin (Vec k) (Vec e)
  let T := (M ∘ₗ X).prod (Y - L ∘ₗ X)
  let G := T ∘ₗ R.subtype
  have hker : Module.finrank Bin (LinearMap.ker G) ≤ Module.finrank Bin (LinearMap.ker M) := by
    let E : LinearMap.ker G →ₗ[Bin] LinearMap.ker M :=
      ((X ∘ₗ R.subtype ∘ₗ (LinearMap.ker G).subtype)).codRestrict _
        (fun z => congrArg Prod.fst (LinearMap.mem_ker.mp z.property))
    apply LinearMap.finrank_le_finrank_of_injective (f := E)
    intro x y hxy
    have hx : x.val.val.1 = y.val.val.1 := congrArg Subtype.val hxy
    have hrel (z : LinearMap.ker G) : z.val.val.2 - L z.val.val.1 = 0 :=
      congrArg Prod.snd (LinearMap.mem_ker.mp z.property)
    exact Subtype.ext (Subtype.ext (Prod.ext hx
      ((sub_eq_zero.mp (hrel x)).trans ((congrArg L hx).trans (sub_eq_zero.mp (hrel y)).symm))))
  have hnull := G.finrank_range_add_finrank_ker
  let d := Module.finrank Bin R
  obtain ⟨S,hs,hin⟩ := small_slice G (d-j) (by dsimp [d,j]; omega)
  obtain ⟨C,hC⟩ := Submodule.exists_isCompl S
  have hcDim := split_dim hC.symm
  have hj : j ≤ d := by dsimp only [d,j]; omega
  have hcard : Nat.card C = 2^j := by rw [card_bin]; congr 1; change _ + _ = d at hcDim; omega
  let p := fun z : R => (z.val+c).2 = q (M (z.val+c).1+a) + L (z.val+c).1 + b
  obtain ⟨u,hu⟩ := max_slice (C.prodEquivOfIsCompl S hC.symm).toEquiv p
  rw [hcard] at hu
  apply hu.trans (Nat.mul_le_mul_left _ ?_)
  let t := u.val.val + c
  let offset := T t + (a,-b)
  have hd' : Module.finrank Bin S + (s+j) = k+e := by change d + s = _ at hdim; omega
  have hb := slice_le (D := S) (s := s+j) q (G ∘ₗ S.subtype) hin offset hd'
  have same (z : S) : p ((C.prodEquivOfIsCompl S hC.symm) (u,z)) =
      (((G ∘ₗ S.subtype) z + offset).2 = q ((G ∘ₗ S.subtype) z + offset).1) :=
    propext (graph_transport q M a L b z.val.val u.val.val c)
  exact (congrArg count (funext same)).le.trans hb

set_option maxHeartbeats 1000000 in
theorem lift_slice {k e s : Nat} (q : Vec k → Vec e) (M : Vec k →ₗ[Bin] Vec k)
    (a : Vec k) (L : Vec k →ₗ[Bin] Vec e) (b : Vec e)
    {D C : Type} [AddCommGroup D] [Module Bin D] [Module.Finite Bin D]
    [AddCommGroup C] [Module Bin C] [Module.Finite Bin C]
    (Z : D →ₗ[Bin] (Vec k × Vec e)) (hz : Function.Injective Z)
    (lift : D →ₗ[Bin] Vec k) (hlift : ∀ z, M (lift z) = (Z z).1)
    (J : C →ₗ[Bin] LinearMap.ker M) (hj : Function.Injective J)
    (v : Vec k × Vec e) (B : Vec k →ₗ[Bin] Vec e)
    (hq : ∀ x, q (x + (v.1-a)) = q x + B x + (q (v.1-a) - q 0))
    (hd : Module.finrank Bin D + Module.finrank Bin C + s = k+e) :
    Nat.card C * count (fun z : D => (Z z + v).2 = q (Z z + v).1) ≤
      best (fun x => q (M x+a) + L x + b) s := by
  let U := LinearMap.fst Bin (Vec k) (Vec e) ∘ₗ Z
  let V := LinearMap.snd Bin (Vec k) (Vec e) ∘ₗ Z
  let X := lift.coprod ((LinearMap.ker M).subtype ∘ₗ J)
  let Y := (V - B ∘ₗ U) ∘ₗ LinearMap.fst Bin D C + L ∘ₗ X
  let E := X.prod Y
  have hM (z : D × C) : M (X z) = U z.1 := by
    change M (lift z.1 + (J z.2).val) = (Z z.1).1
    rw [map_add, hlift, LinearMap.mem_ker.mp (J z.2).property, add_zero]
  have hin : Function.Injective E := by
    intro t u h
    have hx : X t = X u := congrArg Prod.fst h
    have hy : V t.1 - B (U t.1) + L (X t) = V u.1 - B (U u.1) + L (X u) := congrArg Prod.snd h
    have hu : U t.1 = U u.1 := (hM t).symm.trans ((congrArg M hx).trans (hM u))
    rw [hu, hx] at hy
    have he : t.1 = u.1 := hz (Prod.ext hu (sub_left_inj.mp (add_right_cancel hy)))
    refine Prod.ext he (hj (Subtype.ext ?_))
    change lift t.1 + (J t.2).val = lift u.1 + (J u.2).val at hx
    rw [he] at hx
    exact add_left_cancel hx
  let offset : Vec k × Vec e := (0, v.2 - B a - (q (v.1-a) - q 0) + b)
  have hb := slice_le (s := s) (fun x => q (M x+a) + L x + b) E hin offset
    (by simpa only [Module.finrank_prod] using hd)
  let p := fun z : D => (Z z + v).2 = q (Z z + v).1
  have hcount : Nat.card C * count p = count (fun z : D × C => p z.1) := by
    rw [mul_comm, count, ← Nat.card_prod]
    exact Nat.card_congr Equiv.prodSubtypeFstEquivSubtypeProd.symm
  rw [hcount]
  apply le_trans _ hb
  apply Nat.le_of_eq
  apply congrArg count
  funext z
  apply propext
  have hrewrite := hq (U z.1 + a)
  have harg : U z.1 + a + (v.1-a) = U z.1 + v.1 := by abel
  rw [harg, map_add] at hrewrite
  change V z.1 + v.2 = q (U z.1 + v.1) ↔
    V z.1 - B (U z.1) + L (X z) + (v.2 - B a - (q (v.1-a) - q 0) + b) =
      q (M (X z + 0) + a) + L (X z + 0) + b
  rw [add_zero, hM, hrewrite]
  constructor <;> intro he <;> apply sub_eq_zero.mp
  all_goals have hzero := sub_eq_zero.mpr he
  all_goals convert hzero using 1 <;> abel

theorem embedding_of_dim {D C : Type} [AddCommGroup D] [Module Bin D] [Module.Finite Bin D]
    [AddCommGroup C] [Module Bin C] [Module.Finite Bin C]
    (hc : Module.finrank Bin D ≤ Module.finrank Bin C) :
    ∃ J : D →ₗ[Bin] C, Function.Injective J := finrank_le_iff_exists_linearMap.mp hc

set_option maxHeartbeats 1000000 in
theorem lower {k e s : Nat} (q : Vec k → Vec e) (M : Vec k →ₗ[Bin] Vec k)
    (a : Vec k) (L : Vec k →ₗ[Bin] Vec e) (b : Vec e)
    (hq : ∀ d : Vec k, ∃ B : Vec k →ₗ[Bin] Vec e, ∀ x, q (x+d) = q x+B x+(q d-q 0)) :
    best q s ≤ best (fun x => q (M x+a) + L x + b) s := by
  classical
  apply best_le_slices
  intro R c hdim
  let U := LinearMap.fst Bin (Vec k) (Vec e) ∘ₗ R.subtype
  let G := (LinearMap.range M).mkQ ∘ₗ U
  let S := LinearMap.ker G
  obtain ⟨C,hC⟩ := S.exists_isCompl
  have hsum := split_dim hC.symm
  have hr := G.finrank_range_add_finrank_ker
  have hmn := M.finrank_range_add_finrank_ker
  have hqrank := (LinearMap.range M).finrank_quotient_add_finrank
  have hsmall := Submodule.finrank_le (LinearMap.range G)
  have hc : Module.finrank Bin C ≤ Module.finrank Bin (LinearMap.ker M) := by
    change _ + Module.finrank Bin S = _ at hr
    omega
  obtain ⟨J,hj⟩ : ∃ J : C →ₗ[Bin] LinearMap.ker M, Function.Injective J :=
    embedding_of_dim (D := C) (C := LinearMap.ker M) hc
  let p := fun z : R => (z.val+c).2 = q (z.val+c).1
  obtain ⟨u,hu⟩ := max_slice (C.prodEquivOfIsCompl S hC.symm).toEquiv p
  apply hu.trans
  let Z := R.subtype ∘ₗ S.subtype
  let A : S →ₗ[Bin] LinearMap.range M := (U ∘ₗ S.subtype).codRestrict _
    (fun z => (Submodule.Quotient.mk_eq_zero _).mp (LinearMap.mem_ker.mp z.property))
  obtain ⟨r,hright⟩ := M.rangeRestrict.exists_rightInverse_of_surjective M.range_rangeRestrict
  let v := u.val.val + c
  obtain ⟨B,hB⟩ := hq (v.1-a)
  have hlift (z : S) : M ((r ∘ₗ A) z) = (Z z).1 := congrArg Subtype.val (LinearMap.congr_fun hright (A z))
  have hdim' : Module.finrank Bin S + Module.finrank Bin C + s = k+e := by omega
  have hb := lift_slice (s := s) (D := S) (C := C) q M a L b Z (Subtype.val_injective.comp Subtype.val_injective)
    (r ∘ₗ A) hlift J hj v B hB hdim'
  apply le_trans _ hb
  apply Nat.mul_le_mul_left
  apply Nat.le_of_eq
  apply congrArg count
  funext z
  change (((u.val.val + z.val.val) + c).2 = q ((u.val.val + z.val.val) + c).1) =
    ((z.val.val + (u.val.val + c)).2 = q (z.val.val + (u.val.val + c)).1)
  rw [add_comm u.val.val z.val.val, add_assoc]

end PEqualNP.Outside.L_lib_878

theorem PEqualNP.Outside.L_lib_878 : (∀ (k e : Nat),
  let F := ZMod 2
  let U := Fin k → F
  let V := Fin e → F
  let best := fun (φ : U → V) (s : Nat) =>
    sSup {n : Nat | ∃ (P : (U × V) →ₗ[F] (Fin s → F)) (v : Fin s → F),
      Function.Surjective P ∧ n = ((Finset.univ : Finset U).filter
        (fun x => P (x,φ x) = v)).card}
  ∀ q : U → V,
    (∀ d : U, ∃ B : U →ₗ[F] V, ∀ x : U, q (x+d) = q x + B x + (q d - q 0)) →
    ∀ (M : U →ₗ[F] U) (a : U) (L : U →ₗ[F] V) (b : V) (s : Nat),
      s ≤ k+e →
      let h := Module.finrank F (LinearMap.ker M)
      let j := min h (k+e-s)
      let physical := fun x : U => q (M x+a) + L x + b
      best q s ≤ best physical s ∧
        best physical s ≤ min (2^k) (2^j * best q (s+j))) := by
  intro k e
  dsimp only
  intro q hq M a L b s hs
  exact ⟨PEqualNP.Outside.L_lib_878.lower q M a L b hq, le_min (PEqualNP.Outside.L_lib_878.best_total _)
    (PEqualNP.Outside.L_lib_878.upper q M a L b)⟩
