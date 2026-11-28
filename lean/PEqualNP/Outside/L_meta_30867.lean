import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30867

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
  let := Fintype.ofFinite C
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
  all_goals (convert hzero using 1; abel)

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
  all_goals (convert hzero using 1; abel)

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

def ix {k : ℕ} (hk : 0 < k) (pos : ℕ) : Fin k := ⟨pos % k, Nat.mod_lt _ hk⟩

lemma ix_eq_iff {k : ℕ} (hk : 0 < k) (a b : ℕ) : ix hk a = ix hk b ↔ a % k = b % k := by
  simp [ix, Fin.ext_iff]

lemma ix_add_k {k : ℕ} (hk : 0 < k) (a : ℕ) : ix hk (a + k) = ix hk a := by
  rw [ix_eq_iff, Nat.add_mod_right]

lemma ix_self {k : ℕ} (hk : 0 < k) (a : Fin k) : ix hk a.val = a := by
  ext
  exact Nat.mod_eq_of_lt a.2

lemma ix_val_add {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ix hk ((ix hk a).val + b) = ix hk (a + b) := by
  rw [ix_eq_iff]
  simp only [ix]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ix_add_sub_mod {k : ℕ} (hk : 0 < k) (a s : ℕ) :
    ix hk ((ix hk a).val + k - s % k) = ix hk (a + (k - s % k)) := by
  have hs : s % k < k := Nat.mod_lt _ hk
  have h1 : (ix hk a).val + k - s % k = (ix hk a).val + (k - s % k) := by omega
  rw [h1, ix_val_add]

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

lemma zmod2_sum_three_cancel (a b : ZMod 2) : a + b + (a + b) = 0 := by
  fin_cases a <;> fin_cases b <;> decide

def rotLin {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  { toFun := fun w j => w (ix hk (j.val + k - s % k))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

lemma rotLin_bijective {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Function.Bijective (rotLin hk s) := by
  let inv : (Fin k → ZMod 2) → (Fin k → ZMod 2) := fun w j => w (ix hk (j.val + s % k))
  have hs : s % k < k := Nat.mod_lt _ hk
  have h1 : ∀ w, inv (rotLin hk s w) = w := by
    intro w
    ext j
    simp only [inv, rotLin, LinearMap.coe_mk, AddHom.coe_mk]
    have hidx : ix hk ((ix hk (j.val + s % k)).val + k - s % k) = j := by
      rw [ix_add_sub_mod hk (j.val + s % k) s]
      have heq : j.val + s % k + (k - s % k) = j.val + k := by omega
      rw [heq, ix_add_k, ix_self]
    rw [hidx]
  have h2 : ∀ w, rotLin hk s (inv w) = w := by
    intro w
    ext j
    simp only [inv, rotLin, LinearMap.coe_mk, AddHom.coe_mk]
    have hidx : ix hk ((ix hk (j.val + k - s % k)).val + s % k) = j := by
      rw [ix_val_add]
      have heq : j.val + k - s % k + s % k = j.val + k := by omega
      rw [heq, ix_add_k, ix_self]
    rw [hidx]
  exact Function.bijective_iff_has_inverse.mpr ⟨inv, h1, h2⟩

def mixLin {k : ℕ} (hk : 0 < k) (d : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  { toFun := fun z m => z m + z (ix hk (m.val + d)) + z (ix hk (m.val + k - d % k))
    map_add' := fun x y => by ext m; simp only [Pi.add_apply]; ring
    map_smul' := fun c x => by ext m; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

def orb {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) : Fin k :=
  ix hk (r.val + t * d)

lemma orb_add_one {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) :
    ix hk ((orb hk d r t).val + d) = orb hk d r (t + 1) := by
  simp only [orb, ix_val_add]
  congr 1; ring

lemma orb_sub_one {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) :
    ix hk ((orb hk d r (t + 1)).val + k - d % k) = orb hk d r t := by
  simp only [orb, ix_add_sub_mod]
  rw [ix_eq_iff]
  have hd : d % k < k := Nat.mod_lt _ hk
  have htd : (t + 1) * d = t * d + d := by ring
  have h1 : r.val + (t + 1) * d + (k - d % k) = (r.val + t * d) + (d + k - d % k) := by
    rw [htd]; omega
  rw [h1, Nat.add_mod]
  have h2 : (d + k - d % k) % k = 0 := by
    have hdiv := Nat.div_add_mod d k
    have hmul : (d / k + 1) * k = k * (d / k) + k := by ring
    have h3 : d + k - d % k = (d / k + 1) * k := by rw [hmul]; omega
    rw [h3, Nat.mul_mod_left]
  rw [h2, Nat.add_zero, Nat.mod_mod]

lemma orb_period {k : ℕ} (hk : 0 < k) (d : ℕ) (r : Fin (Nat.gcd k d)) (t : ℕ) :
    orb hk d r (t + k / Nat.gcd k d) = orb hk d r t := by
  simp only [orb, ix_eq_iff]
  have hg0 : 0 < Nat.gcd k d := Nat.gcd_pos_of_pos_left d hk
  have h1k : Nat.gcd k d * (k / Nat.gcd k d) = k := Nat.mul_div_cancel' (Nat.gcd_dvd_left k d)
  have h1d : Nat.gcd k d * (d / Nat.gcd k d) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_right k d)
  have hmul : (k / Nat.gcd k d) * d = k * (d / Nat.gcd k d) := by
    apply Nat.eq_of_mul_eq_mul_left hg0
    calc
      Nat.gcd k d * ((k / Nat.gcd k d) * d) = (Nat.gcd k d * (k / Nat.gcd k d)) * d := by ring
      _ = k * d := by rw [h1k]
      _ = k * (Nat.gcd k d * (d / Nat.gcd k d)) := by rw [h1d]
      _ = Nat.gcd k d * (k * (d / Nat.gcd k d)) := by ring
  have h1 : r.val + (t + k / Nat.gcd k d) * d = (r.val + t * d) + k * (d / Nat.gcd k d) := by
    rw [Nat.add_mul, hmul]; ring
  rw [h1, Nat.add_mul_mod_self_left]

lemma orb_bijective {k : ℕ} (hk : 0 < k) (d : ℕ) :
    Function.Bijective (fun p : Fin (Nat.gcd k d) × Fin (k / Nat.gcd k d) =>
      orb hk d p.1 p.2.val) := by
  have hg_pos : 0 < Nat.gcd k d := Nat.gcd_pos_of_pos_left d hk
  have hg_dvd_k : Nat.gcd k d ∣ k := Nat.gcd_dvd_left k d
  have hg_dvd_d : Nat.gcd k d ∣ d := Nat.gcd_dvd_right k d
  have hk_eq : Nat.gcd k d * (k / Nat.gcd k d) = k := Nat.mul_div_cancel' hg_dvd_k
  have hd_eq : Nat.gcd k d * (d / Nat.gcd k d) = d := Nat.mul_div_cancel' hg_dvd_d
  have hcop : Nat.Coprime (k / Nat.gcd k d) (d / Nat.gcd k d) :=
    Nat.coprime_div_gcd_div_gcd hg_pos
  have hcard : Fintype.card (Fin (Nat.gcd k d) × Fin (k / Nat.gcd k d)) = Fintype.card (Fin k) := by
    simp [hk_eq]
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, hcard⟩
  intro ⟨r1, t1⟩ ⟨r2, t2⟩ heq
  simp only [orb, ix_eq_iff] at heq
  have hr_eq : r1 = r2 := by
    have hmod_g : ∀ a, (a % k) % Nat.gcd k d = a % Nat.gcd k d := fun a =>
      Nat.mod_mod_of_dvd a hg_dvd_k
    have h1 := congrArg (fun x => x % Nat.gcd k d) heq
    rw [hmod_g, hmod_g] at h1
    have hmul_g : ∀ t, (t * d) % Nat.gcd k d = 0 := fun t =>
      Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hg_dvd_d t)
    rw [Nat.add_mod, hmul_g, Nat.add_zero, Nat.mod_mod,
      Nat.add_mod, hmul_g, Nat.add_zero, Nat.mod_mod,
      Nat.mod_eq_of_lt r1.2, Nat.mod_eq_of_lt r2.2] at h1
    exact Fin.ext h1
  subst hr_eq
  have ht_eq : t1 = t2 := by
    have haux : ∀ a b : Fin (k / Nat.gcd k d), a.val ≤ b.val →
        (r1.val + a.val * d) % k = (r1.val + b.val * d) % k → a = b := by
      intro a b hab hmod
      have hdvd : k ∣ (r1.val + b.val * d) - (r1.val + a.val * d) := by
        exact (Nat.modEq_iff_dvd' (by nlinarith)).mp hmod
      have hsub : (r1.val + b.val * d) - (r1.val + a.val * d) = (b.val - a.val) * d := by
        rw [Nat.add_sub_add_left, ← Nat.sub_mul]
      have hdvd' : (Nat.gcd k d * (k / Nat.gcd k d)) ∣
          (b.val - a.val) * (Nat.gcd k d * (d / Nat.gcd k d)) := by
        rwa [hk_eq, hd_eq, ← hsub]
      have hdvd2 : (k / Nat.gcd k d) ∣ (b.val - a.val) * (d / Nat.gcd k d) := by
        have hrew : (b.val - a.val) * (Nat.gcd k d * (d / Nat.gcd k d)) =
            Nat.gcd k d * ((b.val - a.val) * (d / Nat.gcd k d)) := by ring
        rw [hrew] at hdvd'
        exact (mul_dvd_mul_iff_left (ne_of_gt hg_pos)).mp hdvd'
      have hdvd3 : (k / Nat.gcd k d) ∣ (b.val - a.val) := hcop.dvd_of_dvd_mul_right hdvd2
      have hlt : b.val - a.val < k / Nat.gcd k d := by omega
      have h0 : b.val - a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd3 hlt
      ext; omega
    by_cases hle : t1.val ≤ t2.val
    · exact haux t1 t2 hle heq
    · exact (haux t2 t1 (by omega) heq.symm).symm
  subst ht_eq
  rfl

lemma ker_seq_period3 {k : ℕ} (hk : 0 < k) (d : ℕ)
    (z : Fin k → ZMod 2) (hz : mixLin hk d z = 0)
    (r : Fin (Nat.gcd k d)) (t : ℕ) :
    z (orb hk d r t) =
      if t % 3 = 0 then z (orb hk d r 0)
      else if t % 3 = 1 then z (orb hk d r 1)
      else z (orb hk d r 0) + z (orb hk d r 1) := by
  have hstep : ∀ n : ℕ, z (orb hk d r (n + 2)) = z (orb hk d r (n + 1)) + z (orb hk d r n) := by
    intro n
    have h0 := congrFun hz (orb hk d r (n + 1))
    simp only [mixLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
    rw [orb_add_one hk d r (n + 1), orb_sub_one hk d r n] at h0
    have h1 := congrArg (fun x => x + z (orb hk d r (n + 2))) h0
    simp only [zero_add] at h1
    have hlhs : z (orb hk d r (n + 1)) + z (orb hk d r (n + 2)) + z (orb hk d r n) +
        z (orb hk d r (n + 2)) = z (orb hk d r (n + 1)) + z (orb hk d r n) := by
      have hz2 := zmod2_add_self (z (orb hk d r (n + 2)))
      calc
        z (orb hk d r (n + 1)) + z (orb hk d r (n + 2)) + z (orb hk d r n) +
            z (orb hk d r (n + 2))
            = z (orb hk d r (n + 1)) + z (orb hk d r n) +
              (z (orb hk d r (n + 2)) + z (orb hk d r (n + 2))) := by ring
        _ = z (orb hk d r (n + 1)) + z (orb hk d r n) := by rw [hz2, add_zero]
    rw [hlhs] at h1
    exact h1.symm
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    match t with
    | 0 => simp
    | 1 => simp
    | n + 2 =>
      rw [hstep n, ih (n + 1) (by omega), ih n (by omega)]
      have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases hmod with h0 | h1 | h2
      · have h1' : (n + 1) % 3 = 1 := by omega
        have h2' : (n + 2) % 3 = 2 := by omega
        simp only [h0, h1', h2', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one]
        ring
      · have h1' : (n + 1) % 3 = 2 := by omega
        have h2' : (n + 2) % 3 = 0 := by omega
        simp only [h1, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_add_self (z (orb hk d r 1))
        calc
          z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 1)
              = z (orb hk d r 0) + (z (orb hk d r 1) + z (orb hk d r 1)) := by ring
          _ = z (orb hk d r 0) := by rw [this, add_zero]
      · have h1' : (n + 1) % 3 = 0 := by omega
        have h2' : (n + 2) % 3 = 1 := by omega
        simp only [h2, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_add_self (z (orb hk d r 0))
        calc
          z (orb hk d r 0) + (z (orb hk d r 0) + z (orb hk d r 1))
              = (z (orb hk d r 0) + z (orb hk d r 0)) + z (orb hk d r 1) := by ring
          _ = z (orb hk d r 1) := by rw [this, zero_add]

lemma finrank_ker_mixLin {k : ℕ} (hk : 0 < k) (d : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.ker (mixLin hk d)) =
      if 3 ∣ k / Nat.gcd k d then 2 * Nat.gcd k d else 0 := by
  let g := Nat.gcd k d
  let L := k / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hk
  have hg_dvd_k : g ∣ k := Nat.gcd_dvd_left k d
  have hL_pos : 0 < L := Nat.div_pos (Nat.le_of_dvd hk hg_dvd_k) hg_pos
  let e : (Fin g × Fin L) ≃ Fin k := Equiv.ofBijective _ (orb_bijective hk d)
  split_ifs with hsing
  · have hL3 : 3 ≤ L := Nat.le_of_dvd hL_pos hsing
    let mkVec : (Fin g × Fin 2 → ZMod 2) → (Fin k → ZMod 2) := fun a v =>
      let p := e.symm v
      if p.2.val % 3 = 0 then a (p.1, 0)
      else if p.2.val % 3 = 1 then a (p.1, 1)
      else a (p.1, 0) + a (p.1, 1)
    have hmk_orb : ∀ a (r : Fin g) (t : ℕ),
        mkVec a (orb hk d r t) =
          if t % 3 = 0 then a (r, 0)
          else if t % 3 = 1 then a (r, 1)
          else a (r, 0) + a (r, 1) := by
      intro a r t
      have hdiv : t = (t / L) * L + t % L := (Nat.div_add_mod' t L).symm
      have horb_mod : orb hk d r t = orb hk d r (t % L) := by
        have hstep : ∀ q : ℕ, orb hk d r (q * L + t % L) = orb hk d r (t % L) := by
          intro q
          induction q with
          | zero => simp
          | succ q ih =>
            rw [show (q + 1) * L + t % L = (q * L + t % L) + L by ring, orb_period, ih]
        conv_lhs => rw [hdiv]
        exact hstep (t / L)
      have he_symm : e.symm (orb hk d r (t % L)) = (r, ⟨t % L, Nat.mod_lt _ hL_pos⟩) := by
        apply e.injective
        rw [Equiv.apply_symm_apply]
        rfl
      have hmod3 : (t % L) % 3 = t % 3 := Nat.mod_mod_of_dvd t hsing
      simp only [mkVec, horb_mod, he_symm, hmod3]
    have hmk_ker : ∀ a, mixLin hk d (mkVec a) = 0 := by
      intro a
      ext v
      have hv : v = orb hk d (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
      let r := (e.symm v).1
      let t := (e.symm v).2.val
      have hv_eq : v = orb hk d r (t + L) := by
        rw [orb_period]; exact hv
      simp only [mixLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      rw [hv_eq, orb_add_one, show t + L = (t + L - 1) + 1 by omega, orb_sub_one]
      rw [hmk_orb, hmk_orb, hmk_orb]
      have hmod : (t + L - 1) % 3 = 0 ∨ (t + L - 1) % 3 = 1 ∨ (t + L - 1) % 3 = 2 := by omega
      rcases hmod with h0 | h1 | h2
      · have h1' : (t + L - 1 + 1) % 3 = 1 := by omega
        have h2' : (t + L - 1 + 1 + 1) % 3 = 2 := by omega
        simp only [h0, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_sum_three_cancel (a (r, 0)) (a (r, 1))
        calc
          a (r, 1) + (a (r, 0) + a (r, 1)) + a (r, 0)
              = a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) := by ring
          _ = 0 := this
      · have h1' : (t + L - 1 + 1) % 3 = 2 := by omega
        have h2' : (t + L - 1 + 1 + 1) % 3 = 0 := by omega
        simp only [h1, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        have := zmod2_sum_three_cancel (a (r, 0)) (a (r, 1))
        calc
          a (r, 0) + a (r, 1) + a (r, 0) + a (r, 1)
              = a (r, 0) + a (r, 1) + (a (r, 0) + a (r, 1)) := by ring
          _ = 0 := this
      · have h1' : (t + L - 1 + 1) % 3 = 0 := by omega
        have h2' : (t + L - 1 + 1 + 1) % 3 = 1 := by omega
        simp only [h2, h1', h2', ↓reduceIte, OfNat.ofNat_ne_zero,
          OfNat.ofNat_ne_one, Nat.one_ne_zero]
        exact zmod2_sum_three_cancel (a (r, 0)) (a (r, 1))
    let Ψ : (Fin g × Fin 2 → ZMod 2) →ₗ[ZMod 2] LinearMap.ker (mixLin hk d) :=
      { toFun := fun a => ⟨mkVec a, hmk_ker a⟩
        map_add' := fun a1 a2 => by
          apply Subtype.ext; ext v; simp only [mkVec, Submodule.coe_add, Pi.add_apply]
          split_ifs <;> ring
        map_smul' := fun c a => by
          apply Subtype.ext; ext v
          simp only [mkVec, SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          split_ifs <;> ring }
    have hΨ_bij : Function.Bijective Ψ := by
      constructor
      · intro a1 a2 heq
        have hval : mkVec a1 = mkVec a2 := congrArg Subtype.val heq
        ext ⟨r, c⟩
        fin_cases c
        · have h0 := congrFun hval (orb hk d r 0)
          simpa [hmk_orb] using h0
        · have h1 := congrFun hval (orb hk d r 1)
          simpa [hmk_orb] using h1
      · rintro ⟨z, hz⟩
        let a : Fin g × Fin 2 → ZMod 2 := fun rc =>
          if rc.2.val = 0 then z (orb hk d rc.1 0) else z (orb hk d rc.1 1)
        refine ⟨a, ?_⟩
        apply Subtype.ext
        ext v
        have hv : v = orb hk d (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
        conv_lhs => rw [hv]
        conv_rhs => rw [hv]
        change mkVec a (orb hk d (e.symm v).1 (e.symm v).2.val) =
          z (orb hk d (e.symm v).1 (e.symm v).2.val)
        rw [hmk_orb, ker_seq_period3 hk d z hz]
        simp [a]
    have hequiv := LinearEquiv.ofBijective Ψ hΨ_bij
    rw [← hequiv.finrank_eq]
    simp [g, Nat.mul_comm]
  · have hker_bot : LinearMap.ker (mixLin hk d) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro z hz
      ext v
      have hv : v = orb hk d (e.symm v).1 (e.symm v).2.val := (e.apply_symm_apply v).symm
      rw [hv]
      let r := (e.symm v).1
      have h0 : z (orb hk d r L) = z (orb hk d r 0) := by
        simpa using congrArg z (orb_period hk d r 0)
      have h1 : z (orb hk d r (L + 1)) = z (orb hk d r 1) := by
        have hp := orb_period hk d r 1
        rw [show 1 + L = L + 1 by omega] at hp
        exact congrArg z hp
      rw [ker_seq_period3 hk d z hz r L] at h0
      rw [ker_seq_period3 hk d z hz r (L + 1)] at h1
      have hmod : L % 3 = 1 ∨ L % 3 = 2 := by
        have hne : L % 3 ≠ 0 := fun h => hsing (Nat.dvd_of_mod_eq_zero h)
        omega
      have hzero01 : z (orb hk d r 0) = 0 ∧ z (orb hk d r 1) = 0 := by
        rcases hmod with hm1 | hm2
        · have hm1' : (L + 1) % 3 = 2 := by omega
          simp only [hm1, hm1', ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero,
            OfNat.ofNat_ne_one] at h0 h1
          have hz0 : z (orb hk d r 0) = 0 := by
            have := congrArg (fun x => x + z (orb hk d r 1)) h1
            have hrhs : z (orb hk d r 1) + z (orb hk d r 1) = 0 := zmod2_add_self _
            have hlhs : z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 1) =
                z (orb hk d r 0) := by
              rw [add_assoc, hrhs, add_zero]
            rw [hlhs, hrhs] at this
            exact this
          exact ⟨hz0, by rw [h0, hz0]⟩
        · have hm2' : (L + 1) % 3 = 0 := by omega
          simp only [hm2, hm2', ↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one] at h0 h1
          have hz1 : z (orb hk d r 1) = 0 := by
            have := congrArg (fun x => x + z (orb hk d r 0)) h0
            have hrhs : z (orb hk d r 0) + z (orb hk d r 0) = 0 := zmod2_add_self _
            have hlhs : z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 0) =
                z (orb hk d r 1) := by
              calc
                z (orb hk d r 0) + z (orb hk d r 1) + z (orb hk d r 0)
                    = (z (orb hk d r 0) + z (orb hk d r 0)) + z (orb hk d r 1) := by ring
                _ = z (orb hk d r 1) := by rw [hrhs, zero_add]
            rw [hlhs, hrhs] at this
            exact this
          exact ⟨by rw [h1, hz1], hz1⟩
      rw [ker_seq_period3 hk d z hz r (e.symm v).2.val, hzero01.1, hzero01.2]
      simp
    rw [hker_bot]
    simp

end PEqualNP.Outside.L_meta_30867

namespace PEqualNP.Outside.L_meta_30867
open Finset

def mon {k : ℕ} (S : Finset (Fin k)) : Vec k → Bin := fun y => ∏ i ∈ S, y i

def wt {k : ℕ} (S : Finset (Fin k)) : ℕ := ∑ i ∈ S, (2 ^ k + 2 ^ i.val)

lemma mon_apply {k : ℕ} (S : Finset (Fin k)) (y : Vec k) :
    mon S y = if ∀ i ∈ S, y i = 1 then 1 else 0 := by
  unfold mon
  split_ifs with h
  · exact Finset.prod_eq_one h
  · push Not at h
    obtain ⟨i, hi, hne⟩ := h
    exact Finset.prod_eq_zero hi (by_contra fun h0 => hne (zmod2_eq_one_of_ne_zero h0))

lemma mon_union {k : ℕ} (S T : Finset (Fin k)) : mon (S ∪ T) = mon S * mon T := by
  funext y
  simp only [Pi.mul_apply, mon_apply, Finset.forall_mem_union]
  split_ifs <;> simp_all

lemma wt_union_le {k : ℕ} (S T : Finset (Fin k)) : wt (S ∪ T) ≤ wt S + wt T := by
  have h := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := fun i : Fin k => 2 ^ k + 2 ^ i.val)
  unfold wt
  omega

lemma wt_sdiff {k : ℕ} {G S : Finset (Fin k)} (h : G ⊆ S) : wt (S \ G) + wt G = wt S :=
  Finset.sum_sdiff h

def low {k : ℕ} (w : ℕ) : Submodule Bin (Vec k → Bin) :=
  Submodule.span Bin (mon '' {T | wt T < w})

lemma mon_mem_low {k : ℕ} {T : Finset (Fin k)} {w : ℕ} (h : wt T < w) : mon T ∈ low w :=
  Submodule.subset_span ⟨T, h, rfl⟩

lemma low_mono {k : ℕ} {w w' : ℕ} (h : w ≤ w') :
    (low w : Submodule Bin (Vec k → Bin)) ≤ low w' :=
  Submodule.span_mono (Set.image_mono fun _ hT => lt_of_lt_of_le hT h)

lemma mul_mem_low {k : ℕ} (S : Finset (Fin k)) {w : ℕ} {f : Vec k → Bin} (hf : f ∈ low w) :
    mon S * f ∈ low (wt S + w) :=
  (Submodule.map_span_le (LinearMap.mulLeft Bin (mon S)) _ (low (wt S + w))).2 (by
    rintro _ ⟨T, hT, rfl⟩
    rw [LinearMap.mulLeft_apply, ← mon_union]
    exact mon_mem_low (lt_of_le_of_lt (wt_union_le S T) (Nat.add_lt_add_left hT _)))
    (Submodule.mem_map_of_mem hf)

lemma mem_span_mon {k : ℕ} (f : Vec k → Bin) :
    f ∈ Submodule.span Bin (Set.range (mon (k := k))) := by
  have hmul : ∀ (S : Finset (Fin k)) (g : Vec k → Bin),
      g ∈ Submodule.span Bin (Set.range (mon (k := k))) →
      mon S * g ∈ Submodule.span Bin (Set.range (mon (k := k))) := fun S g hg =>
    (Submodule.map_span_le (LinearMap.mulLeft Bin (mon S)) _ _).2 (by
      rintro _ ⟨T, rfl⟩
      rw [LinearMap.mulLeft_apply, ← mon_union]
      exact Submodule.subset_span ⟨_, rfl⟩) (Submodule.mem_map_of_mem hg)
  have hprod : ∀ (a : Vec k) (I : Finset (Fin k)),
      ∏ i ∈ I, (mon {i} + (a i + 1) • (1 : Vec k → Bin)) ∈
        Submodule.span Bin (Set.range (mon (k := k))) := by
    intro a I
    induction I using Finset.induction_on with
    | empty => exact Submodule.subset_span ⟨∅, by funext y; simp [mon]⟩
    | insert i I hi ih =>
      rw [Finset.prod_insert hi, add_mul, smul_mul_assoc, one_mul]
      exact add_mem (hmul _ _ ih) (Submodule.smul_mem _ _ ih)
  have h1 : ∀ x : Bin, x + (x + 1) = 1 := by decide
  have h0 : ∀ x y : Bin, x ≠ y → x + (y + 1) = 0 := by decide
  have hf : f = ∑ a : Vec k, f a • ∏ i, (mon {i} + (a i + 1) • (1 : Vec k → Bin)) := by
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, Pi.add_apply, Pi.one_apply,
      smul_eq_mul, mul_one, mon, Finset.prod_singleton]
    rw [Finset.sum_eq_single y]
    · rw [Finset.prod_eq_one (fun i _ => h1 (y i)), mul_one]
    · intro a _ hay
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hay
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (h0 _ _ (Ne.symm hi)), mul_zero]
    · exact fun h => absurd (Finset.mem_univ y) h
  rw [hf]
  exact sum_mem fun a _ => Submodule.smul_mem _ _ (hprod a univ)

def res {k : ℕ} (Z : Finset (Vec k)) : (Vec k → Bin) →ₗ[Bin] (Z → Bin) :=
  LinearMap.funLeft Bin Bin (fun z : Z => (z : Vec k))

lemma res_mon_mem {k : ℕ} (Z : Finset (Vec k)) (LT : Finset (Finset (Fin k)))
    (h : ∀ G ∈ LT, ∃ f ∈ low (wt G), ∀ y ∈ Z, mon G y = f y) (n : ℕ) :
    ∀ S : Finset (Fin k), wt S < n → res Z (mon S) ∈
      Submodule.span Bin ((fun T => res Z (mon T)) '' {T | ∀ G ∈ LT, ¬ G ⊆ T}) := by
  induction n with
  | zero => exact fun S hS => absurd hS (Nat.not_lt_zero _)
  | succ n ih =>
    intro S hS
    by_cases hstd : ∀ G ∈ LT, ¬ G ⊆ S
    · exact Submodule.subset_span ⟨S, hstd, rfl⟩
    · push Not at hstd
      obtain ⟨G, hG, hGS⟩ := hstd
      obtain ⟨f, hf, hZ⟩ := h G hG
      have hres : res Z (mon S) = res Z (mon (S \ G) * f) := by
        ext z
        have hS' : mon S = mon (S \ G) * mon G := by
          rw [← mon_union, Finset.sdiff_union_of_subset hGS]
        simp only [res, LinearMap.funLeft_apply, hS', Pi.mul_apply, hZ z.1 z.2]
      have hlow : mon (S \ G) * f ∈ low (wt S) := by
        rw [← wt_sdiff hGS]
        exact mul_mem_low _ hf
      have hle : (low (wt S) : Submodule Bin (Vec k → Bin)) ≤ (Submodule.span Bin
          ((fun T => res Z (mon T)) '' {T | ∀ G ∈ LT, ¬ G ⊆ T})).comap (res Z) :=
        Submodule.span_le.2 (by
          rintro _ ⟨T, hT, rfl⟩
          exact ih T (lt_of_lt_of_le hT (Nat.lt_succ_iff.1 hS)))
      rw [hres]
      exact hle hlow

theorem footprint {k : ℕ} (Z : Finset (Vec k)) (LT : Finset (Finset (Fin k)))
    (h : ∀ G ∈ LT, ∃ f ∈ low (wt G), ∀ y ∈ Z, mon G y = f y) :
    Z.card ≤ (univ.filter fun T : Finset (Fin k) => ∀ G ∈ LT, ¬ G ⊆ T).card := by
  classical
  have htop : Submodule.span Bin
      ((fun T => res Z (mon T)) '' {T : Finset (Fin k) | ∀ G ∈ LT, ¬ G ⊆ T}) = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : g = res Z (fun y => if hy : y ∈ Z then g ⟨y, hy⟩ else 0) := by
      ext z
      simp [res, LinearMap.funLeft_apply]
    have hle : Submodule.span Bin (Set.range (mon (k := k))) ≤ (Submodule.span Bin
        ((fun T => res Z (mon T)) '' {T | ∀ G ∈ LT, ¬ G ⊆ T})).comap (res Z) :=
      Submodule.span_le.2 (by
        rintro _ ⟨S, rfl⟩
        exact res_mon_mem Z LT h (wt S + 1) S (Nat.lt_succ_self _))
    rw [hg]
    exact hle (mem_span_mon _)
  have h1 := finrank_span_finset_le_card (R := Bin)
    ((univ.filter fun T : Finset (Fin k) => ∀ G ∈ LT, ¬ G ⊆ T).image fun T => res Z (mon T))
  have hset : {T : Finset (Fin k) | T ∈ univ ∧ ∀ G ∈ LT, ¬ G ⊆ T} = {T | ∀ G ∈ LT, ¬ G ⊆ T} := by
    ext T
    simp
  rw [Set.finrank, Finset.coe_image, Finset.coe_filter, hset, htop, finrank_top,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h1
  exact h1.trans Finset.card_image_le

end PEqualNP.Outside.L_meta_30867

namespace PEqualNP.Outside.L_meta_30867

def base (k t : ℕ) : ℕ :=
  if k = 1 then min 2 (2^(2-t))
  else if k = 2 then min 4 (5-t)
  else if t < k then 2^(k-t-1) * Nat.fib (t+3)
  else if t = k then Nat.fib (k-1) + Nat.fib (k+1)
  else if 2*(t-k) < k then 2^(t-k-1) * Nat.fib (k-2*(t-k)+3) else 2^(k-(t-k))

def indep {k : ℕ} (hk : 0 < k) (A E : Finset (Fin k)) : Finset (Fin k → ZMod 2) :=
  Finset.univ.filter fun y => (∀ a ∈ A, y a = 0) ∧ ∀ i ∈ E, y i * y (ix hk (i.val + 1)) = 0

open Finset Nat

def run (a e : ℕ → Prop) [DecidablePred a] [DecidablePred e] : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => s
  | n + 1, s => ((run a e n s).1 + (run a e n s).2,
      if a (n + 1) then 0 else (run a e n s).1 + if e n then 0 else (run a e n s).2)

def crun {k : ℕ} (hk : 0 < k) (A E : Finset (Fin k)) (c : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ :=
  run (fun j => ix hk (c + j) ∈ A) (fun j => ix hk (c + j) ∈ E)

def T {k : ℕ} (hk : 0 < k) (A E : Finset (Fin k)) (c n : ℕ) (b : ZMod 2) :
    Finset (Fin k → ZMod 2) :=
  univ.filter fun y => y (ix hk c) = b ∧ (∀ j < k, n < j → y (ix hk (c + j)) = 0) ∧
    (∀ i ∈ A, y i = 0) ∧
    ∀ j < n, ix hk (c + j) ∈ E → y (ix hk (c + j)) * y (ix hk (c + (j + 1))) = 0

section cycle

variable {k : ℕ} (hk : 0 < k)

lemma val_ix {j : ℕ} (hj : j < k) : (ix hk j).val = j := Nat.mod_eq_of_lt hj

lemma ix_add_inj {c i j : ℕ} (hi : i < k) (hj : j < k) :
    ix hk (c + i) = ix hk (c + j) ↔ i = j :=
  ⟨fun h => (Nat.ModEq.add_left_cancel' c (Fin.ext_iff.1 h)).eq_of_lt_of_lt hi hj,
    fun h => h ▸ rfl⟩

lemma ix_surj (c : ℕ) (i : Fin k) : ∃ j < k, ix hk (c + j) = i := by
  have h : Function.Injective fun j : Fin k => ix hk (c + j.val) :=
    fun a b hab => Fin.ext ((ix_add_inj hk a.2 b.2).1 hab)
  obtain ⟨j, hj⟩ := Finite.injective_iff_surjective.1 h i
  exact ⟨j.val, j.2, hj⟩

lemma zmod_two (x : ZMod 2) : x = 0 ∨ x = 1 := by revert x; decide

lemma card_split (s : Finset (Fin k → ZMod 2)) (i : Fin k) :
    s.card = (s.filter fun y => y i = 0).card + (s.filter fun y => y i = 1).card := by
  rw [← card_filter_add_card_filter_not (s := s) fun y => y i = 0]
  congr 2
  exact filter_congr fun y _ => by rcases zmod_two (y i) with h | h <;> simp [h]

lemma card_filter_imp (s : Finset (Fin k → ZMod 2)) (i : Fin k) (p : Prop) [Decidable p] :
    (s.filter fun y => p → y i = 0).card =
      (s.filter fun y => y i = 0).card + if p then 0 else (s.filter fun y => y i = 1).card := by
  split_ifs with h
  · simp [h]
  · simp [h, ← card_split]

variable (A E : Finset (Fin k)) (c : ℕ)

lemma T_zero (b : ZMod 2) : T hk A E c 0 b =
    if ix hk c ∈ A ∧ b ≠ 0 then ∅ else {Function.update (0 : Fin k → ZMod 2) (ix hk c) b} := by
  ext y
  simp only [T, mem_filter, mem_univ, true_and]
  split_ifs with h
  · simp only [notMem_empty, iff_false]
    rintro ⟨h0, -, hp, -⟩
    exact h.2 (h0.symm.trans (hp _ h.1))
  · rw [mem_singleton]
    constructor
    · rintro ⟨h0, hz, -, -⟩
      funext i
      obtain ⟨j, hj, rfl⟩ := ix_surj hk c i
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simpa using h0
      · rw [hz j hj hj0, Function.update_of_ne (a' := ix hk c) fun hc =>
          hj0.ne ((ix_add_inj hk (c := c) (i := 0) hk hj).1 hc.symm)]
        rfl
    · rintro rfl
      refine ⟨Function.update_self _ _ _, fun j hjk hj => ?_, fun i hi => ?_,
        fun j hj => absurd hj (Nat.not_lt_zero j)⟩
      · exact Function.update_of_ne
          (fun hc => hj.ne ((ix_add_inj hk (c := c) (i := 0) hk hjk).1 hc.symm)) _ _
      · rw [Function.update_apply]
        split_ifs with hi'
        · exact not_not.1 fun hb => h ⟨hi' ▸ hi, hb⟩
        · rfl

variable {c} {n : ℕ}

lemma filter_T_succ_zero (hn : n + 1 < k) (b : ZMod 2) :
    (T hk A E c (n + 1) b).filter (fun y => y (ix hk (c + (n + 1))) = 0) = T hk A E c n b := by
  ext y
  simp only [T, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h0, hz, hp, he⟩, hl⟩
    refine ⟨h0, fun j hjk hj => ?_, hp, fun j hj => he j (by omega)⟩
    rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hj) with h | rfl
    · exact hz j hjk h
    · exact hl
  · rintro ⟨h0, hz, hp, he⟩
    refine ⟨⟨h0, fun j hjk hj => hz j hjk (by omega), hp, fun j hj hj' => ?_⟩,
      hz _ hn (by omega)⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · exact he j h hj'
    · rw [hz (j + 1) hn (by omega), mul_zero]

lemma update_ix (hn : n + 1 < k) (y : Fin k → ZMod 2) (x : ZMod 2) {j : ℕ} (hj : j < k)
    (hne : j ≠ n + 1) :
    Function.update y (ix hk (c + (n + 1))) x (ix hk (c + j)) = y (ix hk (c + j)) :=
  Function.update_of_ne (fun h => hne ((ix_add_inj hk hj hn).1 h)) _ _

lemma update_one_mem (hn : n + 1 < k) (b : ZMod 2) (ha : ix hk (c + (n + 1)) ∉ A)
    {y : Fin k → ZMod 2}
    (hy : y ∈ (T hk A E c n b).filter fun y => ix hk (c + n) ∈ E → y (ix hk (c + n)) = 0) :
    Function.update y (ix hk (c + (n + 1))) 1 ∈
      (T hk A E c (n + 1) b).filter fun y => y (ix hk (c + (n + 1))) = 1 := by
  simp only [T, mem_filter, mem_univ, true_and] at hy ⊢
  obtain ⟨⟨h0, hz, hp, he⟩, hl⟩ := hy
  refine ⟨⟨(update_ix hk hn y 1 (j := 0) hk (by omega)).trans h0,
    fun j hjk hj => (update_ix hk hn y 1 hjk (by omega)).trans (hz j hjk (by omega)),
    fun i hi => (Function.update_of_ne
      (fun h : i = ix hk (c + (n + 1)) => ha (h ▸ hi)) _ _).trans (hp i hi),
    fun j hj hj' => ?_⟩, Function.update_self _ _ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
  · rw [update_ix hk hn y 1 (by omega) (by omega), update_ix hk hn y 1 (by omega) (by omega)]
    exact he j h hj'
  · rw [update_ix hk hn y 1 (by omega) (by omega), hl hj', zero_mul]

lemma update_zero_mem (hn : n + 1 < k) (b : ZMod 2) {y : Fin k → ZMod 2}
    (hy : y ∈ (T hk A E c (n + 1) b).filter fun y => y (ix hk (c + (n + 1))) = 1) :
    Function.update y (ix hk (c + (n + 1))) 0 ∈
      (T hk A E c n b).filter fun y => ix hk (c + n) ∈ E → y (ix hk (c + n)) = 0 := by
  simp only [T, mem_filter, mem_univ, true_and] at hy ⊢
  obtain ⟨⟨h0, hz, hp, he⟩, hl⟩ := hy
  refine ⟨⟨(update_ix hk hn y 0 (j := 0) hk (by omega)).trans h0, fun j hjk hj => ?_,
    fun i hi => ?_, fun j hj hj' => ?_⟩, fun hE => ?_⟩
  · rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hj) with h | rfl
    · exact (update_ix hk hn y 0 hjk (by omega)).trans (hz j hjk h)
    · exact Function.update_self _ _ _
  · rw [Function.update_apply]
    split_ifs
    · rfl
    · exact hp i hi
  · rw [update_ix hk hn y 0 (by omega) (by omega), update_ix hk hn y 0 (by omega) (by omega)]
    exact he j (by omega) hj'
  · rw [update_ix hk hn y 0 (by omega) (by omega)]
    simpa [hl] using he n (by omega) hE

lemma card_filter_T_succ_one (hn : n + 1 < k) (b : ZMod 2) :
    ((T hk A E c (n + 1) b).filter fun y => y (ix hk (c + (n + 1))) = 1).card =
      if ix hk (c + (n + 1)) ∈ A then 0 else
        ((T hk A E c n b).filter fun y => ix hk (c + n) ∈ E → y (ix hk (c + n)) = 0).card := by
  split_ifs with ha
  · refine card_eq_zero.2 (filter_eq_empty_iff.2 fun y hy h1 => ?_)
    exact one_ne_zero (h1.symm.trans ((mem_filter.1 hy).2.2.2.1 _ ha))
  · refine (card_bij' (fun y _ => Function.update y (ix hk (c + (n + 1))) 1)
      (fun y _ => Function.update y (ix hk (c + (n + 1))) 0)
      (fun y hy => update_one_mem hk A E hn b ha hy) (fun y hy => update_zero_mem hk A E hn b hy)
      (fun y hy => ?_) fun y hy => ?_).symm
    · rw [Function.update_idem, Function.update_eq_self_iff,
        (mem_filter.1 (mem_filter.1 hy).1).2.2.1 _ hn (by omega)]
    · rw [Function.update_idem, Function.update_eq_self_iff, (mem_filter.1 hy).2]

theorem card_T (hn : n < k) (b : ZMod 2) :
    (((T hk A E c n b).filter fun y => y (ix hk (c + n)) = 0).card,
      ((T hk A E c n b).filter fun y => y (ix hk (c + n)) = 1).card) =
    crun hk A E c n (if b = 0 then 1 else 0, if b = 0 ∨ ix hk c ∈ A then 0 else 1) := by
  rw [crun]
  induction n with
  | zero =>
    rw [run, T_zero]
    rcases zmod_two b with rfl | rfl <;> by_cases ha : ix hk c ∈ A <;>
      simp [ha, filter_singleton]
  | succ n ih =>
    rw [run, ← ih (by omega), filter_T_succ_zero hk A E hn, card_filter_T_succ_one hk A E hn,
      card_filter_imp, card_split (T hk A E c n b) (ix hk (c + n))]

lemma edges_iff (c : ℕ) (y : Fin k → ZMod 2) :
    (∀ i ∈ E, y i * y (ix hk (i.val + 1)) = 0) ↔
      (∀ j < k - 1, ix hk (c + j) ∈ E → y (ix hk (c + j)) * y (ix hk (c + (j + 1))) = 0) ∧
        (ix hk (c + (k - 1)) ∈ E → y (ix hk (c + (k - 1))) * y (ix hk c) = 0) := by
  have hw : ix hk (c + (k - 1) + 1) = ix hk c := Fin.ext (by
    show (c + (k - 1) + 1) % k = c % k
    rw [show c + (k - 1) + 1 = c + k by omega, Nat.add_mod_right])
  constructor
  · refine fun h => ⟨fun j _ hj => ?_, fun hj => ?_⟩
    · have := h _ hj
      rwa [ix_val_add] at this
    · have := h _ hj
      rwa [ix_val_add, hw] at this
  · rintro ⟨h1, h2⟩ i hi
    obtain ⟨j, hj, rfl⟩ := ix_surj hk c i
    rw [ix_val_add]
    rcases Nat.lt_or_eq_of_le (Nat.le_sub_one_of_lt hj) with h | rfl
    · exact h1 j h hi
    · rw [hw]
      exact h2 hi

theorem card_indep_T (c : ℕ) : (indep hk A E).card = (T hk A E c (k - 1) 0).card +
    ((T hk A E c (k - 1) 1).filter fun y =>
      ix hk (c + (k - 1)) ∈ E → y (ix hk (c + (k - 1))) = 0).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext y
    simp only [indep, T, mem_union, mem_filter, mem_univ, true_and]
    rw [edges_iff hk E c]
    have hv : ∀ j < k, k - 1 < j → y (ix hk (c + j)) = 0 := fun j h1 h2 => absurd h2 (by omega)
    constructor
    · rintro ⟨hp, he, hw⟩
      rcases zmod_two (y (ix hk c)) with h | h
      · exact Or.inl ⟨h, hv, hp, he⟩
      · exact Or.inr ⟨⟨h, hv, hp, he⟩, fun hE => by simpa [h] using hw hE⟩
    · rintro (⟨h, -, hp, he⟩ | ⟨⟨h, -, hp, he⟩, hw⟩)
      · exact ⟨hp, he, fun _ => by rw [h, mul_zero]⟩
      · exact ⟨hp, he, fun hE => by rw [hw hE, zero_mul]⟩
  · exact disjoint_left.2 fun y h0 h1 =>
      zero_ne_one ((mem_filter.1 h0).2.1.symm.trans (mem_filter.1 (mem_filter.1 h1).1).2.1)

lemma run_add (a e : ℕ → Prop) [DecidablePred a] [DecidablePred e] (n : ℕ) (s t : ℕ × ℕ) :
    run a e n (s + t) = run a e n s + run a e n t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run, ih, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq]
    constructor
    · omega
    · split_ifs <;> omega

lemma crun_add (n : ℕ) (s t : ℕ × ℕ) :
    crun hk A E c n (s + t) = crun hk A E c n s + crun hk A E c n t :=
  run_add _ _ n s t

theorem card_indep (c : ℕ) : (indep hk A E).card =
    (crun hk A E c (k - 1) (1, 0)).1 + (crun hk A E c (k - 1) (1, 0)).2 +
      ((crun hk A E c (k - 1) (0, if ix hk c ∈ A then 0 else 1)).1 +
        if ix hk (c + (k - 1)) ∈ E then 0 else
          (crun hk A E c (k - 1) (0, if ix hk c ∈ A then 0 else 1)).2) := by
  have h0 := card_T hk A E (c := c) (n := k - 1) (by omega) 0
  have h1 := card_T hk A E (c := c) (n := k - 1) (by omega) 1
  simp only [ite_true, true_or, one_ne_zero, ite_false, false_or] at h0 h1
  rw [card_indep_T hk A E c, card_filter_imp,
    card_split (T hk A E c (k - 1) 0) (ix hk (c + (k - 1))), ← h0, ← h1]

lemma card_indep_le (c : ℕ) : (indep hk A E).card ≤
    (crun hk A E c (k - 1) (1, if ix hk c ∈ A then 0 else 1)).1 +
      (crun hk A E c (k - 1) (1, if ix hk c ∈ A then 0 else 1)).2 := by
  have h := crun_add hk A E (c := c) (k - 1) (1, 0) (0, if ix hk c ∈ A then 0 else 1)
  rw [Prod.mk_add_mk, Nat.add_zero, Nat.zero_add] at h
  rw [card_indep hk A E c, h, Prod.fst_add, Prod.snd_add]
  split_ifs <;> omega

lemma le_card_indep (c : ℕ) :
    (crun hk A E c (k - 1) (1, 0)).1 + (crun hk A E c (k - 1) (1, 0)).2 ≤ (indep hk A E).card := by
  rw [card_indep hk A E c]
  exact Nat.le_add_right _ _

lemma card_indep_of_wrap (c : ℕ) (hA : ix hk c ∉ A) (hE : ix hk (c + (k - 1)) ∉ E) :
    (indep hk A E).card =
      (crun hk A E c (k - 1) (1, 1)).1 + (crun hk A E c (k - 1) (1, 1)).2 := by
  have h : crun hk A E c (k - 1) (1, 1) = _ := crun_add hk A E (k - 1) (1, 0) (0, 1)
  rw [card_indep hk A E c, ite_eq_right hA, ite_eq_right hE, h, Prod.fst_add, Prod.snd_add]
  omega

lemma count_ix (c : ℕ) : Nat.count (fun j => ix hk (c + j) ∈ A) k = A.card := by
  rw [Nat.count_eq_card_filter_range]
  refine card_bij (fun j _ => ix hk (c + j)) (fun j hj => (mem_filter.1 hj).2)
    (fun i hi j hj h => (ix_add_inj hk (mem_range.1 (mem_filter.1 hi).1)
      (mem_range.1 (mem_filter.1 hj).1)).1 h) fun i hi => ?_
  obtain ⟨j, hj, rfl⟩ := ix_surj hk c i
  exact ⟨j, mem_filter.2 ⟨mem_range.2 hj, hi⟩, rfl⟩

end cycle

section bound

lemma run_fib (a e : ℕ → Prop) [DecidablePred a] [DecidablePred e] (s : ℕ × ℕ) {n₀ X m : ℕ}
    (n : ℕ) (h0 : run a e n₀ s = (X * fib (m + 1), X * fib m))
    (ha : ∀ j < n, ¬a (n₀ + j + 1)) (he : ∀ j < n, e (n₀ + j)) :
    run a e (n₀ + n) s = (X * fib (n + m + 1), X * fib (n + m)) := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [← Nat.add_assoc, run, ih (fun j hj => ha j (by omega)) fun j hj => he j (by omega),
      ite_eq_right (ha n (by omega)), ite_eq_left (he n (by omega)),
      show n + 1 + m + 1 = n + m + 2 by omega, show n + 1 + m = n + m + 1 by omega, fib_add_two]
    exact Prod.ext (by simp only [mul_add, Nat.add_comm]) (Nat.add_zero _)

lemma run_free (a e : ℕ → Prop) [DecidablePred a] [DecidablePred e] (s : ℕ × ℕ) (n₀ n : ℕ)
    (ha : ∀ j < n, ¬a (n₀ + j + 1)) (he : ∀ j < n, ¬e (n₀ + j)) :
    (run a e (n₀ + n) s).1 + (run a e (n₀ + n) s).2 =
      2 ^ n * ((run a e n₀ s).1 + (run a e n₀ s).2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := ih (fun j hj => ha j (by omega)) fun j hj => he j (by omega)
    rw [← Nat.add_assoc, run, ite_eq_right (ha n (by omega)), ite_eq_right (he n (by omega)),
      pow_succ]
    simp only [this]
    ring

lemma run_full (a e : ℕ → Prop) [DecidablePred a] [DecidablePred e] (n : ℕ)
    (ha : ∀ j < n, ¬a (0 + j + 1)) (he : ∀ j < n, e (0 + j)) :
    (run a e n (1, 0)).1 + (run a e n (1, 0)).2 + (run a e n (0, 1)).1 = fib n + fib (n + 2) := by
  have h0 : run a e n (1, 0) = (fib (n + 1), fib n) := by
    simpa using run_fib a e (1, 0) (n₀ := 0) (X := 1) (m := 0) n rfl ha he
  have h1 : run a e n (1, 1) = (fib (n + 2), fib (n + 1)) := by
    simpa using run_fib a e (1, 1) (n₀ := 0) (X := 1) (m := 1) n rfl ha he
  have h : run a e n (1, 1) = run a e n (1, 0) + run a e n (0, 1) := run_add a e n (1, 0) (0, 1)
  rw [h1, h0] at h
  have h2 := congrArg Prod.fst h
  have h3 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
  simp only [Prod.fst_add] at h2
  rw [h0]
  show fib (n + 1) + fib n + (run a e n (0, 1)).1 = _
  omega

lemma run_path (a e : ℕ → Prop) [DecidablePred a] [DecidablePred e] {k s : ℕ} (hs : s < k)
    (ha : ∀ j, j < k → ¬a j) (he : ∀ j, j < k → (e j ↔ j < s)) :
    (run a e (k - 1) (1, 1)).1 + (run a e (k - 1) (1, 1)).2 = 2 ^ (k - 1 - s) * fib (s + 3) := by
  have h1 : run a e s (1, 1) = (fib (s + 2), fib (s + 1)) := by
    simpa using run_fib a e (1, 1) (n₀ := 0) (X := 1) (m := 1) s rfl
      (fun j hj => ha _ (by omega)) fun j hj => (he _ (by omega)).2 (by omega)
  have h2 := run_free a e (1, 1) s (k - 1 - s) (fun j hj => ha _ (by omega))
    fun j hj hc => absurd ((he _ (by omega)).1 hc) (by omega)
  have h3 : fib (s + 3) = fib (s + 1) + fib (s + 2) := fib_add_two
  rw [show s + (k - 1 - s) = k - 1 by omega, h1] at h2
  rw [h2, h3, Nat.add_comm (fib (s + 1))]

lemma run_pins (a e : ℕ → Prop) [DecidablePred a] [DecidablePred e] {k p : ℕ} (hp : 1 ≤ p)
    (hpk : 2 * p < k) (ha : ∀ j, j < k → (a j ↔ ∃ i < p, 2 * i = j)) (he : ∀ j, j < k → e j) :
    (run a e (k - 1) (1, 0)).1 + (run a e (k - 1) (1, 0)).2 =
      2 ^ (p - 1) * fib (k - 2 * p + 3) := by
  have h1 : ∀ i, i < p → run a e (2 * i) (1, 0) = (2 ^ i, 0) := by
    intro i
    induction i with
    | zero => exact fun _ => rfl
    | succ i ih =>
      intro hi
      have ha1 : ¬a (2 * i + 1) := fun h => by
        obtain ⟨j, -, hj⟩ := (ha _ (by omega)).1 h
        omega
      have ha2 : a (2 * i + 1 + 1) := (ha _ (by omega)).2 ⟨i + 1, hi, by omega⟩
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, run, run, ih (by omega), ite_eq_left ha2,
        ite_eq_right ha1]
      simp [pow_succ, mul_two]
  have h2 := run_fib a e (1, 0) (n₀ := 2 * (p - 1)) (X := 2 ^ (p - 1)) (m := 0)
    (k - 1 - 2 * (p - 1)) (by simpa using h1 (p - 1) (by omega))
    (fun j hj h => by
      obtain ⟨i, hi, hj'⟩ := (ha _ (by omega)).1 h
      omega) fun j hj => he _ (by omega)
  rw [show 2 * (p - 1) + (k - 1 - 2 * (p - 1)) = k - 1 by omega] at h2
  simp only [Nat.add_zero] at h2
  rw [h2, show k - 2 * p + 3 = k - 1 - 2 * (p - 1) + 2 by omega, fib_add_two, mul_add]
  exact Nat.add_comm _ _

lemma fib_merge (a b : ℕ) : fib (a + 3) * fib (b + 3) ≤ 2 * fib (a + b + 3) := by
  have h : fib (a + b + 3) = fib (a + 1) * fib (b + 1) + fib (a + 2) * fib (b + 2) := by
    have := fib_add (a + 1) (b + 1)
    rwa [show a + 1 + (b + 1) + 1 = a + b + 3 by ring] at this
  have ha2 : fib (a + 2) = fib a + fib (a + 1) := fib_add_two
  have ha3 : fib (a + 3) = fib (a + 1) + fib (a + 2) := fib_add_two
  have hb2 : fib (b + 2) = fib b + fib (b + 1) := fib_add_two
  have hb3 : fib (b + 3) = fib (b + 1) + fib (b + 2) := fib_add_two
  rw [h, ha3, hb3, ha2, hb2]
  nlinarith [Nat.zero_le (fib a * fib b)]

lemma fib_six (u : ℕ) : 4 * fib (u + 3) ≤ fib (u + 6) := by
  have h2 : fib (u + 2) = fib u + fib (u + 1) := fib_add_two
  have h3 : fib (u + 3) = fib (u + 1) + fib (u + 2) := fib_add_two
  have h4 : fib (u + 4) = fib (u + 2) + fib (u + 3) := fib_add_two
  have h5 : fib (u + 5) = fib (u + 3) + fib (u + 4) := fib_add_two
  have h6 : fib (u + 6) = fib (u + 4) + fib (u + 5) := fib_add_two
  omega

lemma reset_le {X m C r K : ℕ} (h : X * 2 ^ (C + m + 1 + r) ≤ K * fib (C + 3)) :
    X * fib (m + 2) * 2 ^ (C + (m - 1) + 1 + r) ≤ K * fib (C + (m - 1) + 3) := by
  rcases m with _ | m
  · simpa using h
  · show X * fib (m + 3) * 2 ^ (C + m + 1 + r) ≤ K * fib (C + m + 3)
    refine Nat.le_of_mul_le_mul_left (c := 2) ?_ two_pos
    calc 2 * (X * fib (m + 3) * 2 ^ (C + m + 1 + r))
        = X * 2 ^ (C + (m + 1) + 1 + r) * fib (m + 3) := by ring
      _ ≤ K * fib (C + 3) * fib (m + 3) := Nat.mul_le_mul_right _ h
      _ ≤ K * (2 * fib (C + m + 3)) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (fib_merge C m)
      _ = 2 * (K * fib (C + m + 3)) := by ring

lemma run_inv (a e : ℕ → Prop) [DecidablePred a] [DecidablePred e] (n : ℕ) :
    ∃ X m C, run a e n (1, if a 0 then 0 else 1) = (X * fib (m + 1), X * fib m) ∧
      X * 2 ^ (C + m + 1 + Nat.count a (n + 1)) ≤ 2 ^ (n + 1) * fib (C + 3) ∧
      Nat.count e n + (1 - m) + (if a 0 then 1 else 0) ≤
        C + (m - 1) + 2 * Nat.count a (n + 1) := by
  induction n with
  | zero =>
    by_cases h : a 0
    · exact ⟨1, 0, 0, by simp [run, h], by norm_num [Nat.count_succ, h],
        by simp [Nat.count_succ, h]⟩
    · exact ⟨1, 1, 0, by simp [run, h], by norm_num [Nat.count_succ, h],
        by simp [Nat.count_succ, h]⟩
  | succ n ih =>
    obtain ⟨X, m, C, hr, h1, h2⟩ := ih
    have hd := Nat.mul_le_mul_left 2 (reset_le h1)
    have hrun : run a e (n + 1) (1, if a 0 then 0 else 1) = (X * fib (m + 2),
        if a (n + 1) then 0 else X * fib (m + 1) + if e n then 0 else X * fib m) := by
      rw [run, hr]
      simp only [fib_add_two, mul_add, add_comm]
    rw [hrun, Nat.count_succ a (n + 1), Nat.count_succ e n]
    by_cases ha : a (n + 1)
    · simp only [ha, ↓reduceIte]
      refine ⟨X * fib (m + 2), 0, C + (m - 1), by simp, ?_, by split_ifs at h2 ⊢ <;> omega⟩
      convert hd using 1 <;> ring
    · by_cases he : e n
      · simp only [ha, he, ↓reduceIte]
        refine ⟨X, m + 1, C, by simp, ?_, by split_ifs at h2 ⊢ <;> omega⟩
        convert Nat.mul_le_mul_left 2 h1 using 1 <;> ring
      · simp only [ha, he, ↓reduceIte]
        refine ⟨X * fib (m + 2), 1, C + (m - 1), by simp [fib_add_two, mul_add, add_comm], ?_,
          by split_ifs at h2 ⊢ <;> omega⟩
        convert hd using 1 <;> ring

lemma run_le (a e : ℕ → Prop) [DecidablePred a] [DecidablePred e] (n : ℕ) :
    ∃ L, Nat.count e n + (if a 0 then 1 else 0) ≤ L + 2 * Nat.count a (n + 1) ∧
      ((run a e n (1, if a 0 then 0 else 1)).1 + (run a e n (1, if a 0 then 0 else 1)).2) *
        2 ^ (L + 1 + Nat.count a (n + 1)) ≤ 2 ^ (n + 1) * fib (L + 3) := by
  obtain ⟨X, m, C, hr, h1, h2⟩ := run_inv a e n
  refine ⟨C + (m - 1), by split_ifs at h2 ⊢ <;> omega, ?_⟩
  simp only [hr]
  rw [← mul_add, add_comm (fib (m + 1)), ← fib_add_two]
  exact reset_le h1

lemma bound_anti {N K r d L : ℕ} (hd : d ≤ L) (h : N * 2 ^ (L + 1 + r) ≤ K * fib (L + 3)) :
    N * 2 ^ (d + 1 + r) ≤ K * fib (d + 3) := by
  induction L, hd using Nat.le_induction with
  | base => exact h
  | succ L _ ih =>
    refine ih (Nat.le_of_mul_le_mul_left (c := 2) ?_ two_pos)
    have h4 : fib (L + 4) = fib (L + 2) + fib (L + 3) := fib_add_two
    have h3 : fib (L + 2) ≤ fib (L + 3) := fib_le_fib_succ
    calc 2 * (N * 2 ^ (L + 1 + r)) = N * 2 ^ (L + 1 + 1 + r) := by ring
      _ ≤ K * fib (L + 4) := h
      _ ≤ K * (2 * fib (L + 3)) := Nat.mul_le_mul_left K (by omega)
      _ = 2 * (K * fib (L + 3)) := by ring

lemma bound_step {N K r t : ℕ}
    (h : N * 2 ^ (t - 3 * (r + 1) + 1 + (r + 1)) ≤ K * fib (t - 3 * (r + 1) + 3)) :
    N * 2 ^ (t - 3 * r + 1 + r) ≤ K * fib (t - 3 * r + 3) := by
  rcases Nat.lt_or_ge (t - 3 * r) 3 with hd | hd
  · rw [show t - 3 * (r + 1) = 0 by omega] at h
    have e1 : ∀ d, N * 2 ^ (d + 1 + r) = N * 2 ^ r * 2 ^ (d + 1) := fun d => by ring
    rw [show 0 + 1 + (r + 1) = 1 + 1 + r by ring, e1] at h
    rw [e1]
    generalize N * 2 ^ r = Q at h ⊢
    generalize t - 3 * r = d at hd ⊢
    interval_cases d <;> norm_num at h ⊢ <;> omega
  · obtain ⟨d, hd'⟩ : ∃ d, t - 3 * r = d + 3 := ⟨t - 3 * r - 3, by omega⟩
    rw [show t - 3 * (r + 1) = d by omega] at h
    rw [hd']
    calc N * 2 ^ (d + 3 + 1 + r) = 4 * (N * 2 ^ (d + 1 + (r + 1))) := by ring
      _ ≤ 4 * (K * fib (d + 3)) := Nat.mul_le_mul_left 4 h
      _ = K * (4 * fib (d + 3)) := by ring
      _ ≤ K * fib (d + 3 + 3) := Nat.mul_le_mul_left K (fib_six d)

lemma bound_le {N K t r r₀ : ℕ} (hr : r₀ ≤ r)
    (h : N * 2 ^ (t - 3 * r + 1 + r) ≤ K * fib (t - 3 * r + 3)) :
    N * 2 ^ (t - 3 * r₀ + 1 + r₀) ≤ K * fib (t - 3 * r₀ + 3) := by
  induction r, hr using Nat.le_induction with
  | base => exact h
  | succ r _ ih => exact ih (bound_step h)

lemma cancel_pow {N F a b k : ℕ} (hab : b + a = k) (h : N * 2 ^ a ≤ 2 ^ k * F) :
    N ≤ 2 ^ b * F := by
  subst hab
  rw [pow_add, mul_right_comm] at h
  exact Nat.le_of_mul_le_mul_right h (by positivity)

lemma le_base {k N r e L : ℕ} (hk : 3 ≤ k) (hr : r ≤ k) (he : e ≤ k) (hL : e ≤ L + 2 * r)
    (hcut : 1 ≤ r ∨ e < k) (h : N * 2 ^ (L + 1 + r) ≤ 2 ^ k * fib (L + 3)) :
    N ≤ base k (r + e) := by
  have h' : N * 2 ^ (r + e - 3 * r + 1 + r) ≤ 2 ^ k * fib (r + e - 3 * r + 3) :=
    bound_anti (by omega) h
  rw [base, ite_eq_right (by omega), ite_eq_right (by omega)]
  split_ifs with h1 h2 h3
  · have h0 := bound_le (Nat.zero_le r) h'
    rw [Nat.mul_zero, Nat.sub_zero, Nat.add_zero] at h0
    exact cancel_pow (by omega) h0
  · have h0 := bound_le (r₀ := 1) (by omega) h'
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [h2, show 3 + j - 3 * 1 = j by omega] at h0
    have h3 : fib (j + 3) = fib (j + 1) + fib (j + 2) := fib_add_two
    have h4 : fib (j + 4) = fib (j + 2) + fib (j + 3) := fib_add_two
    have h5 : fib (j + 1) ≤ fib (j + 2) := fib_le_fib_succ
    have h6 : N ≤ 2 ^ 1 * fib (j + 3) := cancel_pow (by omega) h0
    rw [show 3 + j - 1 = j + 2 by omega, show 3 + j + 1 = j + 4 by omega]
    omega
  · obtain ⟨p, hp⟩ : ∃ p, r + e = k + p := ⟨r + e - k, by omega⟩
    have h0 := bound_le (r₀ := p) (by omega) h'
    rw [hp] at h0 h3 ⊢
    rw [Nat.add_sub_cancel_left] at h3 ⊢
    rw [show k + p - 3 * p = k - 2 * p by omega] at h0
    exact cancel_pow (by omega) h0
  · obtain ⟨p, hp⟩ : ∃ p, r + e = k + p := ⟨r + e - k, by omega⟩
    have h0 := bound_le (r₀ := p) (by omega) h'
    rw [hp] at h0 h3 ⊢
    rw [Nat.add_sub_cancel_left] at h3 ⊢
    rw [show k + p - 3 * p = 0 by omega] at h0
    have h4 : N * 2 ^ (0 + 1 + p) ≤ 2 ^ (k + 1) * 1 := by
      rw [pow_succ, mul_one]
      exact h0
    simpa using cancel_pow (b := k - p) (by omega) h4

end bound

section main

variable {k : ℕ}

lemma ix_wrap (hk : 0 < k) (i : Fin k) : ix hk (i.val + 1 + (k - 1)) = i := by
  apply Fin.ext
  show (i.val + 1 + (k - 1)) % k = i.val
  rw [show i.val + 1 + (k - 1) = i.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt i.2]

lemma card_indep_full (hk : 0 < k) : (indep hk ∅ univ).card = fib (k - 1) + fib (k + 1) := by
  have h : (crun hk ∅ univ 0 (k - 1) (1, 0)).1 + (crun hk ∅ univ 0 (k - 1) (1, 0)).2 +
      (crun hk ∅ univ 0 (k - 1) (0, 1)).1 = _ :=
    run_full _ _ (k - 1) (fun j _ => notMem_empty _) fun j _ => mem_univ _
  rw [card_indep hk ∅ univ 0, ite_eq_right (notMem_empty _), ite_eq_left (mem_univ _),
    Nat.add_zero, h, show k - 1 + 2 = k + 1 by omega]

lemma indep_card_le_of_cut (hk : 3 ≤ k) (hk0 : 0 < k) (A E : Finset (Fin k)) (c : ℕ)
    (hc : ix hk0 c ∈ A ∨ ix hk0 (c + (k - 1)) ∉ E) :
    (indep hk0 A E).card ≤ base k (A.card + E.card) := by
  obtain ⟨L, hL, hb⟩ :=
    run_le (fun j => ix hk0 (c + j) ∈ A) (fun j => ix hk0 (c + j) ∈ E) (k - 1)
  have hE : Nat.count (fun j => ix hk0 (c + j) ∈ E) (k - 1 + 1) = E.card := by
    rw [Nat.sub_add_cancel hk0]
    exact count_ix hk0 E c
  rw [Nat.count_succ] at hE
  rw [Nat.sub_add_cancel hk0, count_ix hk0 A c] at hL hb
  simp only [Nat.add_zero] at hL hb hE
  have hEL : E.card ≤ L + 2 * A.card := by
    rcases hc with hc | hc
    · simp only [hc, ↓reduceIte] at hL
      split_ifs at hE <;> omega
    · simp only [hc, ↓reduceIte] at hE
      omega
  refine le_base hk (by simpa using card_le_univ A) (by simpa using card_le_univ E) hEL ?_
    ((Nat.mul_le_mul_right _ (card_indep_le hk0 A E c)).trans hb)
  rcases hc with hc | hc
  · exact Or.inl (card_pos.2 ⟨_, hc⟩)
  · exact Or.inr (by simpa using card_lt_univ_of_notMem hc)

theorem indep_card_le {k : ℕ} (hk : 3 ≤ k) (A E : Finset (Fin k)) :
    (indep (by omega) A E).card ≤ base k (A.card + E.card) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · by_cases hE : E = univ
    · subst hE
      rw [card_indep_full, card_empty, Finset.card_univ, Fintype.card_fin, Nat.zero_add, base]
      simp [show k ≠ 1 by omega, show k ≠ 2 by omega]
    · obtain ⟨i, hi⟩ : ∃ i, i ∉ E := by simpa [eq_univ_iff_forall] using hE
      exact indep_card_le_of_cut hk _ ∅ E (i.val + 1) (Or.inr (by rwa [ix_wrap]))
  · exact indep_card_le_of_cut hk _ A E a.val (Or.inl (by rwa [ix_self]))

lemma le_card_indep_of_cover (hk : 0 < k) (A : Finset (Fin k))
    (hcov : ∀ i : Fin k, i ∈ A ∨ ix hk (i.val + 1) ∈ A) :
    2 ^ (k - A.card) ≤ (indep hk A univ).card := by
  have hc : ∀ i : Fin k, (if i ∈ A then ({0} : Finset (ZMod 2)) else univ).card =
      if i ∈ A then 1 else 2 := fun i => by split_ifs <;> simp [ZMod.card]
  have hA := card_filter_add_card_filter_not (s := (univ : Finset (Fin k))) (· ∈ A)
  calc 2 ^ (k - A.card)
      = (Fintype.piFinset fun i => if i ∈ A then ({0} : Finset (ZMod 2)) else univ).card := by
        rw [Fintype.card_piFinset]
        simp only [hc]
        rw [prod_ite, prod_const_one, one_mul, prod_const]
        congr 1
        simp at hA
        omega
    _ ≤ _ := card_le_card fun y hy => ?_
  rw [Fintype.mem_piFinset] at hy
  have h0 : ∀ i ∈ A, y i = 0 := fun i hi => by simpa [hi] using hy i
  refine mem_filter.2 ⟨mem_univ _, h0, fun i _ => ?_⟩
  rcases hcov i with h | h
  · rw [h0 i h, zero_mul]
  · rw [h0 _ h, mul_zero]

lemma exists_cover (hk : 0 < k) {p : ℕ} (h2 : k ≤ 2 * p) (hpk : p ≤ k) :
    ∃ A : Finset (Fin k), A.card = p ∧ ∀ i : Fin k, i ∈ A ∨ ix hk (i.val + 1) ∈ A := by
  have hB : ((range ((k + 1) / 2)).image fun j => ix hk (2 * j)).card ≤ p :=
    card_image_le.trans (by rw [card_range]; omega)
  obtain ⟨A, hBA, -, hA⟩ := exists_subsuperset_card_eq (subset_univ _) hB (by simpa using hpk)
  have hm : ∀ j, j < (k + 1) / 2 → ix hk (2 * j) ∈ A :=
    fun j hj => hBA (mem_image_of_mem _ (mem_range.2 hj))
  refine ⟨A, hA, fun i => ?_⟩
  rcases Nat.even_or_odd' i.val with ⟨j, hj | hj⟩
  · have := hm j (by omega)
    rw [← hj, ix_self] at this
    exact Or.inl this
  · by_cases h : i.val + 1 = k
    · have := hm 0 (by omega)
      rw [show ix hk (2 * 0) = ix hk (i.val + 1) from Fin.ext (by simp [ix, h])] at this
      exact Or.inr this
    · have := hm (j + 1) (by omega)
      rw [show 2 * (j + 1) = i.val + 1 by omega] at this
      exact Or.inr this

theorem exists_indep_card_ge {k : ℕ} (hk : 3 ≤ k) (s : ℕ) (hs : s ≤ 2*k) :
    ∃ A E : Finset (Fin k), A.card + E.card = s ∧ base k s ≤ (indep (by omega) A E).card := by
  have hk0 : 0 < k := by omega
  rw [base, ite_eq_right (by omega), ite_eq_right (by omega)]
  rcases lt_trichotomy s k with h | rfl | h
  · have hE : ∀ j, j < k → (ix hk0 (0 + j) ∈ Iio (⟨s, h⟩ : Fin k) ↔ j < s) := fun j hj => by
      rw [mem_Iio, Fin.lt_def, Nat.zero_add, val_ix hk0 hj]
    refine ⟨∅, Iio ⟨s, h⟩, by simp, ?_⟩
    rw [ite_eq_left h, card_indep_of_wrap hk0 ∅ _ 0 (notMem_empty _)
      (fun hc => absurd ((hE _ (by omega)).1 hc) (by omega)), crun,
      run_path _ _ h (fun j _ => notMem_empty (ix hk0 (0 + j))) hE,
      show k - s - 1 = k - 1 - s by omega]
  · refine ⟨∅, univ, by simp, ?_⟩
    rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, card_indep_full]
  · obtain ⟨p, hp, rfl⟩ : ∃ p, 1 ≤ p ∧ s = k + p := ⟨s - k, by omega, by omega⟩
    rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel_left]
    by_cases h2 : 2 * p < k
    · have hA : ∀ j, j < k → (ix hk0 (0 + j) ∈ (range p).image (fun i => ix hk0 (2 * i)) ↔
          ∃ i < p, 2 * i = j) := fun j hj => by
        rw [Nat.zero_add]
        simp only [mem_image, mem_range]
        refine ⟨fun ⟨i, hi, hij⟩ => ⟨i, hi, ?_⟩, fun ⟨i, hi, hij⟩ => ⟨i, hi, hij ▸ rfl⟩⟩
        have := congrArg Fin.val hij
        rwa [val_ix hk0 (by omega), val_ix hk0 hj] at this
      refine ⟨(range p).image fun i => ix hk0 (2 * i), univ, ?_, ?_⟩
      · rw [Finset.card_image_of_injOn, card_range, Finset.card_univ, Fintype.card_fin,
          Nat.add_comm]
        intro i hi j hj hij
        have := congrArg Fin.val hij
        rw [val_ix hk0 (by have := mem_range.1 hi; omega),
          val_ix hk0 (by have := mem_range.1 hj; omega)] at this
        omega
      · rw [ite_eq_left h2, ← run_pins _ _ hp h2 hA fun j _ => mem_univ (ix hk0 (0 + j))]
        exact le_card_indep hk0 _ univ 0
    · obtain ⟨A, hA, hcov⟩ := exists_cover hk0 (by omega : k ≤ 2 * p) (by omega : p ≤ k)
      refine ⟨A, univ, by rw [hA, Finset.card_univ, Fintype.card_fin, Nat.add_comm], ?_⟩
      rw [ite_eq_right h2, ← hA]
      exact le_card_indep_of_cover hk0 A hcov

end main

end PEqualNP.Outside.L_meta_30867

namespace PEqualNP.Outside.L_meta_30867
open Finset

def chi {k : ℕ} (hk : 0 < k) (y : Vec k) : Vec k :=
  fun i => y i + (1 + y (ix hk (i.val + 1))) * y (ix hk (i.val + 2))

def gen {k : ℕ} (hk : 0 < k) : Fin k ⊕ Fin k → Finset (Fin k) :=
  Sum.elim (fun i => {i}) (fun i => {ix hk (i.val + 1), ix hk (i.val + 2)})

def bas {k : ℕ} : Fin k ⊕ Fin k → Vec k × Vec k :=
  Sum.elim (fun i => (Pi.single i 1, 0)) (fun i => (0, Pi.single i 1))

lemma ix_add_cancel {k : ℕ} (hk : 0 < k) {a b : ℕ} (c : ℕ) (h : ix hk (a + c) = ix hk (b + c)) :
    a % k = b % k := by
  rw [ix_eq_iff] at h
  exact Nat.ModEq.add_right_cancel' c h

lemma ix_succ_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective fun i : Fin k => ix hk (i.val + 1) := fun i j h => by
  have h' := ix_add_cancel hk 1 h
  rw [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at h'
  exact Fin.ext h'

lemma ix_one_ne_two {k : ℕ} (hk : 2 ≤ k) (hk0 : 0 < k) (i : ℕ) :
    ix hk0 (i + 1) ≠ ix hk0 (i + 2) := fun h => by
  have h' : 0 % k = 1 % k :=
    ix_add_cancel hk0 (i + 1) (by rw [zero_add, Nat.add_comm 1 (i + 1)]; exact h)
  rw [Nat.zero_mod, Nat.mod_eq_of_lt hk] at h'
  exact absurd h' (by omega)

lemma wt_singleton {k : ℕ} (i : Fin k) : wt {i} = 2 ^ k + 2 ^ i.val := Finset.sum_singleton _ _

lemma wt_pair {k : ℕ} {a b : Fin k} (h : a ≠ b) :
    wt {a, b} = (2 ^ k + 2 ^ a.val) + (2 ^ k + 2 ^ b.val) := Finset.sum_pair h

lemma wt_singleton_lt_pair {k : ℕ} (i : Fin k) {a b : Fin k} (h : a ≠ b) : wt {i} < wt {a, b} := by
  have h1 := Nat.pow_lt_pow_right (a := 2) (by omega) i.2
  have h2 := Nat.two_pow_pos a.val
  have h3 := Nat.two_pow_pos b.val
  rw [wt_singleton, wt_pair h]
  omega

lemma wt_injective {k : ℕ} : Function.Injective (wt (k := k)) := by
  intro S T h
  have hb : ∀ U : Finset (Fin k), ∑ i ∈ U.map Fin.valEmbedding, 2 ^ i < 2 ^ k := fun U =>
    Nat.geomSum_lt (le_refl 2) fun j hj => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hj
      exact i.2
  have hw : ∀ U : Finset (Fin k),
      wt U = U.card * 2 ^ k + ∑ i ∈ U.map Fin.valEmbedding, 2 ^ i := fun U => by
    simp [wt, Finset.sum_add_distrib, Finset.sum_map]
  rw [hw, hw] at h
  have h2 := congrArg (· % 2 ^ k) h
  simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (hb _)] at h2
  exact Finset.map_injective _ (Finset.geomSum_injective (le_refl 2) h2)

lemma gen_injective {k : ℕ} (hk : 3 ≤ k) : Function.Injective (gen (by omega : 0 < k)) := by
  have hk0 : 0 < k := by omega
  rintro (i | i) (j | j) h <;> simp only [gen, Sum.elim_inl, Sum.elim_inr] at h
  · rw [Finset.singleton_inj.1 h]
  · have := congrArg Finset.card h
    rw [Finset.card_singleton, Finset.card_pair (ix_one_ne_two (by omega) hk0 j.val)] at this
    omega
  · have := congrArg Finset.card h
    rw [Finset.card_singleton, Finset.card_pair (ix_one_ne_two (by omega) hk0 i.val)] at this
    omega
  · have h1 : ix hk0 (i.val + 1) ∈ ({ix hk0 (j.val + 1), ix hk0 (j.val + 2)} : Finset (Fin k)) :=
      h ▸ Finset.mem_insert_self _ _
    have h2 : ix hk0 (i.val + 2) ∈ ({ix hk0 (j.val + 1), ix hk0 (j.val + 2)} : Finset (Fin k)) :=
      h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1
    · rw [ix_succ_injective hk0 h1]
    · exfalso
      rcases h2 with h2 | h2
      · have e : ix hk0 (0 + (j.val + 1)) = ix hk0 (2 + (j.val + 1)) := by
          rw [zero_add, ← h2, show 2 + (j.val + 1) = (j.val + 2) + 1 by omega,
            ← ix_val_add hk0 (j.val + 2) 1, ← h1]
          exact (ix_val_add hk0 (i.val + 1) 1).symm
        have h3 := ix_add_cancel hk0 (j.val + 1) e
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h3
        omega
      · exact ix_one_ne_two (by omega) hk0 i.val (h1.trans h2.symm)

lemma exists_leads {ι : Type} [Fintype ι] (key : ι → ℕ) (R : Submodule Bin (ι → Bin)) :
    ∃ LT : Finset ι, Module.finrank Bin R ≤ LT.card ∧
      ∀ m ∈ LT, ∃ c ∈ R, c m ≠ 0 ∧ ∀ m', c m' ≠ 0 → key m' ≤ key m := by
  classical
  let LT : Finset ι :=
    univ.filter fun m => ∃ c ∈ R, c m ≠ 0 ∧ ∀ m', c m' ≠ 0 → key m' ≤ key m
  refine ⟨LT, ?_, fun m hm => (Finset.mem_filter.1 hm).2⟩
  let π : R →ₗ[Bin] (LT → Bin) :=
    (LinearMap.funLeft Bin Bin (Subtype.val : LT → ι)).comp R.subtype
  have hπ : Function.Injective π := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hne
    obtain ⟨m₀, hm₀⟩ := Function.ne_iff.1 fun h : (c : ι → Bin) = 0 => hne (Subtype.ext h)
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (univ.filter fun m => (c : ι → Bin) m ≠ 0) key
      ⟨m₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, hm₀⟩⟩
    have hm' : (c : ι → Bin) m ≠ 0 := (Finset.mem_filter.1 hm).2
    have hmem : m ∈ LT := Finset.mem_filter.2 ⟨Finset.mem_univ _, c, c.2, hm',
      fun m' h' => hmax m' (Finset.mem_filter.2 ⟨Finset.mem_univ _, h'⟩)⟩
    exact hm' (congrFun hc ⟨m, hmem⟩)
  have h := LinearMap.finrank_le_finrank_of_injective hπ
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h

lemma map_expand {k t : ℕ} (P : (Vec k × Vec k) →ₗ[Bin] Vec t) (y w : Vec k) :
    P (y, w) = ∑ m, Sum.elim y w m • P (bas m) := by
  have h : (y, w) = ∑ m, Sum.elim y w m • (bas m : Vec k × Vec k) := by
    rw [Fintype.sum_sum_type]
    ext j <;> simp [bas, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  simp only [map_sum, map_smul]

def coeffs {k t : ℕ} (P : (Vec k × Vec k) →ₗ[Bin] Vec t) :
    Vec t →ₗ[Bin] (Fin k ⊕ Fin k → Bin) :=
  Matrix.mulVecLin (Matrix.of fun m j => P (bas m) j)

lemma coeffs_dot {k t : ℕ} (P : (Vec k × Vec k) →ₗ[Bin] Vec t) (u : Vec t) (y w : Vec k) :
    ∑ m, coeffs P u m * Sum.elim y w m = ∑ j, u j * P (y, w) j := by
  simp only [coeffs, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    map_expand P y w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring

lemma coeffs_injective {k t : ℕ} (P : (Vec k × Vec k) →ₗ[Bin] Vec t)
    (hP : Function.Surjective P) : Function.Injective (coeffs P) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  funext j
  obtain ⟨⟨y, w⟩, hz⟩ := hP (Pi.single j 1)
  have h := coeffs_dot P u y w
  rw [hu, hz] at h
  simpa [Pi.single_apply] using h.symm

lemma gen_tail_mem_low {k : ℕ} (hk : 2 ≤ k) (hk0 : 0 < k) (m : Fin k ⊕ Fin k) :
    (fun y : Vec k => Sum.elim y (chi hk0 y) m) + mon (gen hk0 m) ∈ low (wt (gen hk0 m)) := by
  rcases m with i | i
  · have h : (fun y : Vec k => Sum.elim y (chi hk0 y) (Sum.inl i)) +
        mon (gen hk0 (Sum.inl i)) = 0 := by
      funext y
      simp [gen, mon, zmod2_add_self]
    rw [h]
    exact zero_mem _
  · have hab := ix_one_ne_two hk hk0 i.val
    have h : (fun y : Vec k => Sum.elim y (chi hk0 y) (Sum.inr i)) + mon (gen hk0 (Sum.inr i)) =
        mon {i} + mon {ix hk0 (i.val + 2)} := by
      funext y
      simp only [Pi.add_apply, Sum.elim_inr, gen, mon, chi, Finset.prod_pair hab,
        Finset.prod_singleton]
      linear_combination zmod2_add_self (y (ix hk0 (i.val + 1)) * y (ix hk0 (i.val + 2)))
    rw [h]
    exact add_mem (mon_mem_low (wt_singleton_lt_pair i hab))
      (mon_mem_low (wt_singleton_lt_pair _ hab))

lemma lead_reduce {k : ℕ} (hk : 3 ≤ k) (hk0 : 0 < k) (Z : Finset (Vec k))
    (c : Fin k ⊕ Fin k → Bin) (κ : Bin) (m : Fin k ⊕ Fin k) (hm : c m ≠ 0)
    (hmax : ∀ m', c m' ≠ 0 → wt (gen hk0 m') ≤ wt (gen hk0 m))
    (hZ : ∀ y ∈ Z, ∑ m', c m' * Sum.elim y (chi hk0 y) m' = κ) :
    ∃ f ∈ low (wt (gen hk0 m)), ∀ y ∈ Z, mon (gen hk0 m) y = f y := by
  classical
  have hpos : wt (∅ : Finset (Fin k)) < wt (gen hk0 m) := by
    rcases m with i | i
    · exact Nat.add_pos_left (Nat.two_pow_pos k) _
    · exact lt_of_le_of_lt (Nat.zero_le _)
        (wt_singleton_lt_pair i (ix_one_ne_two (by omega) hk0 i.val))
  have hlow : ∀ m', m' ≠ m →
      c m' • (fun y : Vec k => Sum.elim y (chi hk0 y) m') ∈ low (wt (gen hk0 m)) := by
    intro m' hne
    by_cases hc : c m' = 0
    · rw [hc, zero_smul]
      exact zero_mem _
    · have hlt : wt (gen hk0 m') < wt (gen hk0 m) :=
        lt_of_le_of_ne (hmax m' hc) fun h => hne (gen_injective hk (wt_injective h))
      have h2 : (fun y : Vec k => Sum.elim y (chi hk0 y) m') =
          ((fun y : Vec k => Sum.elim y (chi hk0 y) m') + mon (gen hk0 m')) + mon (gen hk0 m') := by
        funext y
        simp only [Pi.add_apply]
        linear_combination (-1 : Bin) * zmod2_add_self (mon (gen hk0 m') y)
      rw [h2]
      exact Submodule.smul_mem _ _
        (add_mem (low_mono hlt.le (gen_tail_mem_low (by omega) hk0 m')) (mon_mem_low hlt))
  refine ⟨κ • mon ∅ + ∑ m' ∈ univ.erase m, c m' • (fun y : Vec k => Sum.elim y (chi hk0 y) m') +
    ((fun y : Vec k => Sum.elim y (chi hk0 y) m) + mon (gen hk0 m)),
    Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (mon_mem_low hpos))
      (sum_mem fun m' hm' => hlow m' (Finset.ne_of_mem_erase hm')))
      (gen_tail_mem_low (by omega) hk0 m), fun y hy => ?_⟩
  have h1 := hZ y hy
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), zmod2_eq_one_of_ne_zero hm, one_mul] at h1
  have hG := zmod2_add_self (Sum.elim y (chi hk0 y) m)
  have hS := zmod2_add_self (∑ m' ∈ univ.erase m, c m' * Sum.elim y (chi hk0 y) m')
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, mon, Finset.prod_empty,
    mul_one, ← h1]
  linear_combination (-1 : Bin) * hG - hS

theorem chi_fiber_le {k : ℕ} (hk : 3 ≤ k) (hk0 : 0 < k) {t : ℕ}
    (P : (Vec k × Vec k) →ₗ[Bin] Vec t) (v : Vec t) (hP : Function.Surjective P) :
    (univ.filter fun y => P (y, chi hk0 y) = v).card ≤ base k t := by
  classical
  obtain ⟨LT₀, hcard, hlead⟩ :=
    exists_leads (fun m => wt (gen hk0 m)) (LinearMap.range (coeffs P))
  rw [LinearMap.finrank_range_of_inj (coeffs_injective P hP), Module.finrank_fin_fun] at hcard
  obtain ⟨LT, hsub, hLT⟩ := Finset.exists_subset_card_eq hcard
  have hfoot := footprint (univ.filter fun y => P (y, chi hk0 y) = v) (LT.image (gen hk0)) (by
    intro G hG
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hG
    obtain ⟨_, ⟨u, rfl⟩, hne, hmax⟩ := hlead m (hsub hm)
    refine lead_reduce hk hk0 _ _ (∑ j, u j * v j) m hne hmax fun y hy => ?_
    rw [coeffs_dot, (Finset.mem_filter.1 hy).2])
  refine hfoot.trans (le_trans ?_ ((indep_card_le hk LT.toLeft
    (LT.toRight.image fun i => ix hk0 (i.val + 1))).trans_eq ?_))
  · refine Finset.card_le_card_of_injOn (fun T i => if i ∈ T then 1 else 0) ?_ ?_
    · intro T hT
      have hstd := (Finset.mem_filter.1 hT).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun a ha => ?_, fun j hj => ?_⟩
      · have haT : a ∉ T := fun h =>
          hstd _ (Finset.mem_image_of_mem _ (Finset.mem_toLeft.1 ha)) (by simpa [gen] using h)
        simp [haT]
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
        have hns : ¬ (ix hk0 (i.val + 1) ∈ T ∧ ix hk0 (i.val + 2) ∈ T) := by
          simpa [gen, Finset.insert_subset_iff] using
            hstd _ (Finset.mem_image_of_mem _ (Finset.mem_toRight.1 hi))
        rw [ix_val_add]
        by_cases ha : ix hk0 (i.val + 1) ∈ T
        · have hb : ix hk0 (i.val + 1 + 1) ∉ T := fun hb => hns ⟨ha, hb⟩
          simp [hb]
        · simp [ha]
    · intro T _ T' _ h
      ext i
      have hi := congrFun h i
      by_cases h1 : i ∈ T <;> by_cases h2 : i ∈ T' <;> simp_all
  · rw [Finset.card_image_of_injective _ (ix_succ_injective hk0),
      Finset.card_toLeft_add_card_toRight, hLT]

theorem le_best_of {k s : ℕ} (q : Vec k → Vec k) {M : Type} [AddCommGroup M] [Module Bin M]
    [Module.Finite Bin M] [DecidableEq M] (hM : Module.finrank Bin M = s)
    (P : (Vec k × Vec k) →ₗ[Bin] M) (hP : Function.Surjective P) (v : M) :
    (univ.filter fun x => P (x, q x) = v).card ≤ best q s := by
  let e : M ≃ₗ[Bin] Vec s := LinearEquiv.ofFinrankEq M (Vec s) (by rw [hM, Module.finrank_fin_fun])
  refine le_trans (le_of_eq ?_) (le_best q (e.toLinearMap ∘ₗ P) (e v) (e.surjective.comp hP))
  congr 1
  ext x
  simp

theorem indep_le_best {k : ℕ} (hk0 : 0 < k) (A E : Finset (Fin k)) :
    (indep hk0 A E).card ≤ best (chi hk0) (A.card + E.card) := by
  classical
  have hsurj : Function.Surjective fun i : Fin k => ix hk0 (i.val + 1) :=
    Finite.injective_iff_surjective.1 (ix_succ_injective hk0)
  let S : Finset (Fin k) := univ.filter fun i => ix hk0 (i.val + 1) ∈ E
  have hS : S.card = E.card := by
    rw [← Finset.card_image_of_injective S (ix_succ_injective hk0)]
    congr 1
    ext j
    constructor
    · intro hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      exact (Finset.mem_filter.1 hi).2
    · intro hj
      obtain ⟨i, rfl⟩ := hsurj j
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩)
  let T : Vec k →ₗ[Bin] Vec k :=
    LinearMap.id + LinearMap.funLeft Bin Bin fun i : Fin k => ix hk0 (i.val + 2)
  let P : (Vec k × Vec k) →ₗ[Bin] ((A → Bin) × (S → Bin)) :=
    ((LinearMap.funLeft Bin Bin (Subtype.val : A → Fin k)) ∘ₗ LinearMap.fst Bin _ _).prod
      ((LinearMap.funLeft Bin Bin (Subtype.val : S → Fin k)) ∘ₗ
        (LinearMap.snd Bin _ _ + T ∘ₗ LinearMap.fst Bin _ _))
  have hP : ∀ y w : Vec k, P (y, w) =
      (fun a => y a.1, fun i => w i.1 + (y i.1 + y (ix hk0 (i.1.val + 2)))) := fun y w => rfl
  have hsur : Function.Surjective P := by
    rintro ⟨u, u'⟩
    refine ⟨(fun i => if h : i ∈ A then u ⟨i, h⟩ else 0,
      fun i => (if h : i ∈ S then u' ⟨i, h⟩ else 0) +
        ((if h : i ∈ A then u ⟨i, h⟩ else 0) +
          (if h : ix hk0 (i.val + 2) ∈ A then u ⟨_, h⟩ else 0))), ?_⟩
    rw [hP]
    refine Prod.ext (funext fun a => by simp) (funext fun i => ?_)
    simp only [i.2, ↓reduceDIte]
    linear_combination zmod2_add_self ((if h : i.1 ∈ A then u ⟨i.1, h⟩ else 0) +
      (if h : ix hk0 (i.1.val + 2) ∈ A then u ⟨_, h⟩ else 0))
  have hM : Module.finrank Bin ((A → Bin) × (S → Bin)) = A.card + E.card := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_coe, hS]
  refine le_trans (Finset.card_le_card fun y hy => ?_) (le_best_of (chi hk0) hM P hsur 0)
  obtain ⟨hA, hE⟩ := (Finset.mem_filter.1 hy).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  rw [hP]
  refine Prod.ext (funext fun a => hA a.1 a.2) (funext fun i => ?_)
  have h := hE _ (Finset.mem_filter.1 i.2).2
  rw [ix_val_add] at h
  show chi hk0 y i.1 + (y i.1 + y (ix hk0 (i.1.val + 2))) = 0
  simp only [chi]
  linear_combination h + zmod2_add_self (y i.1) + zmod2_add_self (y (ix hk0 (i.1.val + 2)))

theorem two_pow_le_best_zero {k : ℕ} (q : Vec k → Vec k) : 2 ^ k ≤ best q 0 := by
  have h := le_best q (0 : (Vec k × Vec k) →ₗ[Bin] Vec 0) 0 fun v => ⟨0, Subsingleton.elim _ _⟩
  simpa [Fintype.card_pi, ZMod.card] using h

theorem one_le_best {k s : ℕ} (q : Vec k → Vec k) (hs : s ≤ 2 * k) : 1 ≤ best q s := by
  obtain ⟨J, hJ⟩ : ∃ J : Vec s →ₗ[Bin] (Vec k × Vec k), Function.Injective J :=
    finrank_le_iff_exists_linearMap.mp (by
      rw [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_fin_fun]
      omega)
  obtain ⟨P, hPJ⟩ := J.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hJ)
  have hsur : Function.Surjective P := fun v => ⟨J v, LinearMap.congr_fun hPJ v⟩
  have hmem : (0 : Vec k) ∈ univ.filter fun x => P (x, q x) = P (0, q 0) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  exact le_trans (Finset.card_pos.2 ⟨0, hmem⟩) (le_best q P _ hsur)

theorem best_le_two_pow {k s : ℕ} (q : Vec k → Vec k) : best q s ≤ 2 ^ (2 * k - s) := by
  refine best_le_slices q fun R c hR => ?_
  have h : count (fun z : R => (z.val + c).2 = q (z.val + c).1) ≤ Nat.card R :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [card_bin] at h
  exact h.trans (Nat.pow_le_pow_right (by omega) (by omega))

lemma chi_one (h : 0 < 1) (y : Vec 1) : chi h y = y := by
  funext i
  have e1 : ix h (i.val + 1) = i := Subsingleton.elim _ _
  have e2 : ix h (i.val + 2) = i := Subsingleton.elim _ _
  have hx : ∀ x : Bin, x + (1 + x) * x = x := by decide
  simp only [chi, e1, e2, hx]

lemma chi_two : ∀ y : Vec 2, chi Nat.zero_lt_two y = fun _ => y 0 * y 1 := by decide

lemma card_two_a : 3 ≤ (univ.filter fun y : Vec 2 => y 0 * y 1 = 0).card := by decide

lemma card_two_b : 2 ≤ (univ.filter fun y : Vec 2 => y 0 = 0).card := by decide

lemma two_le_best_chi_one (h : 0 < 1) : 2 ≤ best (chi h) 1 := by
  have hsur : Function.Surjective
      (LinearMap.fst Bin (Vec 1) (Vec 1) + LinearMap.snd Bin (Vec 1) (Vec 1)) :=
    fun v => ⟨(v, 0), by simp⟩
  have h1 := le_best (chi h) _ 0 hsur
  rw [Finset.filter_true_of_mem fun x _ => by
    rw [chi_one]
    funext i
    simp [zmod2_add_self], Finset.card_univ] at h1
  simpa [Fintype.card_pi, ZMod.card] using h1

lemma four_le_best_chi_two : 4 ≤ best (chi Nat.zero_lt_two) 1 := by
  let P : (Vec 2 × Vec 2) →ₗ[Bin] Bin :=
    ((LinearMap.proj 0 : Vec 2 →ₗ[Bin] Bin) + (LinearMap.proj 1 : Vec 2 →ₗ[Bin] Bin)) ∘ₗ
      LinearMap.snd Bin (Vec 2) (Vec 2)
  have hsur : Function.Surjective P := fun c => ⟨(0, Pi.single 0 c), by simp [P]⟩
  have h1 := le_best_of (chi Nat.zero_lt_two) (Module.finrank_self Bin) P hsur 0
  rw [Finset.filter_true_of_mem fun x _ => by
    simp [P, chi_two, zmod2_add_self], Finset.card_univ] at h1
  simpa [Fintype.card_pi, ZMod.card] using h1

lemma three_le_best_chi_two : 3 ≤ best (chi Nat.zero_lt_two) 2 := by
  refine le_trans (card_two_a.trans (Finset.card_le_card fun y hy => ?_))
    (le_best (chi Nat.zero_lt_two) (LinearMap.snd Bin (Vec 2) (Vec 2)) 0
      LinearMap.snd_surjective)
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  rw [LinearMap.snd_apply, chi_two, (Finset.mem_filter.1 hy).2]
  rfl

lemma two_le_best_chi_two : 2 ≤ best (chi Nat.zero_lt_two) 3 := by
  let P : (Vec 2 × Vec 2) →ₗ[Bin] (Vec 2 × Bin) :=
    (LinearMap.snd Bin (Vec 2) (Vec 2)).prod (LinearMap.proj 0 ∘ₗ LinearMap.fst Bin (Vec 2) (Vec 2))
  have hsur : Function.Surjective P := fun v => ⟨(Pi.single 0 v.2, v.1), by simp [P]⟩
  have hM : Module.finrank Bin (Vec 2 × Bin) = 3 := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_self]
  refine le_trans (card_two_b.trans (Finset.card_le_card fun y hy => ?_))
    (le_best_of (chi Nat.zero_lt_two) hM P hsur 0)
  have hy0 : y 0 = 0 := (Finset.mem_filter.1 hy).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  show (chi Nat.zero_lt_two y, y 0) = 0
  rw [chi_two, hy0, zero_mul]
  rfl

lemma chi_two_fiber_le {P : (Vec 2 × Vec 2) →ₗ[Bin] Vec 2} (hP : Function.Surjective P)
    (v : Vec 2) : (univ.filter fun y => P (y, chi Nat.zero_lt_two y) = v).card ≤ 3 := by
  by_contra hlt
  have hcard : (univ.filter fun y : Vec 2 => P (y, chi Nat.zero_lt_two y) = v).card =
      Fintype.card (Vec 2) := by
    have h1 := Finset.card_filter_le (univ : Finset (Vec 2))
      fun y => P (y, chi Nat.zero_lt_two y) = v
    have h2 : Fintype.card (Vec 2) = 4 := by decide
    rw [Finset.card_univ] at h1
    omega
  have hall : ∀ y : Vec 2, P (y, fun _ => y 0 * y 1) = v := fun y => by
    have h := Finset.mem_univ y
    rw [← (Finset.card_eq_iff_eq_univ _).1 hcard] at h
    exact chi_two y ▸ (Finset.mem_filter.1 h).2
  have hexp : ∀ y w : Vec 2, P (y, w) = y 0 • P (bas (Sum.inl 0)) + y 1 • P (bas (Sum.inl 1)) +
      (w 0 • P (bas (Sum.inr 0)) + w 1 • P (bas (Sum.inr 1))) := fun y w => by
    rw [map_expand, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]
    rfl
  have hv : v = 0 := by
    rw [← hall 0, hexp]
    simp
  have hA : P (bas (Sum.inl 0)) = 0 := by
    have h := hall (Pi.single 0 1)
    rw [hexp, hv] at h
    simpa using h
  have hB : P (bas (Sum.inl 1)) = 0 := by
    have h := hall (Pi.single 1 1)
    rw [hexp, hv] at h
    simpa using h
  have hCD : P (bas (Sum.inr 0)) + P (bas (Sum.inr 1)) = 0 := by
    have h := hall (fun _ => 1)
    rw [hexp, hv, hA, hB] at h
    simpa using h
  obtain ⟨⟨y, w⟩, h1⟩ := hP (Pi.single 0 1)
  obtain ⟨⟨y', w'⟩, h2⟩ := hP (Pi.single 1 1)
  rw [hexp, hA, hB] at h1 h2
  have key : ∀ c0 c1 d0 d1 a b a' b' : Bin, c0 + d0 = 0 → c1 + d1 = 0 → a * c0 + b * d0 = 1 →
      a * c1 + b * d1 = 0 → a' * c0 + b' * d0 = 0 → a' * c1 + b' * d1 = 1 → False := by decide
  exact key _ _ _ _ (w 0) (w 1) (w' 0) (w' 1) (congrFun hCD 0) (congrFun hCD 1)
    (by simpa using congrFun h1 0) (by simpa using congrFun h1 1)
    (by simpa using congrFun h2 0) (by simpa using congrFun h2 1)

theorem best_chi_le {k : ℕ} (hk0 : 0 < k) {t : ℕ} (ht : t ≤ 2 * k) :
    best (chi hk0) t ≤ base k t := by
  rcases Nat.lt_or_ge k 3 with h | h
  · have hgen := le_min (best_total (chi hk0) (s := t)) (best_le_two_pow (chi hk0) (s := t))
    interval_cases k
    · simpa [base] using hgen
    · interval_cases t
      · simpa [base] using hgen
      · simpa [base] using hgen
      · exact best_le fun P v hP => chi_two_fiber_le hP v
      · simpa [base] using hgen
      · simpa [base] using hgen
  · exact best_le fun P v hP => chi_fiber_le h hk0 P v hP

theorem base_le_best_chi {k : ℕ} (hk0 : 0 < k) {s : ℕ} (hs : s ≤ 2 * k) :
    base k s ≤ best (chi hk0) s := by
  rcases Nat.lt_or_ge k 3 with h | h
  · interval_cases k
    · interval_cases s
      · exact two_pow_le_best_zero (k := 1) _
      · exact two_le_best_chi_one hk0
      · exact one_le_best _ (le_refl _)
    · interval_cases s
      · exact two_pow_le_best_zero (k := 2) _
      · exact four_le_best_chi_two
      · exact three_le_best_chi_two
      · exact two_le_best_chi_two
      · exact one_le_best _ (le_refl _)
  · obtain ⟨A, E, hAE, hge⟩ := exists_indep_card_ge h s hs
    exact hge.trans (hAE ▸ indep_le_best hk0 A E)

lemma chi_shear {k : ℕ} (hk : 0 < k) (d : Vec k) :
    ∃ B : Vec k →ₗ[Bin] Vec k, ∀ x, chi hk (x + d) = chi hk x + B x + (chi hk d - chi hk 0) := by
  refine ⟨{ toFun := fun x i => x (ix hk (i.val + 1)) * d (ix hk (i.val + 2)) +
              d (ix hk (i.val + 1)) * x (ix hk (i.val + 2))
            map_add' := fun x y => ?_
            map_smul' := fun c x => ?_ }, fun x => ?_⟩
  · funext i
    simp only [Pi.add_apply]
    ring
  · funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  · funext i
    simp only [chi, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, LinearMap.coe_mk, AddHom.coe_mk]
    ring

lemma finrank_ker_mix_rot {k : ℕ} (hk : 0 < k) (column : Bool) :
    Module.finrank Bin (LinearMap.ker
      (mixLin hk (if column then 2 else 1) ∘ₗ rotLin hk (if column then 3 else 1))) =
      if 3 ∣ k then (if column = true ∧ 2 ∣ k then 4 else 2) else 0 := by
  have h1 : ∀ g r : ℕ, LinearMap.ker (mixLin hk g ∘ₗ rotLin hk r) =
      (LinearMap.ker (mixLin hk g)).map (LinearEquiv.ofBijective (rotLin hk r)
        (rotLin_bijective hk r)).symm.toLinearMap := fun g r => by
    rw [LinearMap.ker_comp]
    exact Submodule.comap_equiv_eq_map_symm
      (LinearEquiv.ofBijective (rotLin hk r) (rotLin_bijective hk r)) _
  cases column
  · show Module.finrank Bin (LinearMap.ker (mixLin hk 1 ∘ₗ rotLin hk 1)) =
      if 3 ∣ k then (if false = true ∧ 2 ∣ k then 4 else 2) else 0
    rw [h1, LinearEquiv.finrank_map_eq, finrank_ker_mixLin hk 1]
    simp
  · show Module.finrank Bin (LinearMap.ker (mixLin hk 2 ∘ₗ rotLin hk 3)) =
      if 3 ∣ k then (if true = true ∧ 2 ∣ k then 4 else 2) else 0
    rw [h1, LinearEquiv.finrank_map_eq, finrank_ker_mixLin hk 2]
    simp only [true_and]
    by_cases h2 : 2 ∣ k
    · obtain ⟨m, rfl⟩ := h2
      have h2' : 2 ∣ 2 * m := Dvd.intro m rfl
      rw [Nat.gcd_eq_right h2', Nat.mul_div_cancel_left m Nat.two_pos]
      by_cases h3 : 3 ∣ m
      · have h3' : 3 ∣ 2 * m := Dvd.dvd.mul_left h3 2
        simp only [h2', h3, h3', ↓reduceIte]
      · have h3' : ¬ 3 ∣ 2 * m := fun h => h3 (by omega)
        simp only [h3, h3', ↓reduceIte]
    · rw [Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h2), Nat.div_one]
      simp only [h2, ↓reduceIte, Nat.mul_one]

def runMap {k : ℕ} (hk : 0 < k) (column : Bool) (name constant : Vec k) : Vec k → Vec k :=
  fun raw site =>
    let rot := fun (n : ℕ) (word : Vec k) (i : Fin k) => word (ix hk (i.val + k - n % k))
    let gap := if column then 2 else 1
    let old := rot (if column then 3 else 1) raw + name
    let y := fun u : Fin k => old u + old (ix hk (u.val + gap)) + old (ix hk (u.val + k - gap % k))
    y site + (1 + y (ix hk (site.val + 1))) * y (ix hk (site.val + 2)) +
      rot (if column then 4 else 0) raw site + constant site

theorem main_bound {k : ℕ} (hk : 0 < k) (column : Bool) (name constant : Vec k) {s : ℕ}
    (hs : s ≤ 2 * k) (h j : ℕ)
    (hh : h = if 3 ∣ k then (if column = true ∧ 2 ∣ k then 4 else 2) else 0)
    (hj : j = min h (2 * k - s)) :
    base k s ≤ best (runMap hk column name constant) s ∧
      best (runMap hk column name constant) s ≤ min (2 ^ k) (2 ^ j * base k (s + j)) := by
  have hrun : runMap hk column name constant = fun x =>
      chi hk ((mixLin hk (if column then 2 else 1) ∘ₗ rotLin hk (if column then 3 else 1)) x +
        mixLin hk (if column then 2 else 1) name) + rotLin hk (if column then 4 else 0) x +
        constant := by
    funext raw
    rw [LinearMap.comp_apply, ← map_add]
    rfl
  have hup := upper (s := s) (chi hk)
    (mixLin hk (if column then 2 else 1) ∘ₗ rotLin hk (if column then 3 else 1))
    (mixLin hk (if column then 2 else 1) name) (rotLin hk (if column then 4 else 0)) constant
  simp only [finrank_ker_mix_rot, ← hh, ← two_mul, ← hj] at hup
  rw [hrun]
  exact ⟨(base_le_best_chi hk hs).trans (lower (chi hk) _ _ _ _ (chi_shear hk)),
    le_min (best_total _) (hup.trans (Nat.mul_le_mul_left _ (best_chi_le hk (by omega))))⟩

end PEqualNP.Outside.L_meta_30867

theorem PEqualNP.Outside.L_meta_30867 :
(
∀ (k : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (n : Nat) (word : W) (i : Fin k) => word (ix (i.val+k-n % k))
  let base := fun t : Nat =>
    if k = 1 then min 2 (2^(2-t))
    else if k = 2 then min 4 (5-t)
    else if t < k then 2^(k-t-1) * Nat.fib (t+3)
    else if t = k then Nat.fib (k-1) + Nat.fib (k+1)
    else let p := t-k
         if 2*p < k then 2^(p-1) * Nat.fib (k-2*p+3) else 2^(k-p)
  let best := fun (φ : W → W) (s : Nat) =>
    sSup {n : Nat | ∃ (P : (W × W) →ₗ[F] (Fin s → F)) (v : Fin s → F),
      Function.Surjective P ∧ n = ((Finset.univ : Finset W).filter
        (fun x => P (x,φ x) = v)).card}
  ∀ (column : Bool) (name constant : W) (s : Nat), s ≤ 2*k →
    let gap := if column then 2 else 1
    let run := fun (raw : W) (site : Fin k) =>
      let old := rot (if column then 3 else 1) raw + name
      let y := fun u : Fin k => old u + old (ix (u.val+gap)) + old (ix (u.val+k-gap % k))
      y site + (1+y (ix (site.val+1)))*y (ix (site.val+2)) +
        rot (if column then 4 else 0) raw site + constant site
    let h := if 3 ∣ k then (if column = true ∧ 2 ∣ k then 4 else 2) else 0
    let j := min h (2*k-s)
    base s ≤ best run s ∧ best run s ≤ min (2^k) (2^j * base (s+j))
) := by
  intro k hk F W ix' rot base' best' column name constant s hs gap run h j
  exact PEqualNP.Outside.L_meta_30867.main_bound hk column name constant hs h j rfl rfl
