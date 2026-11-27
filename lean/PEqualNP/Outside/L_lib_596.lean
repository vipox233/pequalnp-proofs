import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_596_aux

private def linGen {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2)) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun a := ∑ h : Fin m, a h • gen h
  map_add' a b := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

private def projSub {k : ℕ} (S : Finset (Fin k)) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (↥S → ZMod 2) where
  toFun w s := w s.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def codeSub {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2)) :
    Submodule (ZMod 2) (Fin k → ZMod 2) :=
  LinearMap.range (linGen gen)

private def kerOn {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2)) (S : Finset (Fin k)) :
    Submodule (ZMod 2) ↥(codeSub gen) :=
  LinearMap.ker ((projSub S).comp (codeSub gen).subtype)

private theorem mem_kerOn_iff {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2))
    (S : Finset (Fin k)) (w : ↥(codeSub gen)) :
    w ∈ kerOn gen S ↔ ∀ x ∈ S, w.val x = 0 := by
  simp only [kerOn, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, projSub,
    LinearMap.coe_mk, AddHom.coe_mk, funext_iff, Pi.zero_apply, Subtype.forall]

private theorem rk_eq_finrank_range {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2))
    (S : Finset (Fin k)) :
    (Matrix.of fun (row : Fin m) (coord : ↥S) => gen row coord.val).rank =
      Module.finrank (ZMod 2) ↥(LinearMap.range ((projSub S).comp (codeSub gen).subtype)) := by
  let M : Matrix (Fin m) ↥S (ZMod 2) := fun row coord => gen row coord.val
  change M.rank = _
  rw [← Matrix.rank_transpose]
  unfold Matrix.rank
  have hmul : M.transpose.mulVecLin = (projSub S).comp (linGen gen) := by
    apply LinearMap.ext
    intro a
    funext c
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M,
      LinearMap.comp_apply, projSub, linGen, LinearMap.coe_mk, AddHom.coe_mk,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  rw [hmul, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
  rfl

private theorem rk_add_ker {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2))
    (S : Finset (Fin k)) :
    (Matrix.of fun (row : Fin m) (coord : ↥S) => gen row coord.val).rank +
      Module.finrank (ZMod 2) ↥(kerOn gen S) =
      Module.finrank (ZMod 2) ↥(codeSub gen) := by
  rw [rk_eq_finrank_range]
  exact LinearMap.finrank_range_add_finrank_ker ((projSub S).comp (codeSub gen).subtype)

private theorem kerOn_univ {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2)) :
    kerOn gen Finset.univ = ⊥ := by
  ext w
  rw [mem_kerOn_iff, Submodule.mem_bot, Subtype.ext_iff]
  simp only [Finset.mem_univ, forall_true_left, Submodule.coe_zero, funext_iff, Pi.zero_apply]

private theorem rk_univ {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2)) :
    (Matrix.of fun (row : Fin m) (coord : ↥(Finset.univ : Finset (Fin k))) => gen row coord.val).rank =
      Module.finrank (ZMod 2) ↥(codeSub gen) := by
  have h := rk_add_ker gen Finset.univ
  rw [kerOn_univ, finrank_bot, Nat.add_zero] at h
  exact h

private theorem kerOn_inf_bot {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2))
    (P Q : Finset (Fin k)) (hPQ : ∀ x : Fin k, x ∈ P ∨ x ∈ Q) :
    kerOn gen P ⊓ kerOn gen Q = ⊥ := by
  ext w
  simp only [Submodule.mem_inf, mem_kerOn_iff, Submodule.mem_bot, Subtype.ext_iff,
    Submodule.coe_zero, funext_iff, Pi.zero_apply]
  constructor
  · rintro ⟨hP, hQ⟩ x
    rcases hPQ x with hx | hx
    · exact hP x hx
    · exact hQ x hx
  · intro h
    exact ⟨fun x _ => h x, fun x _ => h x⟩

private theorem finrank_quot_cut {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2))
    (P Q : Finset (Fin k)) (hPQ : ∀ x : Fin k, x ∈ P ∨ x ∈ Q) :
    Module.finrank (ZMod 2) (↥(codeSub gen) ⧸ (kerOn gen P ⊔ kerOn gen Q)) =
      (Matrix.of fun (row : Fin m) (coord : ↥P) => gen row coord.val).rank +
      (Matrix.of fun (row : Fin m) (coord : ↥Q) => gen row coord.val).rank -
      (Matrix.of fun (row : Fin m) (coord : ↥(Finset.univ : Finset (Fin k))) => gen row coord.val).rank := by
  have hP := rk_add_ker gen P
  have hQ := rk_add_ker gen Q
  have hU := rk_univ gen
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (kerOn gen P) (kerOn gen Q)
  rw [kerOn_inf_bot gen P Q hPQ, finrank_bot, Nat.add_zero] at hsup
  have hq := Submodule.finrank_quotient_add_finrank (kerOn gen P ⊔ kerOn gen Q)
  omega

private theorem card_quot_cut {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2))
    (P Q : Finset (Fin k)) (hPQ : ∀ x : Fin k, x ∈ P ∨ x ∈ Q) :
    Nat.card (↥(codeSub gen) ⧸ (kerOn gen P ⊔ kerOn gen Q)) =
      2 ^ ((Matrix.of fun (row : Fin m) (coord : ↥P) => gen row coord.val).rank +
           (Matrix.of fun (row : Fin m) (coord : ↥Q) => gen row coord.val).rank -
           (Matrix.of fun (row : Fin m) (coord : ↥(Finset.univ : Finset (Fin k))) => gen row coord.val).rank) := by
  let _ : Finite ↥(codeSub gen) := Subtype.finite
  let _ : Finite (↥(codeSub gen) ⧸ (kerOn gen P ⊔ kerOn gen Q)) := Quotient.finite _
  let _ : Fintype (↥(codeSub gen) ⧸ (kerOn gen P ⊔ kerOn gen Q)) := Fintype.ofFinite _
  rw [← finrank_quot_cut gen P Q hPQ, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]

private theorem quot_eq_iff_glued {k m : ℕ} (gen : Fin m → (Fin k → ZMod 2))
    (P Q : Finset (Fin k)) (w₁ w₂ : ↥(codeSub gen)) :
    Submodule.Quotient.mk (p := kerOn gen P ⊔ kerOn gen Q) w₁ =
      Submodule.Quotient.mk (p := kerOn gen P ⊔ kerOn gen Q) w₂ ↔
    ∃ w : ↥(codeSub gen), (∀ x ∈ P, w.val x = w₁.val x) ∧ (∀ x ∈ Q, w.val x = w₂.val x) := by
  rw [Submodule.Quotient.eq, Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    refine ⟨w₁ - u, ?_, ?_⟩
    · intro x hx
      have hux : u.val x = 0 := (mem_kerOn_iff gen P u).mp hu x hx
      simp [hux]
    · intro x hx
      have hvx : v.val x = 0 := (mem_kerOn_iff gen Q v).mp hv x hx
      have hweq : w₁ - u = w₂ + v := by
        have h1 : w₁ - w₂ = u + v := huv.symm
        calc w₁ - u = (w₁ - w₂) + w₂ - u := by abel
          _ = (u + v) + w₂ - u := by rw [h1]
          _ = w₂ + v := by abel
      rw [hweq]
      simp [hvx]
  · rintro ⟨w, hP, hQ⟩
    refine ⟨w₁ - w, ?_, w - w₂, ?_, by abel⟩
    · rw [mem_kerOn_iff]
      intro x hx
      simp [hP x hx]
    · rw [mem_kerOn_iff]
      intro x hx
      simp [hQ x hx]

private def runLin {F : Type} [Field F] {t d : ℕ} {T : Fin t → Type}
    (step : (j : Fin t) → T j → ((Fin d → F) →ₗ[F] (Fin d → F)))
    (tests : (j : Fin t) → T j) (ls : List (Fin t)) : (Fin d → F) →ₗ[F] (Fin d → F) :=
  ls.foldl (fun M j => (step j (tests j)).comp M) LinearMap.id

private theorem runLin_apply {F : Type} [Field F] {t d : ℕ} {T : Fin t → Type}
    (step : (j : Fin t) → T j → ((Fin d → F) →ₗ[F] (Fin d → F)))
    (tests : (j : Fin t) → T j) (ls : List (Fin t)) (x : Fin d → F) :
    runLin step tests ls x = ls.foldl (fun cur j => step j (tests j) cur) x := by
  suffices ∀ (M : (Fin d → F) →ₗ[F] (Fin d → F)),
      (ls.foldl (fun A j => (step j (tests j)).comp A) M) x =
      ls.foldl (fun cur j => step j (tests j) cur) (M x) by
    exact this LinearMap.id
  induction ls with
  | nil => intro M; rfl
  | cons j rest ih =>
    intro M
    simp only [List.foldl_cons]
    exact ih ((step j (tests j)).comp M)

private theorem mem_take_finRange_lt {t i : ℕ} {j : Fin t} (hj : j ∈ (List.finRange t).take i) :
    j.val < i := by
  rcases List.mem_iff_getElem.mp hj with ⟨r, hr, hget⟩
  have hlen : ((List.finRange t).take i).length = min i t := by simp
  have hri : r < i := by omega
  rw [List.getElem_take, List.getElem_finRange] at hget
  rw [← hget]
  exact hri

private theorem mem_drop_finRange_ge {t i : ℕ} {j : Fin t} (hj : j ∈ (List.finRange t).drop i) :
    i ≤ j.val := by
  rcases List.mem_iff_getElem.mp hj with ⟨r, hr, hget⟩
  rw [List.getElem_drop, List.getElem_finRange] at hget
  have hval := congrArg Fin.val hget
  simp only [Fin.val_cast] at hval
  omega

private theorem foldl_congr_mem {α β : Type*} (l : List α) (f g : β → α → β)
    (h : ∀ a ∈ l, ∀ b, f b a = g b a) (init : β) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl_cons, h a (by simp) init]
    exact ih (fun x hx => h x (by simp [hx])) _

private theorem finRange_take_succ {t i : ℕ} (hi : i < t) :
    (List.finRange t).take (i + 1) = (List.finRange t).take i ++ [⟨i, hi⟩] := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left (by omega : i + 1 ≤ t), Nat.min_eq_left (by omega : i ≤ t)]
  · intro r h1 h2
    simp only [List.length_take, List.length_finRange, Nat.min_eq_left (by omega : i + 1 ≤ t)] at h1
    rw [List.getElem_take, List.getElem_finRange]
    by_cases hri : r < i
    · rw [List.getElem_append_left (by simp [Nat.min_eq_left (by omega : i ≤ t), hri]),
        List.getElem_take, List.getElem_finRange]
    · have hreq : r = i := by omega
      apply Fin.ext
      rw [List.getElem_append_right (by simp [Nat.min_eq_left (by omega : i ≤ t), hreq])]
      simp [Nat.min_eq_left (by omega : i ≤ t), hreq]

private theorem dir_le (F : Type) [Field F] (k m t d : ℕ)
    (base : Fin k → ZMod 2) (gen : Fin m → (Fin k → ZMod 2))
    (scope : Fin t → Finset (Fin k))
    (hcov : ∀ v : Fin k, ∃ j : Fin t, v ∈ scope j)
    (s : Fin d → F)
    (step : (j : Fin t) → ((↥(scope j) → ZMod 2) → Bool) → ((Fin d → F) →ₗ[F] (Fin d → F)))
    (out : (Fin d → F) →ₗ[F] F)
    (hrun : ∀ tests : (j : Fin t) → ((↥(scope j) → ZMod 2) → Bool),
      out ((List.finRange t).foldl (fun cur stage => step stage (tests stage) cur) s) =
        (Nat.card {w : Fin k → ZMod 2 //
          w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧
          ∀ j, tests j (fun tested => w tested.val) = true} : F)) :
    (Finset.range (t + 1)).sup (fun i =>
      let P := Finset.univ.filter (fun seen : Fin k => ∃ before : Fin t, before.val < i ∧ seen ∈ scope before)
      let Q := Finset.univ.filter (fun future : Fin k => ∃ after : Fin t, i ≤ after.val ∧ future ∈ scope after)
      2 ^ ((Matrix.of fun (row : Fin m) (coord : ↥P) => gen row coord.val).rank +
           (Matrix.of fun (row : Fin m) (coord : ↥Q) => gen row coord.val).rank -
           (Matrix.of fun (row : Fin m) (coord : ↥(Finset.univ : Finset (Fin k))) => gen row coord.val).rank)) ≤ d := by
  classical
  rw [Finset.sup_le_iff]
  intro i hi
  dsimp only
  let P := Finset.univ.filter (fun seen : Fin k => ∃ before : Fin t, before.val < i ∧ seen ∈ scope before)
  let Q := Finset.univ.filter (fun future : Fin k => ∃ after : Fin t, i ≤ after.val ∧ future ∈ scope after)
  have hPQ : ∀ x : Fin k, x ∈ P ∨ x ∈ Q := by
    intro x
    rcases hcov x with ⟨j, hj⟩
    by_cases hji : j.val < i
    · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, j, hji, hj⟩
    · right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, j, by omega, hj⟩
  let C := ↥(codeSub gen) ⧸ (kerOn gen P ⊔ kerOn gen Q)
  let _ : Fintype C := Fintype.ofFinite C
  have hcardC : Fintype.card C =
      2 ^ ((Matrix.of fun (row : Fin m) (coord : ↥P) => gen row coord.val).rank +
           (Matrix.of fun (row : Fin m) (coord : ↥Q) => gen row coord.val).rank -
           (Matrix.of fun (row : Fin m) (coord : ↥(Finset.univ : Finset (Fin k))) => gen row coord.val).rank) := by
    rw [← Nat.card_eq_fintype_card]
    exact card_quot_cut gen P Q hPQ
  rw [← hcardC]
  have hsurj : ∀ c : C, ∃ w : ↥(codeSub gen), Submodule.Quotient.mk w = c :=
    fun c => Quotient.exists_rep c
  choose rep hrep using hsurj
  let word : C → (Fin k → ZMod 2) := fun c => base + (rep c).val
  let pin : C → (j : Fin t) → ((↥(scope j) → ZMod 2) → Bool) :=
    fun c j x => decide (∀ z : ↥(scope j), x z = word c z.val)
  let comb : C → C → (j : Fin t) → ((↥(scope j) → ZMod 2) → Bool) :=
    fun c₁ c₂ j => if j.val < i then pin c₁ j else pin c₂ j
  let u : C → (Fin d → F) := fun c₁ =>
    ((List.finRange t).take i).foldl (fun cur stage => step stage (pin c₁ stage) cur) s
  let f : C → ((Fin d → F) →ₗ[F] F) := fun c₂ =>
    out.comp (runLin step (pin c₂) ((List.finRange t).drop i))
  have hpair : ∀ c₁ c₂ : C, f c₂ (u c₁) = if c₁ = c₂ then (1 : F) else 0 := by
    intro c₁ c₂
    have hfold_split : out ((List.finRange t).foldl (fun cur stage => step stage (comb c₁ c₂ stage) cur) s) =
        f c₂ (u c₁) := by
      have hsp := (List.take_append_drop i (List.finRange t)).symm
      conv_lhs => rw [hsp, List.foldl_append]
      have hleft : ((List.finRange t).take i).foldl (fun cur stage => step stage (comb c₁ c₂ stage) cur) s =
          u c₁ := by
        apply foldl_congr_mem
        intro j hj cur
        have hlt : j.val < i := mem_take_finRange_lt hj
        simp only [comb, hlt, ite_true]
      rw [hleft]
      have hright : ((List.finRange t).drop i).foldl (fun cur stage => step stage (comb c₁ c₂ stage) cur) (u c₁) =
          ((List.finRange t).drop i).foldl (fun cur stage => step stage (pin c₂ stage) cur) (u c₁) := by
        apply foldl_congr_mem
        intro j hj cur
        have hge : i ≤ j.val := mem_drop_finRange_ge hj
        simp only [comb, show ¬ j.val < i by omega, ite_false]
      rw [hright, ← runLin_apply]
      rfl
    rw [← hfold_split, hrun (comb c₁ c₂)]
    have hsol_iff : ∀ w : Fin k → ZMod 2,
        (w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧
          ∀ j : Fin t, comb c₁ c₂ j (fun tested => w tested.val) = true) ↔
        ∃ v : ↥(codeSub gen), w = base + v.val ∧
          (∀ x ∈ P, v.val x = (rep c₁).val x) ∧ (∀ x ∈ Q, v.val x = (rep c₂).val x) := by
      intro w
      constructor
      · rintro ⟨⟨a, rfl⟩, htests⟩
        refine ⟨⟨linGen gen a, LinearMap.mem_range_self _ a⟩, rfl, ?_, ?_⟩
        · intro x hx
          rcases (Finset.mem_filter.mp hx).2 with ⟨j, hji, hxj⟩
          have ht := htests j
          simp only [comb, hji, ite_true, pin, decide_eq_true_eq] at ht
          have hzx := ht ⟨x, hxj⟩
          simp only [word, Pi.add_apply] at hzx
          change (∑ h : Fin m, a h • gen h) x = (rep c₁).val x
          exact add_left_cancel hzx
        · intro x hx
          rcases (Finset.mem_filter.mp hx).2 with ⟨j, hji, hxj⟩
          have ht := htests j
          simp only [comb, show ¬ j.val < i by omega, ite_false, pin, decide_eq_true_eq] at ht
          have hzx := ht ⟨x, hxj⟩
          simp only [word, Pi.add_apply] at hzx
          change (∑ h : Fin m, a h • gen h) x = (rep c₂).val x
          exact add_left_cancel hzx
      · rintro ⟨v, rfl, hPv, hQv⟩
        rcases v.property with ⟨a, ha⟩
        refine ⟨⟨a, by rw [← ha]; rfl⟩, ?_⟩
        intro j
        by_cases hji : j.val < i
        · simp only [comb, hji, ite_true, pin, decide_eq_true_eq]
          intro z
          have hzP : z.val ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hji, z.property⟩
          simp only [word, Pi.add_apply, hPv z.val hzP]
        · simp only [comb, hji, ite_false, pin, decide_eq_true_eq]
          intro z
          have hzQ : z.val ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, by omega, z.property⟩
          simp only [word, Pi.add_apply, hQv z.val hzQ]
    by_cases heq : c₁ = c₂
    · subst heq
      have huniq : ∀ y : {w : Fin k → ZMod 2 //
          w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧
          ∀ j, comb c₁ c₁ j (fun tested => w tested.val) = true},
          y.val = word c₁ := by
        intro y
        rcases (hsol_iff y.val).mp y.property with ⟨v, hyv, hPv, hQv⟩
        rw [hyv]
        congr 1
        funext x
        rcases hPQ x with hx | hx
        · exact hPv x hx
        · exact hQv x hx
      have hmem0 : word c₁ ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧
          ∀ j, comb c₁ c₁ j (fun tested => word c₁ tested.val) = true :=
        (hsol_iff (word c₁)).mpr ⟨rep c₁, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
      have hcard1 : Nat.card {w : Fin k → ZMod 2 //
          w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧
          ∀ j, comb c₁ c₁ j (fun tested => w tested.val) = true} = 1 := by
        let _ : Unique {w : Fin k → ZMod 2 //
            w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧
            ∀ j, comb c₁ c₁ j (fun tested => w tested.val) = true} :=
          { default := ⟨word c₁, hmem0⟩
            uniq := fun y => Subtype.ext (huniq y) }
        exact Nat.card_unique
      rw [hcard1]
      simp
    · have hemp : IsEmpty {w : Fin k → ZMod 2 //
          w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧
          ∀ j, comb c₁ c₂ j (fun tested => w tested.val) = true} := by
        refine ⟨fun y => ?_⟩
        rcases (hsol_iff y.val).mp y.property with ⟨v, _, hPv, hQv⟩
        have hmk : Submodule.Quotient.mk (p := kerOn gen P ⊔ kerOn gen Q) (rep c₁) =
            Submodule.Quotient.mk (p := kerOn gen P ⊔ kerOn gen Q) (rep c₂) :=
          (quot_eq_iff_glued gen P Q (rep c₁) (rep c₂)).mpr ⟨v, hPv, hQv⟩
        rw [hrep c₁, hrep c₂] at hmk
        exact heq hmk
      have hcard0 : Nat.card {w : Fin k → ZMod 2 //
          w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧
          ∀ j, comb c₁ c₂ j (fun tested => w tested.val) = true} = 0 := by
        rw [Nat.card_eq_fintype_card]
        exact @Fintype.card_eq_zero _ _ hemp
      rw [hcard0]
      simp [heq]
  have hli : LinearIndependent F u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg c₂
    have h0 : f c₂ (∑ c₁ : C, g c₁ • u c₁) = 0 := by rw [hg, map_zero]
    rw [map_sum] at h0
    have hterm : ∀ c₁ : C, f c₂ (g c₁ • u c₁) = if c₁ = c₂ then g c₁ else 0 := by
      intro c₁
      rw [map_smul, smul_eq_mul, hpair c₁ c₂]
      split_ifs <;> simp
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h0
    exact h0
  have hle := hli.fintype_card_le_finrank
  rw [Module.finrank_fin_fun] at hle
  exact hle

private theorem dir_ge (F : Type) [Field F] (k m t d : ℕ)
    (base : Fin k → ZMod 2) (gen : Fin m → (Fin k → ZMod 2))
    (scope : Fin t → Finset (Fin k))
    (hcov : ∀ v : Fin k, ∃ j : Fin t, v ∈ scope j)
    (hneed : (Finset.range (t + 1)).sup (fun i =>
      let P := Finset.univ.filter (fun seen : Fin k => ∃ before : Fin t, before.val < i ∧ seen ∈ scope before)
      let Q := Finset.univ.filter (fun future : Fin k => ∃ after : Fin t, i ≤ after.val ∧ future ∈ scope after)
      2 ^ ((Matrix.of fun (row : Fin m) (coord : ↥P) => gen row coord.val).rank +
           (Matrix.of fun (row : Fin m) (coord : ↥Q) => gen row coord.val).rank -
           (Matrix.of fun (row : Fin m) (coord : ↥(Finset.univ : Finset (Fin k))) => gen row coord.val).rank)) ≤ d) :
    ∃ (s : Fin d → F)
      (step : (j : Fin t) → ((↥(scope j) → ZMod 2) → Bool) → ((Fin d → F) →ₗ[F] (Fin d → F)))
      (out : (Fin d → F) →ₗ[F] F),
      ∀ tests : (j : Fin t) → ((↥(scope j) → ZMod 2) → Bool),
        out ((List.finRange t).foldl (fun cur stage => step stage (tests stage) cur) s) =
          (Nat.card {w : Fin k → ZMod 2 //
            w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧
            ∀ j, tests j (fun tested => w tested.val) = true} : F) := by
  classical
  let P : ℕ → Finset (Fin k) := fun i =>
    Finset.univ.filter (fun seen : Fin k => ∃ before : Fin t, before.val < i ∧ seen ∈ scope before)
  let Q : ℕ → Finset (Fin k) := fun i =>
    Finset.univ.filter (fun future : Fin k => ∃ after : Fin t, i ≤ after.val ∧ future ∈ scope after)
  have hPQ : ∀ i : ℕ, ∀ x : Fin k, x ∈ P i ∨ x ∈ Q i := by
    intro i x
    rcases hcov x with ⟨j, hj⟩
    by_cases hji : j.val < i
    · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, j, hji, hj⟩
    · right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, j, by omega, hj⟩
  let V := codeSub gen
  let KP : ℕ → Submodule (ZMod 2) V := fun i => kerOn gen (P i)
  let KQ : ℕ → Submodule (ZMod 2) V := fun i => kerOn gen (Q i)
  let C : ℕ → Type := fun i => V ⧸ (KP i ⊔ KQ i)
  let Pref : ℕ → Type := fun i => V ⧸ (KP i)
  have hfinC : ∀ i : ℕ, Fintype (C i) := fun i => Fintype.ofFinite (C i)
  have hfinPref : ∀ i : ℕ, Fintype (Pref i) := fun i => Fintype.ofFinite (Pref i)
  let UC : ∀ i : ℕ, Finset (C i) := fun i => @Finset.univ (C i) (hfinC i)
  let UP : ∀ i : ℕ, Finset (Pref i) := fun i => @Finset.univ (Pref i) (hfinPref i)
  have hcardC_le : ∀ i ≤ t, @Fintype.card (C i) (hfinC i) ≤ d := by
    intro i hi
    let _ := hfinC i
    have h1 : Fintype.card (C i) =
        2 ^ ((Matrix.of fun (row : Fin m) (coord : ↥(P i)) => gen row coord.val).rank +
             (Matrix.of fun (row : Fin m) (coord : ↥(Q i)) => gen row coord.val).rank -
             (Matrix.of fun (row : Fin m) (coord : ↥(Finset.univ : Finset (Fin k))) => gen row coord.val).rank) := by
      rw [← Nat.card_eq_fintype_card]
      exact card_quot_cut gen (P i) (Q i) (hPQ i)
    rw [h1]
    exact (Finset.le_sup (f := fun i =>
      let P' := Finset.univ.filter (fun seen : Fin k => ∃ before : Fin t, before.val < i ∧ seen ∈ scope before)
      let Q' := Finset.univ.filter (fun future : Fin k => ∃ after : Fin t, i ≤ after.val ∧ future ∈ scope after)
      2 ^ ((Matrix.of fun (row : Fin m) (coord : ↥P') => gen row coord.val).rank +
           (Matrix.of fun (row : Fin m) (coord : ↥Q') => gen row coord.val).rank -
           (Matrix.of fun (row : Fin m) (coord : ↥(Finset.univ : Finset (Fin k))) => gen row coord.val).rank))
      (Finset.mem_range.mpr (by omega : i < t + 1))).trans hneed
  have hemb_exists : ∀ i : ℕ, ∃ (idx : C i → Fin d) (inv : Fin d → Option (C i)),
      i ≤ t → (∀ c : C i, inv (idx c) = some c) ∧
        (∀ r : Fin d, ∀ c : C i, inv r = some c → idx c = r) := by
    intro i
    by_cases hi : i ≤ t
    · let _ := hfinC i
      let e : C i ≃ Fin (Fintype.card (C i)) := Fintype.equivFin (C i)
      let idx : C i → Fin d := fun c => Fin.castLE (hcardC_le i hi) (e c)
      let inv : Fin d → Option (C i) := fun r =>
        if h : r.val < Fintype.card (C i) then some (e.symm ⟨r.val, h⟩) else none
      refine ⟨idx, inv, fun _ => ⟨?_, ?_⟩⟩
      · intro c
        dsimp only [idx, inv]
        have hlt : (e c).val < Fintype.card (C i) := (e c).isLt
        simp only [Fin.val_castLE, hlt, dite_true, Fin.eta, Equiv.symm_apply_apply]
      · intro r c hrc
        dsimp only [idx, inv] at hrc ⊢
        split_ifs at hrc with hlt
        have heq := Option.some.inj hrc
        subst heq
        exact Fin.ext (by simp)
    · exact ⟨fun _ => ⟨0, by
        have hpos : 1 ≤ d := by
          have h0 := hcardC_le 0 (Nat.zero_le t)
          let _ := hfinC 0
          have hne : Nonempty (C 0) := ⟨0⟩
          have hcpos : 0 < Fintype.card (C 0) := Fintype.card_pos
          omega
        omega⟩, fun _ => none, fun h => absurd h hi⟩
  choose idx inv hidx_inv using hemb_exists
  let classOf : ∀ i : ℕ, Pref i → C i := fun i =>
    Submodule.mapQ (KP i) (KP i ⊔ KQ i) LinearMap.id (by simp [le_sup_left])
  have hclassOf_mk : ∀ (i : ℕ) (w : V),
      classOf i (Submodule.Quotient.mk w) = Submodule.Quotient.mk w := fun _ _ => rfl
  have hP_mono : ∀ j : Fin t, P j.val ⊆ P (j.val + 1) := by
    intro j x hx
    rcases (Finset.mem_filter.mp hx).2 with ⟨b, hb, hxb⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, b, by omega, hxb⟩
  have hscope_sub_P : ∀ j : Fin t, scope j ⊆ P (j.val + 1) := by
    intro j x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, j, by omega, hx⟩
  have hscope_sub_Q : ∀ j : Fin t, scope j ⊆ Q j.val := by
    intro j x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, j, by omega, hx⟩
  have hQ_anti : ∀ j : Fin t, Q (j.val + 1) ⊆ Q j.val := by
    intro j x hx
    rcases (Finset.mem_filter.mp hx).2 with ⟨a, ha, hxa⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, a, by omega, hxa⟩
  have hKP_anti : ∀ j : Fin t, KP (j.val + 1) ≤ KP j.val := by
    intro j w hw
    rw [mem_kerOn_iff] at hw ⊢
    intro x hx
    exact hw x (hP_mono j hx)
  have hKQ_mono : ∀ j : Fin t, KQ j.val ≤ KQ (j.val + 1) := by
    intro j w hw
    rw [mem_kerOn_iff] at hw ⊢
    intro x hx
    exact hw x (hQ_anti j hx)
  let projDown : ∀ j : Fin t, Pref (j.val + 1) → Pref j.val := fun j =>
    Submodule.mapQ (KP (j.val + 1)) (KP j.val) LinearMap.id (by simpa using hKP_anti j)
  have hprojDown_mk : ∀ (j : Fin t) (w : V),
      projDown j (Submodule.Quotient.mk w) = Submodule.Quotient.mk w := fun _ _ => rfl
  let testAt : ∀ (j : Fin t), ((↥(scope j) → ZMod 2) → Bool) → Pref (j.val + 1) → Prop :=
    fun j tbl => Quotient.lift (fun w : V => tbl (fun s => (base + w.val) s.val) = true) (by
      intro w₁ w₂ hrel
      have hdiff : w₁ - w₂ ∈ KP (j.val + 1) := (Submodule.quotientRel_def _).mp hrel
      have hsc : ∀ x ∈ scope j, w₁.val x = w₂.val x := by
        intro x hx
        have hz := (mem_kerOn_iff gen (P (j.val + 1)) (w₁ - w₂)).mp hdiff x (hscope_sub_P j hx)
        simp only [Submodule.coe_sub, Pi.sub_apply, sub_eq_zero] at hz
        exact hz
      have hfun : (fun s : ↥(scope j) => (base + w₁.val) s.val) =
          (fun s : ↥(scope j) => (base + w₂.val) s.val) := by
        funext s; simp only [Pi.add_apply, hsc s.val s.property]
      rw [hfun])
  have htestAt_mk : ∀ (j : Fin t) (tbl : (↥(scope j) → ZMod 2) → Bool) (w : V),
      testAt j tbl (Submodule.Quotient.mk w) ↔ tbl (fun s => (base + w.val) s.val) = true :=
    fun _ _ _ => Iff.rfl
  let goodPref : ∀ (i : ℕ) (tests : (j : Fin t) → ((↥(scope j) → ZMod 2) → Bool)), Pref i → Prop :=
    fun i tests => Quotient.lift (fun w : V => ∀ j : Fin t, j.val < i →
      tests j (fun s => (base + w.val) s.val) = true) (by
      intro w₁ w₂ hrel
      have hdiff : w₁ - w₂ ∈ KP i := (Submodule.quotientRel_def _).mp hrel
      have hPeq : ∀ x ∈ P i, w₁.val x = w₂.val x := by
        intro x hx
        have hz := (mem_kerOn_iff gen (P i) (w₁ - w₂)).mp hdiff x hx
        simp only [Submodule.coe_sub, Pi.sub_apply, sub_eq_zero] at hz
        exact hz
      apply propext
      constructor <;> intro h j hji <;>
        (have hfun : (fun s : ↥(scope j) => (base + w₁.val) s.val) =
            (fun s : ↥(scope j) => (base + w₂.val) s.val) := by
          funext s
          have hsP : s.val ∈ P i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hji, s.property⟩
          simp only [Pi.add_apply, hPeq s.val hsP])
      · rw [← hfun]; exact h j hji
      · rw [hfun]; exact h j hji)
  have hgoodPref_mk : ∀ (i : ℕ) (tests : (j : Fin t) → ((↥(scope j) → ZMod 2) → Bool)) (w : V),
      goodPref i tests (Submodule.Quotient.mk w) ↔
        ∀ j : Fin t, j.val < i → tests j (fun s => (base + w.val) s.val) = true :=
    fun _ _ _ => Iff.rfl
  have hgoodPref_step : ∀ (j : Fin t) (tests : (j' : Fin t) → ((↥(scope j') → ZMod 2) → Bool))
      (p' : Pref (j.val + 1)),
      goodPref (j.val + 1) tests p' ↔ goodPref j.val tests (projDown j p') ∧ testAt j (tests j) p' := by
    intro j tests p'
    rcases Submodule.Quotient.mk_surjective _ p' with ⟨w, rfl⟩
    rw [hprojDown_mk, hgoodPref_mk, hgoodPref_mk, htestAt_mk]
    constructor
    · intro h
      exact ⟨fun j' hj' => h j' (by omega), h j (Nat.lt_succ_self j.val)⟩
    · rintro ⟨hprev, hcur⟩ j' hj'
      by_cases hlt : j'.val < j.val
      · exact hprev j' hlt
      · have hjeq : j' = j := Fin.ext (by omega)
        subst hjeq
        exact hcur
  have hsurjPref : ∀ (i : ℕ) (c : C i), ∃ p : Pref i, classOf i p = c := by
    intro i c
    rcases Submodule.Quotient.mk_surjective _ c with ⟨w, rfl⟩
    exact ⟨Submodule.Quotient.mk w, rfl⟩
  choose repP hrepP using hsurjPref
  let transCoeff : ∀ (j : Fin t) (tbl : (↥(scope j) → ZMod 2) → Bool),
      C j.val → C (j.val + 1) → ℕ := fun j tbl c c' =>
    ((UP (j.val + 1)).filter (fun p' : Pref (j.val + 1) =>
      projDown j p' = repP j.val c ∧ testAt j tbl p' ∧ classOf (j.val + 1) p' = c')).card
  have htrans_indep : ∀ (j : Fin t) (tbl : (↥(scope j) → ZMod 2) → Bool)
      (p : Pref j.val) (c' : C (j.val + 1)),
      ((UP (j.val + 1)).filter (fun p' : Pref (j.val + 1) =>
        projDown j p' = p ∧ testAt j tbl p' ∧ classOf (j.val + 1) p' = c')).card =
      transCoeff j tbl (classOf j.val p) c' := by
    intro j tbl p c'
    rcases Submodule.Quotient.mk_surjective _ p with ⟨w₁, rfl⟩
    rcases Submodule.Quotient.mk_surjective _ (repP j.val (classOf j.val (Submodule.Quotient.mk w₁))) with ⟨w₂, hw2⟩
    have hcl_eq : Submodule.Quotient.mk (p := KP j.val ⊔ KQ j.val) w₁ =
        Submodule.Quotient.mk (p := KP j.val ⊔ KQ j.val) w₂ := by
      have h1 := hrepP j.val (classOf j.val (Submodule.Quotient.mk w₁))
      rw [← hw2, hclassOf_mk, hclassOf_mk] at h1
      exact h1.symm
    rw [Submodule.Quotient.eq, Submodule.mem_sup] at hcl_eq
    rcases hcl_eq with ⟨u, huP, v, hvQ, huv⟩
    let shift : Pref (j.val + 1) → Pref (j.val + 1) :=
      fun p' => p' - Submodule.Quotient.mk v
    have hshift_bij : ∀ p' : Pref (j.val + 1),
        (projDown j p' = Submodule.Quotient.mk w₁ ∧ testAt j tbl p' ∧ classOf (j.val + 1) p' = c') ↔
        (projDown j (shift p') = repP j.val (classOf j.val (Submodule.Quotient.mk w₁)) ∧
          testAt j tbl (shift p') ∧ classOf (j.val + 1) (shift p') = c') := by
      intro p'
      rcases Submodule.Quotient.mk_surjective _ p' with ⟨w, rfl⟩
      have hsh : shift (Submodule.Quotient.mk w) = Submodule.Quotient.mk (w - v) := rfl
      rw [hsh, ← hw2, hprojDown_mk, hprojDown_mk, htestAt_mk, htestAt_mk, hclassOf_mk, hclassOf_mk]
      have hproj_iff : Submodule.Quotient.mk (p := KP j.val) w = Submodule.Quotient.mk w₁ ↔
          Submodule.Quotient.mk (p := KP j.val) (w - v) = Submodule.Quotient.mk w₂ := by
        rw [Submodule.Quotient.eq, Submodule.Quotient.eq]
        have hdiff : (w - v) - w₂ = (w - w₁) + u := by
          have : w₁ - w₂ = u + v := huv.symm
          calc (w - v) - w₂ = (w - w₁) + (w₁ - w₂) - v := by abel
            _ = (w - w₁) + (u + v) - v := by rw [this]
            _ = (w - w₁) + u := by abel
        rw [hdiff]
        constructor
        · intro h; exact Submodule.add_mem _ h huP
        · intro h
          have : w - w₁ = ((w - w₁) + u) - u := by abel
          rw [this]; exact Submodule.sub_mem _ h huP
      have htest_iff : tbl (fun s => (base + w.val) s.val) = true ↔
          tbl (fun s => (base + (w - v).val) s.val) = true := by
        have hfun : (fun s : ↥(scope j) => (base + (w - v).val) s.val) =
            (fun s : ↥(scope j) => (base + w.val) s.val) := by
          funext s
          have hvx : v.val s.val = 0 :=
            (mem_kerOn_iff gen (Q j.val) v).mp hvQ s.val (hscope_sub_Q j s.property)
          simp [hvx]
        rw [hfun]
      have hcl_iff : Submodule.Quotient.mk (p := KP (j.val + 1) ⊔ KQ (j.val + 1)) (w - v) =
          Submodule.Quotient.mk (p := KP (j.val + 1) ⊔ KQ (j.val + 1)) w := by
        rw [Submodule.Quotient.eq]
        have hsub : (w - v) - w = -v := by abel
        rw [hsub]
        exact Submodule.neg_mem _ (Submodule.mem_sup_right (hKQ_mono j hvQ))
      rw [hproj_iff, htest_iff, hcl_iff]
    dsimp only [transCoeff]
    refine Finset.card_bij (fun p' _ => shift p') ?_ ?_ ?_
    · intro p' hp'
      have hp'' := (Finset.mem_filter.mp hp').2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hshift_bij p').mp hp''⟩
    · intro p1 _ p2 _ heq
      dsimp only [shift] at heq
      exact sub_left_inj.mp heq
    · intro q' hq'
      refine ⟨q' + Submodule.Quotient.mk v, ?_, ?_⟩
      · have hq'' := (Finset.mem_filter.mp hq').2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [hshift_bij]
        have hsh : shift (q' + Submodule.Quotient.mk v) = q' := by
          dsimp only [shift]; abel
        rw [hsh]
        exact hq''
      · dsimp only [shift]; abel
  let s : Fin d → F := fun r => if r = idx 0 (0 : C 0) then 1 else 0
  let step : (j : Fin t) → ((↥(scope j) → ZMod 2) → Bool) → ((Fin d → F) →ₗ[F] (Fin d → F)) :=
    fun j tbl =>
      { toFun := fun x r =>
          match inv (j.val + 1) r with
          | none => 0
          | some c' => ∑ c ∈ UC j.val, (transCoeff j tbl c c' : F) * x (idx j.val c)
        map_add' := fun x y => by
          funext r
          simp only [Pi.add_apply]
          cases hinv : inv (j.val + 1) r with
          | none => simp
          | some c' =>
            simp only [mul_add, Finset.sum_add_distrib]
        map_smul' := fun a x => by
          funext r
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
          cases hinv : inv (j.val + 1) r with
          | none => simp
          | some c' =>
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro c _; ring }
  have hstep_apply : ∀ (j : Fin t) (tbl : (↥(scope j) → ZMod 2) → Bool)
      (x : Fin d → F) (c' : C (j.val + 1)),
      step j tbl x (idx (j.val + 1) c') =
        ∑ c ∈ UC j.val, (transCoeff j tbl c c' : F) * x (idx j.val c) := by
    intro j tbl x c'
    dsimp only [step, LinearMap.coe_mk, AddHom.coe_mk]
    rw [(hidx_inv (j.val + 1) j.isLt).1 c']
  let out : (Fin d → F) →ₗ[F] F :=
    { toFun := fun x => x (idx t (0 : C t))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨s, step, out, ?_⟩
  intro tests
  have hinv_state : ∀ i : ℕ, i ≤ t →
      ∀ c : C i,
        (((List.finRange t).take i).foldl (fun cur stage => step stage (tests stage) cur) s) (idx i c) =
          (((UP i).filter (fun p : Pref i => classOf i p = c ∧ goodPref i tests p)).card : F) := by
    intro i
    induction i with
    | zero =>
      intro _ c
      have hKP0 : KP 0 = ⊤ := by
        ext w
        rw [mem_kerOn_iff]
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, Submodule.mem_top, iff_true]
        rintro x ⟨b, hb, _⟩
        omega
      have hc0 : c = 0 := by
        rcases Submodule.Quotient.mk_surjective _ c with ⟨w, rfl⟩
        change Submodule.Quotient.mk w = Submodule.Quotient.mk 0
        rw [Submodule.Quotient.eq, sub_zero]
        exact Submodule.mem_sup_left (by rw [hKP0]; trivial)
      subst hc0
      simp only [List.take_zero, List.foldl_nil, s, ite_true]
      have huniq : (UP 0).filter (fun p : Pref 0 => classOf 0 p = 0 ∧ goodPref 0 tests p) = {0} := by
        ext p
        simp only [UP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro _
          rcases Submodule.Quotient.mk_surjective _ p with ⟨w, rfl⟩
          change Submodule.Quotient.mk w = Submodule.Quotient.mk 0
          rw [Submodule.Quotient.eq, sub_zero, hKP0]
          trivial
        · rintro rfl
          refine ⟨rfl, ?_⟩
          change goodPref 0 tests (Submodule.Quotient.mk 0)
          rw [hgoodPref_mk]
          intro j hj; omega
      rw [huniq]
      simp
    | succ i ih =>
      intro hi c'
      have hilt : i < t := by omega
      let j : Fin t := ⟨i, hilt⟩
      rw [finRange_take_succ hilt, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hstep_apply j (tests j) _ c']
      have hih_rw : ∀ c ∈ UC i,
          (((List.finRange t).take i).foldl (fun cur stage => step stage (tests stage) cur) s) (idx i c) =
            (((UP i).filter (fun p : Pref i => classOf i p = c ∧ goodPref i tests p)).card : F) :=
        fun c _ => ih (by omega) c
      have hsum_eq : ∑ c ∈ UC i, (transCoeff j (tests j) c c' : F) *
          (((List.finRange t).take i).foldl (fun cur stage => step stage (tests stage) cur) s) (idx i c) =
          ∑ c ∈ UC i, (transCoeff j (tests j) c c' : F) *
            (((UP i).filter (fun p : Pref i => classOf i p = c ∧ goodPref i tests p)).card : F) :=
        Finset.sum_congr rfl (fun c hc => by rw [hih_rw c hc])
      rw [hsum_eq]
      simp_rw [← Nat.cast_mul, ← Nat.cast_sum]
      congr 1
      let G : Finset (Pref i) := (UP i).filter (fun p : Pref i => goodPref i tests p)
      let G' : Finset (Pref (i + 1)) :=
        (UP (i + 1)).filter (fun p' : Pref (i + 1) => classOf (i + 1) p' = c' ∧ goodPref (i + 1) tests p')
      have hfib1 : G'.card = ∑ p ∈ G, (G'.filter (fun p' => projDown j p' = p)).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := projDown j) (t := G)]
        intro p' hp'
        have hmem : classOf (i + 1) p' = c' ∧ goodPref (i + 1) tests p' := (Finset.mem_filter.mp hp').2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((hgoodPref_step j tests p').mp hmem.2).1⟩
      have hfib_eq : ∀ p ∈ G, (G'.filter (fun p' => projDown j p' = p)).card =
          transCoeff j (tests j) (classOf i p) c' := by
        intro p hp
        have hgp : goodPref i tests p := (Finset.mem_filter.mp hp).2
        have hset : G'.filter (fun p' => projDown j p' = p) =
            (UP (i + 1)).filter (fun p' : Pref (i + 1) =>
              projDown j p' = p ∧ testAt j (tests j) p' ∧ classOf (i + 1) p' = c') := by
          ext p'
          simp only [G', UP, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨⟨hc', hgp'⟩, hpd⟩
            exact ⟨hpd, ((hgoodPref_step j tests p').mp hgp').2, hc'⟩
          · rintro ⟨hpd, hta, hc'⟩
            exact ⟨⟨hc', (hgoodPref_step j tests p').mpr ⟨hpd.symm ▸ hgp, hta⟩⟩, hpd⟩
        rw [hset]
        exact htrans_indep j (tests j) p c'
      rw [hfib1, Finset.sum_congr rfl hfib_eq]
      have hfib2 : ∑ p ∈ G, transCoeff j (tests j) (classOf i p) c' =
          ∑ c ∈ UC i, ∑ p ∈ G.filter (fun p => classOf i p = c), transCoeff j (tests j) (classOf i p) c' := by
        have hm : ∀ p ∈ G, classOf i p ∈ UC i := fun p _ => Finset.mem_univ _
        rw [← Finset.sum_fiberwise_of_maps_to hm]
      rw [hfib2]
      apply Finset.sum_congr rfl
      intro c _
      have hinner : ∑ p ∈ G.filter (fun p => classOf i p = c), transCoeff j (tests j) (classOf i p) c' =
          (G.filter (fun p => classOf i p = c)).card * transCoeff j (tests j) c c' := by
        trans ∑ _p ∈ G.filter (fun p => classOf i p = c), transCoeff j (tests j) c c'
        · apply Finset.sum_congr rfl
          intro p hp; rw [(Finset.mem_filter.mp hp).2]
        · simp
      rw [hinner, Nat.mul_comm]
      congr 1
      apply congrArg Finset.card
      ext p
      simp only [G, UP, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_comm
  have hfinal := hinv_state t (Nat.le_refl t) (0 : C t)
  rw [show (List.finRange t).take t = List.finRange t by simp] at hfinal
  dsimp only [out, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hfinal]
  congr 1
  let _ := hfinPref t
  have hPt : P t = Finset.univ := by
    ext x
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases hcov x with ⟨j, hj⟩
    exact ⟨j, j.isLt, hj⟩
  have hQt : Q t = ∅ := by
    ext x
    simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨j, hj, _⟩
    have := j.isLt
    omega
  have hKPt : KP t = ⊥ := by rw [show KP t = kerOn gen (P t) from rfl, hPt, kerOn_univ]
  have hKQt : KQ t = ⊤ := by
    ext w
    rw [show KQ t = kerOn gen (Q t) from rfl, hQt, mem_kerOn_iff]
    simp
  have hCt_triv : ∀ p : Pref t, classOf t p = (0 : C t) := by
    intro p
    rcases Submodule.Quotient.mk_surjective _ p with ⟨w, rfl⟩
    rw [hclassOf_mk]
    change Submodule.Quotient.mk w = Submodule.Quotient.mk 0
    rw [Submodule.Quotient.eq, sub_zero]
    exact Submodule.mem_sup_right (by rw [hKQt]; trivial)
  change ((@Finset.univ (Pref t) (hfinPref t)).filter (fun p : Pref t => classOf t p = 0 ∧ goodPref t tests p)).card = _
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  refine Equiv.ofBijective (fun p => ⟨base + (Quotient.out p.val).val, ?_⟩) ⟨?_, ?_⟩
  · have hgp : goodPref t tests p.val := p.property.2
    have hout : Submodule.Quotient.mk (Quotient.out p.val) = p.val := Quotient.out_eq p.val
    rw [← hout, hgoodPref_mk] at hgp
    rcases (Quotient.out p.val).property with ⟨a, ha⟩
    refine ⟨⟨a, by rw [← ha]; rfl⟩, fun j => hgp j j.isLt⟩
  · intro p₁ p₂ heq
    have hval : (Quotient.out p₁.val).val = (Quotient.out p₂.val).val := by
      exact add_left_cancel (congrArg Subtype.val heq)
    have hsub : Quotient.out p₁.val = Quotient.out p₂.val := Subtype.ext hval
    have hp : p₁.val = p₂.val := by
      rw [← Quotient.out_eq p₁.val, ← Quotient.out_eq p₂.val, hsub]
    exact Subtype.ext hp
  · rintro ⟨w, ⟨a, rfl⟩, htests⟩
    let v : V := ⟨linGen gen a, LinearMap.mem_range_self _ a⟩
    let p : Pref t := Submodule.Quotient.mk v
    have hgp : goodPref t tests p := by
      rw [hgoodPref_mk]
      intro j _; exact htests j
    refine ⟨⟨p, hCt_triv p, hgp⟩, Subtype.ext ?_⟩
    have hmk : Quotient.out p - v ∈ KP t := by
      rw [← Submodule.Quotient.eq]
      exact Quotient.out_eq p
    have hrel : Quotient.out p = v := by
      have hbot : Quotient.out p - v ∈ (⊥ : Submodule (ZMod 2) V) := hKPt ▸ hmk
      rw [Submodule.mem_bot] at hbot
      exact sub_eq_zero.mp hbot
    dsimp only
    rw [hrel]
    rfl

end PEqualNP.Outside.L_lib_596_aux

theorem PEqualNP.Outside.L_lib_596 :
∀ (F : Type) [Field F] (k m t d : ℕ),
  let W := Fin k → ZMod 2
  ∀ (base : W) (gen : Fin m → W) (scope : Fin t → Finset (Fin k)),
    (∀ v : Fin k, ∃ j : Fin t, v ∈ scope j) →
    let key := fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h
    let rk := fun S : Finset (Fin k) =>
      let M : Matrix (Fin m) S (ZMod 2) := fun row coord => gen row coord.val
      M.rank
    let need := (Finset.range (t+1)).sup (fun i =>
      let P := Finset.univ.filter (fun seen : Fin k => ∃ before : Fin t, before.val < i ∧ seen ∈ scope before)
      let Q := Finset.univ.filter (fun future : Fin k => ∃ after : Fin t, i ≤ after.val ∧ future ∈ scope after)
      2^(rk P + rk Q - rk Finset.univ))
    let T := fun idx : Fin t => (↥(scope idx) → ZMod 2) → Bool
    let count := fun tests : (j : Fin t) → T j =>
      Nat.card {w : W // w ∈ Set.range key ∧ ∀ j, tests j (fun tested => w tested.val) = true}
    (∃ (s : Fin d → F)
       (step : (j : Fin t) → T j → ((Fin d → F) →ₗ[F] (Fin d → F)))
       (out : (Fin d → F) →ₗ[F] F),
      ∀ tests : (j : Fin t) → T j,
        out ((List.finRange t).foldl (fun cur stage => step stage (tests stage) cur) s) =
          (count tests : F)) ↔ need ≤ d := by
  intro F _ k m t d W base gen scope hcov key rk need T count
  constructor
  · rintro ⟨s, step, out, hrun⟩
    exact PEqualNP.Outside.L_lib_596_aux.dir_le F k m t d base gen scope hcov s step out hrun
  · intro hneed
    exact PEqualNP.Outside.L_lib_596_aux.dir_ge F k m t d base gen scope hcov hneed
