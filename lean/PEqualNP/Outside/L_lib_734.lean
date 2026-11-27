import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_734_aux

private abbrev U (m : Nat) := Fin m → ZMod 2
private abbrev H (h : Nat) := Fin h → ZMod 2
private abbrev I (m h : Nat) := U m × H h
private abbrev W (m h : Nat) := I m h → I m h
private abbrev V (m h : Nat) := I m h → ZMod 2
private abbrev J (m h : Nat) := I m h × (Fin m ⊕ Fin h)

private def bit {m h : Nat} (x : W m h) (j : J m h) : ZMod 2 :=
  Sum.elim (x j.1).1 (x j.1).2 j.2

private def low {m h : Nat} (P : W m h → V m h) : Prop :=
  ∀ i, ∃ T : Finset (Finset (J m h)),
    (∀ mon ∈ T, mon.card ≤ m) ∧ ∀ x, P x i = ∑ mon ∈ T, ∏ j ∈ mon, bit x j

private def unit {m h : Nat} (i j : I m h) : ZMod 2 :=
  if j = i then (1 : ZMod 2) else 0

private def shiftW {m h : Nat} (g : U m) (x : W m h) : W m h :=
  fun i => ((x i).1 + g, (x i).2)

private def shiftPerm {m h : Nat} (g : U m) (p : Equiv.Perm (I m h)) : Equiv.Perm (I m h) :=
  p.trans (Equiv.prodCongr (Equiv.addRight g) (Equiv.refl (H h)))

private theorem shiftPerm_apply {m h : Nat} (g : U m) (p : Equiv.Perm (I m h)) (i : I m h) :
    shiftPerm g p i = ((p i).1 + g, (p i).2) := rfl

private theorem shiftPerm_invol {m h : Nat} (g : U m) (p : Equiv.Perm (I m h)) :
    shiftPerm g (shiftPerm g p) = p := by
  apply Equiv.ext
  intro i
  apply Prod.ext
  · change (p i).1 + g + g = (p i).1
    funext u
    simp only [Pi.add_apply]
    generalize (p i).1 u = a
    generalize g u = b
    fin_cases a <;> fin_cases b <;> rfl
  · rfl

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> rfl

private theorem zmod2_sum_add (a : ZMod 2) : (∑ b : ZMod 2, (a + b)) = 1 := by
  fin_cases a <;> decide

private theorem sum_shift_mon {m h : Nat} (mon : Finset (J m h)) (hcard : mon.card ≤ m)
    (x y : W m h) :
    (∑ g : U m, ∏ j ∈ mon, bit (shiftW g x) j) =
    (∑ g : U m, ∏ j ∈ mon, bit (shiftW g y) j) := by
  classical
  by_cases hall : ∀ u : Fin m, ∃ j ∈ mon, j.2 = Sum.inl u
  · let f : Fin m → J m h := fun u => Classical.choose (hall u)
    have hf_mem : ∀ u, f u ∈ mon := fun u => (Classical.choose_spec (hall u)).1
    have hf_val : ∀ u, (f u).2 = Sum.inl u := fun u => (Classical.choose_spec (hall u)).2
    have hf_inj : Function.Injective f := by
      intro u1 u2 heq
      have h2 := congrArg Prod.snd heq
      rw [hf_val u1, hf_val u2] at h2
      exact Sum.inl.inj h2
    have himg : Finset.univ.image f = mon := by
      apply Finset.eq_of_subset_of_card_le
      · intro j hj
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hj
        exact hf_mem u
      · rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
        exact hcard
    have heval : ∀ w : W m h, (∑ g : U m, ∏ j ∈ mon, bit (shiftW g w) j) = 1 := by
      intro w
      have hprod : ∀ g : U m, (∏ j ∈ mon, bit (shiftW g w) j) =
          ∏ u : Fin m, ((w (f u).1).1 u + g u) := by
        intro g
        rw [← himg, Finset.prod_image (fun a _ b _ hab => hf_inj hab)]
        refine Finset.prod_congr rfl fun u _ => ?_
        simp only [bit, shiftW, hf_val u, Sum.elim_inl, Pi.add_apply]
      simp_rw [hprod]
      rw [← Fintype.prod_sum (fun u (b : ZMod 2) => (w (f u).1).1 u + b)]
      simp_rw [zmod2_sum_add]
      simp
    rw [heval x, heval y]
  · push Not at hall
    obtain ⟨u0, hu0⟩ := hall
    have hzero : ∀ w : W m h, (∑ g : U m, ∏ j ∈ mon, bit (shiftW g w) j) = 0 := by
      intro w
      let flip : U m → U m := fun g => Function.update g u0 (g u0 + 1)
      have hflip_val : ∀ g : U m,
          (∏ j ∈ mon, bit (shiftW (flip g) w) j) = ∏ j ∈ mon, bit (shiftW g w) j := by
        intro g
        refine Finset.prod_congr rfl fun j hj => ?_
        cases hj2 : j.2 with
        | inr v => simp [bit, shiftW, hj2]
        | inl u =>
          have hne : u ≠ u0 := fun heq => hu0 j hj (by rw [hj2, heq])
          simp [bit, shiftW, hj2, flip, Function.update_of_ne hne]
      let A0 : Finset (U m) := Finset.univ.filter (fun g => g u0 = 0)
      let A1 : Finset (U m) := Finset.univ.filter (fun g => g u0 = 1)
      have hpart : A0 ∪ A1 = Finset.univ := by
        ext g
        simp only [A0, A1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        generalize g u0 = b
        fin_cases b
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hdisj : Disjoint A0 A1 := by
        rw [Finset.disjoint_left]
        intro g h0 h1
        have h0' := (Finset.mem_filter.mp h0).2
        have h1' := (Finset.mem_filter.mp h1).2
        rw [h0'] at h1'
        exact zero_ne_one h1'
      have hsum_eq : (∑ g ∈ A1, ∏ j ∈ mon, bit (shiftW g w) j) =
          ∑ g ∈ A0, ∏ j ∈ mon, bit (shiftW g w) j := by
        refine Finset.sum_bij (fun g _ => flip g) ?_ ?_ ?_ ?_
        · intro g hg
          have hg1 := (Finset.mem_filter.mp hg).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simp [flip, hg1]; decide
        · intro g1 _ g2 _ heq
          funext u
          by_cases hu : u = u0
          · subst hu
            have h1 := congrFun heq u
            simp only [flip, Function.update_self] at h1
            have h2 := congrArg (· + 1) h1
            have hadd : ∀ a : ZMod 2, a + 1 + 1 = a := by intro a; fin_cases a <;> rfl
            rw [hadd, hadd] at h2
            exact h2
          · have h1 := congrFun heq u
            simpa [flip, Function.update_of_ne hu] using h1
        · intro g hg
          have hg0 := (Finset.mem_filter.mp hg).2
          refine ⟨flip g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [flip, hg0]⟩, ?_⟩
          funext u
          by_cases hu : u = u0
          · subst hu; simp only [flip, Function.update_self]
            generalize g u = a; fin_cases a <;> rfl
          · simp [flip, Function.update_of_ne hu]
        · intro g _
          exact (hflip_val g).symm
      rw [← hpart, Finset.sum_union hdisj, hsum_eq]
      exact zmod2_add_self _
    rw [hzero x, hzero y]

private theorem sum_shift_low {m h : Nat} {P : W m h → V m h} (hP : low P) (i : I m h)
    (x y : W m h) :
    (∑ g : U m, P (shiftW g x) i) = (∑ g : U m, P (shiftW g y) i) := by
  obtain ⟨T, hTdeg, hTeq⟩ := hP i
  simp_rw [hTeq]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
  refine Finset.sum_congr rfl fun mon hmon => ?_
  exact sum_shift_mon mon (hTdeg mon hmon) x y

private theorem card_fiber {m h : Nat} (r : I m h) (S : Finset (I m h))
    (hr : r ∈ S) (hS : S.card = 2 ^ h) :
    ((Finset.univ : Finset (Equiv.Perm (I m h))).filter (fun p =>
      p.symm (0, 0) = r ∧ Finset.univ.filter (fun i => (p i).1 = 0) = S)).card =
    Nat.factorial (2 ^ h - 1) * Nat.factorial (2 ^ m * 2 ^ h - 2 ^ h) := by
  classical
  let T0 : Finset (I m h) := Finset.univ.filter (fun y => y.1 = 0)
  let T1 : Finset (I m h) := T0.erase (0, 0)
  let T2 : Finset (I m h) := Finset.univ.filter (fun y => y.1 ≠ 0)
  let S1 : Finset (I m h) := S.erase r
  let S2 : Finset (I m h) := Sᶜ
  have hT0_card : T0.card = 2 ^ h := by
    have heq : T0 = Finset.univ.image (fun v : H h => ((0 : U m), v)) := by
      ext y
      simp only [T0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hy; exact ⟨y.2, Prod.ext hy.symm rfl⟩
      · rintro ⟨v, rfl⟩; rfl
    rw [heq, Finset.card_image_of_injective _ (fun a b hab => congrArg Prod.snd hab),
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have h00_T0 : ((0, 0) : I m h) ∈ T0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hT1_card : T1.card = 2 ^ h - 1 := by rw [Finset.card_erase_of_mem h00_T0, hT0_card]
  have hI_card : Fintype.card (I m h) = 2 ^ m * 2 ^ h := by
    simp [I, U, H, Fintype.card_prod, ZMod.card]
  have hT2_card : T2.card = 2 ^ m * 2 ^ h - 2 ^ h := by
    have heq : T2 = T0ᶜ := by ext y; simp [T2, T0]
    rw [heq, Finset.card_compl, hI_card, hT0_card]
  have hS1_card : S1.card = 2 ^ h - 1 := by rw [Finset.card_erase_of_mem hr, hS]
  have hS2_card : S2.card = 2 ^ m * 2 ^ h - 2 ^ h := by rw [Finset.card_compl, hI_card, hS]
  let F := (Finset.univ : Finset (Equiv.Perm (I m h))).filter (fun p =>
    p.symm (0, 0) = r ∧ Finset.univ.filter (fun i => (p i).1 = 0) = S)
  let toPair : {p // p ∈ F} → ({x // x ∈ S1} ≃ {y // y ∈ T1}) × ({x // x ∈ S2} ≃ {y // y ∈ T2}) :=
    fun ⟨p, hp⟩ =>
      have hpr : p r = (0, 0) := by
        have := (Finset.mem_filter.mp hp).2.1
        rw [← this, Equiv.apply_symm_apply]
      have hpS : ∀ i, (p i).1 = 0 ↔ i ∈ S := by
        intro i
        have := congrArg (i ∈ ·) (Finset.mem_filter.mp hp).2.2
        simpa using this
      let e1 : {x // x ∈ S1} ≃ {y // y ∈ T1} :=
        { toFun := fun ⟨x, hx⟩ =>
            ⟨p x, Finset.mem_erase.mpr ⟨fun heq => (Finset.mem_erase.mp hx).1 (p.injective (heq.trans hpr.symm)),
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpS x).mpr (Finset.mem_of_mem_erase hx)⟩⟩⟩
          invFun := fun ⟨y, hy⟩ =>
            ⟨p.symm y, Finset.mem_erase.mpr ⟨fun heq => (Finset.mem_erase.mp hy).1 (by rw [← hpr, ← heq, Equiv.apply_symm_apply]),
              (hpS (p.symm y)).mp (by rw [Equiv.apply_symm_apply]; exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase hy)).2)⟩⟩
          left_inv := fun ⟨x, _⟩ => Subtype.ext (p.symm_apply_apply x)
          right_inv := fun ⟨y, _⟩ => Subtype.ext (p.apply_symm_apply y) }
      let e2 : {x // x ∈ S2} ≃ {y // y ∈ T2} :=
        { toFun := fun ⟨x, hx⟩ =>
            ⟨p x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h0 => (Finset.mem_compl.mp hx) ((hpS x).mp h0)⟩⟩
          invFun := fun ⟨y, hy⟩ =>
            ⟨p.symm y, Finset.mem_compl.mpr (fun hmem => (Finset.mem_filter.mp hy).2 (by rw [← Equiv.apply_symm_apply p y]; exact (hpS _).mpr hmem))⟩
          left_inv := fun ⟨x, _⟩ => Subtype.ext (p.symm_apply_apply x)
          right_inv := fun ⟨y, _⟩ => Subtype.ext (p.apply_symm_apply y) }
      (e1, e2)
  let ofPair : ({x // x ∈ S1} ≃ {y // y ∈ T1}) × ({x // x ∈ S2} ≃ {y // y ∈ T2}) → {p // p ∈ F} :=
    fun ⟨e1, e2⟩ =>
      let fwd : I m h → I m h := fun x =>
        if h1 : x = r then (0, 0)
        else if h2 : x ∈ S then (e1 ⟨x, Finset.mem_erase.mpr ⟨h1, h2⟩⟩).1
        else (e2 ⟨x, Finset.mem_compl.mpr h2⟩).1
      let bwd : I m h → I m h := fun y =>
        if h1 : y = (0, 0) then r
        else if h2 : y.1 = 0 then (e1.symm ⟨y, Finset.mem_erase.mpr ⟨h1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩⟩).1
        else (e2.symm ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩).1
      let p : Equiv.Perm (I m h) :=
        { toFun := fwd
          invFun := bwd
          left_inv := fun x => by
            dsimp only [fwd, bwd]
            by_cases h1 : x = r
            · simp [h1]
            · by_cases h2 : x ∈ S
              · simp only [h1, h2, ↓reduceDIte]
                have hy := (e1 ⟨x, Finset.mem_erase.mpr ⟨h1, h2⟩⟩).2
                have hy1 : (e1 ⟨x, Finset.mem_erase.mpr ⟨h1, h2⟩⟩).1 ≠ (0, 0) := (Finset.mem_erase.mp hy).1
                have hy2 : ((e1 ⟨x, Finset.mem_erase.mpr ⟨h1, h2⟩⟩).1).1 = 0 :=
                  (Finset.mem_filter.mp (Finset.mem_of_mem_erase hy)).2
                simp only [hy1, hy2, ↓reduceDIte]
                exact congrArg Subtype.val (e1.symm_apply_apply ⟨x, Finset.mem_erase.mpr ⟨h1, h2⟩⟩)
              · simp only [h1, h2, ↓reduceDIte]
                have hy := (e2 ⟨x, Finset.mem_compl.mpr h2⟩).2
                have hy2 : ((e2 ⟨x, Finset.mem_compl.mpr h2⟩).1).1 ≠ 0 := (Finset.mem_filter.mp hy).2
                have hy1 : (e2 ⟨x, Finset.mem_compl.mpr h2⟩).1 ≠ (0, 0) := fun heq => hy2 (by rw [heq])
                simp only [hy1, hy2, ↓reduceDIte]
                exact congrArg Subtype.val (e2.symm_apply_apply ⟨x, Finset.mem_compl.mpr h2⟩)
          right_inv := fun y => by
            dsimp only [fwd, bwd]
            by_cases h1 : y = (0, 0)
            · simp [h1]
            · by_cases h2 : y.1 = 0
              · simp only [h1, h2, ↓reduceDIte]
                have hx := (e1.symm ⟨y, Finset.mem_erase.mpr ⟨h1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩⟩).2
                have hx1 := (Finset.mem_erase.mp hx).1
                have hx2 := Finset.mem_of_mem_erase hx
                simp only [hx1, hx2, ↓reduceDIte]
                exact congrArg Subtype.val (e1.apply_symm_apply _)
              · simp only [h1, h2, ↓reduceDIte]
                have hx := (e2.symm ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩).2
                have hx2 : (e2.symm ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩).1 ∉ S :=
                  Finset.mem_compl.mp hx
                have hx1 : (e2.symm ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩).1 ≠ r :=
                  fun heq => hx2 (heq ▸ hr)
                simp only [hx1, hx2, ↓reduceDIte]
                exact congrArg Subtype.val (e2.apply_symm_apply _) }
      have hpF : p ∈ F := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · simp [p, bwd]
        · ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp only [p, Equiv.coe_fn_mk, fwd]
          by_cases h1 : x = r
          · simp [h1, hr]
          · by_cases h2 : x ∈ S
            · simp only [h1, h2, ↓reduceDIte, iff_true]
              exact (Finset.mem_filter.mp (Finset.mem_of_mem_erase (e1 ⟨x, Finset.mem_erase.mpr ⟨h1, h2⟩⟩).2)).2
            · simp only [h1, h2, ↓reduceDIte, iff_false]
              exact (Finset.mem_filter.mp (e2 ⟨x, Finset.mem_compl.mpr h2⟩).2).2
      ⟨p, hpF⟩
  have hbij : {p // p ∈ F} ≃ ({x // x ∈ S1} ≃ {y // y ∈ T1}) × ({x // x ∈ S2} ≃ {y // y ∈ T2}) :=
    { toFun := toPair
      invFun := ofPair
      left_inv := fun ⟨p, hp⟩ => by
        apply Subtype.ext
        apply Equiv.ext
        intro x
        change (ofPair (toPair ⟨p, hp⟩)).1 x = p x
        dsimp only [ofPair, toPair]
        by_cases h1 : x = r
        · subst h1
          have hpr : p x = (0, 0) := by
            have := (Finset.mem_filter.mp hp).2.1
            rw [← this, Equiv.apply_symm_apply]
          simp [hpr]
        · by_cases h2 : x ∈ S
          · simp [h1, h2]
          · simp [h1, h2]
      right_inv := fun ⟨e1, e2⟩ => by
        apply Prod.ext
        · apply Equiv.ext; intro x; apply Subtype.ext
          dsimp only [toPair, ofPair]
          have h1 := (Finset.mem_erase.mp x.2).1
          have h2 := Finset.mem_of_mem_erase x.2
          simp [h1, h2]
        · apply Equiv.ext; intro x; apply Subtype.ext
          dsimp only [toPair, ofPair]
          have h2 := Finset.mem_compl.mp x.2
          have h1 : x.1 ≠ r := fun heq => h2 (heq ▸ hr)
          simp [h1, h2] }
  have hcard1 : Fintype.card ({x // x ∈ S1} ≃ {y // y ∈ T1}) = Nat.factorial (2 ^ h - 1) := by
    have heq : Fintype.card {x // x ∈ S1} = Fintype.card {y // y ∈ T1} := by
      rw [Fintype.card_coe, Fintype.card_coe, hS1_card, hT1_card]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq heq), Fintype.card_coe, hS1_card]
  have hcard2 : Fintype.card ({x // x ∈ S2} ≃ {y // y ∈ T2}) = Nat.factorial (2 ^ m * 2 ^ h - 2 ^ h) := by
    have heq : Fintype.card {x // x ∈ S2} = Fintype.card {y // y ∈ T2} := by
      rw [Fintype.card_coe, Fintype.card_coe, hS2_card, hT2_card]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq heq), Fintype.card_coe, hS2_card]
  calc F.card = Fintype.card {p // p ∈ F} := (Fintype.card_coe F).symm
    _ = Fintype.card (({x // x ∈ S1} ≃ {y // y ∈ T1}) × ({x // x ∈ S2} ≃ {y // y ∈ T2})) :=
        Fintype.card_congr hbij
    _ = Nat.factorial (2 ^ h - 1) * Nat.factorial (2 ^ m * 2 ^ h - 2 ^ h) := by
        rw [Fintype.card_prod, hcard1, hcard2]

private theorem part1 (m h k : Nat) (P : Fin k → W m h → V m h) (hP : ∀ a, low (P a)) :
    let s := 2 ^ h
    let n := 2 ^ m * s
    let fails := fun (A : Fin k → Finset (I m h)) =>
      (Finset.univ : Finset (I m h × Finset (I m h))).filter (fun v =>
        v.1 ∈ v.2 ∧ v.2.card = s ∧ ∀ a, A a ∩ v.2 ≠ {v.1})
    let miss := (Finset.univ : Finset (Equiv.Perm (I m h))).filter (fun p =>
      ∀ a, P a (fun i => p i) ≠ unit (p.symm (0, 0)))
    let outside := ∑ a : Fin k, ∑ p : Equiv.Perm (I m h),
      ((Finset.univ : Finset (I m h)).filter (fun i => (p i).1 ≠ 0 ∧ P a (fun j => p j) i ≠ 0)).card
    ∃ A : Fin k → Finset (I m h),
      Nat.factorial (s - 1) * Nat.factorial (n - s) * (fails A).card ≤ miss.card + outside := by
  classical
  intro s n fails miss outside
  let mask : Fin k → I m h → ZMod 2 := fun a i =>
    ∑ g : U m, P a (shiftW g (fun _ => (0, 0))) i
  have hmask : ∀ (a : Fin k) (p : Equiv.Perm (I m h)) (i : I m h),
      (∑ g : U m, P a (fun j => shiftPerm g p j) i) = mask a i := by
    intro a p i
    exact sum_shift_low (hP a) i (fun j => p j) (fun _ => (0, 0))
  let A : Fin k → Finset (I m h) := fun a => Finset.univ.filter (fun i => mask a i = 1)
  refine ⟨A, ?_⟩
  let cfg : Equiv.Perm (I m h) → I m h × Finset (I m h) := fun p =>
    (p.symm (0, 0), Finset.univ.filter (fun i => (p i).1 = 0))
  let BadPerms : Finset (Equiv.Perm (I m h)) := Finset.univ.filter (fun p => cfg p ∈ fails A)
  have hBad_card : BadPerms.card = Nat.factorial (s - 1) * Nat.factorial (n - s) * (fails A).card := by
    have hbi : BadPerms = (fails A).biUnion (fun v =>
        Finset.univ.filter (fun p : Equiv.Perm (I m h) => p.symm (0, 0) = v.1 ∧
          Finset.univ.filter (fun i => (p i).1 = 0) = v.2)) := by
      ext p
      simp only [BadPerms, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      constructor
      · intro hp; exact ⟨cfg p, hp, rfl, rfl⟩
      · rintro ⟨v, hv, h1, h2⟩
        have : cfg p = v := Prod.ext h1 h2
        rw [this]; exact hv
    have hdisj : Set.PairwiseDisjoint (↑(fails A) : Set (I m h × Finset (I m h)))
        (fun v => Finset.univ.filter (fun p : Equiv.Perm (I m h) => p.symm (0, 0) = v.1 ∧
          Finset.univ.filter (fun i => (p i).1 = 0) = v.2)) := by
      intro v1 _ v2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have h1 := (Finset.mem_filter.mp hp1).2
      have h2 := (Finset.mem_filter.mp hp2).2
      exact hne (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2))
    rw [hbi, Finset.card_biUnion hdisj]
    have hconst : ∀ v ∈ fails A,
        (Finset.univ.filter (fun p : Equiv.Perm (I m h) => p.symm (0, 0) = v.1 ∧
          Finset.univ.filter (fun i => (p i).1 = 0) = v.2)).card =
        Nat.factorial (s - 1) * Nat.factorial (n - s) := by
      intro v hv
      have hv' := (Finset.mem_filter.mp hv).2
      exact card_fiber v.1 v.2 hv'.1 hv'.2.1
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
  let BadHit := BadPerms \ miss
  let Out : Finset (Fin k × Equiv.Perm (I m h) × I m h) :=
    Finset.univ.filter (fun t => (t.2.1 t.2.2).1 ≠ 0 ∧ P t.1 (fun j => t.2.1 j) t.2.2 ≠ 0)
  have hOut_card : Out.card = outside := by
    dsimp only [Out, outside]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_filter]
  have hwit : ∀ p ∈ BadHit, ∃ t ∈ Out,
      (p t.2.2).1 = 0 ∧ p = shiftPerm (t.2.1 t.2.2).1 t.2.1 := by
    intro p hp
    have hpBad : p ∈ BadPerms := (Finset.mem_sdiff.mp hp).1
    have hpNotMiss : p ∉ miss := (Finset.mem_sdiff.mp hp).2
    have hhit : ∃ a : Fin k, P a (fun j => p j) = unit (p.symm (0, 0)) := by
      by_contra hnot
      push Not at hnot
      exact hpNotMiss (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩)
    obtain ⟨a, ha⟩ := hhit
    have hfail := (Finset.mem_filter.mp ((Finset.mem_filter.mp hpBad).2)).2.2.2 a
    have hdiff : ∃ i ∈ (cfg p).2, mask a i ≠ P a (fun j => p j) i := by
      by_contra hsame
      push Not at hsame
      apply hfail
      ext i
      simp only [Finset.mem_inter, Finset.mem_singleton]
      constructor
      · rintro ⟨hiA, hiS⟩
        have hmi : mask a i = 1 := (Finset.mem_filter.mp hiA).2
        have hpi : P a (fun j => p j) i = 1 := by rw [← hsame i hiS, hmi]
        rw [ha] at hpi
        dsimp only [unit] at hpi
        by_contra hne
        have hne' : i ≠ p.symm (0, 0) := hne
        simp only [hne', ↓reduceIte] at hpi
        exact zero_ne_one hpi
      · rintro rfl
        have hrS : p.symm (0, 0) ∈ (cfg p).2 := by
          simp [cfg]
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hrS⟩
        rw [hsame _ hrS, ha]
        simp [unit]
    obtain ⟨i, hiS, hne⟩ := hdiff
    have hpi0 : (p i).1 = 0 := (Finset.mem_filter.mp hiS).2
    have hsum := hmask a p i
    rw [← Finset.add_sum_erase Finset.univ (fun g : U m => P a (fun j => shiftPerm g p j) i) (Finset.mem_univ 0)] at hsum
    have hp0 : shiftPerm 0 p = p := by ext x <;> simp [shiftPerm]
    rw [hp0] at hsum
    have hnz_sum : (∑ g ∈ Finset.univ.erase (0 : U m), P a (fun j => shiftPerm g p j) i) ≠ 0 := by
      intro hz
      rw [hz, add_zero] at hsum
      exact hne hsum.symm
    obtain ⟨g, hg_er, hgnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz_sum
    have hg0 : g ≠ 0 := (Finset.mem_erase.mp hg_er).1
    let q := shiftPerm g p
    have hqi : (q i).1 = g := by
      change (p i).1 + g = g
      rw [hpi0, zero_add]
    refine ⟨(a, q, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hgnz⟩, hpi0, ?_⟩
    · rw [hqi]; exact hg0
    · rw [hqi]; exact (shiftPerm_invol g p).symm
  have hBadHit_le : BadHit.card ≤ Out.card := by
    let f : {p // p ∈ BadHit} → {t // t ∈ Out} := fun p =>
      ⟨Classical.choose (hwit p.1 p.2), (Classical.choose_spec (hwit p.1 p.2)).1⟩
    have hf_inj : Function.Injective f := by
      intro p1 p2 heq
      have h1 := (Classical.choose_spec (hwit p1.1 p1.2)).2.2
      have h2 := (Classical.choose_spec (hwit p2.1 p2.2)).2.2
      have ht : Classical.choose (hwit p1.1 p1.2) = Classical.choose (hwit p2.1 p2.2) :=
        congrArg Subtype.val heq
      apply Subtype.ext
      rw [h1, h2, ht]
    calc BadHit.card = Fintype.card {p // p ∈ BadHit} := (Fintype.card_coe BadHit).symm
      _ ≤ Fintype.card {t // t ∈ Out} := Fintype.card_le_of_injective f hf_inj
      _ = Out.card := Fintype.card_coe Out
  have hsplit : BadPerms.card ≤ miss.card + BadHit.card := by
    have hsub : BadPerms ⊆ miss ∪ BadHit := by
      intro p hp
      by_cases hm : p ∈ miss
      · exact Finset.mem_union_left _ hm
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp, hm⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le miss BadHit)
  rw [← hBad_card, ← hOut_card]
  omega

private theorem part2 (m h k : Nat) :
    let s := 2 ^ h
    let fails := fun (A : Fin k → Finset (I m h)) =>
      (Finset.univ : Finset (I m h × Finset (I m h))).filter (fun v =>
        v.1 ∈ v.2 ∧ v.2.card = s ∧ ∀ a, A a ∩ v.2 ≠ {v.1})
    let miss := fun (P : Fin k → W m h → V m h) =>
      (Finset.univ : Finset (Equiv.Perm (I m h))).filter (fun p =>
        ∀ a, P a (fun i => p i) ≠ unit (p.symm (0, 0)))
    let outside := fun (P : Fin k → W m h → V m h) =>
      ∑ a : Fin k, ∑ p : Equiv.Perm (I m h),
        ((Finset.univ : Finset (I m h)).filter (fun i => (p i).1 ≠ 0 ∧ P a (fun j => p j) i ≠ 0)).card
    (∃ P, (∀ a, low (P a)) ∧ (miss P).card = 0 ∧ outside P = 0) ↔
      ∃ A : Fin k → Finset (I m h), (fails A).card = 0 := by
  classical
  intro s fails miss outside
  constructor
  · rintro ⟨P, hP, hmiss, hout⟩
    obtain ⟨A, hA⟩ := part1 m h k P hP
    change Nat.factorial (s - 1) * Nat.factorial (2 ^ m * s - s) * (fails A).card ≤
      (miss P).card + outside P at hA
    rw [hmiss, hout] at hA
    have hpos : 0 < Nat.factorial (s - 1) * Nat.factorial (2 ^ m * s - s) :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    have hzero : (fails A).card = 0 := by
      by_contra hne
      have h1 : 1 ≤ (fails A).card := Nat.pos_of_ne_zero hne
      have h2 : Nat.factorial (s - 1) * Nat.factorial (2 ^ m * s - s) ≤
          Nat.factorial (s - 1) * Nat.factorial (2 ^ m * s - s) * (fails A).card :=
        Nat.le_mul_of_pos_right _ h1
      omega
    exact ⟨A, hzero⟩
  · rintro ⟨A, hA⟩
    let ind0 : W m h → I m h → ZMod 2 := fun x i => ∏ u : Fin m, (1 + (x i).1 u)
    let P : Fin k → W m h → V m h := fun a x i => if i ∈ A a then ind0 x i else 0
    have hind0_val : ∀ (x : W m h) (i : I m h), ind0 x i = if (x i).1 = 0 then 1 else 0 := by
      intro x i
      dsimp only [ind0]
      by_cases h0 : (x i).1 = 0
      · simp [h0]
      · simp only [h0, ↓reduceIte]
        have hex : ∃ u : Fin m, (x i).1 u ≠ 0 := by
          by_contra hall
          push Not at hall
          exact h0 (funext hall)
        obtain ⟨u, hu⟩ := hex
        apply Finset.prod_eq_zero (Finset.mem_univ u)
        generalize (x i).1 u = b at hu ⊢
        fin_cases b
        · exact absurd rfl hu
        · decide
    refine ⟨P, ?_, ?_, ?_⟩
    · intro a i
      by_cases hi : i ∈ A a
      · let emb : Finset (Fin m) → Finset (J m h) := fun S => S.image (fun u => (i, Sum.inl u))
        have hemb_inj : Function.Injective emb := by
          intro S1 S2 heq
          ext u
          have h1 := congrArg ((i, Sum.inl u) ∈ ·) heq
          simp only [emb, Finset.mem_image, Prod.mk.injEq, true_and, Sum.inl.injEq, exists_eq_right] at h1
          exact eq_iff_iff.mp h1
        refine ⟨(Finset.univ : Finset (Fin m)).powerset.image emb, ?_, ?_⟩
        · intro mon hmon
          obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hmon
          calc (emb S).card ≤ S.card := Finset.card_image_le
            _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ S
            _ = m := Fintype.card_fin m
        · intro x
          simp only [P, hi, ↓reduceIte, ind0]
          rw [Finset.prod_one_add, Finset.sum_image (fun S1 _ S2 _ heq => hemb_inj heq)]
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [Finset.prod_image (fun u1 _ u2 _ heq => Sum.inl.inj (Prod.mk.inj heq).2)]
          refine Finset.prod_congr rfl fun u _ => ?_
          simp [bit]
      · refine ⟨∅, by simp, fun x => by simp [P, hi]⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro p _ hnot
      let r := p.symm (0, 0)
      let S := Finset.univ.filter (fun i : I m h => (p i).1 = 0)
      have hrS : r ∈ S := by simp [S, r]
      have hScard : S.card = s := by
        have hT0 : (Finset.univ.filter (fun y : I m h => y.1 = 0)).card = s := by
          have heq : Finset.univ.filter (fun y : I m h => y.1 = 0) =
              Finset.univ.image (fun v : H h => ((0 : U m), v)) := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · intro hy; exact ⟨y.2, Prod.ext hy.symm rfl⟩
            · rintro ⟨v, rfl⟩; rfl
          rw [heq, Finset.card_image_of_injective _ (fun a b hab => congrArg Prod.snd hab),
            Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
        rw [← hT0]
        refine Finset.card_bij (fun i _ => p i) ?_ ?_ ?_
        · intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
        · intro i1 _ i2 _ heq; exact p.injective heq
        · intro y hy
          refine ⟨p.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, p.apply_symm_apply y⟩
          rw [p.apply_symm_apply]; exact (Finset.mem_filter.mp hy).2
      have hnot_fail : (r, S) ∉ fails A := by
        rw [Finset.card_eq_zero] at hA
        rw [hA]; exact Finset.notMem_empty _
      have hexA : ∃ a : Fin k, A a ∩ S = {r} := by
        by_contra hall
        push Not at hall
        exact hnot_fail (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrS, hScard, hall⟩)
      obtain ⟨a, ha⟩ := hexA
      apply hnot a
      funext i
      dsimp only [P, unit]
      rw [hind0_val]
      by_cases hi0 : (p i).1 = 0
      · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi0⟩
        have hmem : i ∈ A a ↔ i = r := by
          have := congrArg (i ∈ ·) ha
          simpa [hiS] using this
        simp only [hi0, ↓reduceIte]
        by_cases hir : i = r
        · have hiA : i ∈ A a := hmem.mpr hir
          have hir' : i = p.symm (0, 0) := hir
          rw [if_pos hiA, if_pos hir']
        · have hni : i ∉ A a := fun h1 => hir (hmem.mp h1)
          have hir' : i ≠ p.symm (0, 0) := hir
          rw [if_neg hni, if_neg hir']
      · have hne : i ≠ p.symm (0, 0) := by
          intro heq; subst heq; exact hi0 (by simp)
        simp [hi0, hne]
    · dsimp only [outside]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun p _ => ?_
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ h
      have hne0 := h.1
      apply h.2
      dsimp only [P]
      rw [hind0_val]
      simp [hne0]

end PEqualNP.Outside.L_lib_734_aux

theorem PEqualNP.Outside.L_lib_734 : (∀ (m h : Nat),
  let K := ZMod 2
  let U := Fin m → K
  let H := Fin h → K
  let I := U × H
  let W := I → I
  let V := I → K
  let J := I × (Fin m ⊕ Fin h)
  let s := 2^h
  let n := 2^m*s
  let bit := fun (x : W) (j : J) => Sum.elim (x j.1).1 (x j.1).2 j.2
  let low := fun (P : W → V) => ∀ i, ∃ T : Finset (Finset J),
    (∀ mon ∈ T, mon.card ≤ m) ∧ ∀ x, P x i = ∑ mon ∈ T, ∏ j ∈ mon, bit x j
  let unit := fun (i j : I) => if j = i then (1 : K) else 0
  let fails := fun (k : Nat) (A : Fin k → Finset I) =>
    (Finset.univ : Finset (I × Finset I)).filter (fun v =>
      v.1 ∈ v.2 ∧ v.2.card = s ∧ ∀ a, A a ∩ v.2 ≠ {v.1})
  ∀ k : Nat,
    let miss := fun (P : Fin k → W → V) =>
      (Finset.univ : Finset (Equiv.Perm I)).filter (fun p =>
        ∀ a, P a (fun i => p i) ≠ unit (p.symm (0,0)))
    let outside := fun (P : Fin k → W → V) =>
      ∑ a : Fin k, ∑ p : Equiv.Perm I,
        ((Finset.univ : Finset I).filter (fun i => (p i).1 ≠ 0 ∧ P a (fun j => p j) i ≠ 0)).card
    (∀ P, (∀ a, low (P a)) → ∃ A : Fin k → Finset I,
      Nat.factorial (s-1) * Nat.factorial (n-s) * (fails k A).card ≤
        (miss P).card + outside P) ∧
    ((∃ P, (∀ a, low (P a)) ∧ (miss P).card = 0 ∧ outside P = 0) ↔
      ∃ A : Fin k → Finset I, (fails k A).card = 0)) := by
  intro m h K U H I W V J s n bit low unit fails k miss outside
  exact ⟨PEqualNP.Outside.L_lib_734_aux.part1 m h k, PEqualNP.Outside.L_lib_734_aux.part2 m h k⟩
